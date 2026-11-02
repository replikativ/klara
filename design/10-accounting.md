# Accounting: graded tokens at boundaries

Status: vectors, wallets, tokens, settlement and receipts are implemented
(`klara.runtime.account`, `lib/klara/account.clj`, L3.account.*), with a
randomized conservation test (`test/klara/account_test.clj`) and a
showcase (`showcases/accounting.clj`). The declared mode (`defaffine`,
L4.check.affine) checks threaded tokens at definition
(`klara.compile.affine`); compiling declared code with the checks erased,
and the formal semantics, are planned (Plan, at the end). It answers how Klara accounts for more
than memory: time, money, model calls, connections, licences, evidence,
with one small mechanism that composes with kontor's double-entry
accounting at boundaries.

## The question

A running Klara program spends resources: steps, wall time, money for
model calls, slots of a connection pool. Some are consumed (money spent is
gone), some are held and given back (a connection), some may be held by one
user at a time (a writer) or by up to k at once (k readers). Programs need
to pass the right to spend or hold explicitly to the code they call, and
the system needs to account honestly: what was granted, spent and returned,
by whom, and that nothing was spent twice.

Klara's sibling systems already agree on the shape (spindel, kontor,
dvergr):

- **Forks never copy or split authority.** A spindel fork is state; its
  `ForkHandle` is a process-local token that settles the fork exactly once.
  A dvergr child Run receives resources only by one governed kontor
  transfer from its parent's wallet.
- **Quantities live in a ledger with a non-negative cone.** kontor's
  resource vectors (ADR-171) are balances over (account × commodity);
  `mint`, `grant`, `consume` and `return` are balanced transfers with
  receipts, and no wallet may go negative.
- **Settlement replays intents with footprints** (kontor ADR-172), and the
  live token never crosses: what crosses is a descriptor or a receipt.

Klara adopts this shape and adds what a language can give: the tokens are
values the program threads, a judgment can check the threading statically,
and the boundaries are the ones the memory model already has (jobs and the
session, 01-lifetimes.md, 04-ownership.md).

## One algebra

A **resource vector** is a finite map from resource names (keywords) to
exact non-negative amounts (integers, ratios or decimals; floating point is
refused), as kontor's are (`L3.account.vector`). Vectors add pointwise; `v
≤ w` pointwise; `w − v` is defined when `v ≤ w`. This one algebra (the cone
of a free commutative monoid, a partial commutative monoid in the sense of
separation logic) covers every kind the prototype had separate rules for:

| kind | as a vector | operation that uses it |
|---|---|---|
| a consumable quantity (steps, ns, money, model dispatches) | `{:eur 5/2}` | spend: moved to the sink, never returned |
| k-reader permission (a pool of 8 connections, 3 licence seats) | `{:db 8}` minted once; a reader holds `{:db 1}` | hold: `holds?` requires an amount, nothing is consumed; the token is returned later |
| exclusive permission (a writer) | holding all `k` units of it | hold the full amount |
| fractional permission (Boyland) | ratios of 1 unit | hold a fraction to read, `1` to write |

Counting permissions (Bornat, Calcagno, O'Hearn, Parkinson, *Permission
accounting in separation logic*, POPL 2005) are the second and third rows;
the cardinality of a read permission is just how many units were minted. A
resource has no declared kind: whether it is consumed or held is what the
program does with it, and both are accounted by the same ledger.

## Wallets at boundaries

Every activation context has a **wallet** (`L3.account.wallet`): the session
has the root wallet, and every job has its own. The job's `:budget` is a
resource vector (or a token, below) **reserved from the parent's wallet**
when the job starts, exactly as steps are reserved today
(L3.budget.nesting, which becomes the `:steps` instance of this rule).
`:steps` stays metered by the machine on every application and `recur`
(L3.budget.steps); other resources are spent by the program.

Only the session mints (`(account/mint! v)`, `L3.account.mint`); inside a
job minting raises that rule, so a job can never create authority.
Spending from the current wallet is `(account/spend! v)`; spending more
than the wallet holds raises `L3.account.insufficient` and spends nothing.

When a job ends, whatever its status (`L3.account.settle`):

1. every live token taken inside the job goes back to the job's wallet;
2. what the job spent is charged to the parent (it is not refunded when the
   outcome is discarded, as for steps today);
3. what is left in the job's wallet returns to the parent's wallet.

The outcome carries a **receipt** (`L3.account.receipt`): an id, the
granted, spent and returned vectors, and the postings that realize them,
shaped as kontor transfers:

```clojure
{:id #uuid "…" :granted {:steps 1000 :eur 2} :spent {:steps 412 :eur 1/2}
 :returned {:steps 588 :eur 3/2}
 :postings [{:kind :grant   :source :parent :destination :job :resources {:steps 1000 :eur 2}}
            {:kind :consume :source :job    :destination :sink :resources {:steps 412 :eur 1/2}}
            {:kind :return  :source :job    :destination :parent :resources {:steps 588 :eur 3/2}}]}
```

These postings are what composes with kontor: an embedding (dvergr) posts
a job's grant when it starts and its consume and return when it settles,
through `kontor.resource/allocate!`, `consume!` and `return!`, with the
receipt id as the transfer id. Klara keeps the same algebra in memory so
that the step meter costs nothing more than today; kontor is the durable
ledger at the boundary, not on every step.

**Conservation** (`L3.account.conservation`). For the session at any point
between steps: minted = held in wallets + held in live tokens + spent,
for every resource. A job's receipt satisfies granted = spent + returned.
This is checked by a randomized test over mint, spend, take, split, join,
put, nested jobs with vector and token budgets, discard, resume and host
callbacks that run out of steps (as the prototype's AU6 did for evidence),
after every top-level form and for every receipt; it is a theorem target
for the formal semantics.

Two consequences of where wallets live. The session has no step budget, so
its steps are unlimited and not accounted; steps are accounted per job, in
receipts. And a wallet is not part of the job's record: when a host call is
abandoned and its job's record is rolled back, what it spent stays spent.

## Tokens: the affine segment

A **token** holds a resource vector taken out of the current wallet
(`(account/take v)`, `L3.account.token`). Tokens are how a program passes
the right to spend or hold explicitly to the code it calls, instead of
relying on the ambient wallet. A token is used linearly, in the threaded
style of 04-ownership.md: every operation that changes it consumes it and
returns the next one.

| form | consumes | returns |
|---|---|---|
| `(account/take v)` | `v` from the current wallet | a token holding `v` |
| `(account/spend t v)` | `t` | the next token, holding `t − v`; `v` goes to the sink |
| `(account/split t v)` | `t` | `[t1 t2]` holding `v` and `t − v` (`L3.account.split`) |
| `(account/join t1 t2)` | `t1`, `t2` | a token holding their sum |
| `(account/put t)` | `t` | nil; its vector goes back to the current wallet |
| `(account/holds? t v)` | nothing | whether `t` holds at least `v` (`L3.account.holds`) |
| `(account/balance t)` | nothing | the vector `t` holds, as plain data |

`balance` is the token's freeze: the copyable image of a token is a
statement, which carries no right to spend. Freezing never turns a token
into authority that can be copied; that would mint.

**Checked at use** (`L3.affine.reuse`). Using a token that an operation
already consumed raises `L3.affine.reuse`, however the second use reached
it: a second local, a collection, a closure, a definition, or a
continuation resumed twice. Continuations stay multi-shot
(L3.cont.multishot): resuming one twice is allowed, and only the second
*use* of a consumed token fails. Tokens are not data: `lift` refuses them
(L2.lift.mutable), and they compare by identity.

**Tokens belong to their job** (`L3.account.foreign`). A token taken in a
job can be used only in that job; using it in another job (or in the
parent after the job ended, when settlement has put it back) raises
`L3.account.foreign`. A token taken at the session lives until it is put
back, since the session never settles. The one way a token crosses a boundary is a move:
`(job/run {:budget t} thunk)` consumes `t`, and its vector becomes the
job's grant. This is the dvergr rule (a child receives resources only by
one transfer from its parent) in the language.

**Statically** (`L4.check.affine`). In a `defaffine` definition tokens
follow the ownership judgment of 04-ownership.md (rules 1–6), checked when
the definition is made, which proves each token is used at most once on
every path; a definition that fails is not defined, and the diagnostic
names the clause, the place and the local. Today the definition still runs
with the dynamic checks; compiled code admitted under the judgment will
skip the reuse check (L4.check.affine-erase, planned). Unlike owned collections,
an account operation is not erased: spending is the meaning. What the
judgment erases is the check, so the theorem is: for a program that passes
the judgment, the program with checks and the program without them have
the same observations (the check never fires). Proving bounds (that a
`spend` never makes a token negative) is a further, optional step in the
style of amortized resource analysis; it would erase the cone check too.

## Expressiveness: established systems as tokens

| system | in Klara |
|---|---|
| Rust: owned `T`, move | an owned collection or a token, `^:own` parameter |
| Rust: `&mut T` | the token threaded through the callee and returned (reborrowing is the same) |
| Rust: `&T` | `^:borrow`: read-only and not passed on except as a borrow (L4.check.affine); for a collection the callee reads a value, for a token the token itself |
| Rust: `Copy` | data |
| Rust: `Drop` | `put` at the end of the scope; a job puts every live token back when it settles |
| Rust: `Rc`/`Arc`, `RefCell` | counting permissions checked at run time (the dynamic check is always there in the interpreter) |
| Rust: `Send` / `Sync` | a token moves into a job only as its budget / data is shared |
| Rust: lifetimes | job scopes and lexical regions; named lifetimes are not needed while borrows are snapshots |
| Pony `iso` / `val` / `box` / `tag` | exclusive token / data / read permission / the zero vector (identity only) |
| Linear Haskell, QTT (multiplicities 0, 1, ω) | the zero vector, a token, data |
| Granule (graded modalities over semirings) | grades are vectors; Granule's types would be the static version |
| Austral (linear: must consume) | settlement: every token is consumed or put back when its job settles |
| kontor resource vectors | the same algebra; postings at job boundaries |
| spindel `ForkHandle` | a job outcome, adopted at most once (L3.job.adopted) |

What is not covered yet: a shared borrow of a live mutable array without
copying (needs a lexical borrow region with a suspended writer, planned
with arrays in 04-ownership.md), and outcomes that must be settled (today
dropping an outcome discards the job, as in an affine system).

## Where a ledger lives decides what discard means

The prototype had one split rule per authority kind; one question replaces
them. A ledger **outside the forks** (the wallets above, dvergr's control
store) records costs, which a discarded job does not undo. A ledger
**inside the world** (data a job defines, such as evidence weights or a
kontor book in a speculative world) is dropped when the job is discarded
and merged by publication when it is adopted (L1.session.publish, which
like kontor's replay merges disjoint changes and reports overlapping ones
as conflicts). So budgets are charged and evidence is refunded on discard
without a rule for either.

## Plan

1. [x] Design and planned rules (this document, spec/L3-effects.md).
2. [x] Vectors and wallets: the session's root wallet, `mint!`,
   `spend!`, job budgets as vectors reserved from the parent, settlement
   and receipts; `:steps` as the metered instance.
3. [x] Tokens: `take`, `spend`, `split`, `join`, `put`, `holds?`,
   `balance`; dynamic reuse and foreign checks; `{:budget t}`.
4. [x] Conservation test; a showcase with a k-reader pool and a money
   budget passed to callees; the receipt mapped to kontor transfers
   (`klara.account/transfers`, data only: Klara does not depend on kontor).
5. [x] The declared mode (`defaffine`, L4.check.affine) for owned
   collections and tokens, checked at definition with diagnostics.
5b. [ ] Declared code compiled, with the reuse check erased in admitted
   code (L4.check.affine-erase).
6. [ ] Formal: vectors, wallets and tokens in the semantics; conservation
   and the check-erasure theorem.
