# Profiles: authority, exceptions, continuations and erasure

Status: the run-time rules and the declared judgment's clauses below are
implemented (L3.cont.context, L3.job.resumed, L4.check.affine clauses 1–7
and its `try` rule); the accounting calculus λ-acct is in
`spec/formal/src/klara/formal/acct*.clj` with conservation, preservation,
progress without reuse and check erasure proved, and a differential test
against the runtime (Plan, at the end); compiling declared code
and `try` compile (L4.check.affine-erase, L4.lower.try). This note settles how the affine segment of Klara (design/04,
design/10) behaves under exceptions, copied continuations and effects, and
how its claims are made checkable.

## The story

1. **Meaning is dynamic and total.** The CEK machine (worlds, multi-shot
   handlers, jobs, a tree of wallets) defines every program. Misused
   authority is a named error where it is used: `L3.affine.reuse`,
   `L3.account.foreign`, `L3.account.insufficient`. Conservation (minted =
   held + live + spent, every receipt balanced) holds for every program,
   typed or not.
2. **Static judgments are admission rules.** They never change what a
   program means; they let the compiler drop a check or change a
   representation, each with an erasure theorem (equal observations). One
   threading judgment (L4.check.affine) has two erasures: owned collections
   become transients (design/04), and account tokens lose the reuse check
   (design/10).
3. **Confidence, stated per claim.** Proved in ansatz: the core model's
   theorems (spec/formal/README.md), and in the separate accounting
   calculus λ-acct conservation and affine soundness. Tested: that the CEK
   machine refines the models, and that compiled code refines the
   interpreter (differential, deopt-stress and adversarial tests).

Two slogans carry it: **continuations copy control, not authority**, and
**job outcomes are affine handles, continuations are multi-shot**.

## What a continuation copies

A continuation is the captured frames with the world and mint at capture
(`machine.clj`, `Continuation`); resuming it runs them with the
**resumer's** dynamic context: step meter, wallet, default handlers, job
(L3.cont.context). Read as a CESK machine, a continuation captures control
and values, never the store:

| on re-execution | what happens |
|---|---|
| data, closures | shared; they are persistent |
| owned collections | never present: the interpreter only holds persistent values (design/04) |
| world | the captured one is restored, so reads repeat; `def` goes to the resumer's context |
| steps, `spend!`, `take` | charged to the resumer, every time it resumes |
| printing, intents | performed again |
| host objects | shared (the heap is not copied; the `:fresh` caveat of L4.facts.effect) |
| tokens | the copies share the reference; the second consumption raises L3.affine.reuse |

A token in a frame is a reference to a wallet entry, and wallets are never
copied, so **copying cannot create authority**: it is conservation, and it
needs no typing. Programs that copy and need authority have three
patterns: spend from the resumer's ambient wallet; hand tokens through the
effect (the handler gives each resumption its own, and can only give what
it holds); or run each branch as a job with its own budget, forked world
and receipt.

Job outcomes are different: `job/resume` continues the job against its one
record (intents, world, adoption), so an `:exhausted` outcome is resumed at
most once (L3.job.resumed), as it is adopted at most once (L3.job.adopted).
This is spindel's `ForkHandle`: settled exactly once.

## Exceptions

Rust has no exceptions: recoverable errors are `Result` values with `?`,
and `panic!` unwinds, running `Drop` for the values it passes, unless
`panic = "abort"`; `catch_unwind` stops it at a boundary. Rust promises
"at most once": `mem::forget` is safe. Klara takes the same position and
adds a boundary where it is stronger:

- **A raise does not return tokens.** It drops frames; the tokens they held
  stay live and go back when their job settles (L3.account.settle). This
  is the backstop Cyclone (regions), Alms (affine with a collector) and
  Linear Haskell (its resource monad) rely on. Conservation holds without
  put-back on unwind; put-back would only make the return prompt. If it is
  added later it must be `put` itself (it consumes the id), never erased,
  and assigned by which frame holds the token, not where it was taken.
- **`try` in declared code follows `catch_unwind`.** The body may read and
  consume the tokens live before it; those it may consume are unavailable
  after the `try` on both paths (on the handler path the raise point is
  unknown); the `try` gives no token; catch and finally arms only read the
  tokens the body leaves live (L4.check.affine). Tagged results (`[:ok t]`)
  that return authority from fallible code need sum kinds and are left
  out: a job does that (its receipt returns what is left).
- A handler that discards a continuation does not run its `finally`
  (L0.eval.exception): that is `mem::forget`, and settlement is the
  backstop.

## Effects: control-flow linearity

A continuation is multi-shot, so a token live in a frame that a handler
captures could be used once per resumption. Tang, Hillerström, Lindley and
Morris (*Soundly Handling Linearity*, POPL 2024) call this control-flow
linearity. Klara's declared judgment refuses a live token (owned, borrowed
or in a pair) at every place where the computation may be captured: a
`perform`, a `def`, an intrinsic that may perform, a call of a function it
cannot see, and a call of a definition whose effect class
(L4.facts.effect) is above `:shared` or relative to its arguments
(clause 7). Host calls cannot capture (L3.effect.host-boundary), and
neither can `job/run`, since a job frame stops effect search. The callees'
effect facts are the declaration's `:premises`; redefining a callee
invalidates admitted code (L4.check.premises), and until code is admitted
nothing relies on them (the dynamic checks stay). Marking operations as
resumed at most once would relax the rule later.

So in declared code, continuations hold no tokens, and copying them is
always safe. Outside declared code the dynamic check is the rule.

## Profiles

A profile is a declared subset with a stated mapping from an established
programming model. Acceptance is the judgment plus a syntactic subset; that
every accepted definition compiles is a tested obligation of the compiler
(so compiler limits never become language rules, and acceptance does not
change as the compiler grows). The first is the **affine profile**, with
Rust as its reference mapping:

| Rust | Klara |
|---|---|
| move, `&mut` (threaded), `&` | `^:own`, threading, `^:borrow` |
| `Drop`, also on panic | `put`; job settlement puts back what a raise skipped |
| `Result`, `?` | data and a macro |
| `panic!`, `catch_unwind` | `throw`, `try` (the rule above) |
| `FnOnce` closures | planned: a closure capturing tokens is itself a token |
| `Vec<u8>`, slices | planned: primitive arrays as tokens (design/04) |
| `async`, generators | one-shot handlers, compiled as state machines (planned) |
| threads, `Send` | jobs, `run-all`, token budgets |
| `unsafe` | trusted host interop |

Klara has no lifetimes, reborrows or user `Drop`; the name is "affine
profile" for that reason.

## The accounting calculus λ-acct

The core formal model (`core.clj`) stays the specification of Klara Core;
nothing that only the affine story needs goes into its configurations. Each
new core constructor touches about twelve definitions plus the staging
forms. λ-acct is a calculus of its own (`acct.clj`): functions, `let`,
`if`, tokens over one resource (`take`, `spend`, `join`, `put`), deep
handlers by operation name as in core (multi-shot), `raise` and `try`. A
configuration is a store (wallet, spent, next id, live tokens) and a term;
`ev` takes a flag, checked (Klara's semantics) or with the reuse check
erased.

The judgment (`acct_typing.clj`) is simply typed (data, tokens, functions
with a latent effect flag) with two kinds of premise that make it affine:
linearity at binders (a token variable occurs at most once on every path),
and token-freedom where a computation may be captured (function bodies,
handler clauses, and the rest of a term while one part may perform). They
correspond to the declared judgment's clauses:

| L4.check.affine | λ-acct |
|---|---|
| 1 tokens come from operations, declared calls, `^:own` | the token type; `take`, `spend`, `join` give one |
| 2 consumed at most once | linearity premise at binders (occurrences, larger branch of `if`) |
| 3 branches agree | not needed: the calculus is affine, branches may differ |
| 4 no capture, no storing | token-free function bodies and handler clauses; `raise` and `perform` take data |
| 5 declared calls | function types with token parameters |
| 6 none dropped | not needed for soundness (a diagnostic) |
| 7 none live at capture points | the effect flag and the token-free premises on the context |
| `try` | the body and the handler share no token (occurrences add up) |

Klara's judgment is stricter than the calculus (it adds clauses 3 and 6),
so every definition it accepts maps to a typed term.

Theorems, in order:

1. `Acct.conservation`: every step of every term keeps minted = wallet +
   spent + held in live tokens. Untyped, so copying continuations any
   number of times cannot mint.
2. `Acct.preservation`: a typed configuration with the invariant (every
   token id occurs at most once, every id that occurs is live, live ids are
   below the next id) steps to a typed configuration with the invariant.
3. `Acct.progress`, `Acct.no-reuse`: such a configuration is a value,
   steps, performs an unhandled effect, raises, or is stuck, but never on
   reuse or a free variable.
4. `Acct.erasure`: configurations with the invariant step the same with the
   reuse check erased; with preservation, so does every configuration a
   typed program reaches.

All four are proved (about 2,500 lines of ansatz, `clojure -M:formal:test-formal`).
Erasure needs only the invariant, not typing: the judgment's job is to keep
the invariant, and the invariant is what makes the check redundant.

Tested, not proved: that Klara's runtime agrees with λ-acct on generated
token programs (`acct_differential_test.clj`, through `acct_bridge.clj`, as
core is linked to the CEK machine), and that compiled declared code agrees
with the interpreter.

## Plan (P11 in design/PLAN.md)

1. [x] Soundness fixes in the judgment (the `try` rule, clause 7, parts of
   other forms giving tokens), outcomes resumed once, L3.cont.context.
2. [x] This note and the spec rules.
3. [x] λ-acct: syntax and step, conservation, the typing judgment and the
   invariant, preservation, progress, no-reuse, erasure; the differential
   test against the runtime.
4. [x] `try` in compiled code (L4.lower.try): a leave from inside a `try`
   adds an interpreter frame carrying its catch and finally clauses; tested
   with leaves from the body and from a catch arm, and under deopt stress.
5. [x] Compiling declared code at definition (L4.check.affine-erase), with
   the declaration's premises; the affine profile's obligation tested on
   generated programs (every accepted definition compiles and agrees with
   the interpreter). Skipping the reuse check needs unboxed tokens, which
   belong to the bytecode backend.

Later: closures that capture tokens as tokens (`FnOnce`), operations
marked one-shot, tail-resumptive handlers compiled as calls, arrays as
tokens, re-homing tokens on resume, several resources and the wallet tree
in λ-acct.
