# L2 Staging

## Code

`L2.code.value` A Code value holds a Core term (its *body*). Locals bound
inside it have unique names; it may have free locals only while it is being
constructed (below).

## Links

`L2.link.late` `{:kind :late :name q}` resolves `q` in the effective world
of the context in which the code runs.

`L2.link.pinned` `{:kind :pinned :world w :name q}` resolves `q` in `w`, as
`(world/get w 'q)` does, regardless of context.

`L2.link.guarded` `{:kind :guarded :name q :generation g :value v}` means
the same as the late link to `q`. An implementation may use `v` when `q` has
generation `g` in the effective world.

## Construction

`L2.code.build` `(code e)` evaluates to Code for `e`. Each local bound
inside `e` is renamed to a fresh name. Globals in `e` become late links.

`L2.code.csp` A local bound *outside* `(code e)` at the present stage and
used inside `e` is lifted: the Code contains its value as a constant.

`L2.esc.splice` `(esc g)` inside `(code e)` evaluates `g` at the present
stage when the Code is constructed. Its value must be Code
(`L2.esc.not-code` otherwise), whose body replaces the `esc` form.

`L2.code.recur` A `recur` in a fragment, `(code (recur ..))` built in a
hole of a template's `loop` (or `fn`), re-enters that loop: like a local of
the template, the loop it names is renamed with each instantiation, and the
fragment counts as using it (L2.code.extrusion).

`L2.esc.not-code` The generator in `esc` returned something other than Code.

`L2.esc.level` `esc` outside `code` is rejected at expansion.

`L2.stage.level` A local bound inside `code` (a future-stage local) used at
the present stage, for example directly inside an `esc` without an inner
`code`, is rejected at expansion; so is a `recur` whose loop or function is
of another stage than the `recur`.

`L2.code.extrusion` When `(code e)` completes, every free local of its result
must be bound by a `code` construction that is still in progress on the
continuation (its dynamic extent), or by a binder constructor in progress
(L2.code.binders), or be a future-stage variable in scope. The extent
includes host code: a Klara function that host code calls back (through
`apply`, `mapv`, ...) is inside the construction its host call is inside.
Otherwise construction fails: some future-stage local escaped its binder.
Code that escapes through a mutable cell and is run later is caught by
`L2.run.closed`. This is a dynamic check in the sense of Lee et al.,
POPL 2026 ([related work](../design/related-work.md#staging)).

## Lift

`L2.lift.values` `(lift v)` returns Code whose evaluation yields `v`.
Allowed values: immutable data (recursively), closures, host functions,
worlds, Code and candidates.

`L2.lift.mutable` Lifting a mutable host object, or a collection containing
one, is rejected. `(klara.stage/liftable? x)` tells whether `x` can be
lifted.

`L2.lift.preserves` `(run (lift v))` yields `v` itself, in every context.

## Run

`L2.run.closed` `(run c)` requires Code without free locals.

`L2.run.context` `(run c)` evaluates the body of `c` in the current context
(`E`, `m`). It does not compile.

## Reify

`L2.reify.fn` `(reify f)` for a closure returns Code `(fn ...)` with the
closure's arities. Its captured locals are lifted. If the closure has no
basis, its globals become late links; if it has basis `w`, they become
links pinned to `w`.

`L2.reify.host` `(reify f)` for a host function returns `(lift f)`.

`L2.reify.preserves` `(run (reify f))` behaves as `f` in every context.

## Views and printing

`L2.view.total` `code/view` has a view for every construct: `:const`,
`:local`, `:host`, `:global`, `:app`, `:let` (with `:tag`, its host hint, if
it has one), `:if`, `:do`, `:recur`, `:fn`
(`:self` and `:arities`, each `{:params :rest :body}`; a function with one
fixed arity also shows `:params` and `:body`), `:letrec` (`:bindings` of
name and function), `:throw`, `:try` (`:body`, `:catches` of class, name
and body, `:finally`), `:interop`, `:def`, `:code` (`:template`, `:holes`)
and `:hole`. `code/make` builds each back from its view.

`L2.code.binders` `(code/fn* n f)` returns code for `(fn self [p1 .. pn]
body)` with fresh names, where `body` is `(f self p1 .. pn)` called with
each as Code. `(code/loop* inits f)` returns code for a loop with fresh
variables, one per initial value, whose body is `(f [v1 .. vn] recur)`;
`(recur a1 .. an)` returns code that recurs to that loop. While `f` runs its
names count as bound (L2.code.extrusion). A body function that returns
something other than Code, or a recur with the wrong number of arguments,
raises this rule.

`L2.view.unfold` `(code/unfold c)` for Code of a global link (or a lifted
closure) returns Code for the function it denotes, with fresh binders: for
a late link the definition's function, also when compiled code is
installed for it; otherwise nil.

`L2.view.known` `(code/known c)` returns Code for the value of a constant
or of a global defined as immutable data (L4.check.delta-data), else nil.
`(code/pure-host? c)` tells whether `c` is a host function the checker may
evaluate on constants (L4.check.prim).

`L2.view.free` `(code/free c)` returns the names of the locals free in `c`
(those a substitution may replace), sorted.

`L2.view.children` `(code/children c)` returns the direct subterms of `c`
as Code, in evaluation order; `(code/with-children c cs)` returns `c` with
them replaced (same count), keeping what `c` binds. Together they let Klara
code walk and rebuild every construct, including loops.

`L2.view.make` `(code/view c)` returns the top of `c`'s term as a map with Code
values in place of subterms; `(code/make m)` is its inverse. Guest
recipes use these to inspect and build Code.

`L2.print.form` Code prints as `#klara/code <form>`. Late links print as their
qualified symbol, pinned links as `(klara/at <world-id> <symbol>)`, guarded
links as `(klara/guarded <symbol> <generation>)`, non-literal constants as
`(klara/const <printed value>)`.

## Planned

`L2.genlet.restricted` (planned) Let-insertion: binding a generated expression at an
outer code construction point. It will be restricted to expressions that
cannot fail, diverge or perform effects.
