# 9. Redefinition under a running fiber: basis raise

**Demonstrates:** editing a definition at the REPL while a simulation is
in the middle of a run; the simulation keeps the version it started with
until it explicitly raises its basis at a safe point; old and new versions
coexist.

**Exercises:** fibers with a pinned basis and `:world/raise-basis`
(`doc/semantics.md` §7, reference handlers); gate R4 (old and new versions
coexist across pinned fibers, tested concurrently in `r4_test`); the
generator pattern of `doc/guide/03-effects.md` (a handler that does not
resume turns a running computation into a value).

**Runs on:** T0 with the world operations `:world/fiber` and
`:world/call-in` (`klara.defs`). The fiber here is not a separate thread:
"running" means a computation suspended at a `:yield`, which the REPL
resumes step by step. That makes the transcript deterministic. `r4_test`
does the same with real threads and a concurrent writer.

## A simulation that yields

`sim` performs one step per iteration. Between steps it yields its state
to whoever is driving it and receives a command. The step function is
looked up with `(perform :world/resolve 'step)`, which reads the *fiber's*
pinned basis. If the command is `:raise`, the fiber moves its pin to the
newest root before the next step. The yield is the safe point: a raise
never happens in the middle of a step.

```klara-repl
k=> (defn step [s] (+ s 1))
step
k=> (defn sim [g s]
      (let [cmd (perform g :yield s)]
        (when (= cmd :raise) (perform :world/raise-basis))
        (sim g ((perform :world/resolve 'step) s))))
sim
```

## Start it in its own fiber

`(perform :world/fiber)` creates a fiber over the session's world, pinned
at the current root. `:world/call-in` runs a function with that fiber
current. The handler answers `:yield` by returning the state and the
continuation instead of resuming, so the call returns as soon as the
simulation reaches its first safe point.

```klara-repl
k=> (def fib (perform :world/fiber))
fib
k=> (def job (perform :world/call-in fib
               (fn [] (handle [g {:yield (fn [s k] {:state s :k k})}] (sim g 0)))))
job
k=> (:state job)
0
k=> (def job (perform :world/call-in fib (:k job) :go))
job
k=> (:state job)
1
```

## Redefine while it runs

The session redefines `step`. The REPL itself sees the new version at
once. The suspended simulation is pinned and keeps the old one:

```klara-repl
k=> (defn step [s] (+ s 10))
step
k=> (step 1)
11
k=> (def job (perform :world/call-in fib (:k job) :go))
job
k=> (:state job)
2
```

Now the driver tells the simulation to raise at its next safe point. From
then on it uses the new `step`:

```klara-repl
k=> (def job (perform :world/call-in fib (:k job) :raise))
job
k=> (:state job)
12
k=> (def job (perform :world/call-in fib (:k job) :go))
job
k=> (:state job)
22
```

## What to notice

- **Two versions coexist.** Between the redefinition and the raise, the
  session ran `step` version 2 while the simulation ran version 1. Neither
  saw a mixture: the world is one reference to an immutable root, and a
  fiber reads only the root it pinned.
- **Raising is explicit.** The world never pushes a new version into running
  code. The program decides where a raise is safe (here, at a yield);
  the design calls these *safe points* (gap G4 in
  `doc/background/02-examples.md`).
- **Closures keep their basis.** `sim` reaches `step` through
  `:world/resolve` on purpose. A direct call `(step s)` inside `sim` would
  resolve against the basis the running closure was created under, which a
  raise does not change: a closure is a value. Only fresh lookups and later
  top-level evaluations see a raise (S1 decision 16).
- **Macros are different.** Redefining a *macro* makes the definitions
  that expanded it **pending** until they are re-expanded; see
  `doc/guide/02-world.md`.
