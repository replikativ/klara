# Klara

Klara is a Clojure dialect in which a running program can keep several
versions of itself, write new code, try changes in isolation, and adopt an
optimized implementation only after a small trusted checker has shown that
it means the same as the code it replaces.

```clojure
(ns demo
  (:require [klara.stage :refer [code esc]]
            [klara.compiler :as compiler]))

(defn power [n x]                                 ; the meaning
  (if (= n 0) 1 (* x (power (dec n) x))))

(defn power-gen [n x]                             ; a program that writes a program
  (if (= n 0) (code 1) (code (* (esc x) (esc (power-gen (dec n) x))))))

(def outcome                                      ; use the generator as an optimizer
  (compiler/prepare (code (fn [x] (power 3 x)))
                    {:recipe (fn [_] (code (fn [x] (esc (power-gen 3 (code x))))))}))

(:status outcome)                                 ; => :ready, checked against power
((compiler/executable outcome) 3)                 ; => 27, compiled JVM code

(compiler/prepare (code (fn [x] (power 3 x)))     ; a wrong optimizer is rejected
                  {:recipe (fn [_] (code (fn [x] (* x x))))})
;; => {:status :rejected :rule :L4.check.not-equivalent ...}
```

## What Klara adds to Clojure

- **Worlds.** Definitions live in immutable worlds. Old worlds stay usable
  as values; functions can be pinned to the world they came from.
- **Staging.** `code`, `esc`, `lift` and `run` build and run code as data.
  Global names in code carry explicit *links* (late, pinned, guarded), so
  code means the same thing wherever it runs.
- **Effects and jobs.** Effect handlers with multi-shot continuations. A job
  runs a computation in a fork of the world under a step budget and returns
  its outcome as data: printing is deferred, definitions stay in the fork.
- **Checked compilation.** Any program can propose optimized code. The
  kernel admits it only if it is definitionally equivalent to the reference,
  records the premises it relied on, and falls back when they stop holding.
  Ahead-of-time compilation is the special case where all links are pinned.
- **Bounded lifetimes.** What keeps memory alive is a short, named list of
  roots, and every lifetime rule has a test showing that the garbage
  collector can reclaim what it should.

## Run it

Requires the Clojure CLI and a JDK (21 or later).

```sh
clojure -M:klara run examples/worlds/main.clj   # run a Klara file
clojure -M:klara repl                            # interactive REPL
clojure -M:test                                  # all tests
```

From Clojure: `(require '[klara.host.api :as k])`, then
`(k/eval-string (k/session) "(+ 1 2)")`.

## Where things are

| Path | Contents |
|---|---|
| [`design/`](design/00-model.md) | Why: the programming model, lifetimes, compilation, Clojure and agents, related work |
| [`spec/`](spec/README.md) | What: numbered rules per layer, and conformance cases |
| [`examples/`](examples/) | Klara programs: worlds, staging, effects, optimization, memory |
| [`lib/klara/`](lib/klara/) | Klara written in Klara: the compiler API and optimization recipes |
| [`src/klara/`](src/klara/README.md) | The host implementation, by layer |
| [`test/klara/`](test/klara/) | Conformance, examples, lifetime obligations, traceability |
| [`STATUS.md`](STATUS.md) | What is implemented, what is not, and the next milestone |

Read [design/00-model.md](design/00-model.md) first. Rule IDs such as
`L2.run.closed` appear in the spec, in error data, at the implementing code
and in tests, so `grep -r L2.run.closed` finds all of them.

## Status

A research prototype of a deliberately small nucleus, rebuilt around a clear
programming model from the earlier prototype, whose broader experiments it
does not yet include. The prototype is the history of the `main` branch, at
tag `prototype-2026-10-31`; this branch starts afresh and does not share that
history. See [STATUS.md](STATUS.md).

Licensed under Apache-2.0.
