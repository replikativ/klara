| RQ | Workload | Mode | Size | µs/call [95% CI] | B/call [95% CI] |
|---|---|---|---:|---:|---:|
| rq1 | calls | clojure | 200 | 0.229 [0.21, 0.235] | 24.1 [24.1, 24.1] |
| rq1 | calls | clojure | 2000 | 1.34 [1.3, 1.4] | 24.1 [24.1, 24.1] |
| rq1 | calls | compiled | 200 | 21.6 [19, 28.8] | 3.43e+04 [3.43e+04, 3.43e+04] |
| rq1 | calls | compiled | 2000 | 159 [156, 163] | 3.8e+05 [3.8e+05, 3.8e+05] |
| rq1 | calls | java | 200 | 0.197 [0.189, 0.203] | 24.1 [24.1, 24.1] |
| rq1 | calls | java | 2000 | 1.12 [1.05, 1.16] | 24.1 [24.1, 24.1] |
| rq1 | calls | t0 | 200 | 2.5e+03 [2.21e+03, 2.71e+03] | 3.01e+06 [3e+06, 3.02e+06] |
| rq1 | calls | t0 | 2000 | 8.35e+03 [7.65e+03, 9.12e+03] | 2.98e+07 [2.98e+07, 2.99e+07] |
| rq1 | calls-compile | compiled | 200 | 2.66e+04 [2.2e+04, 3.23e+04] | n/a |
| rq1 | calls-compile | compiled | 2000 | 7.66e+03 [6.07e+03, 1e+04] | n/a |
| rq1 | closures | clojure | 200 | 0.217 [0.196, 0.238] | 24.1 [24.1, 24.1] |
| rq1 | closures | clojure | 2000 | 1.4 [1.32, 1.52] | 24.1 [24.1, 24.1] |
| rq1 | closures | compiled | 200 | 0.998 [0.719, 3.08] | 448 [448, 448] |
| rq1 | closures | compiled | 2000 | 1.44 [1.41, 1.48] | 448 [448, 448] |
| rq1 | closures | java | 200 | 0.257 [0.228, 0.318] | 24.1 [24.1, 24.1] |
| rq1 | closures | java | 2000 | 1.4 [1.35, 1.56] | 24.1 [24.1, 24.1] |
| rq1 | closures | t0 | 200 | 1.52e+03 [1.47e+03, 1.82e+03] | 4.07e+06 [4.06e+06, 4.09e+06] |
| rq1 | closures | t0 | 2000 | 1.02e+04 [9.3e+03, 1.13e+04] | 4.06e+07 [4.06e+07, 4.08e+07] |
| rq1 | closures-compile | compiled | 200 | 8.69e+03 [5.77e+03, 1.24e+04] | n/a |
| rq1 | closures-compile | compiled | 2000 | 2.82e+03 [2.68e+03, 2.94e+03] | n/a |
| rq1 | collections | clojure | 200 | 0.459 [0.3, 0.477] | 1.75e+03 [24.1, 1.75e+03] |
| rq1 | collections | clojure | 2000 | 5.14 [2.08, 5.33] | 4.5e+04 [24.1, 4.5e+04] |
| rq1 | collections | compiled | 200 | 2.3 [1.39, 2.39] | 448 [448, 448] |
| rq1 | collections | compiled | 2000 | 1.45 [1.41, 1.5] | 448 [448, 448] |
| rq1 | collections | java | 200 | 0.244 [0.21, 1.25] | 24.1 [24.1, 24.1] |
| rq1 | collections | java | 2000 | 1.36 [1.32, 1.37] | 24.1 [24.1, 24.1] |
| rq1 | collections | t0 | 200 | 1.84e+03 [1.75e+03, 1.94e+03] | 5.09e+06 [5.07e+06, 5.11e+06] |
| rq1 | collections | t0 | 2000 | 1.32e+04 [1.24e+04, 1.45e+04] | 5.08e+07 [5.07e+07, 5.1e+07] |
| rq1 | collections-compile | compiled | 200 | 9.91e+03 [6.4e+03, 1.05e+04] | n/a |
| rq1 | collections-compile | compiled | 2000 | 4.79e+03 [4.64e+03, 6e+03] | n/a |
| rq1 | hof-mapv | clojure | 200 | 6.64 [5.58, 7.32] | 1.26e+04 [1.26e+04, 1.26e+04] |
| rq1 | hof-mapv | clojure | 2000 | 48.7 [44.3, 50.1] | 1.15e+05 [1.15e+05, 1.15e+05] |
| rq1 | hof-mapv | compiled | 200 | 9.67 [9.38, 14.3] | 3.42e+04 [3.41e+04, 3.42e+04] |
| rq1 | hof-mapv | compiled | 2000 | 72.6 [69.7, 75.4] | 3.69e+05 [3.69e+05, 3.69e+05] |
| rq1 | hof-mapv | java | 200 | 1.47 [1.36, 1.68] | 1.64e+03 [1.64e+03, 1.64e+03] |
| rq1 | hof-mapv | java | 2000 | 2.15 [1.92, 2.17] | 1.6e+04 [1.6e+04, 1.6e+04] |
| rq1 | hof-mapv | t0 | 200 | 727 [668, 785] | 1.76e+06 [1.76e+06, 1.77e+06] |
| rq1 | hof-mapv | t0 | 2000 | 4.38e+03 [4.07e+03, 5.22e+03] | 1.76e+07 [1.75e+07, 1.76e+07] |
| rq1 | hof-mapv-compile | compiled | 200 | 6.22e+03 [5.58e+03, 9.91e+03] | n/a |
| rq1 | hof-mapv-compile | compiled | 2000 | 3.57e+03 [3.39e+03, 6e+03] | n/a |
| rq1 | hof-pipeline | clojure | 200 | 5.31 [3.86, 6.98] | 1.07e+04 [8.92e+03, 1.07e+04] |
| rq1 | hof-pipeline | clojure | 2000 | 32.4 [29, 37.2] | 1.38e+05 [1.37e+05, 1.59e+05] |
| rq1 | hof-pipeline | compiled | 200 | 7.58 [6.24, 9.37] | 1.2e+04 [1.1e+04, 1.3e+04] |
| rq1 | hof-pipeline | compiled | 2000 | 37 [34.7, 38.2] | 1.38e+05 [1.38e+05, 1.39e+05] |
| rq1 | hof-pipeline | java | 200 | 1.19 [0.688, 1.29] | 24.1 [24.1, 24.1] |
| rq1 | hof-pipeline | java | 2000 | 0.764 [0.608, 0.963] | 24.1 [24.1, 24.1] |
| rq1 | hof-pipeline | t0 | 200 | 678 [603, 707] | 2.05e+06 [2.05e+06, 2.05e+06] |
| rq1 | hof-pipeline | t0 | 2000 | 4.91e+03 [4.62e+03, 5.27e+03] | 2.05e+07 [2.04e+07, 2.05e+07] |
| rq1 | hof-pipeline-compile | compiled | 200 | 6.82e+03 [5.9e+03, 7.42e+03] | n/a |
| rq1 | hof-pipeline-compile | compiled | 2000 | 3.44e+03 [2.95e+03, 4.94e+03] | n/a |
| rq1 | numeric | clojure | 200 | 0.149 [0.128, 0.172] | 24.1 [24.1, 24.1] |
| rq1 | numeric | clojure | 2000 | 0.706 [0.672, 0.801] | 24.1 [24.1, 24.1] |
| rq1 | numeric | compiled | 200 | 1.33 [0.91, 1.47] | 448 [448, 448] |
| rq1 | numeric | compiled | 2000 | 0.981 [0.927, 1.07] | 448 [448, 448] |
| rq1 | numeric | java | 200 | 1.06 [0.612, 1.1] | 24.1 [24.1, 24.1] |
| rq1 | numeric | java | 2000 | 0.856 [0.805, 0.927] | 24.1 [24.1, 24.1] |
| rq1 | numeric | t0 | 200 | 511 [494, 582] | 1.85e+06 [1.85e+06, 1.86e+06] |
| rq1 | numeric | t0 | 2000 | 4.57e+03 [4.42e+03, 4.8e+03] | 1.85e+07 [1.84e+07, 1.85e+07] |
| rq1 | numeric-compile | compiled | 200 | 5.62e+03 [4.99e+03, 6.2e+03] | n/a |
| rq1 | numeric-compile | compiled | 2000 | 3.53e+03 [3.18e+03, 5.2e+03] | n/a |
| rq1 | smc | clojure | 384 | 623 [579, 726] | 4.72e+05 [4.72e+05, 4.72e+05] |
| rq1 | smc | compiled | 384 | 4.51e+04 [3.66e+04, 4.94e+04] | 6.16e+07 [6.12e+07, 6.18e+07] |
| rq1 | smc | java | 384 | 142 [137, 145] | 7.71e+03 [7.71e+03, 7.71e+03] |
| rq1 | smc | t0 | 384 | 5.41e+04 [5.07e+04, 5.8e+04] | 1.34e+08 [1.34e+08, 1.34e+08] |
| rq1 | tail-effects | clojure | 200 | 0.171 [0.146, 1.04] | 24.1 [24.1, 1.04e+03] |
| rq1 | tail-effects | clojure | 2000 | 0.834 [0.794, 1.09] | 24.1 [24.1, 24.1] |
| rq1 | tail-effects | compiled | 200 | 0.453 [0.396, 0.504] | 504 [504, 504] |
| rq1 | tail-effects | compiled | 2000 | 1.04 [1, 1.23] | 504 [504, 504] |
| rq1 | tail-effects | java | 200 | 0.193 [0.184, 1.34] | 24.1 [24.1, 24.1] |
| rq1 | tail-effects | java | 2000 | 1.14 [1.01, 1.18] | 24.1 [24.1, 24.1] |
| rq1 | tail-effects | t0 | 200 | 1.96e+03 [1.62e+03, 2.04e+03] | 3.64e+06 [3.63e+06, 3.65e+06] |
| rq1 | tail-effects | t0 | 2000 | 1.07e+04 [1.01e+04, 1.19e+04] | 3.61e+07 [3.6e+07, 3.63e+07] |
| rq1 | tail-effects-compile | compiled | 200 | 5.93e+03 [5.08e+03, 6.33e+03] | n/a |
| rq1 | tail-effects-compile | compiled | 2000 | 3.3e+03 [2.57e+03, 4.86e+03] | n/a |
| rq2 | affine-loop | dynamic | 0 | 37.6 [24.4, 42.7] | 1.77e+04 [1.76e+04, 1.78e+04] |
| rq2 | affine-loop | dynamic | 1000 | 1.49e+04 [1.27e+04, 1.6e+04] | 2.12e+07 [2.1e+07, 2.13e+07] |
| rq2 | affine-loop | dynamic | 10000 | 7.51e+04 [7.24e+04, 7.85e+04] | 2.09e+08 [2.07e+08, 2.11e+08] |
| rq2 | affine-loop | erased | 0 | 4.33 [4.17, 5.55] | 5.82e+03 [5.79e+03, 6.04e+03] |
| rq2 | affine-loop | erased | 1000 | 29.4 [28.4, 29.8] | 5.84e+03 [5.8e+03, 6.06e+03] |
| rq2 | affine-loop | erased | 10000 | 255 [242, 261] | 5.82e+03 [5.75e+03, 6.01e+03] |
| rq2 | smc | dynamic | 384 | 8.26e+04 [7.66e+04, 8.58e+04] | 2.28e+08 [2.26e+08, 2.29e+08] |
| rq2 | smc | erased | 384 | 2.43e+04 [2.31e+04, 2.57e+04] | 6.3e+07 [6.24e+07, 6.35e+07] |
| rq3 | first-correct | clojure | 0 | 0.195 [0.125, 0.205] | n/a |
| rq3 | first-correct | klara | 10 | 58.5 [53.3, 63.3] | n/a |
| rq3 | first-correct | klara | 1000 | 35.9 [29.9, 42.1] | n/a |
| rq3 | first-correct | klara | 100000 | 67.7 [29.3, 123] | n/a |
| rq3 | publish | klara | 10 | 2.92 [2.68, 3.08] | 4.41e+03 [4.41e+03, 4.41e+03] |
| rq3 | publish | klara | 1000 | 2.42 [2.22, 2.76] | 5.16e+03 [5.16e+03, 5.16e+03] |
| rq3 | publish | klara | 100000 | 2.22 [1.88, 2.34] | 5.43e+03 [5.43e+03, 5.43e+03] |
| rq4 | mixed-types | feedback | 0 | 2.23e+03 [1.72e+03, 2.32e+03] | 8.57e+05 [8.37e+05, 8.58e+05] |
| rq4 | mixed-types | feedback | 1 | 1.73e+03 [1.45e+03, 1.95e+03] | 8.71e+05 [8.51e+05, 8.73e+05] |
| rq4 | mixed-types | feedback | 10 | 1.55e+03 [1.41e+03, 1.73e+03] | 8.98e+05 [8.78e+05, 9e+05] |
| rq4 | mixed-types | feedback | 100 | 1.23e+03 [804, 1.42e+03] | 9.03e+05 [8.82e+05, 9.04e+05] |
| rq4 | recovery | fresh-cache | 1 | 63.3 [42, 124] | n/a |
