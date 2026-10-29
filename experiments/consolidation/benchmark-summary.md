# Native composition: independent-process pilot

Intel Core Ultra 7 258V, 8 cores. Processes [7 8 9]; no CPU pinning. Times are microseconds per invocation: median [min, max] of three process medians. Ranges describe variability, not confidence intervals.

| n | mapped | functional vector | transient | primitive scalar | emitted body | full guarded | guard scan | T0 |
|---|---|---|---|---|---|---|---|---|
| 16 | 0.23 [0.21, 0.37] | 0.22 [0.21, 0.23] | 0.11 [0.11, 0.11] | 0.06 [0.05, 0.06] | 0.05 [0.05, 0.05] | 4.00 [3.76, 4.23] | 0.06 [0.06, 0.07] | 56.22 [55.99, 58.71] |
| 256 | 2.08 [1.89, 3.17] | 2.45 [2.35, 2.57] | 0.78 [0.76, 0.83] | 0.57 [0.56, 0.75] | 0.44 [0.42, 0.48] | 5.19 [5.16, 5.70] | 0.47 [0.47, 0.51] | 698.91 [628.62, 713.67] |
| 4096 | 28.47 [27.81, 43.33] | 40.02 [36.25, 40.03] | 12.34 [11.89, 12.47] | 12.42 [11.38, 14.56] | 10.18 [9.47, 10.19] | 24.35 [23.20, 30.47] | 10.50 [10.03, 10.52] | 10909.23 [9928.73, 11059.58] |

Preparation (ms): {:median 73.71226, :min 67.518066, :max 84.830126}. Installation (ms): {:median 23.116902, :min 22.547041, :max 24.55367}.

Raw samples, thread allocation, policy costs and phase timings are in the process EDN files. Never/always/bounded policies return the same result; short workloads cannot amortize repeated preparation. T0 receives less warmup. The body result alone is not an end-to-end speedup.

Processes 0–5 preserve development versions of guards, layouts and prover bootstrap. Process 6 uses the final compiler with the earlier per-row warmup protocol. They are excluded from this aggregate. The final protocol warms every size before measuring any size to reduce compiler-tier differences between rows. This is one workload family on one machine, not a broad workload evaluation.
