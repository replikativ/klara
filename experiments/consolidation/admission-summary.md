# Producer–consumer admission pilot

Three sequential JVMs [6 7 8], Intel Core Ultra 7 258V, no CPU pinning. Times are μs per call: median [min, max] of process medians. Ranges are variability, not confidence intervals. All sizes warm before sampling.

| n | ordinary guarded | existing value evidence | pure batch of 100, per call | mapv then guarded | checked producer + evidence consumer | input scan + producer + consumer |
|---|---|---|---|---|---|---|
| 16 | 4.57 [4.36, 5.53] | 2.47 [2.40, 2.90] | 0.08 [0.07, 0.10] | 4.83 [4.49, 5.69] | 3.03 [2.84, 3.43] | 3.12 [2.91, 3.51] |
| 256 | 5.84 [5.55, 6.96] | 3.10 [2.96, 3.51] | 0.59 [0.57, 0.68] | 8.29 [7.66, 9.38] | 6.04 [5.71, 6.92] | 6.34 [6.19, 7.57] |
| 4096 | 31.90 [28.42, 33.29] | 14.57 [13.46, 15.99] | 12.17 [10.96, 12.89] | 66.95 [58.34, 70.39] | 60.19 [59.92, 70.55] | 78.10 [72.95, 84.17] |

The first three columns consume the same input. The final three consume its incremented elements and include materializing the output vector. Existing-evidence cases exclude the initial scan that creates the evidence; the final column includes it. Batch measurements divide an actual 100-call operation by 100 and include one admission. A batch is an explicit known pure driver, not arbitrary user code with guards removed.

Setup costs, milliseconds:

```clojure
{:preparation-ms {:median 96.051714, :min 96.019897, :max 132.185672}, :publication-ms {:median 0.283615, :min 0.272227, :max 0.28398}, :legacy-checked-installation-ms {:median 20.90326, :min 20.882966, :max 21.8559}, :validation-ms {:median 29.632302, :min 26.285469, :max 41.246781}}
```

Preparation includes prevalidation; publication reuses its receipt. Legacy installation checks again. This moves work out of publication, without claiming the same amount of work vanished. Raw files retain allocation samples and an instrumented guard profile; profile components are not additive timings.

Processes 0–5 are development diagnostics: 0–1 precede native-worker host-guard repair, 2–4 precede the primitive-return batch ABI, and 5 precedes the final ABI. S28 measurements are historical and do not describe these changes. One workload family and three JVMs remain a pilot.
