JVM: OpenJDK 64-Bit Server VM 25.0.4.1+1-1-26.04.4-Ubuntu  file: results/raw-openjdk25-c2.edn

| benchmark | unit | best ns | median ns | median range | best / baseline | baseline |
|---|---|---:|---:|---|---:|---|
| :i/cps | perform | 12.06 | 12.53 | 12.13–17.22 (n=3) | 3.06x | :i/direct-fn |
| :i/direct-fn | perform | 3.93 | 4.01 | 3.98–4.14 (n=3) | 1.00x | :i/direct-fn |
| :i/fast-dyn | perform | 17.64 | 18.02 | 17.81–23.35 (n=3) | 4.49x | :i/direct-fn |
| :i/fast-global | perform | 3.96 | 4.04 | 3.99–4.18 (n=3) | 1.01x | :i/direct-fn |
| :i/fast-sv | perform | 4.74 | 5.13 | 5.11–5.45 (n=3) | 1.21x | :i/direct-fn |
| :i/fast-tl | perform | 5.36 | 5.47 | 5.43–5.52 (n=3) | 1.36x | :i/direct-fn |
| :i/fast-tl-depth10 | perform | 5.35 | 5.46 | 5.40–5.51 (n=3) | 1.36x | :i/direct-fn |
| :i/fast-tl-mega | perform | 30.46 | 31.75 | 31.60–37.01 (n=3) | 7.74x | :i/direct-fn |
| :i/list-depth0 | perform | 5.58 | 5.72 | 5.62–6.01 (n=3) | 1.42x | :i/direct-fn |
| :i/list-depth10 | perform | 21.84 | 22.39 | 22.12–23.28 (n=3) | 5.55x | :i/direct-fn |
| :i/loom | perform | 248.45 | 255.71 | 252.16–296.84 (n=3) | 63.17x | :i/direct-fn |
| :i/protocol | perform | 4.56 | 4.65 | 4.64–5.09 (n=3) | 1.16x | :i/direct-fn |
| :iii/abort-iter | iteration | 17.43 | 18.36 | 18.10–32.33 (n=3) | 10.53x | :iii/none-iter |
| :iii/cps-iter | iteration | 18.53 | 19.15 | 19.06–22.33 (n=3) | 11.19x | :iii/none-iter |
| :iii/dyn-iter | iteration | 219.67 | 230.64 | 222.64–358.90 (n=3) | 132.71x | :iii/none-iter |
| :iii/fast-iter | iteration | 14.99 | 15.32 | 15.16–17.46 (n=3) | 9.06x | :iii/none-iter |
| :iii/fast-outer | iteration | 3.87 | 4.01 | 4.00–5.73 (n=3) | 0.98x | :iii/none-1e7 |
| :iii/loom-iter | iteration | 114.93 | 122.16 | 117.45–192.65 (n=3) | 69.43x | :iii/none-iter |
| :iii/maybe-cps | iteration | 10.65 | 11.03 | 11.01–11.23 (n=3) | 2.69x | :iii/none-1e7 |
| :iii/maybe-fast | iteration | 3.91 | 4.01 | 3.99–4.02 (n=3) | 0.99x | :iii/none-1e7 |
| :iii/none-1e7 | iteration | 3.96 | 4.01 | 4.00–4.13 (n=3) | 1.00x | :iii/none-1e7 |
| :iii/none-iter | iteration | 1.66 | 3.98 | 2.06–4.06 (n=3) | 1.00x | :iii/none-iter |
| :iii/sv-iter | iteration | 34.10 | 55.19 | 37.31–56.22 (n=3) | 20.60x | :iii/none-iter |
| :abort/exinfo-d10 | iteration | 25336.67 | 25705.44 | 25646.63–26045.10 (n=3) | 783.10x | :abort/ret-d10 |
| :abort/local | iteration | 68.18 | 70.52 | 69.69–78.40 (n=3) | 2.11x | :abort/ret-d10 |
| :abort/ret-d10 | iteration | 32.35 | 33.43 | 32.73–35.96 (n=3) | 1.00x | :abort/ret-d10 |
| :abort/stackless-d10 | iteration | 520.38 | 541.12 | 534.86–588.59 (n=3) | 16.08x | :abort/ret-d10 |
| :ii/enum-cps | path | 73.75 | 76.52 | 75.98–93.72 (n=3) | 1.65x | :ii/enum-direct |
| :ii/enum-direct | path | 44.81 | 45.76 | 45.53–48.63 (n=3) | 1.00x | :ii/enum-direct |
| :ii/enum-replay | path | 688.05 | 700.36 | 700.25–830.64 (n=3) | 15.36x | :ii/enum-direct |
| :ii/is-cps | particle | 712.73 | 814.76 | 726.18–850.14 (n=3) | 3.94x | :ii/is-direct |
| :ii/is-direct | particle | 180.71 | 191.26 | 184.81–228.87 (n=3) | 1.00x | :ii/is-direct |
| :ii/is-fast | particle | 480.55 | 514.41 | 487.79–735.62 (n=3) | 2.66x | :ii/is-direct |
| :ii/is-loom | particle | 9903.61 | 10193.96 | 10007.80–16464.70 (n=3) | 54.80x | :ii/is-direct |
| :ii/smc-cps | particle | 2580.08 | 2803.82 | 2749.89–3037.34 (n=3) | 14.28x | :ii/is-direct |
| :ii/smc-replay | particle | 11922.74 | 12342.33 | 12062.35–19903.45 (n=3) | 65.98x | :ii/is-direct |

JVM: Java HotSpot(TM) 64-Bit Server VM 25.0.1+8-LTS-jvmci-b01  file: results/raw-graalvm25.edn

| benchmark | unit | best ns | median ns | median range | best / baseline | baseline |
|---|---|---:|---:|---|---:|---|
| :i/cps | perform | 11.16 | 11.62 | 11.59–11.62 (n=2) | 4.43x | :i/direct-fn |
| :i/direct-fn | perform | 2.52 | 2.88 | 2.63–2.88 (n=2) | 1.00x | :i/direct-fn |
| :i/fast-dyn | perform | 15.00 | 19.05 | 15.06–19.05 (n=2) | 5.96x | :i/direct-fn |
| :i/fast-global | perform | 4.83 | 6.51 | 5.79–6.51 (n=2) | 1.92x | :i/direct-fn |
| :i/fast-sv | perform | 5.85 | 7.12 | 6.49–7.12 (n=2) | 2.32x | :i/direct-fn |
| :i/fast-tl | perform | 5.74 | 6.04 | 5.81–6.04 (n=2) | 2.28x | :i/direct-fn |
| :i/fast-tl-depth10 | perform | 5.74 | 11.15 | 6.45–11.15 (n=2) | 2.28x | :i/direct-fn |
| :i/fast-tl-mega | perform | 6.64 | 7.60 | 6.70–7.60 (n=2) | 2.64x | :i/direct-fn |
| :i/list-depth0 | perform | 5.38 | 5.72 | 5.63–5.72 (n=2) | 2.14x | :i/direct-fn |
| :i/list-depth10 | perform | 18.41 | 20.25 | 19.25–20.25 (n=2) | 7.31x | :i/direct-fn |
| :i/loom | perform | 339.24 | 363.99 | 354.71–363.99 (n=2) | 134.75x | :i/direct-fn |
| :i/protocol | perform | 3.01 | 3.21 | 3.15–3.21 (n=2) | 1.19x | :i/direct-fn |
| :iii/abort-iter | iteration | 7.16 | 10.93 | 7.46–10.93 (n=2) | 2.59x | :iii/none-iter |
| :iii/cps-iter | iteration | 6.98 | 9.56 | 7.38–9.56 (n=2) | 2.52x | :iii/none-iter |
| :iii/dyn-iter | iteration | 120.43 | 145.64 | 140.87–145.64 (n=2) | 43.55x | :iii/none-iter |
| :iii/fast-iter | iteration | 4.72 | 4.99 | 4.74–4.99 (n=2) | 1.71x | :iii/none-iter |
| :iii/fast-outer | iteration | 2.63 | 2.75 | 2.75–2.75 (n=2) | 0.96x | :iii/none-1e7 |
| :iii/loom-iter | iteration | 42.90 | 50.03 | 43.10–50.03 (n=2) | 15.51x | :iii/none-iter |
| :iii/maybe-cps | iteration | 7.86 | 11.66 | 7.92–11.66 (n=2) | 2.86x | :iii/none-1e7 |
| :iii/maybe-fast | iteration | 2.63 | 2.75 | 2.69–2.75 (n=2) | 0.96x | :iii/none-1e7 |
| :iii/none-1e7 | iteration | 2.74 | 2.76 | 2.75–2.76 (n=2) | 1.00x | :iii/none-1e7 |
| :iii/none-iter | iteration | 2.77 | 3.23 | 3.15–3.23 (n=2) | 1.00x | :iii/none-iter |
| :iii/sv-iter | iteration | 52.08 | 173.50 | 100.13–173.50 (n=2) | 18.83x | :iii/none-iter |
| :abort/exinfo-d10 | iteration | 15633.62 | 20844.92 | 18602.62–20844.92 (n=2) | 2632.50x | :abort/ret-d10 |
| :abort/local | iteration | 35.16 | 44.23 | 36.22–44.23 (n=2) | 5.92x | :abort/ret-d10 |
| :abort/ret-d10 | iteration | 5.94 | 7.12 | 6.28–7.12 (n=2) | 1.00x | :abort/ret-d10 |
| :abort/stackless-d10 | iteration | 303.37 | 339.66 | 312.83–339.66 (n=2) | 51.08x | :abort/ret-d10 |
| :ii/enum-cps | path | 62.36 | 69.57 | 62.79–69.57 (n=2) | 3.15x | :ii/enum-direct |
| :ii/enum-direct | path | 19.83 | 20.90 | 19.87–20.90 (n=2) | 1.00x | :ii/enum-direct |
| :ii/enum-replay | path | 517.20 | 656.70 | 519.98–656.70 (n=2) | 26.09x | :ii/enum-direct |
| :ii/is-cps | particle | 556.33 | 838.55 | 621.09–838.55 (n=2) | 4.89x | :ii/is-direct |
| :ii/is-direct | particle | 113.88 | 142.08 | 129.34–142.08 (n=2) | 1.00x | :ii/is-direct |
| :ii/is-fast | particle | 373.92 | 451.09 | 443.10–451.09 (n=2) | 3.28x | :ii/is-direct |
| :ii/is-loom | particle | 6048.24 | 12408.80 | 6130.47–12408.80 (n=2) | 53.11x | :ii/is-direct |
| :ii/smc-cps | particle | 1916.03 | 5767.62 | 2341.64–5767.62 (n=2) | 16.83x | :ii/is-direct |
| :ii/smc-replay | particle | 7556.22 | 10277.55 | 8050.95–10277.55 (n=2) | 66.35x | :ii/is-direct |

