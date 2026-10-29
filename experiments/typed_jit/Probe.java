package klara.typedprobe;

import com.sun.management.ThreadMXBean;
import java.lang.management.ManagementFactory;
import java.util.Arrays;
import java.util.function.Function;
import java.util.function.LongSupplier;
import java.util.function.LongUnaryOperator;
import klara.bench.Baselines;

/** Run from one persistent Clojure REPL after in-process Java compilation. */
public final class Probe {
    private Probe() {}
    private static volatile long input;
    private static volatile long sink;

    private static long interfaceLoop(long n, LongUnaryOperator g) {
        long i = n, s = 0;
        while (i > 0) {
            long nextI = Math.decrementExact(i);
            long nextS = Math.addExact(s, g.applyAsLong(i));
            i = nextI; s = nextS;
        }
        return s;
    }

    private static long boxedLoop(long n, Function<Long, Long> g) {
        long i = n, s = 0;
        while (i > 0) {
            long nextI = Math.decrementExact(i);
            long nextS = Math.addExact(s, g.apply(i));
            i = nextI; s = nextS;
        }
        return s;
    }

    private static long[] sample(LongSupplier body, ThreadMXBean bean) {
        for (int k = 0; k < 10_000; ++k) sink = body.getAsLong();
        long[] nanos = new long[9], bytes = new long[9];
        long tid = Thread.currentThread().threadId();
        for (int b = 0; b < 9; ++b) {
            long beforeBytes = bean.getThreadAllocatedBytes(tid);
            long start = System.nanoTime();
            for (int k = 0; k < 10_000; ++k) sink = body.getAsLong();
            nanos[b] = (System.nanoTime() - start) / 10_000;
            bytes[b] = (bean.getThreadAllocatedBytes(tid) - beforeBytes) / 10_000;
        }
        Arrays.sort(nanos); Arrays.sort(bytes);
        return new long[]{nanos[4], bytes[4]};
    }

    public static void run() {
        Context old = new Context(F2.G_VALUE_ID);
        Context newer = new Context(F3.G_VALUE_ID);
        if (F2.run(old, 20) != 420 || F3.run(newer, 20) != 630 ||
            F2.run(old, 20) != 420) throw new AssertionError("old/new roots");
        boolean rejected = false;
        try { F2.run(newer, 20); } catch (IllegalStateException e) { rejected = true; }
        if (!rejected) throw new AssertionError("wrong guard accepted");
        boolean overflow = false;
        try { F2.run(old, Long.MAX_VALUE); }
        catch (ArithmeticException e) { overflow = true; }
        if (!overflow) throw new AssertionError("overflow mismatch");

        LongUnaryOperator primitive = F2::g;
        Function<Long, Long> boxed = x -> Math.multiplyExact(x, 2L);
        ThreadMXBean bean = (ThreadMXBean) ManagementFactory.getThreadMXBean();
        if (!bean.isThreadAllocatedMemoryEnabled())
            bean.setThreadAllocatedMemoryEnabled(true);
        System.out.println("Checks: old=420, new=630, old-again=420, wrong guard rejected, overflow checked");
        System.out.println("Units: median ns and B per whole call; 10k warmups, 9 batches x 10k; one JVM");
        for (long n : new long[]{200, 2_000}) {
            input = n;
            LongSupplier[] bodies = {
                () -> F2.run(old, input),
                () -> Baselines.calls(input),
                () -> interfaceLoop(input, primitive),
                () -> boxedLoop(input, boxed),
                () -> F3.run(newer, input)
            };
            String[] names = {"emitted-guarded-F2", "java-static-baseline",
                              "primitive-interface", "boxed-interface",
                              "emitted-guarded-F3"};
            for (int i = 0; i < bodies.length; ++i) {
                long[] result = sample(bodies[i], bean);
                System.out.printf("n=%d %s ns=%d B=%d%n", n, names[i], result[0], result[1]);
            }
        }
    }
}
