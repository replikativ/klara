package klara.typedprobe;

import clojure.lang.IFn;
import com.sun.management.ThreadMXBean;
import java.lang.management.ManagementFactory;
import java.util.Arrays;
import java.util.function.LongSupplier;
import klara.bench.Baselines;

public final class RegionProbe {
    private static volatile long input, sink;
    private static void sample(String name, LongSupplier body, ThreadMXBean bean) {
        for (int k=0; k<10000; k++) sink=body.getAsLong();
        long tid=Thread.currentThread().threadId();
        long[] ns=new long[9], bytes=new long[9];
        for (int b=0; b<9; b++) {
            long a=bean.getThreadAllocatedBytes(tid), t=System.nanoTime();
            for (int k=0; k<10000; k++) sink=body.getAsLong();
            ns[b]=(System.nanoTime()-t)/10000;
            bytes[b]=(bean.getThreadAllocatedBytes(tid)-a)/10000;
        }
        Arrays.sort(ns); Arrays.sort(bytes);
        System.out.printf("n=%d %s ns=%d B=%d%n", input, name, ns[4], bytes[4]);
    }
    public static void run(IFn klara) {
        Context c=new Context(Region0.G_VALUE_ID);
        ThreadMXBean bean=(ThreadMXBean)ManagementFactory.getThreadMXBean();
        bean.setThreadAllocatedMemoryEnabled(true);
        for (long n : new long[]{200,2000}) {
            input=n;
            if (Region0.direct(c,n)!=n*(n+1) || Region0.inline(c,n)!=n*(n+1)
                || ((Number)klara.invoke(n)).longValue()!=n*(n+1))
                throw new AssertionError("result mismatch");
            sample("typed-direct", () -> Region0.direct(c,input), bean);
            sample("compiler-inlined", () -> Region0.inline(c,input), bean);
            sample("klara-residual", () -> ((Number)klara.invoke(input)).longValue(), bean);
            sample("java-baseline", () -> Baselines.calls(input), bean);
        }
    }
}
