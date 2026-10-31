import java.lang.management.ManagementFactory;
import java.util.Arrays;

/** Diagnostic primitive loop control, not a guest language benchmark. */
public final class LoopModes {
    static volatile long input;
    static volatile long sink;
    public static long plain(long n) {
        long s = 0;
        for (long i = 0; i < n; i++) s += i;
        return s;
    }
    public static long checked(long n) {
        long s = 0;
        for (long i = 0; i < n; i = Math.addExact(i, 1)) s = Math.addExact(s, i);
        return s;
    }
    static long invoke(boolean checked) {
        return checked ? checked(input) : plain(input);
    }
    public static void main(String[] args) {
        String mode = args[0];
        input = Long.parseLong(args[1]);
        long expected = input * (input - 1) / 2;
        int warmup = Integer.parseInt(args[2]);
        System.out.println("# java=" + System.getProperty("java.runtime.version"));
        System.out.println("# vm=" + System.getProperty("java.vm.info"));
        System.out.println("# flags=" + ManagementFactory.getRuntimeMXBean().getInputArguments());
        System.out.println("# warmup=" + warmup + ",samples=9,calls=100");
        for (boolean checked : new boolean[]{false, true}) {
            for (int j = 0; j < warmup; j++) {
                sink = invoke(checked);
                if (sink != expected) throw new AssertionError(sink);
            }
            double[] samples = new double[9];
            for (int sample = 0; sample < samples.length; sample++) {
                long start = System.nanoTime();
                for (int j = 0; j < 100; j++) sink = invoke(checked);
                samples[sample] = (System.nanoTime() - start) / 100.0;
                if (sink != expected) throw new AssertionError(sink);
                System.out.printf("sample\t%s\t%s\t%d\t%.2f\t%d%n", mode,
                                  checked ? "checked" : "plain", sample, samples[sample], sink);
            }
            Arrays.sort(samples);
            System.out.printf("median\t%s\t%s\t%.2f%n", mode, checked ? "checked" : "plain", samples[4]);
        }
    }
}
