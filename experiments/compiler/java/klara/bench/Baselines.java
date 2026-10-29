package klara.bench;

import java.util.Map;
import java.util.function.LongUnaryOperator;

/** Independent Java algorithms for nonnegative long benchmark inputs.
 * Checked arithmetic matches Klara's long overflow contract. Java local
 * containers/lambdas have no observable identity and may be scalar replaced.
 * This is an ultimate algorithm baseline, not an implementation of dynamic
 * Klara numbers, persistent collections, worlds, handlers or deoptimization. */
public final class Baselines {
    private Baselines() {}
    public static long numeric(long n) {
        long sum = 0;
        for (long i = n; i > 0; i = Math.decrementExact(i))
            sum = Math.addExact(sum, i);
        return sum;
    }
    public static long sourceCollections(long n) {
        long sum = 0;
        for (long i = n; i > 0; i = Math.decrementExact(i)) {
            Long[] v = {i, Math.incrementExact(i)};
            Map<String, Long> m = Map.of("a", v[0], "b", v[1]);
            sum = Math.addExact(Math.addExact(sum, m.get("a")), m.get("b"));
        }
        return sum;
    }
    public static long sourceClosures(long n) {
        long sum = 0;
        for (long i = n; i > 0; i = Math.decrementExact(i)) {
            final long captured = i;
            LongUnaryOperator f = x -> Math.addExact(x, captured);
            sum = Math.addExact(Math.addExact(sum, f.applyAsLong(1)), f.applyAsLong(2));
        }
        return sum;
    }
    private static long weight(long x) { return Math.multiplyExact(x, 2); }
    public static long sourceTailEffects(long n) {
        LongUnaryOperator clause = Baselines::weight;
        long sum = 0;
        for (long i = n; i > 0; i = Math.decrementExact(i))
            sum = Math.addExact(sum, clause.applyAsLong(i));
        return sum;
    }
    // Hand scalar replacement and inlining give the ultimate primitive
    // Java baseline. Keep source-shaped versions above as an equality check.
    public static long collections(long n) {
        long sum = 0;
        for (long i = n; i > 0; i = Math.decrementExact(i)) {
            long a = i, b = Math.incrementExact(i);
            sum = Math.addExact(Math.addExact(sum, a), b);
        }
        return sum;
    }
    public static long closures(long n) {
        long sum = 0;
        for (long i = n; i > 0; i = Math.decrementExact(i))
            sum = Math.addExact(Math.addExact(sum, Math.addExact(1, i)), Math.addExact(2, i));
        return sum;
    }
    public static long tailEffects(long n) {
        long sum = 0;
        for (long i = n; i > 0; i = Math.decrementExact(i))
            sum = Math.addExact(sum, weight(i));
        return sum;
    }
    public static long g(long x) { return Math.multiplyExact(x, 2); }
    public static long calls(long n) {
        long sum = 0;
        for (long i = n; i > 0; i = Math.decrementExact(i))
            sum = Math.addExact(sum, g(i));
        return sum;
    }
    // Independent pure pipeline baselines; scalar fusion is legal for these
    // long-only inputs. No claim about effectful/chunked Java equivalence.
    public static long hofPipeline(long n) {
        long sum = 0;
        for (long i = 0; i < n; i = Math.incrementExact(i)) {
            long x = Math.incrementExact(i);
            if (x % 2 == 0) sum = Math.addExact(sum, x);
        }
        return sum;
    }
    public static long hofMapv(long n) {
        long[] mapped = new long[Math.toIntExact(n)];
        for (int i = 0; i < mapped.length; i++)
            mapped[i] = Math.multiplyExact((long) i, 2);
        long sum = 0;
        for (long x : mapped) sum = Math.addExact(sum, x);
        return sum;
    }
}
