package klara.typedprobe;
public final class F2 {
  public static final String G_VALUE_ID = "cea2a9ffed643b94727a2fd4f1a6e19535b2baa22fae22eef87000989215f388";
  private F2() {}
  public static long g(long x) { return Math.multiplyExact(x, 2L); }
  public static long run(Context c, long n) {
    if (!G_VALUE_ID.equals(c.gValueId())) throw new IllegalStateException("guard failed");
    long i = n, s = 0L;
    while (i > 0L) {
      long nextI = Math.decrementExact(i);
      long nextS = Math.addExact(s, g(i));
      i = nextI; s = nextS;
    }
    return s;
  }
}
