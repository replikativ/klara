package klara.typedprobe;
public final class F3 {
  public static final String G_VALUE_ID = "5bb6f596cfa7efb5c716dfa41512647d817d204f51a70a4e1245fc4fd0d8a7f2";
  private F3() {}
  public static long g(long x) { return Math.multiplyExact(x, 3L); }
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
