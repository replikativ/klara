package klara.typedprobe;
public final class Region0 {
public static final String G_VALUE_ID = "cea2a9ffed643b94727a2fd4f1a6e19535b2baa22fae22eef87000989215f388";
public static long direct_f(long t1) {
long t2 = t1;
long t3 = 0L;
t4: while (true) {
boolean t5 = (t2 > 0L);
if (t5) {
long t6 = Math.decrementExact(t2);
long t7 = direct_g(t2);
long t8 = Math.addExact(t3,t7);
long t9 = t6;
long t10 = t8;
t2 = t9;
t3 = t10;
continue t4;
} else {
return t3;
}
}
}
public static long inline_f(long t11) {
long t12 = t11;
long t13 = 0L;
t14: while (true) {
boolean t15 = (t12 > 0L);
if (t15) {
long t16 = Math.decrementExact(t12);
long t17 = Math.multiplyExact(t12,2L);
long t18 = Math.addExact(t13,t17);
long t19 = t16;
long t20 = t18;
t12 = t19;
t13 = t20;
continue t14;
} else {
return t13;
}
}
}
public static long direct_g(long t21) {
long t22 = Math.multiplyExact(t21,2L);
return t22;
}
public static long inline_g(long t23) {
long t24 = Math.multiplyExact(t23,2L);
return t24;
}
public static long direct(Context c, long n) {
if (!G_VALUE_ID.equals(c.gValueId())) throw new IllegalStateException("guard failed");
return direct_f(n);
}
public static long inline(Context c, long n) {
if (!G_VALUE_ID.equals(c.gValueId())) throw new IllegalStateException("guard failed");
return inline_f(n);
}
}
