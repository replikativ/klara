package klara.typedprobe;
public final class Region2 {
public static final String G_VALUE_ID = "486d32ce63a40decf89a7195d66b519b81cd3b645b8f35e89fe4c9a1cfdd25fd";
public static long direct_f(long t1) {
long t2 = t1;
long t3 = 7L;
t4: while (true) {
boolean t5 = (t2 > 0L);
if (t5) {
long t6 = direct_g(t2);
long t7 = Math.decrementExact(t2);
long t8 = Math.addExact(t3,t6);
long t9 = t7;
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
long t13 = 7L;
t14: while (true) {
boolean t15 = (t12 > 0L);
if (t15) {
long t16 = Math.addExact(t12,1L);
boolean t17 = (t16 > 4L);
long t18;
if (t17) {
long t19 = Math.multiplyExact(t16,t16);
t18 = t19;
} else {
long t20 = Math.subtractExact(t16,2L);
t18 = t20;
}
long t21 = Math.decrementExact(t12);
long t22 = Math.addExact(t13,t18);
long t23 = t21;
long t24 = t22;
t12 = t23;
t13 = t24;
continue t14;
} else {
return t13;
}
}
}
public static long direct_g(long t25) {
long t26 = Math.addExact(t25,1L);
boolean t27 = (t26 > 4L);
if (t27) {
long t28 = Math.multiplyExact(t26,t26);
return t28;
} else {
long t29 = Math.subtractExact(t26,2L);
return t29;
}
}
public static long inline_g(long t30) {
long t31 = Math.addExact(t30,1L);
boolean t32 = (t31 > 4L);
if (t32) {
long t33 = Math.multiplyExact(t31,t31);
return t33;
} else {
long t34 = Math.subtractExact(t31,2L);
return t34;
}
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
