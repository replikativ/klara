package klara.typedprobe;
public final class Region3 {
public static final String G_VALUE_ID = "b10ffb3a5e7e681457fa762ce3777b9f841c91ae43f96e7a9fc56791a3f45616";
public static long direct_f(long t1) {
long t2 = t1;
long t3 = 0L;
t4: while (true) {
boolean t5 = (t2 > 0L);
if (t5) {
boolean t6 = (t2 > 3L);
if (t6) {
long t7 = Math.decrementExact(t2);
long t8 = direct_g(t2);
long t9 = Math.addExact(t3,t8);
long t10 = t7;
long t11 = t9;
t2 = t10;
t3 = t11;
continue t4;
} else {
long t12 = Math.decrementExact(t2);
long t13 = direct_g(t2);
long t14 = Math.subtractExact(t3,t13);
long t15 = t12;
long t16 = t14;
t2 = t15;
t3 = t16;
continue t4;
}
} else {
return t3;
}
}
}
public static long inline_f(long t17) {
long t18 = t17;
long t19 = 0L;
t20: while (true) {
boolean t21 = (t18 > 0L);
if (t21) {
boolean t22 = (t18 > 3L);
if (t22) {
long t23 = Math.decrementExact(t18);
long t24 = Math.subtractExact(t18,5L);
long t25 = Math.addExact(t19,t24);
long t26 = t23;
long t27 = t25;
t18 = t26;
t19 = t27;
continue t20;
} else {
long t28 = Math.decrementExact(t18);
long t29 = Math.subtractExact(t18,5L);
long t30 = Math.subtractExact(t19,t29);
long t31 = t28;
long t32 = t30;
t18 = t31;
t19 = t32;
continue t20;
}
} else {
return t19;
}
}
}
public static long direct_g(long t33) {
long t34 = Math.subtractExact(t33,5L);
return t34;
}
public static long inline_g(long t35) {
long t36 = Math.subtractExact(t35,5L);
return t36;
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
