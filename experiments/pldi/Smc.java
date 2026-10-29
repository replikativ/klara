package klara.bench;
/** Independent primitive state-machine baseline; no general handler runtime. */
public final class Smc {
  static long next(long k) { return k * 48271 % 2147483647; }
  static long split(long k, int i) { return next((1000003*k+i+1)%2147483647); }
  static double u(long k) { return (double)k/2147483647; }
  public static double[] run() {
    boolean[] ys={true,true,false,true,false,true,false,false,true,true,true,false};
    boolean[] xs=new boolean[32]; long[] keys=new long[32];
    for(int i=0;i<32;i++){keys[i]=next(split(42,i)); xs[i]=u(keys[i])<0.5;}
    long key=42; double z=1;
    for(int t=0;t<ys.length;t++){
      double[] ws=new double[32]; double total=0;
      for(int i=0;i<32;i++){
        double p=xs[i]?0.9:0.2,q=0.5;
        for(int j=0;j<16;j++)q=(q+p)/2.0;
        ws[i]=ys[t]?q:1.0-q;total+=ws[i];
      }
      key=next(key); boolean[] nx=new boolean[32];long[] nk=new long[32];
      int i=0;double acc=ws[0];
      for(int j=0;j<32;j++){
        double pos=(u(key)+j)/32*total;
        while(acc<pos)acc+=ws[++i];
        nk[j]=split(keys[i],j);
        if(t+1<ys.length){nk[j]=next(nk[j]);nx[j]=u(nk[j])<(xs[i]?0.8:0.2);}
        else nx[j]=xs[i];
      }
      xs=nx;keys=nk;z*=total/32;
    }
    int yes=0;for(boolean x:xs)if(x)yes++;
    return new double[]{yes,z};
  }
}
