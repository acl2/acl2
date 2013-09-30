class Demo {
  public static int fact(int n){
      int a = 1;
      while (n!=0) {a = n*a; n = n-1;}
      return a;
  }

  public static void main(String[] args){
      int n = Integer.parseInt(args[0], 10);
      System.out.println(fact(n));
      return;
    }
}
