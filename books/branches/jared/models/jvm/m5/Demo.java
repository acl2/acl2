class Demo {
  public static int fact(int n){
      if (n>0)
        {return n*fact(n-1);}
      else return 1;
    }

    /* This main method is not translated by jvm2acl2 */
    /* because our M5 model does not support the */
    /* native methods necessary to support IO. */

  public static void main(String[] args){
      int n = Integer.parseInt(args[0], 10);
      System.out.println(fact(n));
      return;
    }
}

