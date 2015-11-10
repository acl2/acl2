class Demo {

    static int ans;

    public static int fact(int n) {
        if (n>0)
            return n*fact(n-1);
        else
            return 1;
    }

    /* Dummy main method */

    public static void main() {
        int k = 4;
        ans = fact(k+1);
    }

    /* This main method is not simulated */
    /* because our M5 model does not support the */
    /* native methods necessary to support IO. */

    public static void main(String[] args) {
        int n = Integer.parseInt(args[0], 10);
        System.out.println(fact(n));
    }
}

