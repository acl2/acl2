class IDemo {

    public static int ifact(int n) {
        int temp = 1;
        while (0<n) {
            temp = n*temp;
	    n = n-1;
        }
        return temp;
    }

    public static void main(String[] args) {
        ifact(8);
    }
}
