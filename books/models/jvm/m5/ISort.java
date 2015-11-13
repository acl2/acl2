class Cons {
    int car;
    Object cdr;
    public static Cons cons(int x, Object y){
	Cons c = new Cons();
        c.car = x;
	c.cdr = y;
	return c;
    }
}

class ListProc extends Cons {
    public static Cons insert(int e,Object x){
	if (x==null)
	    {return cons(e,x);}
	else if (e <= ((Cons)x).car)
	    {return cons(e,x);}
	else return cons(((Cons)x).car,insert(e,((Cons)x).cdr));
    }

    public static Object isort(Object x){
	if (x==null)
	    {return x;}
	else return insert(((Cons)x).car,isort(((Cons)x).cdr));
    }
}
