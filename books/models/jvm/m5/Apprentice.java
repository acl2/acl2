class Container {
    public int counter;
}

class Job extends Thread {
    Container objref;

    public Job incr () {
        synchronized(objref) {
            objref.counter = objref.counter + 1;
	}
        return this;
    }

    public void setref(Container o) {
        objref = o;
    }

    public void run() {
        for (;;) {
            incr();
	}
    }
}

class Apprentice {
    public static void main(String[] args) {

        Container container = new Container();

        for (;;) {
            Job job = new Job();
            job.setref(container);
            job.start();
	}
    }
}
