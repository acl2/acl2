/*
 * Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

import edu.kestrel.acl2.aij.*;

// Test harness for the generated Java code for the factorial function.
public class TestFactShallow {

    // Make n calls of the factorial function on the input,
    // printing the time taken by each call
    // as well as minimum, maximum, and average.
    private static void runTest(Acl2Value input, int n)
        throws Acl2EvaluationException {
        long[] times = new long[n];
        for (int i = 0; i < n; ++i) {
            // record start time:
            long start = System.currentTimeMillis();
            // execute the call:
            Acl2Value result = FactShallow.ACL2.FACT(input);
            // record end time:
            long end = System.currentTimeMillis();
            // prevent unwanted JIT compiler optimizations:
            if (result.equals(Acl2Integer.ZERO)) return; // never happens
            // print time for the call:
            long time = end - start;
            System.out.format("  %.3f%n", time / 1000.0);
            // record time for the call:
            times[i] = time;
        }
        // calculate and print minimum, maximum, and average:
        long min = times[0];
        long max = times[0];
        long sum = times[0];
        for (int i = 1; i < n; ++i) {
            min = java.lang.Math.min(min, times[i]);
            max = java.lang.Math.max(max, times[i]);
            sum += times[i];
        }
        double avg = (sum / 1000.0) / n;
        System.out.format("Minimum: %.3f%n", min / 1000.0);
        System.out.format("Average: %.3f%n", avg);
        System.out.format("Maximum: %.3f%n", max / 1000.0);
    }

    // Make n calls of the factorial function on each input,
    // printing the time taken by each call
    // as well as minimum, maximum, and average for each input.
    private static void runTests(int[] inputs, int n)
        throws Acl2EvaluationException {
        int len = inputs.length;
        for (int i = 0; i < len; ++i) {
            int input = inputs[i];
            System.out.format("%nTimes (in seconds) to run factorial on %d:%n",
                              input);
            Acl2Integer arg = Acl2Integer.make(input);
            runTest(arg, n);
        }
    }

    // Make a specified number of calls of the factorial function
    // on a specified sequence of inputs.
    // The number of calls is arg[0], which must be a non-negative int.
    // The inputs are arg[1], arg[2], ...,
    // which must be non-negative ints.
    // See test-run.sh in this directory for an example of how to run this code.
    public static void main(String[] args) throws Acl2EvaluationException {
        FactShallow.initialize();
        int n = Integer.parseInt(args[0]);
        int numInputs = args.length - 1;
        int[] inputs = new int[numInputs];
        for (int i = 0; i < numInputs; ++i)
            inputs[i] = Integer.parseInt(args[i+1]);
        runTests(inputs, n);
        System.out.println();
    }
}
