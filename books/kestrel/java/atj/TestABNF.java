/*
 * Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
 * License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
 * Author: Alessandro Coglio (coglio@kestrel.edu)
 */

import edu.kestrel.acl2.aij.*;

// Test harness for the generated code Java code fot the ABNF grammar parser.
public class TestABNF {

    // Make n calls of the ABNF parser on the input,
    // printing the time taken by each call
    // as well as minimum, maximum, and average.
    private static void runTest
        (Acl2Symbol parse, Acl2Value[] input, int n)
        throws Acl2EvaluationException {
        long[] times = new long[n];
        for (int i = 0; i < n; ++i) {
            // record start time:
            long start = System.currentTimeMillis();
            // execute the call:
            Acl2Value result = ABNF.call(parse, input);
            // record end time:
            long end = System.currentTimeMillis();
            // prevent unwanted JIT compiler optimizations:
            if (result instanceof Acl2Integer) return; // never happens
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

    // Obtain an ACL2 list of natural numbers from the specified file.
    private static Acl2Value getInputFromFile(String filename)
        throws java.io.FileNotFoundException, java.io.IOException {
        java.io.FileInputStream file = new java.io.FileInputStream(filename);
        java.util.List<Integer> bytes = new java.util.ArrayList<>();
        int byt = file.read();
        while (byt != -1) { // EOF
            bytes.add(byt);
            byt = file.read();
        }
        file.close();
        java.util.Collections.reverse(bytes);
        Acl2Value list = Acl2Symbol.NIL;
        for (Integer nat : bytes)
            list = Acl2Cons.make(Acl2Integer.make(nat), list);
        return list;
    }

    // Make n calls of the ABNF parser on each input,
    // printing the time taken by each call
    // as well as minimum, maximum, and average for each input.
    private static void runTests(Acl2Symbol parse, String[] inputs, int n)
        throws Acl2EvaluationException,
               java.io.FileNotFoundException, java.io.IOException {
        int len = inputs.length;
        for (int i = 0; i < len; ++i) {
            String input = inputs[i];
            System.out.format("%nTimes (in seconds) to run the parser on %s:%n",
                              input);
            Acl2Value arg = getInputFromFile(input);
            Acl2Value[] args = new Acl2Value[]{arg};
            runTest(parse, args, n);
        }
    }

    // Make a specified number of calls of the ABNF parser
    // on a specified sequence of input files.
    // The number of calls is arg[0], which must be a non-negative int.
    // The input file names are arg[1], arg[2], ...,
    // which must be names of files under the test-abnf-files/ directory.
    // See run.sh in this directory for an example of how to run this code.
    public static void main(String[] args)
        throws Acl2EvaluationException,
               java.io.FileNotFoundException, java.io.IOException {
        ABNF.initialize();
        int n = Integer.parseInt(args[0]);
        Acl2Symbol parse = Acl2Symbol.makeAcl2("PARSE-GRAMMAR");
        int numInputs = args.length - 1;
        String[] inputs = new String[numInputs];
        for (int i = 0; i < numInputs; ++i)
            inputs[i] = "test-abnf-files/" + args[i+1];
        runTests(parse, inputs, n);
        System.out.println();
    }
}
