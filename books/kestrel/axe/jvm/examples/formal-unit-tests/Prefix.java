// Formal Unit Tests of a function that checks if an array is a prefix
//
// Copyright (C) 2016-2020 Kestrel Technology, LLC
// Copyright (C) 2020-2023 Kestrel Institute
//
// License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
//
// Author: Eric Smith (eric.smith@kestrel.edu)

////////////////////////////////////////////////////////////////////////////////

public class Prefix {

    // The method to be tested (determines whether x is a prefix of y).
    public static boolean isPrefix(int [] x, int [] y) {
        if (x.length > y.length)
            return false;
        for (int i = 0; i < x.length ; i++)
            if (x[i] != y[i])
                return false;
        return true;
    }

    // Helper function used to express the tests
    public static boolean implies(boolean x, boolean y) {
        return (!x || y);
    }

    // The tests:

    // Test: Every array is a prefix of itself (reflexivity).
    public static boolean test_reflexive (int [] x) {
        if (x.length <= 100) // limit to arrays of size <= 100
            return isPrefix(x,x);
        else
            return true; // skip the test
    }

    // Test: An empty array is a prefix of every array.
    public static boolean test_empty1 (int [] x) {
        int[] empty = {};
        return isPrefix(empty,x);
    }

    // Test: A non-empty array is not a prefix of an empty array.
    public static boolean test_empty2 (int [] x) {
        if (x.length <= 100) { // make the test unrollable
            int[] empty = {};
            return implies (x.length > 0, !isPrefix(x,empty));
        }
        else
            return true; // skip the test
    }

    // Test (Transitivity): If x is a prefix of y, and y is a prefix of
    // z, then x is a prefix of z.
    public static boolean test_transitivity (int [] x, int [] y, int [] z) {
        if (!(x.length <= 2 && y.length <= 4 && z.length == 6))
            return true; // skip the test
        return implies(isPrefix(x,y) && isPrefix(y,z), isPrefix(x,z));
    }

    // Test: If each of two arrays is a prefix of the other, they must be equal.
    public static boolean test_antisymmetry (int [] x, int [] y) {
        if (!(x.length == 20 && y.length == 20)) // limit array sizes // TODO: Generalize
            return true; // skip the test
        // Test whether the arrays are equal:
        boolean equal = true;
        if (x.length == y.length) {
            for (int i = 0 ; i < x.length ; i++ )
                if (y[i] != x[i])
                    equal = false;
        }
        else
            equal = false;
        return implies(isPrefix(x,y) && isPrefix(y,x), equal);
    }

    // Test: If we write x into the beginning of y, then isPrefix(x,y) will return true.
    public static boolean test_copy_in (int [] x, int [] y) {
        // Choose small concrete array sizes for this test:
        if (x.length == 20 && y.length == 40) {
            // copy values from x into y:
            for (int i = 0 ; i < x.length ; i++)
                y[i] = x[i];
            // ask if the result is a prefix:
            return isPrefix(x,y);
        }
        else
            return true; // skip the test
    }

    // Test: If we change an element, an array is no longer a prefix of itself,
    public static boolean test_change_element (int [] x, int index) {
        if (x.length == 20 && index >= 0 && index < x.length) {
            // copy values from x into y:
            int [] y = new int [x.length];
            for (int i = 0 ; i < x.length ; i++)
                y[i] = x[i];
            y[index] = y[index]+1; // change one value
            return !isPrefix(x,y);
        }
        else
            return true; //skip the test
    }

    // TODO: Get this to work:
    // // Test: If we take the first n elements of an array, that's a prefix.
    // public static boolean test_first_n (int [] x, int n) {
    //     if (!(x.length == 2 && n >= 0 && n <= x.length))
    //         return true; // skip the test
    //     int [] y = new int [n];
    //     // Copy in n values:
    //     for (int i = 0 ; i < n ; i++)
    //         y[i] = x[i];
    //     return isPrefix(y,x);
    // }
}
