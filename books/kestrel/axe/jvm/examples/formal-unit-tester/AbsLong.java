// Formal Unit Tests of an absolute value function for longs
//
// Copyright (C) 2016-2020 Kestrel Technology, LLC
// Copyright (C) 2020-2023 Kestrel Institute
//
// License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
//
// Author: Eric Smith (eric.smith@kestrel.edu)

////////////////////////////////////////////////////////////////////////////////

// In this version, the tests return their results as booleans.

public class AbsLong {

    // The method to be tested.  Takes the absolute value of x.
    public static long absLong (long x) {
        if (x < 0)
            return -x;
        else
            return x;
    }

    // Test that abs is idempotent.
    public static boolean testAbsIdempotent (long x) {
        return (absLong(x) == absLong(absLong(x)));
    }

    // Test that abs is always non-negative (fails).
    // Fails, because the property is not true for the most negative Long,
    // whose negation is itself!
    public static boolean fail_testAbsNonNeg (long x) {
        return (absLong(x) >= 0);
    }

    // Same as above but excludes the most negative Long.
    public static boolean testAbsNonNeg (long x) {
        if (x == -9223372036854775808L)
            return true; // exclude this single value
        return (absLong(x) >= 0);
    }

    // Test that abs(x) = abs(-x).
    public static boolean testAbsNeg (long x) {
        return (absLong(x) == absLong(-x));
    }

    // Test that nothing has an absolute value of 0 (fails, obviously).
    // Fails because 0 has an absolute value of 0 (see next test).
    public static boolean fail_testAbsNotZero (long x) {
        return absLong(x) != 0;
    }

    // Test that only 0 has an abs of 0.
    public static boolean testAbsNotZero (long x) {
        if (absLong(x) == 0)
            return x == 0;
        return true;
    }

    // Test that two different values can't have the same abs (fails).
    public static boolean fail_testAbsTwoDiff (long x, long y) {
        if (absLong(x) == absLong(y))
            return (x == y);
        return true;
    }

    // Test that three different values can't have all the same abs.
    public static boolean testAbsThreeDiff (long x, long y, long z) {
        if (x == y || y == z || x == z)
            return true ; // ensures all different
        // they can't all have the same abs:
        return !(absLong(x) == absLong(y) && absLong(y) == absLong(z));
    }

    // Test that if x and y differ by 2, so do their abs values (fails).
    // Fails because not true for 1 and -1.
    public static boolean fail_testAbsTwoSep (long x, long y) {
        if (absLong(x) > 1000000 || absLong(y) > 1000000)
            return true; // avoid over/underflow
        if (x == y + 2) {
            long diff = absLong(x) - absLong(y);
            return (diff == 2 || diff == -2);
        }
        return true;
    }

}
