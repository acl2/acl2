// Formal Unit Tests of an absolute value function for longs
//
// Copyright (C) 2016-2020 Kestrel Technology, LLC
// Copyright (C) 2020-2026 Kestrel Institute
//
// License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
//
// Author: Eric Smith (eric.smith@kestrel.edu)

////////////////////////////////////////////////////////////////////////////////

// In this example, the test and the code are in separate classes

public class AbsLong2Test {
    // Test that abs is idempotent.
    public static boolean testAbsIdempotent (long x) {
        return (AbsLong2.absLong(x) == AbsLong2.absLong(AbsLong2.absLong(x)));
    }

}
