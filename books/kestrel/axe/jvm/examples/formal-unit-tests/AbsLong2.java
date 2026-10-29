// Formal Unit Tests of an absolute value function for longs
//
// Copyright (C) 2016-2020 Kestrel Technology, LLC
// Copyright (C) 2020-2026 Kestrel Institute
//
// License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
//
// Author: Eric Smith (eric.smith@kestrel.edu)

////////////////////////////////////////////////////////////////////////////////

// In this version, the tests are in a separate class

public class AbsLong2 {

    // The method to be tested.  Takes the absolute value of x.
    public static long absLong (long x) {
        if (x < 0)
            return -x;
        else
            return x;
    }
}
