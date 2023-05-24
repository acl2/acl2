// Formal Unit Tests of a binary search function
//
// Copyright (C) 2023 Kestrel Institute
//
// License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
//
// Author: Eric Smith (eric.smith@kestrel.edu)

////////////////////////////////////////////////////////////////////////////////

public class BinarySearch {

    // The routine to test:
    // Returns an index i into the data array that data[i] is target, or -1
    // if target is not present.  The data array must be sorted.
    // Assumes the array is not null.
    public static int binarySearch (int target, int [] data) {
        int low = 0;
        int high = data.length - 1;
        while (low <= high) {
            int mid = low + (high - low) / 2;
            if (data[mid] == target)
                return mid; // found
            if (data[mid] < target)
                low = mid+1;
            else
                high = mid-1;
        }
        return -1; // not found
    }

    // Spec routine: Linear search
    public static int linearSearch (int target, int[] data) {
        for (int i = 0; i < data.length ; i++)
            if (data[i] == target)
                return i;
        return -1; // not found
    }

    // Spec routine: sortedness check
    public static boolean sorted(int [] data) {
        for (int i = 0; i < data.length - 1; i++)
            if (data[i] > data[i+1])
                return false;
        return true;
    }

    // The formal unit test: Compare binarySearch with linearSearch:
    public static boolean test (int target, int [] data) {
        if (data.length != 10) // ensure loops can be unrolled
            return true;
        if (!sorted(data))
            return true; // require the list to be sorted
        // Proceed with the test:
        // Use linear search as the specification:
        int spec_result = linearSearch(target, data);
        int bs_result = binarySearch(target, data);
        // If the item is present, binary search must find an
        // occurrence of it (not necessarily at the same index):
        if (spec_result != -1) // item present
            return bs_result >= 0 && bs_result < data.length && data[bs_result] == target;
        else // item not present, so binary search must return -1:
            return bs_result == -1;
    }
}
