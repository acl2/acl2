# Help from http://ferd.ca/awk-in-20-minutes.html
# Run as:
#    $ awk -v lo=<lo> hi=<hi> -f regress-stats.awk <list of cert.out files>
#
# Default value for lo is 5 and for hi is 50.

BEGIN {
    vs = 0 # inside vac stats output
    if (lo == "") {
        lo = 5
    }
    if (hi == "") {
        hi = 50
    }
    print "VACUOUS TESTS STATISTICS"
    print "======================="
    FS=";"
}

/^Temp lisp file/ {print "Bookname:",FILENAME}

/^__Vacuous_test_statistics_BEGIN__/ {vs=1}
vs == 1 && /^CTX/ {totalEvents++; print ""; print $2}
vs == 1 && /^__SUBGOAL_BEGIN__/ {totalSubgoals++}
vs == 1 && /^SUBGOAL_NAME/ {if ($4 <= 0) vacSubgoals++; print "",$2,"%sat:",$4}
vs == 1 && /^Constraint/ {totalHyps++; print " ", $2}
vs == 1 && /^Kind/ {print "    ", $2,$4,$6;incrementKinds($2,$4); incrementKinds_pos_shallow($2,$4)}
/^__Vacuous_test_statistics_END__/ {vs=0}

function incrementKinds(K,pc) {
    kinds = substr(K,2,length(K)-2) #remove parens
    n = split(kinds,temp, " ")
    for (i = 1; i <= n; i++) {
        Count[temp[i]]++
        if (pc <= lo) Low[temp[i]]++
        if (pc > hi) High[temp[i]]++
    }
    return n
}

function incrementKinds_pos_shallow(K,pc) {
    kinds = substr(K,2,length(K)-2) #remove parens
    n = split(kinds,temp, " ")
    incrementKinds_pos_shallow_aux(temp[1], temp[2], n, temp,pc)
    return n
}

function incrementKinds_pos_shallow_aux(pn, sns, n, pskinds,pc) {
    if (pn == ":POS") {
        for (i = 3; i <= n; i++) {
            PCount[pskinds[i]]++
            if (pc <= lo) PLow[pskinds[i]]++
            if (pc > hi)  PHigh[pskinds[i]]++
        }
    }
    else {
        for (i = 3; i <= n; i++) {
            NCount[pskinds[i]]++
            if (pc <= lo) NLow[pskinds[i]]++
            if (pc > hi)  NHigh[pskinds[i]]++
        }
    }

    if (sns == ":SHALLOW") {
        for (i = 3; i <= n; i++) {
            SCount[pskinds[i]]++
            if (pc <= lo) SLow[pskinds[i]]++
            if (pc > hi)  SHigh[pskinds[i]]++
        }
    }
    else {
        for (i = 3; i <= n; i++) {
            DCount[pskinds[i]]++
            if (pc <= lo) DLow[pskinds[i]]++
            if (pc > hi)  DHigh[pskinds[i]]++
        }
    }
    
}


END {
    print ""
    print "=============================================================="
    print "Total Events:", totalEvents
    print "Total Subgoals:", totalSubgoals, "Vacuous:", vacSubgoals
    print "Total Hyps (Constraints):", totalHyps
    printf("%-25s %-10s %7s %7s\n", "Constraint Kind/Type", "Count", "LOW (< "lo"%)", "HIGH (> "hi"%)")
    for (i in Count) {
        if (i == ":NEG" || i == ":POS" || i == ":SHALLOW" || i == ":NON-SHALLOW") 
            printf("%-25s %-10d %7d %7d\n", i, Count[i], Low[i], High[i])
    }

    print ""
    print "POSITIVE constraints"
    printf("%-25s %-10s %7s %7s\n", "Constraint Kind/Type", "Count", "LOW (< "lo"%)", "HIGH (> "hi"%)")
    for (i in PLow)
        printf("%-25s %-10s %7d (%2d) %7d\n", i, PCount[i], PLow[i], PLow[i]*100/PCount[i], PHigh[i])

    print ""
    print "NEGATIVE constraints"
    printf("%-25s %-10s %7s %7s\n", "Constraint Kind/Type", "Count", "LOW (< "lo"%)", "HIGH (> "hi"%)")
    for (i in NLow)
        printf("%-25s %-10s %7d (%2d) %7d\n", i, NCount[i],NLow[i],NLow[i]*100/NCount[i], NHigh[i])

    print ""
    print "SHALLOW constraints"
    printf("%-25s %-10s %7s %7s\n", "Constraint Kind/Type", "Count", "LOW (< "lo"%)", "HIGH (> "hi"%)")
    for (i in SLow)
        printf("%-25s %-10s %7d (%2d) %7d\n", i, SCount[i],SLow[i],SLow[i]*100/SCount[i], SHigh[i])

    print ""
    print "NON-SHALLOW constraints"
    printf("%-25s %-10s %7s %7s\n", "Constraint Kind/Type", "Count", "LOW (< "lo"%)", "HIGH (> "hi"%)")
    for (i in DLow)
        printf("%-25s %-10s %7d (%2d) %7d\n", i, DCount[i], DLow[i],DLow[i]*100/DCount[i], DHigh[i])

    
    print ""
    print "------------------ CUMULATIVE ---------------------------"
    print "ALL constraints"
    for (i in Count) {
        if (i == ":NEG" || i == ":POS" || i == ":SHALLOW" || i == ":NON-SHALLOW") continue;
        printf("%-25s %-10d %7d %7d\n", i, Count[i], Low[i], High[i])
    }

    
    
}



