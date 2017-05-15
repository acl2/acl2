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
vs == 1 && /^Constraint/ {totalHyps++; constraint=$2 ; print " ", $2}
vs == 1 && /^Kind/ {print "    ", $2,$4,$6;incrementKinds($2,$4); incrementKinds_pos_shallow($2,$4)}
/^__Vacuous_test_statistics_END__/ {vs=0}


function incrementKinds(K,pc) {
    kinds = substr(K,2,length(K)-2) #remove parens
    n = split(kinds,kinds_array, " ")
        
    for (i = 1; i <= n; i++) {
        ACount[kinds_array[i]]++
        if (pc <= lo) ALow[kinds_array[i]]++
        if (pc > hi) AHigh[kinds_array[i]]++
    }

    if (pc <= lo && (kinds_array[3] == ":MONADIC/PREDICATE" || kinds_array[3] == ":BINARY/PREDICATE")) {
        print "Constraint is " constraint 
        fn111 = get_top_fn_symbol(constraint)
        if (kinds_array[1] == ":POS") {
            posfnCount[fn111]++
        } else {
            negfnCount[fn111]++
        }
        
    }
    
    
    return n
}

function find_closing_paren_pos (x) {
    for (i = length(x); i >= 1; i--) {
        if (substr(x,i,1) == ")")
            return i
    }
    return 0
}

function substr1 (s, starti, endi) {
    return substr(s, starti, endi - starti)
}

function get_top_fn_symbol (c1) {
    cs = substr1(c1,2,find_closing_paren_pos(c1))
    print "cs is " cs
    n = split(cs,temp1, " ")
    print "cs is " cs
    print "temp1[1] is:" temp1[1] " temp1[2] is:" temp1[2] " temp1[3] is:" temp1[3]
    ans = temp1[1]
    if (temp1[1] == "NOT") {
        not_arg = substr(cs,5)
        print "not_arg is " not_arg
        ans =  get_top_fn_symbol(not_arg)
        print "NOT case: ans is " ans
    }
    if (temp1[1] == "EQUAL" || temp1[1] == "EQL" || temp1[1] == "EQ" || temp1[1] == "=") {
        print "if cond:" index(temp1[2],"(") " else if:" index(temp1[3],"(")
        if (index(temp1[2],"(") > 0) {
            ans = substr(temp1[2], 2)
            print "returning first args fn: " ans
        }
        else if (index(temp1[3],"(") > 0) {
            ans = substr(temp1[3], 2)
            print "returning second args fn: " ans
        }
        else {
            print "returning equal"
            ans = "EQUAL";
        }
    }
    return ans
    
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
    for (i in ACount) {
        if (i == ":NEG" || i == ":POS" || i == ":SHALLOW" || i == ":NON-SHALLOW") 
            printf("%-25s %-10d %7d %7d\n", i, ACount[i], ALow[i], AHigh[i])
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
    for (i in ALow) {
        if (i == ":NEG" || i == ":POS" || i == ":SHALLOW" || i == ":NON-SHALLOW") continue;
        printf("%-25s %-10d %7d %7d\n", i, ACount[i], ALow[i], AHigh[i])
    }

    print "----------------POS/per-constraint counts----------"
    
    PROCINFO["sorted_in"] = "@val_num_asc"
    for (i in posfnCount) {
        if (posfnCount[i] > 50)
            printf("%-50s %10d\n", i, posfnCount[i])
    }
    print "----------------NEG/per-constraint counts----------"
    for (i in negfnCount) {
        if (negfnCount[i] > 5)
            printf("%-50s %10d\n", i, negfnCount[i])
    }
    
}



