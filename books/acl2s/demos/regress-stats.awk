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
    print "CGEN TEST GEN STATISTICS"
    print "======================="
    FS=";"

}

/^Temp lisp file/ {print "Bookname:",FILENAME}

/^__Vacuous_test_statistics_BEGIN__/ {vs=1}
vs == 1 && /^CTX/ {totalEvents++; print ""; print $2}
vs == 1 && /^__SUBGOAL_BEGIN__/ {totalSubgoals++}
vs == 1 && /^SUBGOAL_NAME/ { satGoals($4) ; print "",$2,"%sat:",$4}

vs == 1 && /^Constraint/ {totalHyps++; constraint=$2 ; print " ", $2}
vs == 1 && /^Kind/ {print "    ", $2,$4,$6;incrementKinds($2,$4);}
/^__Vacuous_test_statistics_END__/ {vs=0}

function satGoals (satpct) {
    if ($4 <= 0) vacSubgoals++;
    if ($4 < lo) loSubgoals++;
    if ($4 > hi) hiSubgoals++;
}
    

function incrementKinds(K,pc) {
    kinds = substr(K,2,length(K)-2) #remove parens
    n = split(kinds,kinds_array, " ")
        
    for (i = 1; i <= n; i++) {
        ACount[kinds_array[i]]++
        if (pc < lo) ALow[kinds_array[i]]++
        if (pc > hi) AHigh[kinds_array[i]]++
    }

    fn111 = get_top_fn_symbol(constraint)
    if (fn111 == "")
        print "constraint with empty fn symbol was " constraint
    CCount[fn111]++
    if (pc < lo) {
        CLo[fn111]++
    }
    if (pc > hi) CHi[fn111]++

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
    n = split(cs,temp1, " ")
    ans = temp1[1]
    if (temp1[1] == "NOT") {
        not_arg = substr(cs,5)
    
        ans =  get_top_fn_symbol(not_arg)
        if (ans == "") ans = "NOT"
        
    }
    if (temp1[1] == "EQUAL" || temp1[1] == "EQL" || temp1[1] == "EQ" || temp1[1] == "=") {
        
        if (index(temp1[2],"(") > 0) {
            ans = substr(temp1[2], 2)
            
        }
        else if (index(temp1[3],"(") > 0) {
            ans = substr(temp1[3], 2)
            
        }
        else {
            
            ans = "EQUAL";
        }
    }
    return ans
    
}
    



END {
    print ""
    print "=============================================================="
    print "Total Events:", totalEvents
    print "Total Subgoals:", totalSubgoals, "Vacuous:", vacSubgoals
    print "Total Hyps (Constraints):", totalHyps
    printf("%-25s %-14s %-14s %-7s\n", "Constraint Name", "Count", "# sat% < "lo, "# sat% > "hi)
    for (i in CCount) 
        printf("%-25s %-10d %7d (%2d) %7d (%2d)\n", i, CCount[i], CLo[i], CLo[i]*100/CCount[i], CHi[i], CHi[i]*100/CCount[i])

    print ""
    print "=============================================================="
    print "Constraints satisfied with a low probability (descending order)"
    PROCINFO["sorted_in"] = "@val_num_desc"
    for (j in CLo) {
        if (CLo[j] > 0)
            printf("%-25s %-10d\n", j, CLo[j])
    }

    print "=============================================================="
    print "Total Goals:", totalSubgoals, "Vacuous:", vacSubgoals, "Lo:", loSubgoals, "Hi:", hiSubgoals 
   
    
}



