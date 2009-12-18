;; Safe-case macro
;; Jared Davis <jared@cs.utexas.edu>

(in-package "ACL2")

(defmacro safe-case (&rest l)
  ":Doc-Section Case
   Error-checking alternative to `case'.~/
   ~c[;; (include-book \"tools/safe-case\" :dir :system)] ~/
   ~c[Safe-case] is a drop-in replacement for ~il[case], and is logically identical 
   to ~c[case].  The only difference is during execution.  When ~c[case] is used and 
   none of the cases match, the answer is ~c[nil]:
   ~bv[]
   ACL2 !> (case 3
             (1 'one)
             (2 'two))
   NIL
   ~ev[]

   But when ~c[safe-case] is used and none of the cases match, the result is an
   error:
   ~bv[]
   ACL2 !> (safe-case (+ 0 3)
             (1 'one)
             (2 'two))
   
   HARD ACL2 ERROR in SAFE-CASE:  No case matched: 
   (SAFE-CASE (+ 0 3) (1 'ONE) (2 'TWO)).  Test was 3.
   ~ev[]"
  (declare (xargs :guard (and (consp l)
                              (legal-case-clausesp (cdr l)))))
  (let* ((clauses (cdr l))
         (tests   (strip-cars clauses)))
    (if (or (member t tests)
            (member 'otherwise tests))
        `(case ,@l)
      `(case ,@l
         (otherwise 
          (er hard? 'safe-case "No case matched: ~x0.  Test was ~x1.~%" 
              '(safe-case ,@l) ,(car l)))))))



