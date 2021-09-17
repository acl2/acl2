; A utility to count IFs in then and else branches
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)

(mutual-recursion
 ;; Unlike count-ifs, this has no special treatment for HIDE
 (defund count-ifs-in-then-and-else-branches (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ; done below
                   ))
   (if (or (variablep term)
           (fquotep term))
       0
     (let ((fn (ffn-symb term)))
       (if (eq 'if fn)
           ;; doesn't count ifs in the test
           (+ 1 (count-ifs-in-then-and-else-branches (farg2 term))
              (count-ifs-in-then-and-else-branches (farg3 term)))
         ;;it's a function call (maybe a lambda application):
         (let* ((args (fargs term))
                (args-count (count-ifs-in-then-and-else-branches-list args)) ;process the args first
                )
           (if (flambdap fn) ;test for ((lambda (...formals...) body) ...args...)
               (+ args-count
                  (count-ifs-in-then-and-else-branches (lambda-body fn)))
             args-count))))))

 (defund count-ifs-in-then-and-else-branches-list (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       0
     (+ (count-ifs-in-then-and-else-branches (first terms))
        (count-ifs-in-then-and-else-branches-list (rest terms))))))

(defthm <=-of-count-ifs-in-then-and-else-branches-list-of-fargs
  (implies (and (consp term)
                (not (equal 'quote (car term)))
                (not (equal 'if (car term))))
           (<= (count-ifs-in-then-and-else-branches-list (fargs term))
               (count-ifs-in-then-and-else-branches term)))
  :rule-classes :linear
  :hints (("Goal" :expand (count-ifs-in-then-and-else-branches term)
           :in-theory (enable COUNT-IFS))))

(defthm <=-of-count-ifs-in-then-and-else-branches-of-lambda-body-of-car
  (implies (and (consp (car term))
                )
           (<= (count-ifs-in-then-and-else-branches (lambda-body (car term)))
               (count-ifs-in-then-and-else-branches term)))
  :rule-classes :linear
  :hints (("Goal" :expand (count-ifs-in-then-and-else-branches term)
           :in-theory (enable count-ifs))))

(defthm <=-of-count-ifs-in-then-and-else-branches-list-of-cdr-2
  (implies (consp terms)
           (<= (count-ifs-in-then-and-else-branches-list (cdr terms))
               (count-ifs-in-then-and-else-branches-list terms)))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable count-ifs-in-then-and-else-branches-list))))

(defthm <=-of-count-ifs-in-then-and-else-branches-list-of-car
  (implies (consp terms)
           (<= (count-ifs-in-then-and-else-branches (car terms))
               (count-ifs-in-then-and-else-branches-list terms)))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable count-ifs-in-then-and-else-branches-list))))
