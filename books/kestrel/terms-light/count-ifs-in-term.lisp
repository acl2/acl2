; A utility to count IFs in terms
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(mutual-recursion
 (defund count-ifs-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil))
   (if (variablep term)
       0
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           0
         (let* ((args (fargs term))
                (args-count (count-ifs-in-terms args))
                )
           (if (flambdap fn)
               (+ args-count
                  (count-ifs-in-term (lambda-body fn)))
             (if (eq 'if fn)
                 (+ 1 args-count)
               args-count)))))))
 (defund count-ifs-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       0
     (+ (count-ifs-in-term (first terms))
        (count-ifs-in-terms (rest terms))))))

(defthm <=-of-count-ifs-in-term-of-fargs
  (implies (and (consp term)
                (not (equal 'quote (car term))))
           (<= (count-ifs-in-terms (fargs term))
               (count-ifs-in-term term)))
  :rule-classes :linear
  :hints (("Goal" :expand (count-ifs-in-term term)
           :in-theory (enable count-ifs))))

(defthm <=-of-count-ifs-in-term-of-lambda-body-of-car
  (implies (consp (car term))
           (<= (count-ifs-in-term (lambda-body (car term)))
               (count-ifs-in-term term)))
  :rule-classes :linear
  :hints (("Goal" :expand (count-ifs-in-term term)
           :in-theory (enable count-ifs))))

(defthm <=-of-count-ifs-in-term-of-cdr-2
  (implies (consp terms)
           (<= (count-ifs-in-terms (cdr terms))
               (count-ifs-in-terms terms)))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable count-ifs-in-terms))))

(defthm <=-of-count-ifs-in-term-of-car
  (implies (consp terms)
           (<= (count-ifs-in-term (car terms))
               (count-ifs-in-terms terms)))
  :rule-classes :linear
  :hints (("Goal"
           :in-theory (enable count-ifs-in-terms))))
