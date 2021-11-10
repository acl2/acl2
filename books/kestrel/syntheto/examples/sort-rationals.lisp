(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/soft/define-sk2" :dir :system)
(include-book "kestrel/soft/defunvar" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define myabs ((x integerp))
  :returns (a integerp)
  (b* ((x (ifix x)))
    (if (>= x 0)
        x
      (- x)))
  :hooks (:fix)
  ///
  (defret myabs-ensures
    (>= a 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define mygcd ((x integerp) (y integerp))
  :guard (and (>= x 0) (>= y 0))
  :returns (z integerp)
  (b* ((x (ifix x))
       (y (ifix y)))
    (if (mbt (and (>= x 0) (>= y 0)))
        (if (= x 0)
            y
          (if (= y 0)
              x
            (if (< x y)
                (mygcd x (rem y x))
              (mygcd (rem x y) y))))
      0)) ; any integer here
  :hooks (:fix)
  :measure (+ (nfix x) (nfix y))
  :prepwork ((local (include-book "arithmetic-5/top" :dir :system))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define positivep (x)
  :returns (yes/no booleanp)
  (and (integerp x)
       (> x 0))
  ///
  (defrule integerp-when-positivep
    (implies (positivep x)
             (integerp x))))

(std::deffixer positive-fix
  :pred positivep
  :body-fix 1)

(fty::deffixtype positive
  :pred positivep
  :fix positive-fix
  :equiv positive-equiv
  :define t
  :forward t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod myrational
  ((numerator int
              :reqfix (if (= (mygcd (myabs numerator) (myabs denominator)) 1)
                          numerator
                        0))
   (denominator positive
                :reqfix (if (= (mygcd (myabs numerator) (myabs denominator)) 1)
                            denominator
                          1)))
  :require (= (mygcd (myabs numerator) (myabs denominator)) 1)
  :pred myrationalp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist myrational-list
  :elt-type myrational
  :true-listp t
  :elementp-of-nil nil
  :pred myrational-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Matt K. mod for ACL2(r):
#+:non-standard-analysis
(local
 (defthm rationalp-implies-realp
   (implies (rationalp x) (realp x))))

(define lteq ((x myrationalp) (y myrationalp))
  :returns (b booleanp)
  (b* ((x (myrational-fix x))
       (y (myrational-fix y)))
    (<= (* (myrational->numerator x)
           (myrational->denominator y))
        (* (myrational->numerator y)
           (myrational->denominator x))))
  ///
  (defrule lteq_reflexive
    (implies (myrationalp x)
             (lteq x x))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ordered ((x myrational-listp))
  :returns (b booleanp)
  (b* ((x (myrational-list-fix x)))
    (if (endp x)
        t
      (if (endp (rest x))
          t
        (and (lteq (first x) (first (rest x)))
             (ordered (rest (rest x)))))))
  :measure (len (myrational-list-fix x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define permutation ((x myrational-listp) (y myrational-listp))
  :returns (b booleanp)
  (b* ((x (myrational-list-fix x))
       (y (myrational-list-fix y)))
    (if (endp x)
        (endp y)
      (if (endp y)
          nil
        (and (member-equal (car x) y)
             (permutation (cdr x) (remove1-equal (car x) y))))))
  :measure (len (myrational-list-fix x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defunvar ?sort (*) => *)

(define-sk2 sort_spec[?sort] ()
  (forall (in)
          (impliez (myrational-listp in)
                   (b* ((out (?sort in)))
                     (and (myrational-listp out)
                          (ordered out)
                          (permutation out in))))))
