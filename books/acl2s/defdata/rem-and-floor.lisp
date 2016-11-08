#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book);$ACL2s-Preamble$|#


(in-package "DEFDATA")

(encapsulate nil
  
  ;; load in & build up some theory on integer division
  
  (local (include-book "arithmetic-5/top" :dir :system))
  
  (defthm floor-less
    (implies (and (integerp x)
                  (< 0 x)
                  (integerp y)
                  (<= 2 y))
             (< (floor x y) x))
    :rule-classes (:linear :rewrite))
  
  (defthm floor-0
    (implies (equal x 0)
             (equal (floor x y) x)))
  
  (defthm floor-less-eq
    (implies (and (integerp x)
                  (<= 0 x)
                  (integerp y)
                  (<= 2 y))
             (<= (floor x y) x))
    :hints (("Goal" :in-theory (disable floor)
                    :cases ((< 0 x))))
    :rule-classes (:linear :rewrite))

  (defthm rem-floor-decomp
    (implies (and (integerp x)
                  (<= 0 x)
                  (integerp y)
                  (<= 0 y))
             (equal (+ (rem x y)
                       (* y
                          (floor x y)))
                    x)))
  
  (defthm rem-0
    (equal (rem 0 x)
           0))
  
  (defthm rem--0
    (implies (acl2-numberp x)
             (equal (rem x 0)
                    x)))
  
  (defthm rem-integerp
    (implies (and (integerp x)
                  (integerp y))
             (integerp (rem x y)))
    :rule-classes (:rewrite :type-prescription))
  
  (defthm rem-upper-bound
    (implies (and (integerp x) (<= 0 x)
                  (integerp y) (< 0 y))
             (<= (rem x y) x))
    :rule-classes (:linear :rewrite))

  (local (in-theory (disable rem)))
  
  (defthm rem-lower-bound2
    (implies (and (integerp x) (<= 0 x) (integerp y) (<= 0 y))
             (<= 0 (rem x y)))
    :rule-classes (:linear :rewrite)
    :hints (("Goal" :cases ((equal x 0)
                            (equal y 0)))))
  
  (defthm rem-upper-bound2
    (implies (and (integerp x) (<= 0 x) (integerp y) (< 0 y))
             (< (rem x y) y))
    :rule-classes (:linear :rewrite)
    :hints (("Goal" :cases ((equal x 0)))))
  
  (defthm floor-integerp
    (implies (and (integerp x)
                  (integerp y))
             (integerp (floor x y)))
    :rule-classes (:rewrite :type-prescription))
  
  (defthm floor-nat
    (implies (and (integerp x)
                  (<= 0 x)
                  (integerp y)
                  (<= 0 y))
             (<= 0 (floor x y)))
    :rule-classes (:linear :rewrite)))



