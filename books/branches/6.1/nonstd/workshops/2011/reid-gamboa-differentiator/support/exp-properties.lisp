(in-package "ACL2")

(include-book "nsa/exp-continuous" :dir :system)
(include-book "nsa-ex")

(defthm exp-limited-for-limited
  (implies (i-limited x)  
           (i-limited (acl2-exp x)))
  :hints (("Goal" 
           :in-theory (disable acl2-exp)
           :use (:instance i-close-limited-2
                           (x (acl2-exp x) )
                           (y (acl2-exp (standard-part x)))))))

(defthm close-to-standard-part
  (implies (i-close x y)
           (i-close (standard-part x) y))
  :hints (("Goal" :in-theory (enable nsa-theory))))

(defthm exp-continuous-for-limited
  (implies (and (i-limited x)
                (i-close x y))
           (i-close (acl2-exp x) (acl2-exp y)))
  :hints (("Goal"
           :in-theory (disable acl2-exp)
           :use ((:instance i-close-transitive
                           (x (acl2-exp x))
                           (y (acl2-exp (standard-part x)))
                           (z (acl2-exp y)))))))


(encapsulate
 nil

 ; The ln book already proves this theorem, but I don't want the
 ; rest of the book.
 (local (include-book "nsa/ln" :dir :system))

 (defthm exp-real-positive
   (implies (realp x)
            (< 0 (acl2-exp x)))
   :rule-classes (:type-prescription :rewrite :linear))

 (defthm acl2-exp-increasing
   (implies (and (realp x)
                 (realp y)
                 (< x y))
            (< (acl2-exp x) (acl2-exp y)))
   :rule-classes (:linear :rewrite))
 )

(encapsulate
 nil
 (local 

; Each term in the Taylor series expansion of exp is real...
  (defthm taylor-exp-list-real-list
    (implies (and (natp nterms)
                  (natp counter)
                  (realp x))
             (real-listp (taylor-exp-list nterms counter x)))
    :rule-classes (:type-prescription)))


; ...so exp itself is real.
 (defthm-std exp-real
   (implies (realp x)
            (realp (acl2-exp x)))
   :hints (("Goal" :in-theory (enable acl2-exp)
            :use (:instance taylor-exp-list-real-list
                            (nterms (i-large-integer))
                            (counter 0))))
   :rule-classes (:type-prescription :rewrite)))

;(local
; (include-book "nsa/ln" :dir :system))

;(defthm acl2-exp-1-1
;  (implies (and (acl2-numberp x)
;                (acl2-numberp y)
;                (<= 0 (imagpart x))
;                (< (imagpart x) (* 2 (acl2-pi)))
;                (<= 0 (imagpart y))
;                (< (imagpart y) (* 2 (acl2-pi)))
;                (equal (acl2-exp x) (acl2-exp y)))
;           (equal y x))
;  :hints (("Goal"
;           :in-theory (disable ln-exp E^IX-COS-I-SIN exp-complex  uniqueness-of-ln)
;           :use ((:instance uniqueness-of-ln (x x) (y (acl2-exp y)))
;                 (:instance ln-exp (x y)))))
;  :rule-classes nil)
           