(in-package "ACL2")


(include-book "meta/meta-times-equal" :dir :system)
(include-book "meta/meta-plus-equal" :dir :system)
(include-book "meta/meta-plus-lessp" :dir :system)

(include-book "common-factor-defuns")

(defthm mult-both-sides-of-equal
  (implies (and (case-split (acl2-numberp a))
                (case-split (acl2-numberp b))
                (case-split (acl2-numberp c))
                )
           (equal (equal (* a c) (* b c))
                  (if (equal c 0)
                      t
                    (equal a b))))
  :rule-classes nil)

;BOZO see a9
(defthm COMMUTATIVITY-2-OF-*
  (equal (* x (* y z)) (* y (* x z))))

;BOZO see a8
(defthm inverse-of-*-2
  (implies (and (case-split (acl2-numberp x))
                (case-split (not (equal x 0))))
           (equal (* x (* (/ x) y)) (fix y)))
  :hints (("Goal" :cases ((acl2-numberp x))))
  )

(defthm cancel-common-factors-in-equal
  (implies (and (bind-free (bind-k-to-common-factors lhs rhs) (k))
                (case-split (not (equal 0 k)))
                (case-split (acl2-numberp k))
                (case-split (acl2-numberp lhs))
                (case-split (acl2-numberp rhs))
                )
                (equal (equal lhs rhs)
                       (equal (* (/ k) lhs) (* (/ k) rhs))))
  :hints (("Goal" :use (:instance  mult-both-sides-of-equal (a lhs) (b rhs) (c (/ k))))))

(local (include-book "predicate"))
(local (include-book "fp2"))

;changed the var names 'cause "x" was too heavy
;BOZO gen?, rephrase
(defthm cancel-in-prods-<
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c))
           (equal (< (* a b) (* a c))
                  (if (equal 0 a)
                      nil
                    (if (> a 0)
                        (< b c)
                      (> b c))))))

;BOZO gen?
(defthm cancel-common-factors-in-<
  (implies (and (bind-free (bind-k-to-common-factors lhs rhs) (k))
                (syntaxp (not (equal lhs rhs))) ;don't apply to (< x x) since we can cause case-splits...
                ;BOZO is a check like the above needed for the equal case?  I'm guessing not...
                (case-split (not (equal 0 k)))
                (case-split (rationalp k))
                (case-split (rationalp lhs))
                (case-split (rationalp rhs))
                )
                (equal (< lhs rhs)
                       (if (< 0 k)
                           (< (* (/ k) lhs) (* (/ k) rhs))
                         (if (equal 0 k)
                             nil
                           (< (* (/ k) rhs) (* (/ k) lhs))
                           ))))
  :hints (("Goal" :use (:instance  cancel-in-prods-< (a lhs) (b rhs) (c (/ k))))))

(defun find-common-factors-to-cancel-1 (expr)
  (declare (xargs :guard (and (pseudo-termp expr))))
  (remove-cancelling-factor-pairs
   (find-common-factors-in-sum-of-products expr)))

(defund bind-k-to-common-factors-1 (expr)
  (declare (xargs :guard-hints (("Goal" :use (:instance remove-cancelling-factor-pairs-preserves-true-listp
                                                        (l (FIND-COMMON-FACTORS-IN-SUM-OF-PRODUCTS expr)))))
                  :guard (and (pseudo-termp expr))))
  (let* ((common-factor-list (find-common-factors-to-cancel-1 expr)))
    (if (endp common-factor-list)
        nil
      (list (cons 'k (make-product-from-list-of-factors common-factor-list))))))

(local (include-book "product"))

(defthm cancel-common-factors-in-equal-with-0
  (implies (and (bind-free (bind-k-to-common-factors-1 rhs) (k))
                (syntaxp (not (equal k rhs))) ;helps prevent loops
                (case-split (not (equal 0 k)))
                (case-split (rationalp k))
                (case-split (rationalp lhs))
                (case-split (rationalp rhs))
                )
           (equal (equal 0 rhs)
                  (or (equal 0 k) (equal 0 (* (/ k) rhs))))))

#|
;BOZO
(defthm cancel-common-factors-<-0
  (implies (and (bind-free (bind-k-to-common-factors-1 rhs) (k))
                (case-split (not (equal 0 k)))
                (case-split (rationalp k))
                (case-split (rationalp lhs))
                (case-split (rationalp rhs))
                )
           (equal (equal 0 rhs)
                  (or (equal 0 k) (equal 0 (* (/ k) rhs))))))
|#





;check that the inverse isn't a factor too...


;returns an alist binding k to the product of all common factors in term



