; Prime fields library: cancellation using bind-free
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; TODO: Add theory-invariants.

(include-book "prime-fields")
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "bind-free-common")
(include-book "prime-fields-rules") ;needed just for some "add of neg" rules?
(local (include-book "kestrel/arithmetic-light/mod" :dir :system)) ;;for integerp of mod
(local (include-book "kestrel/utilities/symbol-term-alistp" :dir :system))

(defun negate-non-excluded-terms (terms p exclude-fns)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (pseudo-termp p)
                              (symbol-listp exclude-fns))
                  :guard-hints (("Goal" :in-theory (enable pseudo-term-listp)))))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (if (not (and (consp term)
                    (member-eq (ffn-symb term) exclude-fns)))
          (cons (if (acl2::call-of 'neg term)
                    (acl2::farg1 term)
                  ;; If cancelling a neg, we negate it by stripping the NEG:
                  `(neg ,term ,p))
                (negate-non-excluded-terms (rest terms) p exclude-fns))
        (negate-non-excluded-terms (rest terms) p exclude-fns)))))

(defthm pseudo-term-listp-of-negate-non-excluded-terms
  (implies (and (pseudo-term-listp terms)
                (pseudo-termp p))
           (pseudo-term-listp (negate-non-excluded-terms terms p exclude-fns)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(local
 (defthm pseudo-term-listp-of-intersection-equal
   (implies (and (pseudo-term-listp x)
                 (pseudo-term-listp y))
            (pseudo-term-listp (intersection-equal x y)))
   :hints (("Goal" :in-theory (enable pseudo-term-listp intersection-equal)))))

(defun bind-negated-sum-of-common-terms (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))))
  (if (not (or (acl2::call-of 'add x)
               (acl2::call-of 'add y)))
      nil ;; fail if neither side of the equality is an add
    (let* ((p (if (acl2::call-of 'add x)
                  (acl2::farg3 x)
                (acl2::farg3 y)))
           (x-addends (get-addends x p))
           (y-addends (get-addends y p))
           (common-addends (intersection-equal x-addends y-addends)))
      (let* ((exclude-fns '(if mod ifix add)) ;these indicate that things have not been simplified as we expect)
             (negations-of-common-addends (negate-non-excluded-terms common-addends p exclude-fns)))
        (if (not negations-of-common-addends)
            nil ;; fail (nothing to cancel)
          (if (or (intersection-equal x-addends negations-of-common-addends)
                  (intersection-equal y-addends negations-of-common-addends))
              nil ;; fail (something is wrong)
            ;; TODO: Think about how best to associate this nest:
            (acons 'negs (make-add-nest negations-of-common-addends p)
                   (acons 'p p nil))))))))

;; Just to check that the return type is right.
(local
 (defthm symbol-term-alistp-of-bind-negated-sum-of-common-terms
   (implies (and (pseudo-termp x)
                 (pseudo-termp y))
            (acl2::symbol-term-alistp (bind-negated-sum-of-common-terms x y)))
   :hints (("Goal" :in-theory (enable acl2::symbol-term-alistp)))))

;; TODO: Deal with constant multiples of terms...
(defthm equal-of-add-cancel-bind-free
  (implies (and (bind-free (bind-negated-sum-of-common-terms x y) (negs p))
                ;; (integerp negs) ;may help prevent loops
                (integerp p)
                (fep x p)
                (fep y p))
           (equal (equal x y)
                  (equal (add negs x p) (add negs y p))))
  :hints (("Goal" :in-theory (enable add equal-of-add-and-add-cancel ifix))))

;; Having both of these enabled will cause loops (other loops may be possible
;; as well, so its best not to include books defining both of these rules).
(theory-invariant (incompatible (:rewrite equal-of-add-and-add-cancel-1-gen)
                                (:rewrite equal-of-add-cancel-bind-free)))
