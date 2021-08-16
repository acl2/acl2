; Prime fields library: moving negated addends using bind-free
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFIELD")

;; An approach to moving NEG terms to the other sides of equalities
;; TODO: Disable cancellation rules if using the rule equal-of-add-move-negations.
;; TODO: Add theory-invariants.

(include-book "prime-fields")
(include-book "bind-free-common")
(include-book "prime-fields-rules") ;needed just for some "add of neg" rules?
(local (include-book "kestrel/arithmetic-light/mod" :dir :system)) ;;for integerp of mod
(local (include-book "kestrel/utilities/symbol-term-alistp" :dir :system))
(local (include-book "system/all-fnnames" :dir :system))

(local (in-theory (disable intersection-equal pseudo-term-listp)))

(local
 (defthm pseudo-term-listp-of-append
   (implies (and (pseudo-term-listp x)
                 (pseudo-term-listp y))
            (pseudo-term-listp (append x y)))
   :hints (("Goal" :in-theory (enable pseudo-term-listp)))))

(local
 (defthm pseudo-term-listp-of-cdr
   (implies (pseudo-term-listp x)
            (pseudo-term-listp (cdr x)))
   :hints (("Goal" :in-theory (enable pseudo-term-listp)))))

(local
 (defthm pseudo-termp-of-car
   (implies (pseudo-term-listp x)
            (pseudo-termp (car x)))
   :hints (("Goal" :in-theory (enable pseudo-term-listp)))))

;; Extract the addends of TERM, where TERM is a nest of calls to ADD with P as
;; the prime.
(defund get-addends (term p)
  (declare (xargs :guard (pseudo-termp term)
                  :guard-hints (("Goal" :in-theory (enable pseudo-term-listp)))))
  (if (and (acl2::call-of 'add term)
           (equal p (acl2::farg3 term)))
      (append (get-addends (acl2::farg1 term) p)
              (get-addends (acl2::farg2 term) p))
    (list term)))

(defthm pseudo-term-listp-of-get-addends
  (implies (pseudo-termp term)
           (pseudo-term-listp (get-addends term p)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp get-addends))))

;; Extract the elements of TERMS that are calls of NEG with P as the prime
(defun get-negated-addends (terms p exclude-fns)
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (pseudo-termp p)
                              (symbol-listp exclude-fns))
                  :guard-hints (("Goal" :in-theory (enable pseudo-term-listp)))))
  (if (endp terms)
      nil
    (let ((term (first terms)))
      (if (and (acl2::call-of 'neg term)
               (equal p (acl2::farg2 term)))
          (let ((negated-addend (acl2::farg1 term))) ;strip the neg
            (if (not (and (consp negated-addend)
                          (member-eq (ffn-symb negated-addend) exclude-fns)))
                (cons negated-addend
                      (get-negated-addends (rest terms) p exclude-fns))
              (get-negated-addends (rest terms) p exclude-fns)))
        (get-negated-addends (rest terms) p exclude-fns)))))

(defthm pseudo-term-listp-of-get-negated-addends
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (get-negated-addends terms p exclude-fns)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp))))

(defun bind-sum-of-negated-terms (x y)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y))
                  :guard-hints (("Goal" :in-theory (enable pseudo-term-listp)))))
  (if (not (or (acl2::call-of 'add x)
               (acl2::call-of 'add y)))
      nil ;; fail if neither side of the equality is an add
    (let* ((p (if (acl2::call-of 'add x)
                  (acl2::farg3 x)
                (acl2::farg3 y)))
           (x-addends (get-addends x p))
           (y-addends (get-addends y p))
           (exclude-fns '(if mod ifix add)) ;these indicate that things have not been simplified as we expect)
           ;; these have the NEG removed (TODO: fail if any is a call of neg?):
           (x-negated-addends (get-negated-addends x-addends p exclude-fns))
           (y-negated-addends (get-negated-addends y-addends p exclude-fns)))
      (if (or (intersection-equal x-addends x-negated-addends)
              (intersection-equal y-addends y-negated-addends))
          nil ;; fail (something is wrong because one side has both a term and its negation as addends
        ;; We to both sides the stripped versions of any negated addends that appear on either side:
        (let ((negated-addends (append x-negated-addends y-negated-addends)))
          (if (consp negated-addends)
              ;; TODO: Think about how best to associate this nest:
              (acons 'negs (make-add-nest negated-addends p)
                     (acons 'p p nil))
            nil ;fail
            ))))))

;; Just to check that the return type is right.
(local
 (defthm symbol-term-alistp-of-bind-sum-of-negated-terms
   (implies (and (pseudo-termp x)
                 (pseudo-termp y))
            (acl2::symbol-term-alistp (bind-sum-of-negated-terms x y)))
   :hints (("Goal" :in-theory (enable acl2::symbol-term-alistp)))))

;; The rule for moving negated addends to the other side.
;; Gather all the addends that are negated and add them (not negated) to both
;; sides.  Simplification should then combine the added items with the original
;; negated items, removing them all from the sums.
(defthm equal-of-add-move-negations-bind-free
  (implies (and (bind-free (bind-sum-of-negated-terms x y) (negs p))
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
                                (:rewrite equal-of-add-move-negations-bind-free)))

;; try to use rules 2a and 2b instead:
(in-theory (disable equal-of-add-move-negations-bind-free))

;;;
;;; rule 2 (simpler)
;;;

;; Returns a negated added (with the negation stripped) in a nest off adds with
;; prime p, or nil to indicate failure.
(defund find-negated-addend (term p)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (acl2::call-of 'neg term) ; (neg x p)
           (equal p (acl2::farg2 term)))
      (acl2::farg1 term) ; strip the neg
    (if (and (acl2::call-of 'add term)
             (equal p (acl2::farg3 term)))
        ;; todo: consider assuming the nest is assocated right...
        (or (find-negated-addend (acl2::farg1 term) p)
            (find-negated-addend (acl2::farg2 term) p))
      nil ;fail
      )))

;; Returns nil or an alist binding 'negated-addend and 'p.
(defund bind-a-negated-addend (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (not (acl2::call-of 'add term))
      nil ;fail TODO: Consider allowing a single negated added (the argument to neg would give us the prime, I guess)
    (if (member-eq 'bind-free-id (acl2::all-fnnames term))
        nil ; something has gone wrong with a previous bind-free attempt
      (let* ((p (acl2::farg3 term)) ; the prime in (add x y p)
             (maybe-negated-addend (find-negated-addend term p)))
        (if maybe-negated-addend
            (acons 'negated-addend maybe-negated-addend
                   (acons 'p p nil))
          nil ;fail
          )))))

(defthm equal-of-add-move-negations-bind-free-2a
  (implies (and (bind-free (bind-a-negated-addend x) (negated-addend p))
                ;;(integerp negated-addend) ;may help prevent loops?
                (integerp p)
                (fep x p)
                (fep y p))
           (equal (equal x y)
                  (equal (add (bind-free-id negated-addend) x p) ; we wrap the addend to help ensure this rule doesn't loop
                         (add negated-addend y p))))
  :hints (("Goal" :in-theory (enable;
                               equal-of-add-and-add-cancel
                              BIND-FREE-ID
                              ))))

(defthm equal-of-add-move-negations-bind-free-2b
  (implies (and (bind-free (bind-a-negated-addend y) (negated-addend p))
                ;;(integerp negated-addend) ;may help prevent loops?
                (integerp p)
                (fep x p)
                (fep y p))
           (equal (equal x y)
                  (equal (add negated-addend x p)
                         (add (bind-free-id negated-addend) y p)  ; we wrap the addend to help ensure this rule doesn't loop
                         )))
  :hints (("Goal" :in-theory (enable;
                               equal-of-add-and-add-cancel
                              BIND-FREE-ID
                              ))))

;; Rules to complete the job, by combining the addend (still wrapped in a call
;; of bind-free-id) with its negated version;

(defthm add-of-neg-same-arg2-gen-with-bind-free-id
  (equal (add (bind-free-id x) (neg x p) p)
         0)
  :hints (("Goal" :in-theory (enable bind-free-id))))

(defthm add-of-add-of-neg-same-with-bind-free-id
  (implies (posp p)
           (equal (add (bind-free-id x) (add (neg x p) y p) p)
                  ;; Can be further simplified but may introduce ifix:
                  (add 0 y p)))
  :hints (("Goal" :in-theory (enable bind-free-id))))
