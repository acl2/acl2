; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "BAG")
(include-book "../lists/basic")
(include-book "../lists/memberp")

; bzo eventually, our rules will be about these names:

;; TEMP (jcd) - changed these to use backquotes.  Previously they were just
;; plain wrong, e.g., we had (defmacro bag-insert (a x) (cons a x)) which was
;; certainly the wrong thing.

(defmacro bag-insert (a x)
  `(cons ,a ,x))

(defmacro bag-sum (x y)
  `(append ,x ,y))

(defmacro bagp (x)
  (declare (ignore x))
  t)

(defmacro empty-bagp (x)
  `(not (consp ,x)))

;We have tried to follow the convention that elements are letters from the
;start of the alphabet (a,b,c) and bags are letters from the end of the
;alphabet (x,y,z).


;isn't nfix enabled?
(defthm not-zp-nfix-reduction
  (implies (not (zp n))
           (and (equal (nfix n)
                       n)
                (equal (nfix (1- n)) ;will this fire?  how do we normalize differences?
                       (1- n)))))

;isn't nfix enabled?
(defthm zp-nfix
  (implies (zp n)
           (equal (nfix n)
                  0)))

(defthm dumb
  (equal (< x x)
         nil))

;The affect of this is to rewrite an equality involving two predicates (one of
;which is <) into two implications.  move!
(defthm <-equal-rewrite
  (implies (booleanp z)
           (equal (equal (< x y) z)
                  (iff (< x y) z))))


;; jcd - bzo? remove this??
(defthm len-at-most-1-and-memberp-mean-len-exactly-1
  (implies (memberp a x) ;a is a free variable
           (equal (< 1 (len x))
                  (not (equal 1 (len x))))))

;; jcd - bzo? remove this??
(defthm x-equal-cons-own-car-rewrite
  (equal (EQUAL X (CONS (CAR X) y))
         (and (consp x)
              (equal y (cdr x)))))

;; jcd - bzo? remove this??
(defthm len-1-and-memberp-means-you-know-x
  (implies (memberp a x) ;a is a free variable
           (equal (equal 1 (len x))
                  (equal x (cons a (finalcdr x)))
                  )))




;;;
;;;
;;; remove-1
;;;
;;;

;Remove one copy (the first one) of element A from bag X.

;; jcd - changing this function to list fix its argument.

(defund remove-1 (a x)
  (declare (type t a x))
  (if (consp x)
      (if (equal a (car x))
          (list::fix (cdr x))
        (cons (car x) (remove-1 a (cdr x))))
    nil))

;; jcd - added this congruence
(defcong list::equiv equal (remove-1 a x) 2
  :hints(("Goal"
          :in-theory (enable remove-1)
          :induct (list::len-len-induction x x-equiv))))

;; jcd - strenghtened this rule since it is now always true.
;;
;; (defthm true-listp-of-remove-1
;;   (equal (true-listp (remove-1 a x))
;;          (true-listp x))
;;   :hints (("Goal" :in-theory (enable remove-1))))
(defthm true-listp-of-remove-1
  (true-listp (remove-1 a x))
  :hints(("Goal" :in-theory (enable remove-1))))


;; jcd - a stronger type prescription, (true-listp (remove-1 a x)), is
;; now automatically deduced, so we don't add this rule anymore.
;;
;; (defthm remove-1-true-listp-type-prescription
;;   (implies (true-listp x)
;;            (true-listp (remove-1 a x)))
;;   :rule-classes (:type-prescription)
;;   :hints (("Goal" :in-theory (enable remove-1))))


;; jcd - changed the right hand side to nil instead of x.
;; jcd - consider adding type prescription to do the same thing??
(defthm remove-1-of-non-consp
  (implies (not (consp x))
           (equal (remove-1 a x)
                  nil))
  :hints (("Goal" :in-theory (enable remove-1))))

;; jcd - changed the right hand side to nil instead of x.
(defthm remove-1-of-non-consp-cheap
  (implies (not (consp x))
           (equal (remove-1 a x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable remove-1))))

;; jcd - added a list fix here, changed base case to nil instead of x
(defthm remove-1-of-car
  (equal (remove-1 (car x) x)
         (if (consp x)
             (list::fix (cdr x))
           nil))
  :hints (("Goal" :in-theory (enable remove-1))))

(defthm car-of-remove-1
  (equal (car (remove-1 a x))
         (if (equal a (car x))
             (cadr x)
           (car x)))
  :hints (("Goal" :in-theory (enable remove-1))))

;; jcd - changed rhs to list-fix.
(defthm non-membership-remove-1
  (implies (not (memberp a x))
           (equal (remove-1 a x)
                  (list::fix x)))
  :hints (("Goal" :in-theory (enable remove-1))))

;; jcd - changed rhs to list-fix.
(defthm remove-1-of-cons-same
  (equal (remove-1 a (cons a x))
         (list::fix x))
  :hints (("Goal" :in-theory (enable remove-1))))

;will disable later
(defthm remove-1-of-cons-both
  (equal (remove-1 a (cons b x))
         (if (equal a b)
             (list::fix x) ;; jcd - changed to list::fix
           (cons b (remove-1 a x))))
  :hints (("Goal" :in-theory (enable remove-1))))

;something similar was named mem-rem
(defthm memberp-of-remove-1-irrel
  (implies (not (equal a b))
           (equal (memberp a (remove-1 b x))
                  (memberp a x)))
  :hints (("Goal" :in-theory (enable remove-1))))

;Note the backchain-limit.
(defthm memberp-of-remove-1-irrel-cheap
  (implies (not (equal a b))
           (equal (memberp a (remove-1 b x))
                  (memberp a x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable remove-1))))

(defthm list-fix-of-remove-1
  (equal (list::fix (remove-1 a x))
         (remove-1 a x))
  :hints (("Goal" :in-theory (enable remove-1))))

(defthm remove-1-of-remove-1
  (equal (remove-1 a (remove-1 b x))
         (remove-1 b (remove-1 a x)))
   :rule-classes ((:rewrite :loop-stopper ((a b))))
   :hints (("Goal" :in-theory (enable remove-1))))

(defthmd non-membership-removal-free
  (implies (and (not (memberp b x)) ;b is a free variable
                (equal b a))
           (equal (remove-1 a x)
                  (list::fix x)))) ; jcd - added list::fix

;expensive?
(defthm memberp-of-remove-1
  (implies (memberp a (remove-1 b x)) ;b is a free variable
           (memberp a x))
  :hints (("goal" :in-theory (enable remove-1))))

(defthm not-memberp-implies-not-memberp-remove-1
  (implies (not (memberp a x))
           (not (memberp a (remove-1 b x)))))

(defthm consp-remove-1-rewrite
  (equal (consp (remove-1 a x))
         (or (and (not (memberp a x))
                  (consp x))
             (< 1 (len x))))
  :hints (("Goal" :in-theory (enable remove-1))))

(encapsulate
 ()
 (local (defthm lemma1
          (implies (true-listp x)
                   (equal (equal x (remove-1 a x))
                          (not (memberp a x))))
          :hints(("Goal" :in-theory (enable remove-1 memberp)))))

 ;; jcd - added true-listp to the conclusion
 (defthm remove-1-does-nothing-rewrite
   (equal (equal x (remove-1 a x))
          (and (true-listp x)
               (not (memberp a x))))
   :hints(("Goal" :cases ((true-listp x))))))


;expensive?
(defthm memberp-x-remove-x-implies-memberp-x-remove-1-y
  (implies (and (syntaxp (not (equal a b))) ;prevents loops
                (memberp a (remove-1 a x)))
           (memberp a (remove-1 b x)))
  :hints (("Goal" :cases ((equal a b)))))

(defthmd equality-from-mem-and-remove
  (implies (and (not (memberp a (remove-1 b x)))
                (memberp a x))
           (equal b a))
  :rule-classes :forward-chaining)


;; jcd - added a list::fix to y.
(defthm remove-1-append
  (equal (remove-1 a (append x y))
         (if (memberp a x)
             (append (remove-1 a x) (list::fix y))
           (append x (remove-1 a y))))
  :hints (("Goal" :in-theory (enable append))))

;; jcd - this theorem becomes really lousy with our changes to remove-1,
;; because append does not properly list::fix its result.  Is this a reason to
;; consider dropping append for a different function?  I've changed the
;; equivalence to list::equiv in the meantime.
(defthmd append-of-remove-1-one
  (list::equiv (append (remove-1 a x) y)
             (if (memberp a x)
                 (remove-1 a (append x y))
               (append x y))))

;improve?
(defthmd append-of-remove-1-two
  (implies (not (memberp a x))
           (equal (append x (remove-1 a y))
                  (remove-1 a (append x y)))))

(theory-invariant (incompatible (:rewrite append-of-remove-1-one)
                                (:rewrite remove-1-append)))

(theory-invariant (incompatible (:rewrite append-of-remove-1-two)
                                (:rewrite remove-1-append)))


;; jcd - looks like we can remove this, it was commented out when I found it.
;;
;; (defthm memberp-remove-implication
;;   (implies (and (not (memberp x (remove-1 y list)))
;;                 (memberp x list))
;;            (equal y x))
;;   :rule-classes :forward-chaining)


;; jcd - looks like we can remove this, it was local defthmd and commented
;; out when I found it.
;;
;; (local (defthmd memberp-remove-implication-rw
;;          (implies (and (not (memberp a (remove-1 b x)))
;;                        (not (equal b a)))
;;             (not (memberp a x)))))

(defthm len-of-remove-1
  (equal (len (remove-1 a x))
         (if (memberp a x)
             (+ -1 (len x))
           (len x)))
  :hints (("Goal" :in-theory (enable len))))

;strengthen?  (what exactly does acl2-count of remove-1 equal?)
(defthm acl2-count-of-remove-1-decreases-when-memberp
  (implies (memberp a bag)
           (< (acl2-count (remove-1 a bag))
              (acl2-count bag)))
  :hints (("Goal" :induct t :in-theory (enable remove-1))))

;seemed to cause problems...
(defthmd cons-car-onto-remove-1-of-cdr
  (implies (and (not (equal (car x) b))
                (consp x))
           (equal (cons (car x) (remove-1 b (cdr x)))
                  (remove-1 b x)))
  :hints (("Goal" :in-theory (enable remove-1))))



;;;
;;;
;;; remove-bag
;;;
;;;

;; jcd - changed remove-bag to list::fix its result
(defund remove-bag (x y)
  (declare (type t x y))
  (if (consp x)
      (remove-bag (cdr x) (remove-1 (car x) y))
    (list::fix y)))

;; jcd - added this congruence
(encapsulate
 ()
 (local (defun my-induction (x x-equiv y)
          (if (consp x)
              (my-induction (cdr x) (cdr x-equiv) (remove-1 (car x) y))
            (list x x-equiv y))))

 (defcong list::equiv equal (remove-bag x y) 1
   :hints(("Goal"
           :in-theory (enable remove-bag)
           :induct (my-induction x x-equiv y)))))

;; jcd - added this congruence
(defcong list::equiv equal (remove-bag x y) 2
  :hints(("Goal" :in-theory (enable remove-bag))))

;; jcd - fixed the macro here, originally it was (defmacro bag-difference (x y)
;; (remove-bag y x)), but of course it needs to be quoted and escaped properly.
(defmacro bag-difference (x y)
  `(remove-bag ,y ,x))

;; jcd - changed rhs to list::fix
(defthm remove-bag-of-nil-one
  (equal (remove-bag nil x)
         (list::fix x))
  :hints (("Goal" :in-theory (enable remove-bag))))

;; jcd - redundant with remove-bag-of-non-consp-cheap?
(defthm remove-bag-of-nil-two
  (equal (remove-bag x nil)
         nil)
  :hints (("Goal" :in-theory (enable remove-bag))))

;; jcd - changed rhs to nil.  consider type prescription?
(defthm remove-bag-of-non-consp
  (implies (not (consp y))
           (equal (remove-bag x y)
                  nil))
  :hints (("Goal" :in-theory (enable remove-bag))))

;; jcd - changed rhs to nil.
(defthm remove-bag-of-non-consp-cheap
  (implies (not (consp y))
           (equal (remove-bag x y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable remove-bag))))

;; jcd - removed this, we now inferred that (remove-bag x y) always returns
;; a true list.
;;
;; (defthm true-listp-remove-bag
;;   (equal (true-listp (remove-bag x y))
;;          (true-listp y))
;;   :hints (("Goal" :in-theory (enable remove-bag))))

;; jcd - this was commented out when I found it.  Do we want to consider
;; adding it or rules like it, e.g., type prescription rules for consp?
;;
;; (defthm remove-bag-x-not-consp
;;   (implies (not (consp y))
;;            (not (consp (remove-bag x y)))))

;; jcd - removed this, remove-bag doesn't do the same as it used to.
;;
;; ;proof that the new version of remove-bag does the same thing as the old version:
;; (encapsulate
;;  ()
;;  (local
;;   (defund remove-bag-old (list1 list2)
;;           (declare (type t list1 list2))
;;           (if (consp list1)
;;               (if (memberp (car list1) list2)
;;                   (let ((list2 (remove-1 (car list1) list2)))
;;                     (remove-bag-old (cdr list1) list2))
;;                 (remove-bag-old (cdr list1) list2))
;;             list2)))
;;
;;  (local
;;   (defthm remove-bag-old-and-new-match
;;     (equal (remove-bag-old x y)
;;            (remove-bag     x y))
;;   :hints (("Goal" :in-theory (enable remove-bag remove-bag-old)))
;;   ))
;;  )

;; jcd - changed rhs from (finalcdr x) to nil.
(defthm remove-bag-self
  (equal (remove-bag x x)
         nil)
  :hints (("Goal" :in-theory (enable remove-bag))))

(defthm memberp-of-remove-bag-means-memberp
  (implies (memberp a (remove-bag x y))
           (memberp a y))
  :hints (("goal" :in-theory (enable memberp remove-bag))))

;; jcd - changed rhs to list::fix y
(defthm remove-bag-not-consp-x
  (implies (not (consp x))
           (equal (remove-bag x y)
                  (list::fix y)))
  :hints (("Goal" :in-theory (enable remove-bag))))

;; bzo (jcd) - This is horrible! Can we get rid of it?
(defthm remove-bag-unit
  (implies (equal x y)
           (not (consp (remove-bag x y)))))

(defthm remove-bag-of-cons-non-memberp
  (implies (not (memberp a x))
           (equal (remove-bag x (cons a y))
                  (cons a (remove-bag x y))))
  :hints (("Goal" :in-theory (enable remove-bag))))

;; jcd - looks like we can just remove this, it was commented out before I
;; found it.  in any event, subbagp should not be in the name of this theorem.
;;
;; (defthmd subbagp-implies-subbagp-append-rec-not-consp-version
;;   (implies (not (consp (remove-bag list blk1)))
;;            (not (consp (remove-bag (append blk2 list) blk1))))
;;   :hints (("Goal" :in-theory (disable subbagp-implies-subbagp-append-rec)
;;            :use ((:instance subbagp-implies-subbagp-append-rec)))))

;; jcd - remove this?  it was commented out when i found it.
;;
;; (defthm not-remove-bag-implies-not-remove-bag-remove-1
;;   (implies (not (consp (remove-bag x y)))
;;            (not (consp (remove-bag x (remove-1 a y))))))

(defthmd not-remove-bag-cons-implies-memberp
  (implies (not (remove-bag x (cons a y)))
           (memberp a x))
  :rule-classes (:forward-chaining))

;subsumed?
(defthm remove-bag-adds-no-terms
  (implies (not (memberp a y))
           (not (memberp a (remove-bag x y))))
  :hints (("Goal" :in-theory (enable remove-bag))))

(defthm remove-bag-cons
  (equal (remove-bag (cons a x) y)
         (remove-1 a (remove-bag x y)))
  :hints (("Goal" :in-theory (enable remove-bag))))


(defthm remove-bag-remove-1
  (equal (remove-bag x (remove-1 a y))
         (remove-1 a (remove-bag x y)))
  :hints (("Goal" :in-theory (enable remove-bag))))

;disable?
(defthm remove-1-implies-remove-bag-singleton
  (implies (and (not (remove-1 a (remove-bag x y))) ;a is a free var
                (remove-bag x y))
           (equal (remove-bag x y)
                  (list a)))
  :hints (("Goal" :in-theory (enable remove-1
                                     remove-bag))))


(encapsulate
 ()

;bzo
 (local
  (defthm cons-remove-1-not-equal
    (implies (not (equal a b))
             (equal (cons a (remove-1 b x))
                    (remove-1 b (cons a x))))))

 (defthm remove-bag-cons-remove-1-not-equal
   (implies (not (equal a b))
            (equal (remove-bag x (cons a (remove-1 b y)))
                   (remove-1 b (remove-bag x (cons a y)))))
   :hints (("goal" :in-theory (disable remove-1
                                       REMOVE-1-OF-CONS-BOTH
                                       )))
   ))

;loop?
(defthmd remove-1-of-remove-bag
  (equal (remove-1 a (remove-bag x y))
         (remove-bag x (remove-1 a y))))

(theory-invariant (incompatible (:rewrite remove-1-of-remove-bag)
                                (:rewrite remove-bag-remove-1)))

(theory-invariant (incompatible (:rewrite remove-1-of-remove-bag)
                                (:rewrite remove-bag-cons-remove-1-not-equal) ;bzo think about this
                                ))



(local (defthm membership-remove-bag-reduction
         (implies (and (consp y)
                       (memberp (car y) x))
                  (equal (remove-bag x y)
                         (remove-bag (remove-1 (car y) x) (cdr y))))
         :hints (("Goal"
                  :in-theory (e/d (remove-bag)
                                  (REMOVE-BAG-REMOVE-1 ; bzo
                                   consp-remove-1-rewrite ; speedup
                                   remove-bag-of-non-consp ; speedup
                                   ))))))

;rename params
;this sort of recurses down the second argument to remove-bag, whereas the definition of remove-bag recurses down the first argument.
(defthmd remove-bag-reduction
  (implies (consp y)
           (equal (remove-bag x y)
                  (if (memberp (car y) x)
                      (remove-bag (remove-1 (car y) x) (cdr y))
                    (cons (car y)
                          (remove-bag x (cdr y)))))))

(encapsulate
 ()
 (local
  (defthm remove-bag-of-remove-1-of-car-and-cdr-helper
    (implies (true-listp x) ;gen?
             (equal (remove-bag (remove-1 (car x) y) (cdr x))
                    (if (memberp (car x) y)
                        (remove-bag y x)
                      (remove-bag y (cdr x)))))
    :hints (("Goal"
             :in-theory (enable remove-bag)))))

    ;improve this?
 (defthmd remove-bag-of-remove-1-of-car-and-cdr
   (equal (remove-bag (remove-1 (car x) y) (cdr x))
          (if (not (consp x))
              nil
            (if (memberp (car x) y) ;move this if to the outside?
                (remove-bag y x)
              (remove-bag y (cdr x)))))
   :hints (("Goal" :use (:instance remove-bag-of-remove-1-of-car-and-cdr-helper))))
 )

(theory-invariant (incompatible (:rewrite remove-bag-of-remove-1-of-car-and-cdr)
                                (:rewrite membership-remove-bag-reduction)))

;was expensive when enabled?
(defthmd remove-bag-append
  (equal (remove-bag x (append y z))
         (append (remove-bag x y)
                 (remove-bag (remove-bag y x) z)))
  :hints (("Goal" :in-theory (e/d (remove-bag
                                   append-of-remove-1-two
                                   append-of-remove-1-one)
                                  (remove-1-append)))))


;drop?
(defthmd membership-extraction
  (implies (and (not (memberp a x))
                (memberp a y))
           (consp (remove-bag x y)))
  :hints(("Goal" :in-theory (enable remove-bag))))

;drop?
(defthmd membership-extraction-instance
  (implies (and (not (memberp a x))
                (memberp a (remove-1 a y)))
           (consp (remove-bag x (remove-1 a y))))
  :hints(("Goal" :use (:instance membership-extraction
                                 (y (remove-1 a y))))))


(defthm append-remove-bag
  (equal (remove-bag (append x y) z)
         (remove-bag y (remove-bag x z)))
  :hints (("Goal" :in-theory (enable append))))


(defthmd memberp-of-remove-bag-irrel
  (implies (not (memberp a x))
           (equal (memberp a (remove-bag x y))
                  (memberp a y)))
  :hints (("Goal" :in-theory (enable remove-bag))))

;rename?
(defthm remove-1-remove-bag-memberp
  (implies (memberp a x)
           (equal (remove-1 a (remove-bag (remove-1 a x) y))
                  (remove-bag x y)))
  :hints (("Goal" :in-theory (enable remove-bag))))

;; jcd - changed rhs to list::fix
;bzo renamed -2 because of clash..
;rename
(defthm remove-bag-append-2
  (equal (remove-bag x (append x y))
         (list::fix y))
  :hints (("goal" :in-theory (enable binary-append remove-bag))))

(defthm remove-bag-over-remove-1
  (equal (remove-bag x (remove-1 a y))
         (remove-1 a (remove-bag x y)))
  :hints (("Goal" :in-theory (enable remove-bag))))

;bad name
(defthmd remove-bag-consp
  (implies (consp x)
           (equal (remove-bag x y)
                  (remove-1 (car x) (remove-bag (cdr x) y))))
  :hints (("goal" :do-not-induct t
           :in-theory (enable memberp
                              remove-bag
                              REMOVE-BAG-ADDS-NO-TERMS
                              remove-bag-over-remove-1))))


;rename
(defthm remove-1-not-memberp
  (implies (not (memberp a y))
           (equal (remove-1 a (remove-bag x y))
                  (remove-bag x y)))
  :hints (("Goal" :in-theory (enable remove-bag))))

;was called remove-bag-over-remove-bag
(defthm remove-bag-commutativity-2
  (equal (remove-bag x (remove-bag y z))
         (remove-bag y (remove-bag x z)))
   :rule-classes ((:rewrite :loop-stopper ((x y))))
   :hints (("Goal" :in-theory (enable remove-bag))))


;; jcd - removing this rule, it is trivial with our congruence rule for
;; list::equiv over remove-bag 1.
;;
;; (defthm remove-bag-of-list-fix-one
;;   (equal (remove-bag (list::fix x) y)
;;          (remove-bag x y))
;;   :hints (("Goal" :in-theory (enable remove-bag list::fix))))



;; jcd - Removing this theorem, this should be trivial now that remove-bag
;; always returns a true list.
;;
;; jcd - Strenghtened the rhs from (remove-bag x (list::fix y)) to (remove-bag x
;; y).
;;
;; (defthm list-fix-of-remove-bag
;;   (equal (list::fix (remove-bag x y))
;;          (remove-bag x y))
;;   :hints (("Goal" :in-theory (enable remove-bag))))

(defthm remove-bag-of-singleton
  (equal (remove-bag (list a) x)
         (remove-1 a x)))





;;
;;
;; subbagp
;;
;;

;Eric's new definition
(defund subbagp (x y)
  (declare (type t x y))
  (if (consp x)
      (and (memberp (car x) y)
           (subbagp (cdr x) (remove-1 (car x) y)))
      t))

;; An old definition:
;; (defun subbagp (list1 list2)
;;   (declare (type t list1 list2))
;;   (not (consp (remove-bag list2 list1))))

;; jcd - consider removing this?  are we not satisifed that subbagp is what
;; we want?
(local (encapsulate
;This proves that Eric's new version of subbagp matches the old version.
        ()
        ;;The version of subbagp we used to have:
        (local (defun old-subset (list1 list2)
                 (declare (type t list1 list2))
                 (not (consp (remove-bag list2 list1)))))

        ;;The new version matches the old one.
        (local (defthm subsets-match
                 (equal (old-subset x y)
                        (subbagp x y))
                 :hints(("Goal" :in-theory (enable subbagp)))))))


;Make sure subbagp's :type-prescription rule is as strong as we think.
(encapsulate
 ()
 (local (defthm subbagp-type-prescription-test
          (booleanp (subbagp x y))
          :hints (("Goal" :in-theory (union-theories '(booleanp
                                                       (:type-prescription subbagp))
                                                     (theory 'minimal-theory)))))))

;; jcd - added this congruence
(encapsulate
 ()
 (local (defun my-induction (x x-equiv y)
          (if (consp x)
              (my-induction (cdr x) (cdr x-equiv) (remove-1 (car x) y))
            (list x x-equiv y))))

 (defcong list::equiv equal (subbagp x y) 1
   :hints(("Goal" :in-theory (enable subbagp)
           :induct (my-induction x x-equiv y)))))

;; jcd - added this congruence
(defcong list::equiv equal (subbagp x y) 2
  :hints(("Goal" :in-theory (enable subbagp))))

;; jcd - redundant with subbagp-of-non-consp-one-cheap?
(defthm subbagp-nil-x
  (subbagp nil x)
  :hints (("goal" :in-theory (enable subbagp))))

(defthm subbagp-of-non-consp-one
  (implies (not (consp x))
           (subbagp x y))
  :hints (("Goal" :in-theory (enable subbagp))))

;; jcd - consider adding type prescription equivalent??
(defthm subbagp-of-non-consp-one-cheap
  (implies (not (consp x))
           (subbagp x y))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm subbagp-of-non-consp-two
  (implies (not (consp y))
           (equal (subbagp x y)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable subbagp))))

;; jcd - consider adding type prescription equivalent??
(defthm subbagp-of-non-consp-two-cheap
  (implies (not (consp y))
           (equal (subbagp x y)
                  (not (consp x))))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; jcd - what is this crazy rule?  subsumed by our regular boolean
;; rewrite?
(defthm equal-of-subbagp-becomes-iff
  (implies (booleanp z)
           (equal (equal (subbagp x y) z)
                  (iff (subbagp x y) z))))

;; jcd - removing this rule, we don't need it with the congruence
;; (defthm subbagp-of-list-fix-one
;;   (equal (subbagp (list::fix x) y)
;;          (subbagp x y))
;;   :hints (("Goal" :in-theory (enable subbagp list::fix))))

;; jcd - removing this rule, we don't need it with the new congruence
;; ;bzo more like this?
;; (defthm subbagp-of-list-fix-two
;;   (equal (subbagp x (list::fix y))
;;          (subbagp x y))
;;   :hints (("Goal" :in-theory (enable subbagp list::fix))))

(defthm subbagp-of-cons-non-member
  (implies (not (memberp a y))
           (equal (subbagp (cons a x) y)
                  nil))
  :hints (("Goal" :in-theory (enable subbagp))))

;bzo loops with defn subbagp! -think about this..
;move the hyp to the conclusion?
(defthmd subbagp-of-remove-1-two
  (implies (memberp a y)
           (equal (subbagp x (remove-1 a y))
                  (subbagp (cons a x) y)))
  :hints (("Goal" :in-theory (enable subbagp))))

(defthm subbagp-of-cons
  (equal (subbagp (cons a x) y)
         (and (memberp a y)
              (subbagp x (remove-1 a y))))
  :hints (("Goal" :in-theory (enable subbagp-of-remove-1-two))))

(theory-invariant (incompatible (:rewrite subbagp-of-cons)
                                (:rewrite subbagp-of-remove-1-two)))

(defthm subbagp-of-remove-1-implies-subbagp
  (implies (subbagp x (remove-1 a y)) ;a is a free variable
           (subbagp x y))
  :hints (("Goal" :in-theory (enable subbagp))))

(defthm subbagp-implies-subbagp-cons
  (implies (subbagp x y)
           (subbagp x (cons a y)))
  :hints (("Goal" :in-theory (enable subbagp)
           :expand (subbagp x (cons a y))
           :induct (subbagp x y))))

;make into an equal rule?
;less general that our subbagp of cons rule
;bzo rename...
(defthm subbagp-cons
  (implies (subbagp x y)
           (subbagp (cons a x)
                    (cons a y)))
  :hints (("Goal" :in-theory (enable subbagp))))

(defthm subbagp-implies-subbagp-append-rec
  (implies (subbagp x z)
           (subbagp x (append y z)))
  :hints (("Goal" :in-theory (enable append))))

;make a -two version?
(defthm subbagp-of-cons-irrel
  (implies (not (memberp a x))
           (equal (subbagp x (cons a y))
                  (subbagp x y)))
  :hints (("Goal" :in-theory (enable subbagp))))

;; bzo lengthy proof
(defthm subbagp-of-remove-1-and-remove-1
  (implies (and (memberp a x)
                (memberp a y))
           (equal (subbagp (remove-1 a x) (remove-1 a y))
                  (subbagp x y)))
 :hints (("Goal" :in-theory (enable subbagp))))

(defthm subbagp-of-remove-1-and-remove-1-strong
  (equal (subbagp (remove-1 a x) (remove-1 a y))
         (if (memberp a x)
             (if (memberp a y)
                 (subbagp x y)
               (subbagp (remove-1 a x) y))
           (if (memberp a y)
               (subbagp x (remove-1 a y))
             (subbagp x y)))))

(defthm subbagp-of-remove-1-of-car-and-cdr
  (equal (subbagp (remove-1 (car y) x) (cdr y))
         (if (consp y)
             (if (memberp (car y) x)
                 (subbagp x y) ;the usual case
               (subbagp x (cdr y)))
           (if (memberp nil x)
               (or (equal x nil)
                   (and (consp x)
                        (equal (car x) nil)
                        (not (consp (cdr x)))))
             (not (consp x)))))
  :hints (("Goal"
           :use (:instance subbagp-of-remove-1-and-remove-1 (a (car y)))
           :in-theory (disable subbagp-of-remove-1-and-remove-1
                               SUBBAGP-OF-REMOVE-1-AND-REMOVE-1-STRONG))))

;; jcd - removed (true-listp y) hypothesis
(defthm subbagp-means-remove-bag-is-nil
  (implies (subbagp y x)
           (equal (remove-bag x y)
                  nil))
  :hints (("Goal" :in-theory (enable remove-bag))))

;add a remove-bag iff rule?
(defthm consp-remove-bag-rewrite
  (equal (consp (remove-bag x y))
         (not (subbagp y x)))
  :hints (("Goal" :in-theory (enable remove-bag))))

;could be expensive?
;rename?
(defthm memberp-subbagp
  (implies (and (memberp a y) ;y is a free variable
                (subbagp y x))
           (memberp a x))
  :hints (("Goal" :in-theory (enable subbagp))))

(defthmd memberp-subbagp-alt
  (implies (and (subbagp y x) ;y is a free variable
                (memberp a y))
           (memberp a x)))

;was called subbagp-x-x
(defthm subbagp-self
  (subbagp x x)
  :hints (("Goal" :in-theory (enable subbagp))))

;why is car in the name?
(defthm subbagp-implies-subbagp-append-car
  (implies (subbagp x y)
           (subbagp x (append y z)))
  :hints (("Goal" :in-theory (enable subbagp))))


;; jcd - can we get rid of this?  it was commented when I found it.
;;
;; (defthm subbagp-implies-subbagp-append-car-not-consp-version
;;   (implies (not (consp (remove-bag blk2 blk1)))
;;            (not (consp (remove-bag (append blk2 list) blk1)))))

(defthm subbagp-of-remove-1-irrel
  (implies (not (memberp a x))
           (equal (subbagp x (remove-1 a y))
                  (subbagp x y)))
  :hints (("Goal" :in-theory (e/d (subbagp)
                                  (memberp-subbagp) ; minor speed boost
                                  ))))

(defthm subbagp-append-append-left
  (implies (subbagp x z)
           (subbagp (append x y) (append z y)))
  :hints (("Goal"
           :in-theory (enable subbagp))))

(defthm subbagp-append-append
  (implies (and (subbagp x z)
                (subbagp y w))
           (subbagp (append x y)
                    (append z w)))
  :hints (("Goal" :in-theory (enable subbagp))))

(defthm subbagp-implies-subbagp-of-remove-1
  (implies (subbagp x y)
           (subbagp (remove-1 a x) y))
  :hints (("Goal" :in-theory (e/d (subbagp)
                                  (memberp-subbagp) ; minor speed boost
                                  ))))



(defthm subbagp-implies-common-members-are-irrelevant
  (implies (subbagp x y)
           (subbagp (remove-1 a x)
                    (remove-1 a y))))

;bzo maybe we want to leave the remove-1 where it is??
(defthm subbagp-of-remove-1-both
  (equal (subbagp (remove-1 a x) y)
         (if (memberp a x)
             (subbagp x (cons a y))
           (subbagp x y)))
  :hints (("Goal"
           :in-theory (e/d (subbagp)
                           ;; disables give a minor speed boost
                           (memberp-subbagp consp-remove-1-rewrite)))))

;bzo also prove one which reverses the lhs?
(defthm subbagp-cdr
  (subbagp (cdr x) x))

;use a perm rule?
(defthm subbagp-of-cons-of-remove-1
  (equal (subbagp x (cons a (remove-1 a y)))
         (if (memberp a y)
             (subbagp x y)
           (subbagp x (cons a y))))
  :hints (("Goal" :in-theory (e/d (subbagp)
                                  (memberp-subbagp) ; minor speed boost
                                  ))))

(encapsulate
 ()
 ;; jcd - making this local!
 (local (defun subbagp-subbagp-induction (a b c)
          (declare (type t a b c))
          (if (consp c)
              (let ((a (remove-1 (car c) a))
                    (b (remove-1 (car c) b)))
                (subbagp-subbagp-induction a b (cdr c)))
            (cons a b))))

 (defthm subbagp-chaining
   (implies (and (subbagp x z) ;z is a free variable
                 (subbagp z y))
            (subbagp x y))
   :hints (("goal" :in-theory (e/d (subbagp)
                                   (memberp-subbagp)) ; minor speed boost
            :induct (subbagp-subbagp-induction z x y)))))


;bzo expensive?
;rename to mention car?
(defthm subbagp-implies-membership
  (implies (subbagp x y)
           (equal (memberp (car x) y)
                  (if (consp x)
                      t
                    (memberp nil y)))))

(defthm subbagp-implies-remove-bag
   (implies (subbagp y z)
            (subbagp (remove-bag x y)
                     (remove-bag x z)))
   :hints (("Goal" :in-theory (enable remove-bag))))


;reverse lhs too?
(defthm subbagp-remove-1
  (subbagp (remove-1 a x) x))

;rename?
(defthm subbagp-remove
  (implies (subbagp x (remove-1 a y))
           (subbagp x y)))

(defthm subbagp-remove-bag
  (implies (subbagp x (remove-bag z y))
           (subbagp x y))
  :hints (("Goal" :in-theory (enable remove-bag))))


;expensive?
(defthm subbagp-remove-bag-append ;make conclusion into equal?
  (implies (subbagp (remove-bag x y) z)
           (subbagp y (append x z)))
  :hints (("goal" :in-theory (enable remove-bag))))

#|
(defthm subbagp-cdr-remove-1
  (implies (subbagp x y)
           (subbagp (cdr x) (remove-1 (car x) y)))
  :hints (("Goal" :in-theory (enable subbagp))))
|#

(defthmd subbagp-cons-car-memberp
  (implies (subbagp (cons a x) y)
           (memberp a y))
  :hints (("Goal" :in-theory (enable subbagp))))

;which way do we want to rewrite this?
(defthmd subbagp-cons-to-subbagp-remove-1
  (implies (memberp a x)
           (equal (subbagp x (cons a y))
                  (subbagp (remove-1 a x) y)))
  :hints (("goal" :in-theory (enable subbagp remove-bag))))

(defthmd subbagp-append-to-subbagp-remove-bag
  (implies (subbagp y x)
           (equal (subbagp x (append y z))
                  (subbagp (remove-bag y x) z)))
  :hints (("goal" :in-theory (e/d (remove-bag)
                                  (consp-remove-1-rewrite) ; minor speedup
                                  ))))

;make an -alt version
(defthm subbagp-false-from-witness
  (implies (and (memberp a x) ; a is a free variable
                (not (memberp a y)))
           (equal (subbagp x y)
                  nil)))

(defthm subbagp-implies-subbagp-cons-common
  (equal (subbagp (cons a x) (cons a y))
         (subbagp x y))
  :hints (("goal" :in-theory (enable subbagp))))

(defthm subbagp-implies-subbagp-append-common
  (equal (subbagp (append x y) (append x z))
         (subbagp y z))
  :hints (("goal" :in-theory (enable subbagp append))))

(defthm memberp-subbagp-remove-1-memberp-remove-bag
  (implies (and (memberp a y)
                (subbagp x (remove-1 a y)))
           (memberp a (remove-bag x y)))
  :hints(("Goal" :in-theory (enable remove-bag
                                    equality-from-mem-and-remove
                                    ))))

;bzo name clashed with something in gacc, so I added the -2.  did all
;references to this get updated?
(defthm subbagp-append-2
  (implies (subbagp x z)
           (subbagp x (append y z))))

;could be expensive?
(defthmd subbagp-cdr-lemma
  (implies (and (not (subbagp y (cdr x)))
                (subbagp y x)
                (consp x))
           (memberp (car x) y)))


(defthm subbagp-memberp-remove-1
  (implies (and (subbagp x (remove-1 a y))
                (memberp a y))
           (subbagp (cons a x) y))
  :hints (("goal" :in-theory (enable subbagp))))

(defthm subbagp-remove-bag-subbagp-append
  (implies (and (subbagp y (remove-bag x z))
                (subbagp x z))
           (subbagp (append x y) z))
  :hints (("goal" :in-theory (e/d (subbagp)
                                  (consp-remove-1-rewrite ; speedup
                                   subbagp-of-non-consp-two ; speedup
                                   subbagp-chaining ; speedup
                                   subbagp-cdr-lemma ; speedup
                                   )))))

(defthmd subbagp-subbagp-cdr
  (implies (subbagp x y)
           (subbagp x (cons a y))))

(defthmd not-subbagp-remove-1
  (implies (not (subbagp x y))
           (not (subbagp x (remove-1 a y)))))

(defthm subbagp-of-cdr
  (implies (subbagp x y)
           (subbagp (cdr x) y))
  :hints (("Goal" :in-theory (enable subbagp))))

;; jcd - changed the rhs to list::fix the final argument to append
(defthm remove-bag-of-append-when-subbagp
  (implies (subbagp x y)
           (equal (remove-bag x (append y z))
                  (append (remove-bag x y) (list::fix z))))
  :hints(("Goal"
           :in-theory (e/d (subbagp remove-bag)
                           (consp-remove-1-rewrite ; speedup
                            subbagp-cdr-lemma ; speedup
                            subbagp-of-non-consp-two ; speedup
                            subbagp-chaining ; speedup
                            subbagp-implies-membership ; speedup
                            )))))

;drop?
(defthm not-subbagp-of-cons-from-not-subbagp
  (implies (not (subbagp x y))
           (not (subbagp (cons a x) y))))

(defthm subbagp-cdr-remove-1-rewrite
  (equal (subbagp (cdr x) (remove-1 (car x) y))
         (if (memberp (car x) y)
             (subbagp x y)
           (subbagp (cdr x) y)))
  :hints (("Goal" :in-theory (enable subbagp))))

(theory-invariant (incompatible (:rewrite subbagp-cdr-remove-1-rewrite)
                                (:definition subbagp)))

(defthm subbagp-of-remove-bag-and-remove-bag
  (implies (subbagp x y)
           (subbagp (remove-bag z x)
                    (remove-bag z y))))

(defthm subbagp-of-remove-bag
  (subbagp (remove-bag x y) y)
  :hints (("Goal" :in-theory (enable remove-bag))))

(defthm subbagp-of-remove-bag-and-remove-bag-2
  (implies (subbagp x2 x)
           (subbagp (remove-bag x bag) (remove-bag x2 bag)))
  :hints (("Goal" :in-theory (e/d (subbagp remove-bag)
                                  (subbagp-cdr-remove-1-rewrite ; incompatible
                                   consp-remove-1-rewrite ; speedup
                                   subbagp-of-non-consp-two ; speedup
                                   subbagp-chaining ; speedup
                                   consp-remove-bag-rewrite ; speedup
                                   subbagp-cdr-lemma ; speedup
                                   subbagp-of-cdr ; speedup
                                   )))))

(defthm subbagp-of-remove-bag-and-remove-1
  (implies (memberp a x)
           (subbagp (remove-bag x bag)
                    (remove-1 a bag)))
  :hints  (("Goal"
            :in-theory (disable subbagp-of-remove-bag-and-remove-bag-2)
            :use ((:instance subbagp-of-remove-bag-and-remove-bag-2
                             (x2 (list a)))))))



;;
;;
;; perm
;;
;;

(defund perm (x y)
  (declare (type t x y))
  (if (atom x)
      (atom y)
    (if (memberp (car x) y)
        (perm (cdr x) (remove-1 (car x) y))
      nil)))

;; jcd - fixed this macro, before it was (defmacro bag-equal (x y) (perm x y)).
;; Now it properly quotes the perm and so forth.

(defmacro bag-equal (x y)
  `(perm ,x ,y))


;could be expensive! ;trying to use just perm-nil-rewrite
;drop?
(defthmd perm-nil-y
  (implies (perm nil y)
           (not (consp y)))
  :hints (("Goal" :in-theory (enable perm))))

;make an alt version?
(defthm perm-nil-rewrite
  (equal (perm nil x)
         (not (consp x)))
  :hints (("Goal" :in-theory (enable perm))))

;; do we want this rule?  put it back for the forward chaining?
;; (defthmd perm-not-consp-nil
;;   (implies (not (consp x))
;;            (perm nil x))
;;   :hints (("Goal" :in-theory (enable perm)))
;;   :rule-classes :forward-chaining)

(defthm perm-of-non-consp-one
  (implies (not (consp x))
           (equal (perm x y)
                  (not (consp y))))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-of-non-consp-two
  (implies (not (consp y))
           (equal (perm x y)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable perm))))

(encapsulate
 ()

 (local (defun my-induction (x x-equiv y)
          (if (consp x)
              (my-induction (cdr x) (cdr x-equiv) (remove-1 (car x) y))
            (list x x-equiv y))))

 ;; jcd - added this congruence.  keep this local because in a moment we will
 ;; show that perm is a refinement of list::equiv, and this becomes trivial.  See
 ;; the notes right after (defrefinement list::equiv perm) for more.
 (local (defcong list::equiv equal (perm x y) 1
          :hints(("Goal"
                  :in-theory (enable perm)
                  :induct (my-induction x x-equiv y)))))

 ;; jcd - added this congruence.  keep this local because in a moment we will
 ;; show that perm is a refinement of list::equiv, and this becomes trivial.  See
 ;; the notes right after (defrefinement list::equiv perm) for more.
 (local (defcong list::equiv equal (perm x y) 2
          :hints(("Goal"
                  :in-theory (enable perm)))))

 ;; jcd - make this local?
 ;;make a -one version?
 (defthmd perm-of-cons-two
   (equal (perm x (cons a y))
          (if (memberp a x)
              (perm (remove-1 a x) y)
            nil))
   :hints (("Goal" :in-theory (enable perm)
            :induct (perm x y))))

 ;; jcd - i initially thought there was no reason to leave this enabled, since
 ;; we know that perm is an equivalence.  However, it turns out that this is
 ;; actually useful and necessary for, e.g., perm-with-cdr-of-self-rewrite.  I
 ;; wonder if this implies we should always be proving "both rules".
 (defthm perm-commutative
   (equal (perm x y)
          (perm y x))
   :rule-classes ((:rewrite :loop-stopper ((x y))))
   :hints (("Goal" :in-theory (enable perm perm-of-cons-two))))

 (local (defthm perm-x-x
          (perm x x)
          :hints (("Goal" :in-theory (enable perm)))))

 ;; jcd - keep this local?
 (local (defthm perm-of-remove-1-and-remove-1-blah
          (implies (perm x y)
                   (perm (remove-1 a x) (remove-1 a y)))
          :hints (("Goal" :in-theory (e/d (perm
                                           perm-of-cons-two)
                                          (perm-of-non-consp-one
                                           perm-of-non-consp-two))))))

 ;; jcd - i wondered why this is local, but then realized that in a few lemmas
 ;; we'll prove that perm is a congruence over memberp, so there is no reason
 ;; to have this theorem afterwards.
 (local (defthm perm-memberp
          (implies (and (perm x y)
                        (memberp a x))
                   (memberp a y))
          :hints (("Goal" :in-theory (enable perm)))))

 (local (defthm perm-transitivity
          (implies (and (perm x y)
                        (perm y z))
                   (perm x z))
          :hints (("Goal" :in-theory (enable perm)))))

 (defequiv perm)

 )

;; jcd - added the following refinement rule.  Note that, because of this rule,
;; the following congruences are not necessary, and in fact it is an error to
;; submit them after the refinement rule has been processed.
;;
;; (defcong list::equiv equal (perm x y) 1)
;; (defcong list::equiv equal (perm x y) 2)

(defrefinement list::equiv perm
  :hints(("Goal" :in-theory (enable perm))))


;; jcd - why do we want this crazy thing?
(defthm equal-perm-to-iff
  (implies (booleanp z)
           (equal (equal (perm x y) z)
                  (iff (perm x y) z))))

(defthm not-perm-of-cons-onto-same
  (equal (perm x (cons a x))
         nil)
  :hints (("Goal" :in-theory (enable perm))))


;; jcd - note that to get this through, I had to leave perm-commutative enabled
;; so that not-perm-of-cons-onto-same could get a chance to fire.  I think we
;; might want to prove "both versions" of not-perm-of-cons-onto-same instead?
;; Is this an insight that should be applied to other theorems as well?

;alt version?
(defthm perm-with-cdr-of-self-rewrite
  (equal (perm x (cdr x))
         (not (consp x))))

;; jcd - removed this, it's redundant with our congruences/refinements
;; (defthm perm-of-list-fix-two
;;   (equal (perm x (list::fix y))
;;          (perm x y))
;;   :hints (("Goal" :in-theory (enable perm list::fix))))

;; jcd - removed this, it's redundant with our congruences/refinements.
;; (defthm perm-of-list-fix-one
;;   (equal (perm (list::fix x) y)
;;          (perm x y)))

(defcong perm perm (cons a x) 2
  :hints (("Goal" :in-theory (enable perm))))

(defcong perm equal (memberp a x) 2
  :hints (("Goal" :in-theory (enable perm))))

(defcong perm perm (append x y) 2
  :hints (("Goal" :in-theory (enable append))))

(defthm perm-of-cons-to-false
  (implies (not (memberp a x))
           (equal (perm x (cons a y))
                  nil))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-of-cons-to-false-alt
  (implies (not (memberp a x))
           (equal (perm (cons a y) x)
                  nil)))

;was called cons-association
(defthm commutativity-2-of-cons-inside-perm
  (perm (cons a (cons b x))
        (cons b (cons a x)))
  :rule-classes ((:rewrite :loop-stopper ((a b))))
  :hints (("Goal" :in-theory (enable perm))))

(defthm append-2-over-cons
  (perm (append x (cons a y))
        (cons a (append x y)))
  :hints (("Goal" :in-theory (enable append))))

;was called append-association
(defthm commutativity-2-of-append-inside-perm
  (perm (append y (append x z))
        (append x (append y z)))
  :rule-classes ((:rewrite :loop-stopper ((y x))))
  :hints (("Goal" :in-theory (enable perm append))))

;; jcd - getting rid of this theorem since we have the duplicate theorem
;; perm-of-cons-and-cons below, and it has a better name.
;;
;; (defthm cons-common-reduction
;;   (equal (perm (cons a x)
;;                (cons a y))
;;          (perm x y))
;;   :hints (("Goal" :in-theory (enable perm))))

;; jcd - getting rid of this theorem since we already have the duplicate
;; theorem perm-cons-x-y-z below, and it has a better name.  (dammit man,
;; how do you disable anything when you prove theorems three times!)
;;
;; (defthm perm-cons-x-y-z
;;   (equal (perm (cons a x)
;;                (cons a y))
;;          (perm x y))
;;   :hints (("goal" :in-theory (enable perm))))

(defthm perm-of-cons-and-cons
  (equal (perm (cons a x)
               (cons a y))
         (perm x y))
   :hints (("Goal" :in-theory (enable perm))))


;; jcd - getting rid of this theorem since it duplicates the theorem
;; below.
;;
;; ;bzo ;add the two "cross" cases for this.
;; (defthm perm-append-x-y-z
;;   (equal (perm (append x y)
;;                (append x z))
;;          (perm y z))
;;   :hints (("goal" :in-theory (enable binary-append perm))))

;rename
(defthm append-common-reduction
  (equal (perm (append x y)
               (append x z))
         (perm y z))
  :hints (("Goal" :in-theory (enable append))))



;; jcd - removing this rule.  we already have this for list::equiv, and since
;; list::equiv refines perm, this is kind of like proving (iff foo bar) after
;; you already have proven (equal foo bar).
;;
;; (defthm perm-of-finalcdr
;;   (perm (finalcdr x)
;;         nil))

;instead move remove-1 outside of append within a perm context??
(defthm perm-cons-append
  (implies (memberp a y)
           (perm (cons a (append x (remove-1 a y)))
                 (append x y)))
   :hints (("goal" :in-theory (e/d (append perm)
                                   (consp-remove-1-rewrite) ; minor speedup
                                   ))))



(defthm perm-append-remove-1
  (implies (and (memberp a y)
                (memberp a x))
           (perm (append x (remove-1 a y))
                 (append (remove-1 a x) y)))
  :hints (("Goal" :in-theory (e/d (append)
                                  (consp-remove-1-rewrite) ; minor speedup
                                  ))))


(encapsulate
 ()
 (local (defun my-induction (x x-equiv y)
          (if (consp x)
              (my-induction (cdr x) (cdr x-equiv) (remove-1 (car x) y))
            (list x x-equiv y))))

 (local (defun bad-boy (x y)
          (if (consp x)
              (if (memberp (car x) y)
                  (bad-boy (cdr x) (remove-1 (car x) y))
                (list (car x)))
            (if (consp y) (list (car y)) nil))))

 (local (defcong list::equiv equal (bad-boy x y) 1
          :hints(("goal" :induct (my-induction x x-equiv y)))))

 (local (defthm perm-has-no-badboy
          (equal (perm x y)
                 (not (bad-boy x y)))
          :hints (("goal" :in-theory (enable perm)))))

 (defcong perm perm (remove-1 a x) 2
   :hints(("Goal" :in-theory (disable consp-remove-1-rewrite
                                      memberp-subbagp))))

 )


(encapsulate
 ()
 (local (defthm perm-remove-bag
          (implies (and (perm y z)
                        (syntaxp (not (term-order y z))))
                   (perm (remove-bag x y)
                         (remove-bag x z)))
          :hints (("Goal" :in-theory (enable remove-bag perm)))))

 (local (defthm perm-remove-bag-2
          (implies (and (perm x z)
                        (syntaxp (not (term-order x z))))
                   (equal (remove-bag x y)
                          (remove-bag z y)))
          :hints (("Goal" :in-theory (enable remove-bag perm)))))

 (defcong perm equal (remove-bag x y) 1)
 (defcong perm perm (remove-bag x y) 2)
 )


;loops with defn perm?
(defthmd perm-of-cdr-x-and-remove-1-of-car-x
  (equal (perm (cdr x) (remove-1 (car x) y))
         (if (consp x)
             (if (memberp (car x) y)
                 (perm x y)
               (perm (cdr x) y))
           (or (not (consp y)) ;weird case
               (and (equal (car y) nil)
                    (not (consp (cdr y)))))))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-cons-remove
  (implies (memberp a x) ;handle other case?
           (perm (cons a (remove-1 a x))
                 x))
  :hints (("Goal" :in-theory (enable perm))))

(defthm perm-of-remove-1-and-remove-1
  (implies (and (memberp a x) ;handle other case?
                (memberp a y))
           (equal (perm (remove-1 a x) (remove-1 a y))
                  (perm x y)))
  :hints (("Goal"
           :use (:instance perm-of-cons-and-cons
                           (x (remove-1 a x)) (y (remove-1 a y)))
           :in-theory (disable perm-of-cons-and-cons
                               perm-implies-perm-cons-2
                               ))))

(defthm perm-of-remove-1-and-remove-1-strong
  (equal (perm (remove-1 a x) (remove-1 a y))
         (if (memberp a x)
             (if (memberp a y)
                 (perm x y)
               (perm (remove-1 a x) y)
               )
           (if (memberp a y)
               (perm x (remove-1 a y))
             (perm x y)))))

;drop?
(local (defthmd perm-membership-reduction
         (implies (and (memberp a x)
                       (memberp a y)
                       (syntaxp (not (term-order x y))))
                  (equal (perm x y)
                         (perm (remove-1 a x)
                               (remove-1 a y))))))




;; jcd - bzo subsumed by append-commutative-inside-perm?
(defthmd subbagp-perm-append-remove-bag
  (implies (subbagp y z)
           (perm (append x (remove-bag y z))
                 (remove-bag y (append x z))))
  :hints (("goal" :in-theory (e/d (remove-bag)
                                  (remove-bag-append
                                   consp-remove-1-rewrite
                                   )))))

(defthm remove-bag-append-reduction
  (implies (subbagp x z)
           (perm (remove-bag x (append y z))
                 (append y (remove-bag x z))))
  :hints (("Goal" :in-theory (e/d (remove-bag)
                                  (consp-remove-1-rewrite))
           :use (:instance subbagp-perm-append-remove-bag))))

;can split cases
;rename
(defthm cons-onto-remove
  (perm (cons a (remove-1 a x))
        (if (memberp a x)
            x
          (cons a x))))

(defthm perm-of-cons-memberp-case
  (implies (memberp a x)
           (equal (perm x (cons a y))
                  (perm (remove-1 a x) y))))

(defthm perm-of-cons-non-memberp-case
  (implies (not (memberp a x))
           (equal (perm x (cons a y))
                  nil)))

;make an -alt?
(defthm perm-of-cons
  (equal (perm x (cons a y))
         (if (memberp a x)
             (perm (remove-1 a x) y)
           nil)))

;was called perm-append-a-b
(defthm append-commutative-inside-perm
  (perm (append x y)
        (append y x))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("goal" :in-theory (e/d (append)
                                  (append-2-over-cons
                                   consp-remove-1-rewrite
                                   subbagp-implies-membership)))))

;; jcd - try to move closer to append-common-reduction?  horrible name...
(defthm perm-append-y-z-a
  (equal (perm (append x z)
               (append y z))
         (perm x y))
  :hints (("Goal"
           :in-theory (disable append-common-reduction)
           :use (:instance append-common-reduction
                           (x z) (y y) (z x)))))

(defcong perm perm (append x y) 1)

(defthmd append-of-cons-under-perm
  (perm (append x (cons a y))
        (cons a (append x y))))

(defthm append-of-remove-1-and-cons
  (perm (append (remove-1 a x)
                (cons a y))
        (if (memberp a x)
            (append x y)
          (append x (cons a y))))
  :hints (("Goal" :in-theory (enable append))))


;this seems ungeneral.  there are all sorts of calls to perm with two append
;nests which could have common stuff "cancelled".  (consider a bind-free rule).

(defthm perm-append-x-a-y-append-a-z
  (equal (perm (append w z)
               (append x (append w y)))
         (perm z (append x y))))


;; jcd - This is a good congruence rule.  the perm assumption is weaker than
;; list::equiv, so we get more information out of this than we do from the same
;; rule for list::equiv.

(defcong perm equal (len x) 1
  :hints (("Goal" :in-theory (enable len perm))))

;; jcd - removing this rule which is redundant with the defcong above and,
;; incidentally, terrible.
;;
;; ;can loop? ;kill now that we have the defcong?
;; (defthmd perm-means-len-equal
;;   (implies (perm x y)
;;            (equal (len x)
;;                   (len y)))
;;   :hints (("Goal" :in-theory (enable perm))))


(defcong perm equal (consp x) 1
  :hints(("goal" :in-theory (enable perm))))

;; jcd - removing the following rule: we know that remove-1 returns perm
;; results under perm, so with our new rule above about consp we are set.
;;
;; ;trying disabled.
;; ;drop?
;; (defthmd perm-consp-remove-1
;;   (implies (perm x y)
;;            (equal (consp (remove-1 a x))
;;                   (consp (remove-1 a y)))))


;; jcd - removing this rule since it's just a bad repeat of our above
;; congruence rule.
;;
;; ;drop?
;; (defthm perm-implies-consp-correlation
;;   (implies (perm x y)
;;            (equal (consp x)
;;                   (consp y)))
;;   :rule-classes nil
;;   :hints (("Goal" :in-theory (enable perm))))

(defcong perm equal (subbagp x y) 1
   :hints (("goal"
            :in-theory (e/d (subbagp perm)
                            (subbagp-cdr-remove-1-rewrite ; incompatible
                             )))))

(defcong perm equal (subbagp x y) 2
   :hints (("goal"
            :in-theory (e/d (subbagp)
                            (subbagp-cdr-remove-1-rewrite ; incompatible
                             )))))



;bzo PERM-APPEND-REMOVE-1 loops with APPEND-COMMUTATIVE-INSIDE-PERM

;bzo REMOVE-1-APPEND-REDUCTION loops with APPEND-COMMUTATIVE-INSIDE-PERM and
;remove-1-append

;bzo think about REMOVE-1-APPEND-REDUCTION vs. PERM-APPEND-REMOVE-1

(in-theory (disable PERM-APPEND-REMOVE-1)) ;bzo

(defthm append-remove-1-reduction
  (implies (memberp a x)
           (perm (append (remove-1 a x) y)
                 (remove-1 a (append x y)))))

;; jcd - added list::fix to rhs
;bzo move
(defthmd remove-1-of-append-when-memberp
  (implies (memberp a x)
           (equal (remove-1 a (append x y))
                  (append (remove-1 a x) (list::fix y))))
  :hints (("Goal" :in-theory (enable remove-1))))

(theory-invariant (incompatible (:rewrite append-remove-1-reduction)
                                (:rewrite remove-1-of-append-when-memberp)))

(in-theory (disable remove-1-append))

;should this go the other way?
(defthmd remove-1-append-reduction
  (implies (memberp a y)
           (perm (append x (remove-1 a y))
                 (remove-1 a (append x y))))
  :hints (("goal" :in-theory (disable append-remove-1-reduction)
           :use (:instance append-remove-1-reduction (x y) (y x)))))


(defthm cons-remove-1-perm
  (implies (memberp a x)
           (perm (cons a (remove-1 a x))
                 x)))

(defthm remove-bag-remove-1-reduction
  (implies (and (memberp a x)
                (subbagp x y))
           (perm (remove-bag (remove-1 a x) y)
                 (cons a (remove-bag x y)))))

(defthmd perm-becomes-two-subbagp-claims
  (equal (perm x y)
         (and (subbagp x y)
              (subbagp y x)))
  :hints (("Goal" :in-theory (enable perm))))

;looped with defn perm
(defthmd perm-of-remove-1-one
  (equal (perm x (remove-1 a y))
         (if (memberp a y)
             (perm (cons a x) y)
           (perm x y))))

(defthmd perm-of-remove-1-two
  (equal (perm (remove-1 a y) x)
         (if (memberp a y)
             (perm (cons a x) y)
           (perm x y))))

;make an alt version?
(defthmd perm-cons-reduction
  (implies (memberp a y)
           (equal (perm (cons a x) y)
                  (perm x (remove-1 a y)))))

(theory-invariant (incompatible (:rewrite perm-cons-reduction)
                                (:rewrite perm-of-remove-1-two)))

(defthm perm-append-remove
  (implies (subbagp x y)
           (perm (append (remove-bag x y) x)
                 y))
  :hints (("Goal" :in-theory (enable perm-of-remove-1-one
                                     append))))

;bzo move or kill
(defthm perm-nil-reduction
  (and (equal (perm nil x)
              (atom x))
       (equal (perm x nil)
              (atom x)))
  :hints (("goal" :in-theory (enable perm))))

(defthm perm-subbagp-subbagp
  (implies (and (perm z y) ;z is a free var
                (subbagp x z))
           (subbagp x y)))

;rename. dup?
(defthm remove-1-cons
  (implies (memberp a x)
           (perm (cons a (remove-1 a x))
                  x)))


(defthm perm-of-append-of-remove-bag-same
  (implies (subbagp x y)
           (perm (append x (remove-bag x y))
                 y))
  :hints (("Goal" :in-theory (e/d (subbagp)
                                  (subbagp-cdr-remove-1-rewrite ; incompat
                                   consp-remove-1-rewrite ; speedup
                                   consp-remove-bag-rewrite ; speedup
                                   subbagp-cdr-lemma ; speedup
                                   subbagp-of-non-consp-two ; speedup
                                   )))))

(defthmd perm-of-append-one
  (implies (subbagp x z)
           (equal (perm (append x y) z)
                  (perm y (remove-bag x z)))))

(defthmd perm-of-append-two
  (implies (subbagp y x)
           (equal (perm x (append y z))
                  (perm z (remove-bag y x)))))

(defthmd perm-of-remove-bag-one
  (implies (subbagp x y)
           (equal (perm (remove-bag x y) z)
                  (perm (append x z) y))))

(defthmd perm-of-remove-bag-two
  (implies (subbagp y z)
           (equal (perm x (remove-bag y z))
                  (perm (append y x) z)))
  :hints (("Goal" :in-theory (disable perm-of-remove-bag-one)
           :use (:instance perm-of-remove-bag-one (x y) (y z) (z x)))))

(defthm perm-of-remove-bag-and-remove-bag
  (implies (and (subbagp x y)
                (subbagp x z))
           (equal (perm (remove-bag x y)
                        (remove-bag x z))
                  (perm y z)))
  :hints (("Goal" :in-theory (enable perm-of-remove-bag-one))))

(defthm append-of-remove-1-under-perm
  (implies (and (syntaxp (term-order y x)) ;prevents loops - moves the remove-1 to the heavier term (where maybe it'll cancel with something)
                (memberp a x))
           (perm (append x (remove-1 a y))
                 (if (memberp a y)
                     (append (remove-1 a x) y)
                   (append x y))))
  :hints (("Goal" :in-theory (enable append))))

(defthm perm-of-remove-1-means-not-memberp
  (equal (perm x (remove-1 a x))
         (not (memberp a x)))
  :hints (("Goal" :in-theory (enable remove-1 perm))))

(defthm perm-of-remove-1-means-not-memberp-alt
  (equal (perm (remove-1 a x) x)
         (not (memberp a x)))
  :hints (("Goal" :in-theory (enable remove-1 perm))))

(defthm perm-of-singleton
  (equal (perm (list a) x)
         (and (consp x)
              (equal a (car x))
              (endp (cdr x))))
  :hints (("Goal" :in-theory (enable perm))))

;; jcd - this doesn't mention perm so I'd like to move it up, but its proof
;; relies upon append-2-over-cons
(defthm not-subbagp-of-append-from-not-subbagp
  (implies (not (subbagp x y))
           (not (subbagp (append a x) y)))
  :hints (("Goal" :in-theory (e/d (subbagp)
                                  (subbagp-cdr-remove-1-rewrite ;incompatible
                                   consp-remove-1-rewrite ; speedup
                                   subbagp-remove-bag-subbagp-append ; speedup
                                   subbagp-of-non-consp-two ; speedup
                                   memberp-subbagp ; speedup
                                   subbagp-of-cdr ; speedup
                                   consp-remove-bag-rewrite ; speedup
                                   )))))

;;
;;
;; disjoint
;;
;;

(include-book "../lists/disjoint")

;Make sure disjoint's :type-prescription rule is as strong as we think.
;Don't remove this just because its has no effect on the world.
(encapsulate
 ()
 (local (defthm disjoint-type-prescription-test
          (booleanp (disjoint a x))
          :hints (("Goal"  :in-theory (union-theories '(booleanp
                                                       (:type-prescription disjoint))
                                                     (theory 'minimal-theory)))))))


;; jcd - added this rule
(defcong list::equiv equal (disjoint x y) 1
  :hints(("Goal"
          :in-theory (enable disjoint)
          :induct (list::len-len-induction x x-equiv))))

;; jcd - added this rule
(defcong list::equiv equal (disjoint x y) 2
  :hints(("Goal" :in-theory (enable disjoint))))

;; bzo jcd - We should eventually add rules that say perm is congruent over
;; disjoint.

(defthm disjoint-of-cons-one
  (equal (disjoint (cons a x) y)
         (and (not (memberp a y))
              (disjoint x y)))
    :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-of-cons-two
  (equal (disjoint x (cons a y))
         (and (not (memberp a x))
              (disjoint x y)))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-of-non-consp-one
  (implies (not (consp x))
           (equal (disjoint x y)
                  t))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-of-non-consp-two
  (implies (not (consp y))
           (equal (disjoint x y)
                  t))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-commutative
  (equal (disjoint x y)
         (disjoint y x))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :in-theory (enable disjoint))))

; something similar was called disjoint-equal-append
(defthm disjoint-of-append-one
  (equal (disjoint (append x y) z)
         (and (disjoint x z)
              (disjoint y z)))
  :hints (("Goal" :in-theory (enable append))))

(defthm disjoint-of-append-two
  (equal (disjoint x (append y z))
         (and (disjoint x y)
              (disjoint x z)))
  :hints (("Goal" :in-theory (enable append))))

;could be expensive?
;rename
;-alt version?
;was called memberp-from-disjoint-memberp
(defthm memberp-false-from-disjointness
  (implies (and (disjoint x y) ;x is a free var
                (memberp a x))
           (equal (memberp a y)
                  nil))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-despite-remove-1-two
  (implies (disjoint x y)
           (disjoint x (remove-1 a y)))
    :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-despite-remove-1-one
  (implies (disjoint x y)
           (disjoint (remove-1 a x) y)))

(defthm disjoint-remove-bag-backchain-1
  (implies (disjoint x z)
           (disjoint x (remove-bag y z)))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-remove-bag-backchain-2
  (implies (disjoint y z)
           (disjoint (remove-bag x y) z)))

;drop?
(defthm subbagp-not-disjoint
  (implies (and (subbagp x y)
                (consp x))
           (not (disjoint x y)))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthmd subbagp-means-rarely-disjoint
  (implies (subbagp x y)
           (equal (disjoint x y)
                  (not (consp x))))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthmd subbagp-means-rarely-disjoint-two
  (implies (subbagp y x)
           (equal (disjoint x y)
                  (not (consp y))))
  :hints (("Goal" :in-theory (enable disjoint))))

;bzo rename params on these?
;rename?
(defthm subbagp-disjoint
   (implies (and (disjoint w z)
                 (subbagp x w)
                 (subbagp y z))
            (disjoint x y))
   :hints (("goal" :in-theory (e/d (disjoint subbagp)
                                   (subbagp-cdr-remove-1-rewrite ; incompat
                                    ))))
   :rule-classes (:rewrite :forward-chaining))

(defthm subbagp-disjoint-commute
   (implies (and (disjoint w z)
                 (subbagp x z)
                 (subbagp y w))
            (disjoint x y))
   :hints (("Goal" :in-theory (disable subbagp-disjoint)
           :use (:instance subbagp-disjoint (w z) (z w)))))

(defcong perm equal (disjoint x y) 2
  :hints (("goal" :in-theory (enable disjoint))))

(defcong perm equal (disjoint x y) 1
  :hints (("goal"
           :use ((:instance perm-implies-equal-disjoint-2
                            (x y) (y x) (y-equiv x-equiv)))
           :in-theory (disable perm-implies-equal-disjoint-2))))


(defthm memberp-car-when-disjoint
  (implies (disjoint x y)
           (equal (memberp (car x) y)
                  (if (not (consp x))
                      (memberp nil y)
                    nil))))

(defthm memberp-car-when-disjoint-cheap
  (implies (disjoint x y)
           (equal (memberp (car x) y)
                  (if (not (consp x))
                      (memberp nil y)
                    nil)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; jcd - added list fix to rhs
(defthm remove-bag-does-nothing
  (implies (disjoint x y)
           (equal (remove-bag x y)
                  (list::fix y)))
  :hints (("Goal" :in-theory (enable remove-bag disjoint))))

(defthmd remove-bag-append-disjoint
  (implies (disjoint y x)
           (equal (remove-bag x (append y z))
                  (append y (remove-bag x z))))
  :hints (("Goal" :in-theory (enable remove-bag-append))))

(defthmd disjoint-memberp-implies-non-membership
  (implies (and (disjoint x y) ;y is a free variable
                (memberp a y))
           (equal (memberp a x)
                  nil)))

;changing disjoint could improve this rule..
(defthm disjoint-self-means-not-consp
  (equal (disjoint x x)
         (not (consp x)))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthmd disjoint-subbagp-rewrite
     (implies (disjoint x y )
              (equal (subbagp x y)
                     (not (consp x))))
     :hints (("goal" :in-theory (enable disjoint))))

;; jcd - removing this rule, it is trivial with our congruence rule for perm
;; over disjoint 2.
;; (defthm disjoint-of-list-fix-two
;;   (equal (disjoint x (list::fix y))
;;          (disjoint x y))
;;   :hints (("Goal" :in-theory (enable list::fix disjoint))))

;; ;; jcd - removing this rule, it is trivial with our congruence rule for perm
;; ;; over disjoint 1.
;; (defthm disjoint-of-list-fix-one
;;   (equal (disjoint (list::fix x) y)
;;          (disjoint x y)))

;the stuff below may duplicate other stuff...

;this is interesting - should we worry about when (car z) might be a cons,
;whose second argument is an append?
(defthm disjoint-append-reduction
  (implies (syntaxp (not (and (consp z)
                              (equal (car z) 'binary-append))))
           (equal (disjoint x (append y z))
                  (and (disjoint x y)
                       (disjoint x z)))))

;bzo
(defthm disjoint-of-cons-reduce-cheap
  (implies (disjoint x y)
           (equal (disjoint x (cons a y))
                  (not (memberp a x))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable disjoint))))

;bzo
(defthmd disjoint-append
  (implies (disjoint x y)
           (equal (disjoint x (append y z))
                  (disjoint x z)))
  :hints (("goal" :induct (append y z)
           :in-theory (enable binary-append disjoint))))

(defthm disjoint-with-remove-1-of-irrel
  (implies (not (memberp a x))
           (equal (disjoint x (remove-1 a y))
                  (disjoint x y)))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-removed-memberp
  (implies (and (subbagp z x)
                (disjoint x (remove-bag x y)))
           (disjoint (remove-bag x y) z)))

;bzo rename params?
(defthm disjoint-removed-memberp-commute
  (implies (and (subbagp z x)
                (disjoint x (remove-bag x y)))
           (disjoint z (remove-bag x y))))

;; jcd - changed rhs to list::fix
(defthmd disjoint-remove-bag
  (implies (disjoint x y)
           (equal (remove-bag x y)
                  (list::fix y)))
  :hints (("goal" :in-theory (enable disjoint))))


;do we already have this?
(defthm disjoint-of-remove-bag-irrel
  (implies (disjoint x z)
           (equal (disjoint (remove-bag x y) z)
                  (disjoint y z)))
  :hints(("Goal" :in-theory (e/d (disjoint)
                                 (consp-remove-bag-rewrite ; speedup
                                  consp-remove-1-rewrite ; speedup
                                  subbagp-disjoint-commute ; speedup
                                  subbagp-not-disjoint ; speedup
                                  subbagp-of-non-consp-two ; speedup
                                  )))))


;bzo rename params?
(defthm disjoint-of-remove-bag-irrel-alt
  (implies (disjoint x z)
           (equal (disjoint z (remove-bag x y))
                  (disjoint y z)))
  :hints(("goal"
          :in-theory (disable disjoint-commutative)
          :use (:instance disjoint-commutative
                          (x z) (y (remove-bag x y))))))

(defthm disjoint-of-singleton-one
  (equal (disjoint (list a) x)
         (not (memberp a x)))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-of-singleton-two
  (equal (disjoint x (list a))
         (not (memberp a x)))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-cdr-from-disjoint
  (implies (disjoint x y)
           (disjoint (cdr x) y))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm disjoint-cdr-from-disjoint-cheap
  (implies (disjoint x y)
           (disjoint (cdr x) y))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm disjoint-of-cons-false-from-memberp-two
  (implies (memberp a x)
           (equal (disjoint x (cons a y))
                  nil))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-of-cons-false-from-memberp-one
  (implies (memberp a y)
           (equal (disjoint (cons a x) y)
                  nil)))

(defthm disjoint-of-cons-false-from-memberp-two-cheap
  (implies (memberp a x)
           (equal (disjoint x (cons a y))
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable disjoint))))

(defthm disjoint-of-cons-false-from-memberp-one-cheap
  (implies (memberp a y)
           (equal (disjoint (cons a x) y)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm memberp-false-from-disjoint-of-cons-one
  (implies (disjoint (cons a y) x) ;y is a free var
           (equal (memberp a x)
                  nil)))

(defthm memberp-false-from-disjoint-of-cons-two
  (implies (disjoint x (cons a y)) ;y is a free var
           (equal (memberp a x)
                  nil)))

(defthmd not-memberp-from-disjointness-one
  (implies (and (disjoint y z)
                (memberp a y)
                (subbagp x z))
           (not (memberp a x))))

(defthmd not-memberp-from-disjointness-two
  (implies (and (disjoint y z)
                (memberp a z)
                (subbagp x y))
           (not (memberp a x))))

;keep disabled, since we have a :meta rule for this
(defthmd not-equal-from-member-of-disjoint-facts
  (implies (and (disjoint x y) ;x and y are free
                (memberp a x)
                (memberp b y))
           (not (equal a b))))

;keep disabled, since we have a :meta rule for this
(defthmd not-equal-from-member-of-disjoint-facts-alt
  (implies (and (disjoint x y) ;x and y are free
                (memberp a y)
                (memberp b x))
           (not (equal a b))))



;;
;;
;; unique
;;
;;

(defund unique (x)
  (declare (type t x))
  (if (consp x)
      (and (not (memberp (car x) (cdr x)))
           (unique (cdr x)))
    t))

(defthmd unique-of-non-consp
  (implies (not (consp x))
           (unique x))
  :hints (("Goal" :in-theory (enable unique))))

;even this was really expensive in some cases (namely, when the argument to
;unique was a huge nest of appends).
(defthm unique-of-non-consp-cheap
  (implies (not (consp x))
           (unique x))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable unique))))

(defthm unique-of-append
  (equal (unique (append x y))
         (and (unique x)
              (unique y)
              (disjoint x y)))
  :hints (("goal" :in-theory (enable unique append)
           :induct (binary-append x y))))

;rename
(defthm unique-memberp-remove
  (implies (and (not (unique x))
                (unique (remove-1 a x)))
           (memberp a (remove-1 a x)))
  :hints (("Goal" :in-theory (enable unique))))

(defthm unique-despite-remove-1
  (implies (unique x)
           (unique (remove-1 a x)))
  :hints (("Goal" :in-theory (enable unique))))

;lhs isn't in normal form?
(defthm unique-means-not-memberp-of-remove-1-same
  (implies (unique x)
           (not (memberp a (remove-1 a x))))
  :hints (("Goal" :in-theory (enable unique))))

(defthm non-unique-not-subbagp-of-unique
  (implies (and (not (unique x))
                (unique y))
           (not (subbagp x y)))
  :hints (("Goal"
           :in-theory (e/d (subbagp unique)
                           (subbagp-cdr-remove-1-rewrite ; incompatible
                            consp-remove-1-rewrite ; speedup
                            subbagp-of-non-consp-two ; speedup
                            subbagp-cdr-lemma ; speedup
                            subbagp-of-cdr ; speedup
                            subbagp-implies-membership ; speedup
                            )))))

;bzo won't fire? make local to an encap? or delete if not used!
(defthmd non-uniqueness-implications
  (implies (and (not (unique y))
                (unique x))
           (consp (remove-bag x y))))

;could be expensive...
(defthm subbagp-uniqueness
  (implies (and (unique y)  ;y is a free variable
                (subbagp x y))
           (unique x))
  :hints (("goal" :in-theory (enable unique))))

;; jcd - Removing this, because we will have a congruence rule for perm over
;; unique which will be much better.
;;
;; ;disable?
;; (defthm unique-if-perm-of-something-unique
;;   (implies (and (perm x y) ;y is a free var
;;                 (unique y))
;;            (unique x)))

;disable later?
(defthm unique-of-cons
  (equal (unique (cons a x))
         (and (not (memberp a x))
              (unique x)))
  :hints (("Goal" :in-theory (enable unique))))

;; jcd - added this rule
(defthm unique-of-cdr
  (implies (unique x)
           (unique (cdr x))))

;; jcd - added this rule
(defthm unique-of-nthcdr
  (implies (unique x)
           (unique (nthcdr n x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

;; jcd - added this rule
(defthm unique-of-firstn
  (implies (unique x)
           (unique (firstn n x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm unique-equal-rewrite
  (implies (booleanp y)
           (equal (equal (unique x) y)
                  (iff (unique x) y))))

;; jcd - removing this rule, which is trivial given our congruence rule
;; for perm over unique 1.
;;
;; (defthm unique-of-list-fix
;;   (equal (unique (list::fix x))
;;          (unique x))
;;   :hints (("Goal" :in-theory (enable unique list::fix))))

(defcong perm equal (unique x) 1
  :hints (("Goal"
           :induct (perm x x-equiv)
           :in-theory (enable perm perm-of-cdr-x-and-remove-1-of-car-x))))

(defthm disjoint-from-common-uniquenss
  (implies (and (unique (append y z))
                (subbagp x z))
           (disjoint x y))
  :hints (("Goal" :in-theory (enable disjoint))))


(defthm unique-despite-remove-bag
  (implies (unique y)
           (unique (remove-bag x y)))
  :hints (("Goal" :in-theory (enable remove-bag))))




;;
;;
;; count
;;
;;

;counts how many times A appears in the bag X
(defund count (a x)
  (declare (type t a x))
  (if (consp x)
      (if (equal a (car x))
          (+ 1 (count a (cdr x)))
        (count a (cdr x)))
    0))

;Make sure count's :type-prescription rule is as strong as we think.
(encapsulate
 ()
 (local (defthm count-type-prescription-test
          (and (integerp (count a x))
               (<= 0 (count a x)))
          :hints (("Goal"  :in-theory (union-theories '(booleanp
                                                       (:type-prescription count))
                                                     (theory 'minimal-theory)))))))

;; jcd - consider renaming since many linear facts might be known about count
(defthm count-linear
  (<= 0 (count a x))
  :rule-classes :linear)

(defthm count-<-1-rewrite
  (equal (< (count a x) 1)
         (equal 0 (count a x)))
  :hints(("Goal" :in-theory (enable count))))

(defthm count-equal-0-rewrite
  (equal (equal 0 (count a x))
         (not (memberp a x)))
  :hints (("Goal" :in-theory (enable count))))

(defthm non-zero-count-implies-memberp
  (implies
   (and
    (equal n (count a x))
    (not (equal n 0)))
   (memberp a x))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable (:rewrite non-zero-count-implies-memberp)))

(defthm zero-count-implies-non-memberp
  (implies
   (and
    (equal n (count a x))
    (equal n 0))
   (not (memberp a x)))
  :rule-classes (:rewrite :forward-chaining))

(in-theory (disable (:rewrite zero-count-implies-non-memberp)))

(defthm count-when-non-member
  (implies (not (memberp a x))
           (equal (count a x) 0))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable count))))

(defthm count-when-memberp
  (implies (memberp a x)
           (not (equal (count a x) 0)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable count))))

(defthm count-<-0-rewrite
  (equal (< 0 (count a x))
         (memberp a x))
  :hints (("Goal" :in-theory (enable count))))

(defthm count-of-cons
  (equal (count a (cons b x))
         (if (equal a b)
             (+ 1 (count a x))
           (count a x)))
  :hints (("Goal" :in-theory (enable count))))

;watch for loops
(defthmd count-car
  (equal (count (car x) x)
         (if (consp x)
             (+ 1 (count (car x) (cdr x)))
           0)))

(defthm count-of-append
  (equal (count a (append x y))
         (+ (count a x)
            (count a y)))
  :hints (("Goal" :in-theory (enable count))))


(encapsulate
 ()

 ;; jcd - Changing this to local, because the congruence rule we are about
 ;; to prove is much stronger.
 (local (defthm count-of-list-fix
          (equal (count a (list::fix x))
                 (count a x))
          :hints (("Goal" :in-theory (e/d (count list::fix) ())))))

 ;; jcd - leave this nonlocal?
 (defthmd count-of-remove-1-diff
   (implies (not (equal a b))
            (equal (count a (remove-1 b x))
                   (count a x)))
   :hints (("Goal" :in-theory (enable count))))

 ;; jcd - leave this nonlocal?
 (defthmd count-of-remove-1-same
   (equal (count a (remove-1 a x))
          (nfix (+ -1 (count a x))))
   :hints (("Goal" :in-theory (enable count))))

 (defthm count-of-remove-1-both
   (equal (count a (remove-1 b x))
          (if (equal a b)
              (nfix (+ -1 (count a x)))
            (count a x)))
   :hints (("Goal" :in-theory (enable count-of-remove-1-same
                                      count-of-remove-1-diff))))

 ;; jcd - added this congruence rule
 (defcong perm equal (count a x) 2
   :hints(("Goal"
           :induct (perm x x-equiv)
           :in-theory (e/d (count perm)
                           (consp-remove-1-rewrite ; minor speedup
                            memberp-subbagp)))))   ; minor speedup
 )


(defthm count-of-remove-bag
  (equal (count a (remove-bag x y))
         (nfix (- (count a y)
                  (count a x))))
  :hints (("Goal" :in-theory (e/d (remove-bag)
                                  (consp-remove-1-rewrite ; minor speedup
                                   subbagp-of-remove-1-both ; minor speedup
                                   non-membership-remove-1 ; minor speedup
                                   consp-remove-bag-rewrite ; minor speedup
                                   )))))

;loops with defn count
(defthm count-of-cdr
  (equal (count a (cdr x))
         (if (consp x)
             (if (equal a (car x))
                 (+ -1 (count a x))
               (count a x))
           0)))

(theory-invariant (incompatible (:rewrite count-of-cdr)
                                (:definition count)))


(defthm memberp-of-remove-bag
  (equal (memberp a (remove-bag x y))
         (< (count a x) (count a y)))
  :hints (("Goal" :in-theory (enable remove-bag)
           :do-not '(generalize eliminate-destructors))))

(defthm memberp-of-remove-1-same
  (equal (memberp a (remove-1 a x))
         (< 1 (count a x)))
  :hints (("Goal" :in-theory (enable memberp remove-1))))

(defthm unique-means-count-at-most-one
  (implies (unique x)
           (<= (count a x) 1))
  :hints (("goal"
           :use unique-means-not-memberp-of-remove-1-same
           :in-theory (disable unique-means-not-memberp-of-remove-1-same))))

(defthm unique-memberp-means-count-is-one
  (implies
   (and
    (unique x)
    (memberp a x))
   (equal (count a x) 1))
  :hints (("Goal" :use unique-means-count-at-most-one
	   :in-theory (disable unique-means-count-at-most-one)))
  :rule-classes (:rewrite :forward-chaining))

(defthm non-simular-count-implies-not-unique
  (implies
   (and
    (memberp a x)
    (equal n (count a x))
    (not (equal n 1)))
   (not (unique x)))
  :rule-classes (:rewrite :forward-chaining))

(defthmd memberp-from-count
  (implies (< 0 (count a x))
           (memberp a x)))

(defthmd subbagp-false-from-counts
  (implies (< (count a y) (count a x))
           (not (subbagp x y)))
  :hints (("Goal" :in-theory (e/d (subbagp)
                                  (subbagp-cdr-remove-1-rewrite ; incompatible
                                   )))))

(defthmd subbagp-of-remove-1-false-from-counts
  (implies (<= (count a y) (count a x))
           (equal (subbagp x (remove-1 a y))
                  (if (memberp a y)
                      nil
                    (subbagp x y))))
  :hints (("Goal"
           :use (:instance subbagp-false-from-counts (y (remove-1 a y)))
           :in-theory (disable subbagp-false-from-counts))))

(encapsulate
 ()

 (local (defthm lemma
          (implies (and (consp x)
                        (memberp a y)
                        (subbagp x (remove-1 a y)))
                   (equal (< (count a x) (count a y))
                          (< (count a (cdr x)) (count a y))))
          :hints (("Goal"
                   :use (:instance subbagp-false-from-counts
                                   (x (cdr x))
                                   (y (remove-1 (car x)
                                                (remove-1 (car x) y)))
                                   (a (car x)))))))

 (local (defthm lemma2
          (implies (and (memberp a y)
                        (subbagp x y))
                   (implies (subbagp x (remove-1 a y))
                            (memberp a (remove-bag x y))))
          :hints (("Goal"
                   :do-not '(generalize eliminate-destructors)
                   :in-theory (e/d (subbagp)
                                   (subbagp-cdr-remove-1-rewrite ; incompatible
                                    consp-remove-1-rewrite ; speedup
                                    subbagp-of-non-consp-two ; speedup
                                    subbagp-cdr-lemma ; speedup
                                    memberp-car-when-disjoint ; speedup
                                    ))))))

 (local (defthm lemma3
          (implies (and (subbagp x y)
                        (< (count a x) (count a y)))
                   (subbagp x (remove-1 a y)))
          :hints (("Goal"
                   :in-theory (e/d (subbagp count)
                                   (subbagp-cdr-remove-1-rewrite ; incompatible
                                    count-of-cdr ; incompatible with count
                                    consp-remove-1-rewrite ; speedup
                                    subbagp-of-non-consp-two ; speedup
                                    subbagp-cdr-lemma ; speedup
                                    subbagp-implies-membership ; speedup
                                    subbagp-of-cdr ; speedup
                                    ))))))

 (defthm subbagp-of-remove-1-from-subbagp
   (implies (subbagp x y)
            (equal (subbagp x (remove-1 a y))
                   (if (memberp a y)
                       (memberp a (remove-bag x y))
                     t)))
   :hints (("Goal" :in-theory (enable subbagp-of-remove-1-false-from-counts))))

 )


;; jcd - bzo this is long overdue for a renaming
(defthm homestar
  (implies (< (count a y) (count a x))
           (equal (remove-bag x (cons a y))
                  (remove-bag x y)))
  :hints (("Goal"
           :in-theory (e/d (remove-bag)
                           (consp-remove-1-rewrite ; speedup
                            remove-bag-does-nothing ; speedup
                            disjoint-cdr-from-disjoint ; speedup
                            disjoint-of-non-consp-two ; speedup
                            subbagp-cdr-lemma ; speedup
                            )))))

;; jcd - bzo this is long overdue for a renaming
(defthm runnerdotcom
  (implies (<= (count a x) (count a y))
           (perm (remove-bag x (cons a y))
                 (cons a (remove-bag x y))
                 ))
  :hints (("Goal"
           :in-theory (e/d (remove-bag)
                           (consp-remove-1-rewrite ; speedup
                            consp-remove-bag-rewrite ; speedup
                            subbagp-of-cons ; speedup
                            perm-of-non-consp-two ; speedup
                            subbagp-of-remove-1-both ; speedup
                            subbagp-cdr-lemma ; speedup
                            subbagp-false-from-witness ; speedup
                            )))))

;; jcd - bzo this is long overdue for a renaming
(defthm marzipan
  (perm (remove-bag x (cons a y))
        (if (<= (count a x) (count a y))
            (cons a (remove-bag x y))
          (remove-bag x y))))

(defthm subbagp-means-counts-<=
  (implies (subbagp x y)
           (<= (count a x)
               (count a y)))
  :hints (("Goal" :in-theory (e/d (subbagp)
                                  (subbagp-cdr-remove-1-rewrite)))))

;expensive?
(defthm count-0-for-non-memberp
  (implies (not (memberp a x))
           (equal (count a x)
                  0)))

;gen
(defthm count-of-nil
  (equal (count elem nil)
         0))

(defthm subbagp-nil-from-<-of-counts
  (implies (< (count a y) (count a x)) ; a is a free var
           (equal (subbagp x y)
                  nil)))

(defthm count-with-subbagp-linear
  (implies (subbagp x y) ; y is a free var
           (<= (count a x) (count a y)))
  :rule-classes :linear)


;;
;;
;; uniquify
;;
;;

;; jcd - how abuot a list::equiv congruence?

;add more lemmas about uniquify?

(defund uniquify (x)
  (declare (type t x))
  (if (consp x)
      (if (memberp (car x) (cdr x))
          (uniquify (cdr x))
        (cons (car x) (uniquify (cdr x))))
    nil))

(defthm memberp-uniquify
  (equal (memberp a (uniquify x))
         (memberp a x))
  :hints (("Goal" :in-theory (enable uniquify))))

(defthm unique-uniquify
  (unique (uniquify x))
  :hints (("goal" :in-theory (enable unique uniquify))))






;;
;;
;; remove-all
;;
;;


;Remove all copies of element A from bag X.  bzo think about what to do for
;non-consp args (return that non-consp arg or return nil?).

;; jcd - changing remove-all to return a true list, like the other remove
;; functions.
(defund remove-all (a x)
  (declare (type t a x))
  (if (consp x)
      (if (equal a (car x))
          (remove-all a (cdr x))
        (cons (car x) (remove-all a (cdr x))))
    nil))

;; jcd - added this congruence
(encapsulate
 ()

 (local (defun my-induction (x x-equiv)
          (if (consp x)
              (my-induction (cdr x) (remove-1 (car x) x-equiv))
            (list x x-equiv))))

 (defcong list::equiv equal (remove-all a x) 2
   :hints(("Goal"
           :in-theory (enable remove-all)
           :induct (my-induction x x-equiv))))
 )

;; jcd - strenghened rhs from (true-listp x) to t, now that remove-all returns
;; nil at the end.
(defthm true-listp-of-remove-all
   (true-listp (remove-all a x))
   :hints (("Goal" :in-theory (enable remove-all))))

;; jcd - removed this because a stronger type prescription is now inferred.
;; (defthm remove-all-true-listp-type-prescription
;;   (implies (true-listp x)
;;            (true-listp (remove-all a x)))
;;   :rule-classes (:type-prescription)
;;   :hints (("Goal" :in-theory (enable remove-all))))

;; jcd - strenghened rhs from x to nil.
(defthm remove-all-of-non-consp
  (implies (not (consp x))
           (equal (remove-all a x)
                  nil))
  :hints (("Goal" :in-theory (enable remove-all))))

;; jcd - strenghtened rhs from x to nil
(defthm remove-all-of-non-consp-cheap
  (implies (not (consp x))
           (equal (remove-all a x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable remove-all))))

;; jcd - removed this rule since it is an exact copy of
;; remove-all-does-nothing.
;;
;; jcd - changed rhs from x to (list::fix x)
;;
;; (defthm non-membership-remove-all
;;   (implies (not (memberp a x))
;;            (equal (remove-all a x)
;;                   (list::fix x)))
;;   :hints (("Goal" :in-theory (enable remove-all))))

;; jcd - changed rhs from x to (list::fix x)
(defthm remove-all-does-nothing
  (implies (not (memberp a x))
           (equal (remove-all a x)
                  (list::fix x)))
  :hints (("Goal" :in-theory (enable remove-all))))

(defthm memberp-of-remove-all-is-false
  (equal (memberp a (remove-all a x))
         nil)
  :hints (("Goal" :in-theory (enable remove-all))))

(defthm memberp-of-remove-all-irrel
  (implies (not (equal a b))
           (equal (memberp a (remove-all b x))
                  (memberp a x)))
  :hints (("Goal" :in-theory (enable remove-all))))

(defthm memberp-of-remove-all-irrel-cheap
  (implies (not (equal a b))
           (equal (memberp a (remove-all b x))
                  (memberp a x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable remove-all))))

;; jcd - added true-listp to the rhs.  this theorem is a little weaker now
;; that remove-all returns a true list.  I think it's worth it!
(defthm remove-all-does-nothing-rewrite
  (equal (equal x (remove-all a x))
         (and (true-listp x)
              (not (memberp a x)))))

(defthm remove-all-of-cons-same
  (equal (remove-all a (cons a x))
         (remove-all a x))
  :hints (("Goal" :in-theory (enable remove-all))))

;disable later?
(defthm remove-all-of-cons-both
  (equal (remove-all a (cons b x))
         (if (equal a b)
             (remove-all a x)
           (cons b (remove-all a x))))
  :hints (("Goal" :in-theory (enable remove-all))))

(defthm remove-all-of-remove-all
  (equal (remove-all a (remove-all b x))
         (remove-all b (remove-all a x)))
   :rule-classes ((:rewrite :loop-stopper ((a b))))
   :hints (("Goal" :in-theory (enable remove-all))))

;bzo remove-all and remove-1 commute? which way should that go?
(defthm remove-all-of-remove-1
  (equal (remove-all a (remove-1 b x))
         (remove-1 b (remove-all a x)))
  :hints (("Goal" :in-theory (e/d (remove-all)
                                  (consp-remove-1-rewrite ;; minor speedup
                                   )))))

(defthmd remove-1-of-remove-all
  (equal (remove-1 a (remove-all b x))
         (remove-all b (remove-1 a x))))

(theory-invariant (incompatible (:rewrite remove-1-of-remove-all)
                                (:rewrite remove-all-of-remove-1)))


;make remove-all analogues of all the remove-1 theorems!

(defthm remove-all-of-remove-1-same-one
  (equal (remove-all a (remove-1 a x))
         (remove-all a x))
   :hints (("Goal" :in-theory (enable remove-all))))

(defthm remove-all-of-remove-1-same-two
  (equal (remove-1 a (remove-all a x))
         (remove-all a x))
   :hints (("Goal" :in-theory (enable remove-all))))

;; jcd - strenghthened rhs since we don't need list::fix over there anymore.
;; jcd - removing this rule because we know that remove-all creates a
;; true-listp, so this is obvious.
;;
;; (defthm list-fix-of-remove-all
;;   (equal (list::fix (remove-all a x))
;;          (remove-all a x))
;;   :hints (("Goal" :in-theory (enable remove-all list::fix))))

;; jcd - added this rule
(defthm unique-of-remove-all
  (implies (unique x)
           (unique (remove-all a x)))
  :hints(("Goal" :in-theory (enable remove-all))))

(defthm memberp-of-remove-all
  (implies (memberp a (remove-all b x)) ;b is a free variable
           (memberp a x))
  :hints (("goal" :in-theory (enable remove-all))))

(defthm not-memberp-implies-not-memberp-remove-all
  (implies (not (memberp a x))
           (not (memberp a (remove-all b x)))))

(defthm memberp-x-remove-x-implies-memberp-x-remove-all-y
  (implies (and (syntaxp (not (equal a b))) ;prevents loops
                (memberp a (remove-all a x)))
           (memberp a (remove-all b x)))
  :hints (("Goal" :cases ((equal a b)))))

(defthm subbagp-of-remove-all
  (equal (subbagp x (remove-all a y))
         (if (memberp a x)
             nil
           (subbagp x y)))
  :hints (("Goal" :in-theory (e/d (subbagp)
                                  (subbagp-cdr-remove-1-rewrite ; incompatible
                                   consp-remove-1-rewrite ; speedup
                                   subbagp-of-non-consp-two ; speedup
                                   subbagp-of-cdr ; speedup
                                   memberp-subbagp ; speedup
                                   subbagp-cdr-lemma ; speedup
                                   )))))


;see subbagp-of-remove-all
(defthm subbagp-of-remove-all-irrel-two
  (implies (not (memberp a x))
           (equal (subbagp x (remove-all a y))
                  (subbagp x y))))

(defthm subbagp-of-remove-all-two
  (equal (subbagp x (remove-all a y))
         (and (not (memberp a x))
              (subbagp x y))))

(defthm remove-all-of-remove-bag
  (equal (remove-all a (remove-bag x y))
         (remove-bag x (remove-all a y)))
  :hints (("Goal" :in-theory (e/d (remove-all remove-bag)
                                  (consp-remove-1-rewrite)))))

(defthmd remove-bag-of-remove-all
  (equal (remove-bag x (remove-all a y))
         (remove-all a (remove-bag x y))))

(theory-invariant (incompatible (:rewrite remove-all-of-remove-bag)
                                (:rewrite remove-bag-of-remove-all)))

(defthm remove-all-of-append
  (equal (remove-all a (append x y))
         (append (remove-all a x)
                 (remove-all a y)))
  :hints (("Goal" :in-theory (enable remove-all))))




;;
;;
;; bag-intersection
;;
;;

;returns the intersection of two bags.  the count of an element in the
;intersection is the minimum of its counts in the arguments.

;; jcd - changed this to always return nil instead of x when x is not a
;; consp, so that it will always return a true list.
(defund bag-intersection (x y)
  (declare (type t x y))
  (if (consp x)
      (if (memberp (car x) y)
          (cons (car x) (bag-intersection (cdr x) (remove-1 (car x) y)))
        (bag-intersection (cdr x) y))
    nil))

;; jcd - added this congruence
(encapsulate
 ()
 (local (defun my-induction (x x-equiv y)
          (if (consp x)
              (if (memberp (car x) y)
                  (my-induction (cdr x) (cdr x-equiv) (remove-1 (car x) y))
                (my-induction (cdr x) (cdr x-equiv) y))
            (list x x-equiv y))))

 (defcong list::equiv equal (bag-intersection x y) 1
   :hints(("Goal"
           :in-theory (enable bag-intersection)
           :induct (my-induction x x-equiv y)))))

;; jcd - added this congruence
(defcong list::equiv equal (bag-intersection x y) 2
  :hints(("Goal" :in-theory (enable bag-intersection))))

(defthm memberp-of-bag-intersection
  (equal (memberp a (bag-intersection x y))
         (and (memberp a x)
              (memberp a y)))
  :hints (("Goal" :in-theory (enable bag-intersection))))

(defthm bag-intersection-of-nil-one
  (equal (bag-intersection nil x)
         nil)
  :hints (("Goal" :in-theory (enable bag-intersection))))

(defthm bag-intersection-of-nil-two
  (perm (bag-intersection x nil)
        nil)
  :hints (("Goal" :in-theory (enable bag-intersection))))

;; jcd - strengthened rhs from x to nil
(defthm bag-intersection-of-non-consp-one
  (implies (not (consp x))
           (equal (bag-intersection x y)
                  nil))
  :hints (("Goal" :in-theory (enable bag-intersection))))

(defthm bag-intersection-of-non-consp-two
  (implies (not (consp y))
           (perm (bag-intersection x y)
                 nil))
  :hints (("Goal" :in-theory (enable bag-intersection))))

(defthm bag-intersection-of-cons-irrel-one
  (implies (not (memberp a x))
           (equal (bag-intersection x (cons a y))
                  (bag-intersection x y)))
  :hints (("Goal" :in-theory (enable bag-intersection))))

(defthm bag-intersection-of-cons-irrel-two
  (implies (not (memberp a y))
           (equal (bag-intersection (cons a x) y)
                  (bag-intersection x y)))
  :hints (("Goal" :in-theory (enable bag-intersection))))

(defthm remove-1-of-bag-intersection
 (equal (remove-1 a (bag-intersection x y))
        (bag-intersection (remove-1 a x) (remove-1 a y)))
 :hints (("Goal" :in-theory (e/d (bag-intersection)
                                 (memberp-subbagp ; speedup
                                  subbagp-cdr-lemma ; speedup
                                  consp-remove-1-rewrite ; speedup
                                  subbagp-false-from-witness ; speedup
                                  )))))

(defthm bag-intersection-of-remove-1-helper-one
  (implies (< (count a x) (count a y))
           (equal (bag-intersection x (remove-1 a y))
                  (bag-intersection x y)))
  :hints(("Goal" :in-theory (e/d (bag-intersection)
                                 (subbagp-cdr-lemma ; speedup
                                  subbagp-of-remove-1-both ; speedup
                                  consp-remove-1-rewrite ; speedup
                                  subbagp-implies-membership ; speedup
                                  subbagp-false-from-witness ; speedup
                                  memberp-car-when-disjoint ; speedup
                                  )))))

(defthm bag-intersection-of-cons-1
  (equal (bag-intersection (cons a x) y)
         (if (memberp a y)
             (cons a (bag-intersection x (remove-1 a y)))
           (bag-intersection x y)))
 :hints (("Goal" :in-theory (enable bag-intersection))))


(defthmd bag-intersection-of-cdr
  (implies (not (memberp (car x) y))
           (equal (bag-intersection (cdr x) y)
                  (if (consp x)
                      (bag-intersection x y)
                    nil))))

(theory-invariant (incompatible (:rewrite bag-intersection-of-cdr)
                                (:rewrite bag-intersection)))

;; jcd - bzo - add congruence rules for perm over bag-intersection??







;;
;;
;; unique-subbagps
;;
;;

;bzo rename?  X and Y are non-overlapping subbagps of Z.  That is, X is a
;subbagp of Z, and even when X is removed from Z, Y is still a subbagp of Z.
;Equivalently, the bag-sum of X and Y is a subbagp of Z.

;; jcd - changed to defund.  It was already disabled later in the file using
;; an in-theory event.
;;
;; jcd - renamed LIST to Z.

(defund unique-subbagps (x y z)
  (declare (type t x y z))
  (if (subbagp x z)
      (let ((z (remove-bag x z)))
        (subbagp y z))
    nil))

;; jcd - added this congruence
(defcong perm equal (unique-subbagps x y z) 1
  :hints(("Goal" :in-theory (enable unique-subbagps))))

;; jcd - added this congruence
(defcong perm equal (unique-subbagps x y z) 2
  :hints(("Goal" :in-theory (enable unique-subbagps))))

;; jcd - added this congruence
(defcong perm equal (unique-subbagps x y z) 3
  :hints(("Goal" :in-theory (enable unique-subbagps))))

(defthm unique-subbagps-from-unique-subbagps-and-subbagp
  (implies (and (unique-subbagps x y z2)
                (subbagp z2 z))
           (unique-subbagps x y z))
  :hints (("Goal" :in-theory (enable unique-subbagps))))

(defthm unique-subbagps-from-unique-subbagps-and-subbagp-2
  (implies (and (unique-subbagps x2 y z)
                (subbagp x x2))
           (unique-subbagps x y z))
  :hints (("Goal" :in-theory (enable unique-subbagps))))

(encapsulate
 ()

 ;; jcd - split this out from subgoal hints from eric-hack-1
 (local (defthm lemma
          (implies (and (subbagp y bag)
                        (not (memberp (car y) (remove-bag x bag)))
                        (not (subbagp y (remove-bag x bag))))
                   (equal (subbagp x (remove-bag y bag))
                          nil))
          :hints(("Goal"
                  :in-theory (disable subbagp-nil-from-<-of-counts ; going to :use
                                      subbagp-false-from-counts ; bzo!
                                      subbagp-of-remove-1-from-subbagp
                                      )
                  :use (:instance subbagp-nil-from-<-of-counts
                                  (y (remove-1 (car y)
                                               (remove-bag (cdr y) bag)))
                                  (a (car y)))))))

 ;; jcd - changing to local
 (local (defthmd eric-hack-1
          (implies (and (subbagp y bag) ;drop?
                        (not (subbagp y (remove-bag x bag))))
                   (not (subbagp x (remove-bag y bag))))
          :hints (("Goal"
                   :in-theory (e/d (subbagp)
                                   (subbagp-cdr-remove-1-rewrite ;incompatible
                                    subbagp-of-remove-1-from-subbagp
                                    consp-remove-1-rewrite ; speedup
                                    subbagp-of-non-consp-two ; speedup
                                    memberp-of-remove-bag ; speedup
                                    subbagp-of-non-consp-one ; speedup
                                    subbagp-cdr-lemma ; speedup
                                    subbagp-of-cdr ; speedup
                                    memberp-subbagp ; speedup
                                    memberp-car-when-disjoint ; speedup
                                    subbagp-chaining ; speedup
                                    memberp-x-remove-x-implies-memberp-x-remove-1-y
                                    non-membership-remove-1 ; speedup
                                    consp-remove-bag-rewrite ; speedup
                                    )))
                  ("Subgoal *1/4" :use (:instance lemma)))))

 (defthm unique-subbagps-commutative
   (equal (unique-subbagps x y bag)
          (unique-subbagps y x bag))
   :hints (("Goal" :use ((:instance eric-hack-1)
                         (:instance eric-hack-1 (x y) (y x)))
            :in-theory (enable unique-subbagps))))
 )

;; jcd - bzo name too long
(defthm unique-subbagps-from-unique-subbagps-and-subbagp-2-blah
  (implies (and (unique-subbagps y x2 z)
                (subbagp x x2))
           (unique-subbagps x y z))
  :hints (("Goal"
           :in-theory (disable unique-subbagps-from-unique-subbagps-and-subbagp-2)
           :use unique-subbagps-from-unique-subbagps-and-subbagp-2)))

;; jcd - bzo name too long
(defthm unique-subbagps-from-unique-subbagps-and-subbagp-2-alt
  (implies (and (unique-subbagps x y2 z)
                (subbagp y y2))
           (unique-subbagps x y z))
  :hints (("Goal" :in-theory (enable unique-subbagps))))

;; jcd - bzo name too long
(defthm unique-subbagps-from-unique-subbagps-and-subbagp-2-alt-blah
  (implies (and (unique-subbagps y2 x z)
                (subbagp y y2))
           (unique-subbagps x y z))
  :hints (("Goal" :in-theory (disable unique-subbagps-from-unique-subbagps-and-subbagp-2-alt)
           :use unique-subbagps-from-unique-subbagps-and-subbagp-2-alt)))

(defthmd not-memberp-from-unique-subbagps-of-something-unique
  (implies (and (unique y) ;y is a free var
                (unique-subbagps (list a) x y))
           (not (memberp a x)))
  :hints (("Goal" :in-theory (enable unique-subbagps))))

(defthmd not-memberp-from-unique-subbagps-of-something-unique-alt
  (implies (and (unique y) ;y is a free var
                (unique-subbagps (list a) x y))
           (not (memberp a x)))
  :hints (("Goal" :in-theory (enable unique-subbagps))))




;; jcd - bzo document this function somewhat
(defund unique-memberps (a b bag)
  (declare (type t a b bag))
  (and (memberp a bag)
       (memberp b (remove-1 a bag))))


;; jcd - bzo document this function somewhat
(defund unique-memberp-and-subbagp (a x bag)
  (declare (type t a x bag))
  (and (memberp a bag)
       (subbagp x (remove-1 a bag))))



;; jcd - added this lemma
(defthm count-of-remove-bag-when-member-of-both-bags
  (implies (and (memberp a z)
                (memberp a x))
           (< (count a (remove-bag x z))
              (count a z)))
  :rule-classes :linear)

(defthm unique-memberp-and-subbagp-when-unique-subbagps-and-memberp
  (implies (and (unique-subbagps x y z)
                (memberp a x))
           (unique-memberp-and-subbagp a y z))
  :hints (("Goal" :in-theory (e/d (unique-memberp-and-subbagp
                                   unique-subbagps)
                                  (count-of-remove-bag-when-member-of-both-bags
                                   ))
           :use count-of-remove-bag-when-member-of-both-bags
           )))

(defthm unique-memberp-and-subbagp-when-unique-subbagps-and-memberp-alt
  (implies (and (unique-subbagps y x z)
                (memberp a x))
           (unique-memberp-and-subbagp a y z))
  :hints (("Goal"
           :use (:instance unique-memberp-and-subbagp-when-unique-subbagps-and-memberp)
           :in-theory (disable unique-memberp-and-subbagp-when-unique-subbagps-and-memberp))))

(defthm unique-memberp-and-subbagp-when-unique-memberp-and-subbagp-and-subbagp
  (implies (and (unique-memberp-and-subbagp a x z)
                (subbagp z y))
           (unique-memberp-and-subbagp a x y))
  :hints (("Goal" :in-theory (enable unique-memberp-and-subbagp
                                     unique-subbagps))))

(defthm unique-memberp-and-subbagp-when-unique-memberp-and-subbagp-and-subbagp-two
  (implies (and (unique-memberp-and-subbagp a y z) ; y is a free var
                (subbagp x y))
           (unique-memberp-and-subbagp a x z))
  :hints (("Goal" :in-theory (enable unique-memberp-and-subbagp
                                     unique-subbagps))))

(defthm unique-memberps-when-unique-memberp-and-subbagp-and-memberp
  (implies (and (unique-memberp-and-subbagp a x z)
                (memberp b x))
           (unique-memberps a b z))
  :hints (("Goal" :in-theory (enable unique-memberp-and-subbagp
                                     unique-memberps))))

(defthm unique-memberps-when-unique-memberp-and-subbagp-and-memberp-alt
  (implies (and (unique-memberp-and-subbagp b x y)
                (memberp a x))
           (unique-memberps a b y))
  :hints (("Goal" :cases ((equal a b))
           :in-theory (enable unique-memberp-and-subbagp
                              unique-memberps))))

(defthm unique-memberps-when-unique-memberp-and-subbagp-and-memberp-three
  (implies (and (memberp b x)
                (unique-memberp-and-subbagp a x y))
           (unique-memberps a b y))
  :hints (("Goal" :in-theory (enable unique-memberp-and-subbagp
                                     unique-memberps))))

(defthm unique-memberps-when-unique-memberp-and-subbagp-and-memberp-four
  (implies (and (memberp a x)
                (unique-memberp-and-subbagp b x bag))
           (unique-memberps a b bag)))

(defthm unique-memberps-when-unique-memberps-and-subbagp
  (implies (and (subbagp x bag)
                (unique-memberps a b x))
           (unique-memberps a b bag))
  :hints (("Goal" :in-theory (enable unique-memberps))))

(defthm unique-memberps-when-unique-memberps-and-subbagp-alt
  (implies (and (unique-memberps a b x)
                (subbagp x bag))
           (unique-memberps a b bag)))

 ;prove more like this?
(defthm not-unique-memberps-when-unique
  (implies (unique bag)
           (not (unique-memberps a a bag)))
 :hints (("Goal" :in-theory (enable unique-memberps))))

(defthmd not-equal-when-unique-and-unique-memberps
  (implies (and (unique bag)
                (unique-memberps a b bag))
           (not (equal a b))))



;; jcd - Everything below this point was already commented out when I found it.

;; #|
;; (encapsulate
;;  ()

;;  (local
;;   (encapsulate
;;    ()

;;    (defun raw-remove-bag (list1 list2)
;;      (if (consp list1)
;;          (let ((list2 (remove-1 (car list1) list2)))
;;            (raw-remove-bag (cdr list1) list2))
;;        list2))

;;    (defthm raw-remove-bag-reduction
;;      (equal (raw-remove-bag list1 list2)
;;             (remove-bag list1 list2))
;;      :hints (("Goal" :in-theory (enable remove-bag))))

;;    (defthm raw-remove-bag-reduction-instance
;;      (equal (raw-remove-bag (cdr list1) list2)
;;             (remove-bag (cdr list1) list2)))

;;    (defun raw-remove-bag-double (list1 listx listy)
;;      (if (consp list1)
;;          (let ((listx (remove-1 (car list1) listx))
;;                (listy (remove-1 (car list1) listy)))
;;            (raw-remove-bag-double (cdr list1) listx listy))
;;        (cons listx listy)))

;;    (defthm subbagp-implies-subbagp-raw-remove-bag
;;      (implies
;;       (subbagp listx listy)
;;       (subbagp (raw-remove-bag list1 listx) (raw-remove-bag list1 listy)))
;;      :hints (("goal"
;;               :in-theory (disable raw-remove-bag-reduction)
;;               :induct (raw-remove-bag-double list1 listx listy))))
;;    ))

;;  )
;; |#



;; #|
;; (defun perm-remove-bag-induction (p x y)
;;   (declare (xargs :guard (equal y y)))
;;   (if (consp p)
;;       (if (memberp (car p) x)
;;           (perm-remove-bag-induction (cdr p) (remove-1 (car p) x)
;;                                      (remove-1 (car p) y))
;;         (perm-remove-bag-induction (cdr p) x y))
;;     nil))
;; |#

;; #|
;; (defthm perm-of-cdr-x-and-remove-1-of-car-x
;;   (implies (consp x) ;bzo handle other case
;;            (equal (perm (cdr x) (remove-1 (car x) y))
;;                   (if (memberp (car x) y)
;;                       (perm x y)
;;                     (perm (cdr x) y))))
;;   :hints (("Goal" :in-theory (enable perm))))
;; |#




;; #|
;; ;bad name?
;; (defthm perm-not-consp
;;   (implies (perm x x-equiv)
;;            (iff (not (consp (remove-bag p x)))
;;                 (not (consp (remove-bag p x-equiv)))))
;;   :hints (("Goal" :induct (perm-remove-bag-induction p x x-equiv)
;;            :in-theory (enable remove-bag))
;;           ("Subgoal *1/3.2''" :in-theory (enable perm))
;;           ("Subgoal *1/3.1''" :in-theory (enable perm))
;;           ))
;; |#

;; #|
;; (defthm remove-bag-of-remove-1-both
;;   (implies (and (memberp a y)
;;                 ;(memberp a x)
;;                 )
;;            (equal (remove-bag (remove-1 a y) x)
;;                   (remove-1 a (remove-bag y x)))
;;            )
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :expand  (REMOVE-1 A Y)
;;            :in-theory (e/d ( NON-MEMBERSHIP-REMOVE-1) ()))))

;; (defthm remove-bag-of-remove-1-both
;;   (equal (remove-bag (remove-1 a y) x)
;;          (if (memberp a y)
;;              (remove-1 a (remove-bag y x))
;;            (remove-bag y x)))
;;   )
;; |#



;; #|
;; ;--------- added for unique-subbagps---------------
;; (defun perm-remove-bag-induction-2 (x y a)
;;   (declare (xargs :guard (and (equal y y)
;;                               (equal a a))))
;;   (if (consp x)
;;       (perm-remove-bag-induction-2 (cdr x) (remove-1 (car x) y)
;;                                    (remove-1 (car x) a))
;;     nil))
;; |#

;; #|
;;  (local
;;   (defthm perm-implies-consp-remove-bag-correlation
;;     (implies
;;      (and
;;       (perm x y)
;;       (syntaxp (not (term-order x y))))
;;      (iff (consp (remove-bag a x))
;;           (consp (remove-bag a y))))
;;     :hints (("goal" :use (:instance perm-implies-consp-correlation
;;                                     (a (remove-bag a x))
;;                                     (b (remove-bag a y)))))))
;; |#

;; #|
;; (defthm remove-bag-smaller
;;   (implies (not (consp (remove-bag (remove-1 x y) z)))
;;            (not (consp (remove-bag y z))))
;;   :hints (("Goal" :in-theory (enable REMOVE-BAG-REMOVE-1 remove-1
;;                                      remove-bag ))))
;; |#

;; #|
;; (defthmd count-of-remove-1-same
;;   (equal (count a (remove-1 a l))
;;          (if (memberp a l)
;;              (+ -1 (count a l))
;;            0))
;;   :hints (("Goal" :in-theory (enable count))))
;; |#


;; #|
;; ;mine
;; (defthm remove-bag-remove-1-reduction
;;   (implies (and (memberp a x)
;;                 ;(subbagp x y)
;;                 (memberp a y)
;;                 )
;;            (perm (remove-bag (remove-1 a x) y)
;;                  (cons a (remove-bag x y))))
;;   :hints (("goal" :induct (remove-1 a x)
;;            :in-theory (enable subbagp remove-bag remove-1 memberp))))
;; |#

;; #|
;; (defthm remove-bag-consp
;;   (implies (consp list)
;;            (equal (remove-bag list zed)
;;                   (remove-1 (car list) (remove-bag (cdr list) zed))))
;;   :hints (("goal" :in-theory (cons 'remove-bag-over-remove-1


;; ;gross theory hint...
;; (defthm memberp-subbagp-remove-1-memberp-remove-bag
;;   (implies
;;    (and
;;     (memberp x zed)
;;     (subbagp cdr (remove-1 x zed)))
;;    (memberp x (remove-bag cdr zed)))
;;   :hints (("goal" :in-theory (cons 'subbagp (current-theory 'gacc::integerp-unicity-of-0)))))

;; (thm
;;  (implies (and (memberp a x)
;;                (< (count a x) (count a y)))
;;           (perm (remove-bag (remove-1 a x) y)
;;                 (cons a (remove-bag x y))))
;;  :hints (("Goal" ;:induct t
;;           :do-not-induct t)))


;; (thm
;;  (implies (and (memberp a x)
;;                (not (< (count a x) (count a y))))
;;           (perm (remove-bag (remove-1 a x) y)
;;                 (remove-bag x y)))
;;  :otf-flg t
;;  :hints (("Goal" :induct t
;;           :in-theory (enable perm-becomes-two-subbagp-claims
;;                               ;perm
;;                               )
;;           :do-not '(generalize eliminate-destructors)
;;           :do-not-induct t)))

;; (thm
;;  (perm (remove-bag (remove-1 a x) y)
;;        (if (memberp a x)
;;            (if (< (count a x) (count a y))
;;                (cons a (remove-bag x y))
;;              (remove-bag x y))
;;          (remove-bag x y)))
;;  :hints (("Goal" ;:induct t
;;           :do-not-induct t)))

;; (defthmd integerp-<-lemma
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (equal (< (+ -1 x) y)
;;                   (<= x y))))
;; |#

;; #|
;; (defthm perm-of-remove-bag-cdr-and-cons-of-car
;;   (perm (remove-bag (cdr list) zed)
;;         (cons (car list)
;;               (remove-bag list zed)))
;; |#



;; #|

;; ;drop? or combine?
;;  (local
;;   (defthm perm-append-to-perm-remove-bag
;;     (implies (subbagp x list)
;;              (equal (perm (append x y) list)
;;                     (perm y (remove-bag x list))))
;;     :hints (("Goal" :in-theory (enable perm subbagp remove-bag
;;                                        memberp-of-cons
;;                                        binary-append)))))
;; |#


;; #|
;;  (local
;;   (encapsulate
;;    ()

;;    (defthm disjoint-remove-1-not-memberp
;;      (and
;;       (implies (and (disjoint (remove-1 x set3) setx)
;;                     (not (memberp x setx)))
;;                (disjoint set3 setx))
;;       (implies (and (disjoint setx (remove-1 x set3))
;;                     (not (memberp x setx)))
;;                (disjoint setx set3)))
;;      :hints (("Goal" :in-theory (enable disjoint))))

;;    (defthm subbagp-disjoint-setx-1
;;      (implies (and (disjoint set1 setx)
;;                    (subbagp set3 set1)
;;                    )
;;               (disjoint set3 setx))
;;      :hints (("goal" :in-theory (e/d (subbagp)  ())))
;;      :rule-classes (:rewrite :forward-chaining))

;;    (defthm subbagp-disjoint-setx-2
;;      (implies
;;       (and
;;        (disjoint setx set1)
;;        (subbagp set3 set1)
;;        )
;;       (disjoint setx set3))
;;      :hints (("goal" :in-theory (e/d (disjoint) (  disjoint-commutative))))
;;               :rule-classes (:rewrite :forward-chaining))
;;              ))
;; |#

;; #|
;;
;; (defthmd subbagp-perm-subbagp-cons
;;   (implies (and (subbagp (append (cdr u) v)
;;                         (remove-1 (car u) y))
;;                 (perm (cons (car u) (remove-1 (car u) y))
;;                       y))
;;            (subbagp (cons (car u) (append (cdr u) v))
;;                    y)))
;; |#

;; #|
;; (defthm subbagp-memberp-remove-1
;;   (implies (and (consp u)
;;                 (memberp (car u) y)
;;                 (subbagp u y))
;;            (subbagp (cdr u) (remove-1 (car u) y)))
;;   :hints (("Goal'" :in-theory (enable subbagp))))
;; |#

;; #|
;; (defthm perm-subbagp-subbagp-2
;;   (implies (and (perm y x)
;;                 (subbagp v x))
;;            (subbagp v y))
;;   :hints (("Goal" :in-theory (enable subbagp))))
;; |#



;; #|
;; (encapsulate
;;  ()

;;  (local
;;   (encapsulate
;;    ()

;;    (defthm not-consp-perm
;;      (implies
;;       (and (perm x y)
;;            (not (consp x)))
;;       (not (consp y)))
;;      :hints (("goal" :in-theory (enable perm)))
;;      :rule-classes (:forward-chaining))

;;    (defthm membership-remove-1
;;      (implies (memberp x (remove-1 y list))
;;               (memberp x list))
;;      :hints (("goal" :in-theory (enable memberp remove-1))))

;;    (defthm not-unique-remove-1
;;      (implies (not (unique (remove-1 x list)))
;;               (not (unique list)))
;;      :hints (("goal" :induct (remove-1 x list)
;;               :in-theory (enable unique remove-1))))

;;    (defthm unique-remove-1-not-memberp-unique
;;      (implies
;;       (and
;;        (unique (remove-1 x list))
;;        (memberp x list)
;;        )
;;       (equal (unique list)
;;              (not (memberp x (remove-1 x list)))))
;;      :hints (("goal" :in-theory (enable unique memberp remove-1))))

;;    )))
;; |#

;; #|
;; (local
;;  (defthmd non-membership-remove-bag-reduction-generalization
;;    (implies (and (consp y)
;;                  (not (memberp (car y) x)))
;;             (equal (remove-bag x y)
;;                    (cons (car y) (remove-bag x (cdr y)))))))
;; |#

;; #|
;; prove remove-bag of list::fix instead??
;; do we want to drive the list::fix in or out???
;; (defthm remove-bag-of-list-fix-two
;;   (equal (remove-bag y (list::fix y))
;;          (remove-bag x y))
;;   :hints (("Goal" :in-theory (enable remove-bag list::fix))))
;; |#

;; #|
;; bzo not quite right
;; (defthm subbagp-of-append
;;   (equal (subbagp (append x y) z)
;;          (and (subbagp x (remove-bag y z))
;;               (subbagp y z)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable subbagp append remove-1))))
;; |#


;; #|
;;  (encapsulate
;;   ()

;;   (local
;;    (encapsulate
;;     ()

;;     (local
;;      (encapsulate
;;       ()

;;       (defthm memberp-append-tail
;;         (implies (consp a)
;;                  (memberp (car a) (append b a)))
;;         :hints (("goal" :in-theory (enable memberp binary-append))))

;;       (defthm memberp-append-middle
;;         (implies (consp b)
;;                  (memberp (car b) (append a b c)))
;;         :hints (("goal" :in-theory (enable memberp binary-append))))

;;       (defthm append-cdr-tail-perm-remove-1
;;         (implies
;;          (consp y)
;;          (perm (append x (cdr y))
;;                (remove-1 (car y) (append x y))))
;;         :hints (("goal" :in-theory (enable perm binary-append memberp remove-1))))

;;       (defthm append-cdr-middle-perm-remove-1
;;         (implies
;;          (consp y)
;;          (perm (append x (cdr y) z)
;;                (remove-1 (car y) (append x y z))))
;;         :hints (("goal" :in-theory (enable perm binary-append memberp remove-1))))

;;       ))



;;     ))


;;   )
;; |#

;; #|
;; (defthmd perm-of-append
;;   (equal (perm (append x y) z)
;;          (and (subbagp x z)
;;               (perm y (remove-bag x z)))))

;; (defthm remove-bag-of-remove-1
;;   (implies (and (memberp a x)
;;                 (memberp a y))
;;            (perm (remove-bag (remove-1 a x) y)
;;                  (cons a (remove-bag x y))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (remove-bag) (remove-1)))))

;; (defthm remove-bag-almost-all-1
;;   (implies (and (memberp a x)
;;                 (true-listp x))
;;            (equal (remove-bag (remove-1 a x) x)
;;                   (list a)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (remove-bag) (remove-1)))))

;; (defthm remove-bag-almost-all
;;   (equal (remove-bag (remove-1 a x) x)
;;          (if (memberp a x)
;;              (list a)
;;            nil)))
;; |#

;; #|
;;
;; (defthmd remove-all-of-car
;;   (equal (remove-all (car x) x)
;;          (if (consp x)
;;              (remove-all (car x) (cdr x))
;;            x))
;;   :hints (("Goal" :in-theory (enable remove-all))))

;; (defthm car-of-remove-all
;;   (equal (car (remove-all a x))
;;          (if (equal a (car x))
;;              (cadr x)
;;            (car x)))
;;   :hints (("Goal" :in-theory (enable remove-all))))
;; |#

;; #|
;; ;try disabled?
;; (defthmd non-membership-removal-free
;;   (implies (and (not (memberp b x)) ;b is a free variable
;;                 (equal b a))
;;            (equal (remove-all a x)
;;                   x)))
;; |#

;; #|
;; ;need a nice way to say this...
;; (defthm consp-remove-all-rewrite
;;   (equal (consp (remove-all a x))
;;          (or (and (not (memberp a x))
;;                   (consp x))
;;              (< 1 (len x))))
;;   :hints (("Goal" :in-theory (enable remove-all))))
;; |#

;; #|
;; ;try disabled?
;; (defthm equality-from-mem-and-remove-all
;;   (implies (and (not (memberp a (remove-all b x)))
;;                 (memberp a x))
;;            (equal b a))
;;   :rule-classes :forward-chaining)
;; |#

;; #|
;; ;or should we rewrite (subbagp x (remove-all a y))??
;; (defthm subbagp-from-subbagp-of-remove-all
;;   (implies (subbagp x (remove-all a y)) ;a is a free variable
;;            (subbagp x y))
;;   :hints (("Goal" :in-theory (enable remove-all subbagp))))
;; |#

;; #|
;; (defthm subbagp-of-remove-all-irrel-one
;;   (implies (not (memberp a y))
;;            (equal (subbagp (remove-all a x) y)
;;                   (subbagp x y)))
;; ;  :otf-flg t
;;   :hints (("Goal" :in-theory (enable remove-all subbagp))))
;; |#


;; #|
;; (thm
;;  (implies
;;   (and ;(memberp a y)
;;    (subbagp x y)
;;    (memberp a (remove-bag x y))
;;    )
;;   (subbagp x (remove-1 a y)))
;;  :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;           :in-theory (enable remove-1))))

;; |#

;; #|
;; (defthm runnerdotcom-2
;;   (implies (<= (count a x) (count a y))
;;            (perm (remove-1 a (remove-bag x (cons a y)))
;;                  (remove-bag x y))))
;; |#

;; #|

;; (defthm bag-intersection-of-remove-1-helper-two
;;   (implies (= (count a y) (count a x))
;;            (equal (bag-intersection x (remove-1 a y))
;;                   (remove-1 a (bag-intersection x y))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (bag-intersection remove-1 count) (COUNT-OF-CDR)))))

;; (defthm bag-intersection-of-remove-1-helper-two-alt
;;   (implies (= (count a y) (count a x))
;;            (equal (bag-intersection x (remove-1 a y))
;;                   (remove-1 a (bag-intersection x y))))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (bag-intersection remove-1 count) (COUNT-OF-CDR)))))


;; (defthm bag-intersection-of-remove-1-one
;;  (equal (bag-intersection x (remove-1 a y))
;;         (if (< (count a x) (count a y))
;;             (bag-intersection x y)
;;           (remove-1 a (bag-intersection x y))))
;;  :hints (("Goal" :in-theory (enable bag-intersection remove-1))))
;; |#

;; #|
;; (defthmd bag-intersection-when-car-not-memberp
;;   (implies (not (memberp (car x) y))
;;            (equal (bag-intersection x y)
;;                   (if (consp x)
;;                       (bag-intersection (cdr x) y)
;;                     (finalcdr x)))))
;; |#


;; #|
;; ;note that we use PERM, not EQUAL
;; (defthm bag-intersection-commutative
;;   (perm (bag-intersection x y)
;;         (bag-intersection y x))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable bag-intersection))))

;; (defthm bag-intersection-associative
;;   (perm (bag-intersection (bag-intersection x y) z)
;;         (bag-intersection x (bag-intersection y z)))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (e/d (bag-intersection remove-1 memberp) (REMOVE-1-OF-BAG-INTERSECTION)))))



;; zz

;; (defthm bag-intersection-of-cons-2
;;   (perm (bag-intersection x (cons a y))
;;         (if (memberp a x)
;;             (cons a (bag-intersection y (remove-1 a x)))
;;           (bag-intersection y x)))
;;   :hints (("Goal" :in-theory (disable  bag-intersection-of-cons-1)
;;            :use (:instance bag-intersection-of-cons-1 (x y) (y x)))))

;; (thm
;;  (equal (bag-intersection x (cons a y))
;;         (if (memberp a x)
;;             (cons a (bag-intersection (remove-1 a x) y))
;;           (bag-intersection x (cons a y))))
;;  :hints (("Goal" :in-theory (enable bag-intersection))))

;; (thm
;;  (perm (remove-bag (remove-bag z y) x)
;;        (append (remove-bag y x)
;;                (bag-intersection x (bag-intersection y z))))
;;  :hints (("Goal" :in-theory (enable remove-bag bag-intersection append)
;;           :do-not '(generalize eliminate-destructors))))
;; |#




;; Example of how this rule helps us:  If we know:
;;(LIST::MEMBERP a '(1 2 3 4 5)) this rule lets us rewrite:
;;(LIST::MEMBERP a '(6 7 8 9 10))) to nil without splitting into cases based
;;on whether a is 1 or 2 or 3 or 4 or 5.

(defthm non-memberp-from-memberp-of-other-cheap
  (implies (and (syntaxp (quotep x))
                (list::memberp a free)
                (syntaxp (quotep free))
                (bag::disjoint x free)
                )
           (equal (list::memberp a x)
                  nil)))

(defthm subbagp-of-x-and-cons-car-x
  (implies (consp x)
           (equal (bag::subbagp x (cons (car x) y))
                  (bag::subbagp (cdr x) y))))

;looped?
;; (defthm subbagp-of-singleton
;;   (equal (bag::subbagp x (cons a nil))
;;          (or (bag::empty-bagp x)
;;              (list::equiv a (cons a nil))
;; ;             (and (equal 1 (len x)) ;rephrase as congruence to singleton bag?
;;  ;                 (equal a (car x)))

;;              ))
;;   :hints (("Goal" :cases ( (equal 1 (len x)))
;;            :in-theory (enable list::memberp-of-cons
;;                               bag::subbagp-of-cons))))


(defthm subbagp-of-singleton
  (equal (bag::subbagp x (cons a nil))
         (or (bag::empty-bagp x)
             (list::equiv x (cons a nil)) ;use perm here?
             ))
  :hints (("Goal" :in-theory (enable list::memberp-of-cons
                                     bag::subbagp-of-cons))))


;Is there a non-cheap version?
(defthm subbagp-from-subbagp-of-cdr-cheap
  (implies (bag::subbagp x (cdr y))
           (bag::subbagp x y))
  :rule-classes((:rewrite :backchain-limit-lst (0))))

(defthm unique-means-car-not-memberp-of-cdr
  (implies (unique x)
           (not (memberp (car x) (cdr x)))))

(defthm subbagp-of-remove-all-self
  (bag::subbagp (bag::remove-all a x) x)
  :hints (("Goal" :in-theory (enable bag::remove-all))))

(defthm subbagp-of-remove-all-first-arg
  (implies (bag::subbagp x y)
           (bag::subbagp (bag::remove-all a x) y))
  :hints (("Goal" :use (:instance subbagp-of-remove-all-self)
           :in-theory (disable subbagp-of-remove-all-self))))

(defthm perm-of-append-cdr-self
  (equal (bag::perm x (append (cdr x) y))
         (if (consp x)
             (bag::perm y (list (car x))) ;simplify this?
           (not (consp y))))
 :hints (("Goal" :in-theory (enable bag::perm-of-append-two))))


(defthm remove-bag-of-cons-and-cons
  (equal (bag::remove-bag (cons a x) (cons a y))
         (bag::remove-bag x y))
  :hints (("Goal" :in-theory (enable bag::remove-bag))))

(defthm subbagp-nil-when-not-memberp-car-cheap
  (implies (and (not (memberp (car ads1) ads2))
                (consp ads1))
           (not (bag::subbagp ads1 ads2)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

(defthm remove-bag-of-cons
  (equal (bag::remove-bag (cons a y) z)
         (bag::remove-1 a (bag::remove-bag y z)))
  :hints (("Goal" :in-theory (enable bag::remove-bag))))

(defthm bag::subbagp-of-remove-1-two-both
  (equal (bag::subbagp bag::x (bag::remove-1 bag::a bag::y))
         (if (memberp bag::a bag::y)
             (bag::subbagp (cons bag::a bag::x)
                           bag::y)
           (bag::subbagp bag::x bag::y)))
  :hints (("Goal" :in-theory (e/d (bag::subbagp-of-remove-1-two) (SUBBAGP-OF-CONS)))))

;bzo drop hyp?
(defthm subbagp-of-remove-bag-of-cons
  (implies (not (list::memberp a y))
           (equal (bag::subbagp x (bag::remove-bag (cons a y) z))
                  (if (list::memberp a z)
                      (bag::subbagp (cons a x) (bag::remove-bag y z))
                    (bag::subbagp x (bag::remove-bag y z)))))
  :hints (("Goal" :in-theory (e/d (BAG::SUBBAGP-OF-REMOVE-1-TWO
                                   BAG::MEMBERP-OF-REMOVE-BAG-IRREL
                                   )
                                  (BAG::MEMBERP-OF-REMOVE-BAG
                                   SUBBAGP-OF-CONS)))))

;expensive?
(defthmd memberp-of-car-from-subbagp
  (implies (and (bag::subbagp x y)
                (consp x))
           (bag::memberp (car x) y)))

(in-theory (disable SUBBAGP-OF-REMOVE-1-TWO-BOTH))

(theory-invariant (incompatible (:rewrite SUBBAGP-OF-CONS) (:rewrite SUBBAGP-OF-REMOVE-1-TWO-BOTH)))

(defthm subbagp-of-cdr-and-remove-1-same
  (equal (bag::subbagp (cdr lst) (bag::remove-1 (car lst) lst2))
         (if (list::memberp (car lst) lst2)
             (bag::subbagp lst lst2)
           (bag::subbagp (cdr lst) lst2)))
  :hints (("Goal" :in-theory (e/d (bag::subbagp) (SUBBAGP-CDR-REMOVE-1-REWRITE)))))
