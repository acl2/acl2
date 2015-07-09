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

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility
(error "Is anyone using this?  If so please remove this error.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; bags-definitions.lisp
;; John D. Powell
(in-package "BAGS")

;;
;; This file isolates bags definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the bags book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

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


;loop?
(defthmd remove-1-of-remove-bag
  (equal (remove-1 a (remove-bag x y))
         (remove-bag x (remove-1 a y))))

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
(defthm subbagp-cdr-lemma
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

(defund disjoint (x y)
  (declare (type t x y))
  (if (consp x)
      (if (memberp (car x) y)
          nil
        (disjoint (cdr x) y))
    t))

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

(defthm count-when-non-member
  (implies (not (memberp a x))
           (equal (count a x)
                  0))
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

(defthm subbagp-of-cdr-and-remove-1-same
  (equal (bag::subbagp (cdr lst) (bag::remove-1 (car lst) lst2))
         (if (list::memberp (car lst) lst2)
             (bag::subbagp lst lst2)
           (bag::subbagp (cdr lst) lst2)))
  :hints (("Goal" :in-theory (e/d (bag::subbagp) (SUBBAGP-CDR-REMOVE-1-REWRITE)))))
(in-theory
 (disable
  (:REWRITE SUBBAGP-IMPLIES-REMOVE-BAG)
  (:REWRITE REMOVE-BAG-CONS-REMOVE-1-NOT-EQUAL)
  (:REWRITE REMOVE-BAG-REMOVE-1)
  (:REWRITE REMOVE-BAG-CONS)
  (:REWRITE SUBBAGP-CDR)
  (:REWRITE SUBBAGP-IMPLIES-COMMON-MEMBERS-ARE-IRRELEVANT)
;  (:REWRITE NOT-REMOVE-BAG-IMPLIES-NOT-REMOVE-BAG-REMOVE-1)
  (:REWRITE SUBBAGP-APPEND-APPEND)
  (:REWRITE SUBBAGP-APPEND-APPEND-LEFT)
  (:REWRITE SUBBAGP-IMPLIES-SUBBAGP-CONS)
  (:REWRITE MEMBERSHIP-EXTRACTION-INSTANCE)
  ))

(in-theory
 (disable
  (:REWRITE *TRIGGER*-UNIQUE-SUBBAGPS-IMPLIES-DISJOINTNESS)
  (:REWRITE *TRIGGER*-SUBBAGP-PAIR-DISJOINT) ;can we get rid of this then?
 ))

;we look through HYPS for a term of the form (subbagp x y)
;if such an item is found, we return (mv t y).  else, we return (mv nil nil)
;what if multple such things might be found?
(defun find-exact-subbagp-instance (x hyps)
  (declare (type t hyps)
           )
  (if (consp hyps)
      (let ((entry (car hyps)))
        (if (and (consp entry)
                 ; (not (subbagp term zed))
                 (equal (car entry) 'not)
                 (consp (cdr entry))
                 (consp (cadr entry))
                 (equal (car (cadr entry)) 'subbagp)
                 (consp (cdr (cadr entry)))
                 (equal (cadr (cadr entry)) x)
                 (consp (cddr (cadr entry))))
            (mv t (caddr (cadr entry)))
          (find-exact-subbagp-instance x (cdr hyps))))
    (mv nil nil)))

;look through HYPS for a term of the form (subbagp term zed) where x is a
;syntactic subbagp of TERM.  if such a term is found, return (mv t term zed
;rh) where rh contains the remainder of HYPS (the stuff not yet processed by
;this function) else, return (mv nil nil nil nil)

(defun find-syntax-subbagp-instance (x hyps)
  (declare (type t hyps)
           (xargs :guard (and (PSEUDO-TERM-LISTP hyps)
                              (PSEUDO-TERMP X)))
           )
  (if (consp hyps)
      (let ((entry (car hyps)))
        (let ((hit ;(not (subbagp term zed))
               (and
                (consp entry)
                (equal (car entry) 'not)
                (consp (cdr entry))
                (consp (cadr entry))
                (equal (car (cadr entry)) 'subbagp) ;;(subbagp term zed)
                (consp (cdr (cadr entry)))
                (consp (cddr (cadr entry)))
                (let ((term (cadr (cadr entry)))
                      (zed (caddr (cadr entry))))
                  (and (syntax-subbagp-fn nil x term)
                       (cons term zed))))))
          (if hit
              (mv t (car hit) (cdr hit) (cdr hyps))
            (find-syntax-subbagp-instance x (cdr hyps)))))
    (mv nil nil nil nil)))

;n seems to be a counter which restricts the amount of looking we do (hence the "bounded" in the function name).
(defun find-bounded-subbagp-path (top x rh y hyps n res)
  (declare (type (integer 0 *) n)
           (xargs :guard (and (PSEUDO-TERM-LISTP hyps) ;i'm not sure all the guards are necessary, but they worked!
                              (PSEUDO-TERM-LISTP rh)
                              (PSEUDO-TERMP X)
                              (PSEUDO-TERMP y))
                  :measure (nfix n)))
  (if (zp n)
      nil
    (if (and top (equal x y))
        (cons (cons y t) res)
      (if (and top (syntax-subbagp-fn nil x y))
          (cons (cons y nil) res)
        (met ((hit x0) (if top (find-exact-subbagp-instance x rh) (mv nil nil)))
             (or (and hit (find-bounded-subbagp-path t x0 hyps y hyps (1- n) (cons (cons x0 t) res)))
                 (met ((hit x0 x1 nrh) (find-syntax-subbagp-instance x rh))
                      (and hit
                           (or (find-bounded-subbagp-path t   x1 hyps y hyps (1- n) (cons (cons x1 t) (cons (cons x0 nil) res)))
                               (find-bounded-subbagp-path nil x  nrh  y hyps (1- n) res))))))))))

(defun reverse-path (path res)
  (declare (type t path res))
  (if (consp path)
      (let ((entry (car path)))
        (and (consp entry)
             (let ((res `(cons (cons ,(car entry) (quote ,(cdr entry))) ,res)))
               (reverse-path (cdr path) res))))
    res))

;what does this do?
;we look through HYPS for a term of the form (subbagp x BLAH)
;if such an item is found, we test whether BLAH equals y.  else, we return nil
;what if multple such things might be found?
(defun subbagp-instance (x y hyps)
  (declare (type t x y hyps))
  (met ((hit res) (find-exact-subbagp-instance x hyps))
       (and hit
            (equal y res))))

(defun bind-subbagp-argument (key xlist x y mfc state)
  (declare (xargs  :guard (and
                           (PSEUDO-TERMP X)
                           (PSEUDO-TERMP y))
                   :stobjs (state)
                   :verify-guards t)
           (ignore state))
  (if (syntax-subbagp-fn nil x y)
      `((,key   . (quote t))
        (,xlist . (quote nil)))
    (let ((hyps (mfc-clause mfc)))
      (and (not (subbagp-instance x y hyps))
           (let ((res (find-bounded-subbagp-path t x hyps y hyps (len hyps) nil)))
             (if (and (consp res)
                      (consp (car res)))
;(prog2$
;(cw "~%dag: bind-subbagp-argument!~%")
                 (let ((type (cdar res)))
                   (let ((path (reverse-path (cdr res) `(quote ,type))))
                     `((,key   . (quote t))
                       (,xlist . ,path))))
               nil))))))


;add guard?
(defun subbagp-chain (x xlist x0)
  (if (consp xlist)
      (and (if (cdar xlist) (hide-subbagp x (caar xlist)) (meta-subbagp x (caar xlist)))
           (subbagp-chain (caar xlist) (cdr xlist) x0))
    (if xlist
        (hide-subbagp x x0)
      (meta-subbagp x x0))))

;add guard?
(defun subbagp-hyp (key x xlist y)
  (and key (subbagp-chain x xlist y)))

(defthm subbagp-computation
  (implies (and (bind-free (bind-subbagp-argument 'key 'xlist x y mfc state) (key xlist))
                (subbagp-hyp key x xlist y)
                )
           (subbagp x y))
  :hints (("goal" :in-theory (enable hide-subbagp meta-subbagp))))

;-------------------------- UNIQUENESS --------------------------;
;finds a single potential subbagp-path and returns the path
(defun find-subbagp-path (x hyps n res)
  (declare (type (integer 0 *) n)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-term-listp hyps))
                  :measure (nfix n)))
  (if (zp n) res
    (met ((hit x0) (find-exact-subbagp-instance x hyps))
         (if hit
             (find-subbagp-path x0 hyps (1- n) (cons (cons x0 t) res))
           (met ((hit x0 x1 rh) (find-syntax-subbagp-instance x hyps))
                (declare (ignore rh))
                (if hit
                    (find-subbagp-path x1 hyps (1- n) (cons (cons x1 t) (cons (cons x0 nil) res)))
                  res))))))

;searches through hyps for a call to UNIQUE which gives us (unique x)
(defun find-unique-instance (x hyps)
  (declare (type t x hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-term-listp hyps))))
  (if (consp hyps)
      (let ((entry (car hyps)))
        (let ((args (and (consp entry)
                         (equal (car entry) 'not)
                         (consp (cdr entry))
                         (let ((fn (cadr entry)))
                           (and (consp fn)
                                (equal (car fn) 'unique)
                                (consp (cdr fn))
                                (cadr fn))))))
          (if (equal x args)
              (mv args t)
            (if (and args (syntax-subbagp-fn nil x args))
                (mv args nil) ;why nil?
              (find-unique-instance x (cdr hyps))))))
    (mv nil nil)))

;added by eric for guard reasons
(defun list-whose-caars-are-pseudo-termsp (x)
  (declare (type t x))
  (if (consp x)
      (and (consp (car x))
           (pseudo-termp (caar x))
           (list-whose-caars-are-pseudo-termsp (cdr x)))
    t))


(defun find-unique-instance-list (xlist hyps)
  (declare (type t xlist hyps)
           (xargs :guard (and (list-whose-caars-are-pseudo-termsp xlist) ;(pseudo-termp xlist)
                              (pseudo-term-listp hyps))))
  (if (consp xlist)
      (let ((z0 (if (consp (car xlist)) (caar xlist) nil)))
        (met ((uni syntax) (find-unique-instance z0 hyps))
          (if uni
              (if syntax
                  xlist
                (append `((,uni . nil) (,z0 . t)) (cdr xlist))) ;reversed since list still needs to be reversed
            (find-unique-instance-list (cdr xlist) hyps))))
    nil))

(defthm pseudo-termp-of-v2-of-find-syntax-subbagp-instance
  (implies (pseudo-term-listp hyps)
           (pseudo-termp (val 2 (find-syntax-subbagp-instance x hyps)))))

(defthm pseudo-termp-of-v1-of-find-syntax-subbagp-instance
  (implies (pseudo-term-listp hyps)
           (pseudo-termp (val 1 (find-syntax-subbagp-instance x hyps)))))

(defthm pseudo-termp-of-v2-of-find-exact-subbagp-instance
  (implies (pseudo-term-listp hyps)
           (pseudo-termp (val 2 (find-exact-subbagp-instance x hyps)))))

(defthm pseudo-termp-of-v1-of-find-exact-subbagp-instance
  (implies (pseudo-term-listp hyps)
           (pseudo-termp (val 1 (find-exact-subbagp-instance x hyps)))))

(defthm list-whose-caars-are-pseudo-termsp-of-find-subbagp-path
  (implies (and (pseudo-term-listp hyps)
                (list-whose-caars-are-pseudo-termsp res)
                )
           (list-whose-caars-are-pseudo-termsp (find-subbagp-path x hyps n res)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defun unique-uniqueness (x hyps)
  (declare (type t x hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-term-listp hyps))))
  (let ((n (len hyps)))
    (let ((xlist (find-subbagp-path x hyps n `((,x . t)))))
      (let ((newlist (find-unique-instance-list xlist hyps)))
        (let ((uni (if (and (consp newlist) (consp (car newlist))) (caar newlist) nil)))
          (mv uni (reverse-path newlist '(quote t))))))))

(defun in-hyps-unique (x hyps)
  (declare (type t x hyps))
  (if (consp hyps)
      (let ((entry (car hyps)))
        (if (and (consp entry)
                 (consp (cdr entry)))
            (if (and (equal (car entry) 'unique)
                     (equal (cadr entry) x))
                t
              (in-hyps-unique x (cdr hyps)))
          (in-hyps-unique x (cdr hyps))))
    nil))

(defun bind-unique-argument (key xlist uni x mfc state)
  (declare (xargs :stobjs (state)
                  :guard (pseudo-termp x)
                  )
           (ignore state))
  (let ((hyps (mfc-clause mfc)))
    (and (or (mfc-ancestors mfc)
             (in-hyps-unique x hyps))
         (met ((hit list) (unique-uniqueness x hyps))
                (if hit
                    `((,key . (quote t))
                      (,xlist . ,list)
                      (,uni . ,hit))
                  nil)))))

;; hide-unique is defined in meta as unique

;add guard?
(defun unique-chain (x xlist uni)
  (if (consp xlist)
      (and (if (cdar xlist) (hide-subbagp x (caar xlist)) (meta-subbagp x (caar xlist)));(subbagp x (car xlist))
           (unique-chain (caar xlist) (cdr xlist) uni))
    (if xlist
        (and (hide-subbagp x uni)
             (hide-unique uni))
      (and (meta-subbagp x uni)
           (hide-unique uni)))))

;add guard?
(defun unique-hyp (key x xlist uni)
  (and key (unique-chain x xlist uni)))

(defthm unique-computation
  (implies (and (bind-free (bind-unique-argument 'key 'xlist 'uni x mfc state) (key xlist uni))
                (unique-hyp key x xlist uni))
           (unique x))
  :hints (("Goal" :in-theory (enable hide-unique hide-subbagp meta-subbagp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;--------------------------DISJOINTNESS---------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun find-disjointness (x y hyps)
  (declare (type t x y hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps)
                              )
                  ))
  (if (consp hyps)
      (let ((entry (car hyps)))
        (let ((args (and (consp entry)
                         (equal (car entry) 'not)
                         (consp (cdr entry))
                         (let ((fn (cadr entry)))
                           (and (consp fn)
                                (equal (car fn) 'disjoint)
                                (consp (cdr fn))
                                (consp (cddr fn))
                                (cons (cadr fn) (caddr fn)))))))
          (if (equal args nil)
              (find-disjointness x y (cdr hyps))
            (if (syntax-subbagp-pair-fn nil x y (car args) (cdr args))
                (mv t t (car args) (cdr args))
              (if (syntax-subbagp-pair-fn nil x y (car args) (cdr args))
                  (mv t nil (car args) (cdr args))
                (find-disjointness x y (cdr hyps)))))))
    (mv nil nil nil nil))) ;return list is hit syntax p q

(defun find-disjointness* (x ylist hyps)
  (declare (type t x ylist hyps)
           (xargs :guard (and (pseudo-termp x)
                              (list-whose-caars-are-pseudo-termsp ylist)
                              (pseudo-term-listp hyps))
                  ))

  (if (and (consp ylist)
           (consp (car ylist)))
      (met ((hit syn p q) (find-disjointness  x (caar ylist) hyps))
           (if hit
               (mv hit syn p q ylist)
             (find-disjointness* x (cdr ylist) hyps)))
    (mv nil nil nil nil nil)))

(defun find-disjointness** (xlist ylist hyps)
  (declare (type t xlist ylist hyps)
           (xargs :guard (and (list-whose-caars-are-pseudo-termsp xlist)
                              (list-whose-caars-are-pseudo-termsp ylist)
                              (pseudo-term-listp hyps))
                             ))
  (if (and (consp xlist)
           (consp (car xlist)))
      (met ((hit syn p q ylist2) (find-disjointness*  (caar xlist) ylist hyps))
           (if hit
               (mv hit syn xlist ylist2 p q)
             (find-disjointness** (cdr xlist) ylist hyps)))
    (mv nil nil nil nil nil nil)))

;checks for subbagp paths up to disjoint
;argument for disjointness comes from a disjoint in hyps
(defun disjoint-disjointness (x y hyps)
  (declare (type t x hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps))
                  ))
  (let ((n (len hyps)))
    (let ((xlist (find-subbagp-path x hyps n `((,x . t))))
          (ylist (find-subbagp-path y hyps n `((,y . t)))))
      (met ((hit syn newx newy p q) (find-disjointness** xlist ylist hyps))
           (if hit
               (let ((x0 (if (and (consp newx) (consp (car newx))) (caar newx) nil))
                     (y0 (if (and (consp newy) (consp (car newy))) (caar newy) nil)))
                 (mv t ;key
                     (reverse-path newx '(quote t)) ;xlist
                     x0
                     (reverse-path newy '(quote t)) ;ylist
                     y0
                     `(quote ,syn)
                     p
                     q)) ;z's are irrelevent in this argument
;but use z positions for subbagp-pair type argument
             (mv nil nil nil nil nil nil nil nil) ;no disjoint hyp found
             )))))
;move?
(defun revlist (list res)
  (declare (type t list res))
  (if (consp list)
      (revlist (cdr list) (cons (car list) res))
    res))

(defun find-subbagp-pair-zlist (x y zlist)
  (declare (type t x y zlist)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (list-whose-caars-are-pseudo-termsp zlist))
                  ))
  (if (consp zlist)
      (let ((args (and (consp (car zlist))
                       (caar zlist))))
        (if (syntax-unique-subbagps-fn nil x y args) ;once you have this, want to return list from args to unique
            (let ((newzlist (revlist zlist nil)))
              (let ((z0 (if (and (consp newzlist) (consp (car newzlist))) (caar newzlist) nil)))
                (mv t args newzlist z0)))
          (find-subbagp-pair-zlist x y (cdr zlist))))
    (mv nil nil nil nil)))


(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-revlist
  (IMPLIES (AND (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP list)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP res))
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP (REVLIST list res))))


(defun find-unique-subbagp (x y zlist hyps)
  (declare (type t x y hyps zlist)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps)
                              (list-whose-caars-are-pseudo-termsp zlist))
                  ))
  (if (consp hyps)
      (let ((entry (car hyps)))
        (let ((args (and (consp entry)
                         (equal (car entry) 'not)
                         (consp (cdr entry))
                         (let ((fn (cadr entry)))
                           (and (consp fn)
                                (equal (car fn) 'unique)
                                (consp (cdr fn))
                                (cadr fn))))))
          (if (and args (syntax-unique-subbagps-fn nil x y args)) ;if subbagp-pair of something unique
              (mv t args nil nil) ;(hit unique-element not-chain)
            (find-unique-subbagp x y zlist (cdr hyps)))))
    (met ((hit first chain z0) (find-subbagp-pair-zlist x y (revlist zlist nil)))
         (mv hit first (reverse-path chain '(quote t)) z0))))

(defun find-unique-subbagp* (x ylist zlist hyps)
  (declare (type t x ylist zlist hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-term-listp hyps)
                              (list-whose-caars-are-pseudo-termsp ylist)
                              (list-whose-caars-are-pseudo-termsp zlist))
                  ))
  (if (and (consp ylist)
           (consp (car ylist)))
      (met ((hit z chain z0) (find-unique-subbagp x (caar ylist) zlist hyps))
           (if hit
               (mv t (caar ylist) ylist z chain z0)
             (find-unique-subbagp* x (cdr ylist) zlist hyps)))
    (mv nil nil nil nil nil nil)))

(defun find-unique-subbagp** (xlist ylist zlist hyps)
  (declare (type t xlist ylist zlist hyps)
           (xargs :guard (and (pseudo-term-listp hyps)
                              (list-whose-caars-are-pseudo-termsp ylist)
                              (list-whose-caars-are-pseudo-termsp xlist)
                              (list-whose-caars-are-pseudo-termsp zlist))
                  ))
  (if (and (consp xlist)
           (consp (car xlist)))
      (met ((hit y0 ylist z chain z0) (find-unique-subbagp* (caar xlist) ylist zlist hyps))
           (if hit
               (if (not chain)
                   (mv t xlist (caar xlist) ylist y0 z '(quote nil) z)
                 (mv t xlist (caar xlist) ylist y0 z chain z0))
             (find-unique-subbagp** (cdr  xlist) ylist zlist hyps)))
    (mv nil nil nil nil nil nil nil nil)))

(defun find-shared-ancestor-list (x ylist yres)
  (declare (type t x ylist yres))
  (if (consp ylist)
      (if (and (consp (car ylist))
               (equal x (caar ylist)))
          (mv t yres)
        (find-shared-ancestor-list x (cdr ylist) (cons (car ylist) yres)))
    (mv nil nil)))

(defun find-shared-ancestor (xlist ylist xres)
  (declare (type t xlist ylist xres))
  (if (and (consp xlist)
           (consp (car xlist)))
      (met ((hit yres) (find-shared-ancestor-list (caar xlist) ylist nil))
           (if hit (mv xres yres xlist)
             (find-shared-ancestor (cdr xlist) ylist (cons (car xlist) xres))))
    (mv xres (revlist ylist nil) nil)))


(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-v0-of-FIND-SHARED-ANCESTOR
  (implies (and (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
               ; (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP ylist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xres)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP
            (VAL
             0
             (FIND-SHARED-ANCESTOR XLIST YLIST XRES)))))

(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-v1-of-FIND-SHARED-ANCESTOR-list
  (implies (and; (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP ylist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP yres)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP
            (VAL
             1
             (FIND-SHARED-ANCESTOR-list X YLIST yRES)))))

(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-v1-of-FIND-SHARED-ANCESTOR
  (implies (and (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP ylist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xres)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP
            (VAL
             1
             (FIND-SHARED-ANCESTOR XLIST YLIST XRES)))))

(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-v2-of-FIND-SHARED-ANCESTOR
  (implies (and (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP ylist)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xres)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP
            (VAL
             2
             (FIND-SHARED-ANCESTOR XLIST YLIST XRES)))))

(defthm PSEUDO-TERMP-of-v0-of-FIND-UNIQUE-INSTANCE
  (implies (PSEUDO-TERM-LISTP HYPS)
           (PSEUDO-TERMP (VAL 0 (FIND-UNIQUE-INSTANCE x HYPS)))))

(defthm LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP-of-FIND-UNIQUE-INSTANCE-LIST
  (IMPLIES (AND (PSEUDO-TERM-LISTP HYPS)
                (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP xlist)
                )
           (LIST-WHOSE-CAARS-ARE-PSEUDO-TERMSP (FIND-UNIQUE-INSTANCE-LIST xlist hyps))))

(defun unique-disjointness (x y hyps)
  (declare (type t x y hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps))
                  ))

  (let ((n (len hyps)))
    (let ((xlist (find-subbagp-path x hyps n `((,x . t))))
          (ylist (find-subbagp-path y hyps n `((,y . t)))))
      (let ((xlist (revlist xlist nil))
            (ylist (revlist ylist nil)))               ; smallest to largest
        (met ((xlist ylist zlist) (find-shared-ancestor xlist ylist nil)) ; x/y largest to smallest

             (let ((newzlist (find-unique-instance-list (revlist zlist nil) hyps)))
               ;; newzlist path from something unique down subbagps
               (met ((hit newxlist x0 newylist y0 z zlist z0) (find-unique-subbagp** xlist ylist newzlist hyps))
                    (mv hit (reverse-path newxlist '(quote t))
                        x0  (reverse-path newylist '(quote t))
                        y0 z zlist z0))))))))

;search for (disjoint X Y) in CLAUSE
;since we look for it non-negated, we are essentially looking for it as a conclusion
(defun in-clause-disjoint (x y clause)
  (declare (type t x y clause))
  (if (consp clause)
      (let ((entry (car clause)))
        (if (and (consp entry)
                 (equal (car entry) 'disjoint)
                 (consp (cdr entry))
                 (equal (cadr entry) x)
                 (consp (cddr entry))
                 (equal (caddr entry) y))
            t
          (in-clause-disjoint x y (cdr clause))))
    nil))

(defun bind-disjoint-argument (flg key xlist x0 ylist y0 z zlist z0 x y mfc state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              )
                  )
           (ignore state))
  (let ((hyps (mfc-clause mfc)))
    (and (or flg
             t
             (mfc-ancestors mfc) ;bzo why are we doing these checks?
             (in-clause-disjoint x y hyps)
             )
         (met ((hit xlist* x0* ylist* y0* z* zlist* z0*) (unique-disjointness x y hyps))
              (if hit
                  `((,key . (quote :unique))
                    (,xlist . ,xlist*)
                    (,x0 . ,x0*)
                    (,ylist . ,ylist*)
                    (,y0 . ,y0*)
                    (,z . ,z*)
                    (,zlist . ,zlist*)
                    (,z0 . ,z0*))
                (met ((hit xlist* x0* ylist* y0* z* zlist* z0*) (disjoint-disjointness x y hyps))
                     (if hit
                         `((,key . (quote :disjoint))
                           (,xlist . ,xlist*)
                           (,x0 . ,x0*)
                           (,ylist . ,ylist*)
                           (,y0 . ,y0*)
                           (,z . ,z*)
                           (,zlist . ,zlist*)
                           (,z0 . ,z0*))
                       nil)))))))

;rename!
(defthm subbagp-pair-x-x-y-y
  (subbagp-pair x y x y)
  :hints (("goal" :in-theory (enable subbagp-pair))))

;add guard?
(defun unique-subbagp-chain (x0 y0 z zlist z0)
  (and (unique-subbagps x0 y0 z)
       (unique-chain z zlist z0)))

;add guard?
(defun disjoint-hyp (key x xlist x0 y ylist y0 z-syn zlist-p z0-q)
  (cond
   ((equal key ':disjoint)
    (and (subbagp-pair x0 y0 zlist-p z0-q)
         (hide-disjoint zlist-p z0-q)
         (subbagp-chain x xlist x0)
         (subbagp-chain y ylist y0)))
   ((equal key ':unique)
    (and
     (unique-subbagp-chain x0 y0 z-syn zlist-p z0-q)
     (subbagp-chain x xlist x0)
     (subbagp-chain y ylist y0)
     ))
   (t nil)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;----------------------------- MEMBERP --------------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Collect up a list of all BLAH such that (memberp X BLAH) exists as a hyp in CLAUSE
(defun find-memberp-instance-list (x clause res)
  (declare (type t x clause res))
  (if (consp clause)
      (let ((entry (car clause)))
        (if (and (consp entry)
                ; (not (memberp x x0))
                 (equal (car entry) 'not)
                 (consp (cdr entry))
                 (consp (cadr entry))
                 (or (equal (car (cadr entry)) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                     (equal (car (cadr entry)) 'acl2::member-equal))
                 (consp (cdr (cadr entry)))
                 (consp (cddr (cadr entry)))
                 (equal (cadr (cadr entry)) x))
            (find-memberp-instance-list x (cdr clause)
                                       (cons (caddr (car (cdr entry))) res))
          (find-memberp-instance-list x (cdr clause) res)))
    res))

(defun find-memberp-subbagp-list (x0list y hyps)
  (declare (type t x0list y hyps)
           (xargs :guard (and (pseudo-termp y)
                              (pseudo-term-listp hyps)
                              (pseudo-term-listp x0list))
                  )
           )
  (if (consp x0list)
      (let ((x0 (car x0list)))
        (let ((res (find-bounded-subbagp-path t x0 hyps y hyps (len hyps) nil)))
          (if (and (consp res)
                   (consp (car res)))
              (let ((type (cdar res)))
                (let ((path (reverse-path (cdr res) `(quote ,type))))
                  (mv t x0 path)))
            (find-memberp-subbagp-list (cdr x0list) y hyps))))
    (mv nil nil nil)))

(defthm PSEUDO-TERM-LISTP-of-FIND-MEMBERP-INSTANCE-LIST
  (IMPLIES (AND (PSEUDO-TERM-LISTP clause)
                (PSEUDO-TERM-LISTP res)
                )
           (PSEUDO-TERM-LISTP (FIND-MEMBERP-INSTANCE-LIST x clause res))))

(defun memberp-membership (x y hyps)
  (declare (type t x y hyps)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              (pseudo-term-listp hyps))
                  ))
  (let ((x0list (find-memberp-instance-list x hyps nil)))
    (met ((hit x0 path) (find-memberp-subbagp-list x0list y hyps))
         (mv hit x0 path))))

(defun in-hyps-memberp (x y hyps)
  (declare (type t x y hyps))
  (if (consp hyps)
      (let ((entry (car hyps)))
        (if (and (consp entry)
                 (consp (cdr entry))
                 (consp (cddr entry)))
            (if (and (or (equal (car entry) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                         (equal (car entry) 'acl2::member-equal))
                     (equal (cadr entry) x)
                     (equal (caddr entry) y))
                t
              (in-hyps-memberp x y (cdr hyps)))
          (in-hyps-memberp x y (cdr hyps))))
    nil))

(defun bind-memberp-argument (key xlist x0 x y mfc state)
  (declare (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp y)
                              )
                  :stobjs (state)
                  )
           (ignore state))
  (let ((hyps (mfc-clause mfc)))
    (and (or (mfc-ancestors mfc)
             (in-hyps-memberp x y hyps))
         (met ((hit val list) (memberp-membership x y hyps))
              (if hit
                  `((,key . (quote t))
                    (,x0 . ,val)
                    (,xlist . ,list))
                nil)))))


;add guard?
(defun memberp-hyp (key x x0 xlist y)
  (and key
       (hide-memberp x x0)
       (subbagp-chain x0 xlist y)))

(defthm memberp-computation
  (implies
   (and
    (bind-free (bind-memberp-argument 'key 'xlist 'x0 x y mfc state)
               (key x0 xlist))
    (memberp-hyp key x x0 xlist y)
    )
   (memberp x y))
  :hints (("goal" :in-theory (enable hide-subbagp meta-subbagp hide-memberp))))

(local (in-theory (disable LIST::memberp-of-append)))

;------------------------ NON-MEMBERP -------------------------;
(defun remove-y (list y res)
  (declare (type t list y res))
  (if (consp list)
      (if (equal (car list) y)
          (cdr list)
        (remove-y (cdr list) y (cons (car list) res)))
    res))

(defun in-hyps-not-memberp (x y hyps)
  (declare (type t x y hyps))
  (if (consp hyps)
      (let ((entry (car hyps)))
        (if (and (consp entry)
                 (equal (car entry) 'not)
                 (consp (cdr entry))
                 (let ((fn (cadr entry)))
                   (and (consp fn)
                        (consp (cdr fn))
                        (consp (cddr fn))
                        (or (equal (car fn) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                            (equal (car fn) 'acl2::member-equal))
                        (equal (cadr fn) x)
                        (equal (caddr fn) y))))
            t
          (in-hyps-not-memberp x y (cdr hyps))))
    nil))

(defun disjoint-not-membership (memlist y mfc state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-termp y)
                              (pseudo-term-listp memlist)
                              )
                  ))
  (if (consp memlist)
      (let ((x* (car memlist)))
        (let ((disjoint-arg
               (bind-disjoint-argument t 'key 'xlist 'x0 'ylist 'y0 'z 'zlist 'z0 x* y mfc state)))
          (if disjoint-arg
              (mv t x* disjoint-arg)
            (disjoint-not-membership (cdr memlist) y mfc state))))
    (mv nil nil nil)))

(defthm PSEUDO-TERM-LISTP-of-REMOVE-Y
  (IMPLIES (and (PSEUDO-TERM-LISTP list)
                (PSEUDO-TERM-LISTP res))
           (PSEUDO-TERM-LISTP (REMOVE-Y list y res))))

(defun bind-non-memberp-argument (hit x* x y mfc state)
  (declare (xargs :stobjs (state)
                  :guard (and (pseudo-termp x)
                              (pseudo-termp y)
;                              (pseudo-term-listp memlist)
                              )
                  :guard-hints (("Goal" :in-theory (disable DISJOINT-NOT-MEMBERSHIP ;major speedup
                                                            PSEUDO-TERMP ;speedup
                                                            )))
                  )
;(ignore state)
           )
  (let ((hyps (mfc-clause mfc)))
    (and (or (mfc-ancestors mfc)
             (in-hyps-not-memberp x y hyps))
         (let ((memlist (remove-y (find-memberp-instance-list x hyps nil) y nil)))
           (met ((hit1 x*1 disjoint-arg) (disjoint-not-membership memlist y mfc state))
                (if (and hit1 (alistp disjoint-arg))
                    (append `((,hit . (quote t))
                              (,x* . ,x*1))
                            disjoint-arg)
                  nil))))))

;add guard?
(defun non-memberp-hyp (hit x* key x xlist x0 y ylist y0 z zlist z0)
  (and hit
       (hide-memberp x x*)
       (disjoint-hyp key x* xlist x0 y ylist y0 z zlist z0)))

(defthm non-memberp-computation
  (implies
   (and
    (bind-free (bind-non-memberp-argument 'hit 'x* x y mfc state)
               (hit x* key xlist x0 ylist y0 z zlist z0))
    (non-memberp-hyp hit x* key x xlist x0 y ylist y0 z zlist z0))
   (not (memberp x y)))
  :hints (("goal" :in-theory (e/d (hide-memberp disjoint-computation-lemma) (disjoint-hyp)))))

(in-theory (disable
            memberp ;just in case
            disjoint
;                           MEMBERP-SUBBAGP-NOT-CONSP-VERSION
            REMOVE-BAG
            REMOVE-1))

;;; from proof-common.lisp:


(defun find-remove-bag-instance-unique (y z term)
  (declare (type t term))
  (and (consp term)
       (if (and (equal (car term) 'binary-append) ; (binary-append a b)
                (consp (cdr term))
                (consp (cddr term)))
           (or (let ((a (cadr term)))
                 (and (consp a)
                      (equal (car a) 'remove-bag) ; (remove-bag x y)
                      (consp (cdr a))
                      (consp (cddr a))
                      (let ((zed nil)) ; (cw "x = ~p0 ~%" (caddr a))))
                        (declare (ignore zed))
                        (or (and (equal y (caddr a))
                                 (cons t (cadr a)))
                            (and (equal z (caddr a))
                                 (cons nil (cadr a)))))))
               (find-remove-bag-instance-unique y z (caddr term)))
         (and (equal (car term) 'remove-bag)
              (and (consp (cdr term))
                   (consp (cddr term))
                   (or (and (equal y (caddr term))
                            (cons t (cadr term)))
                       (and (equal z (caddr term))
                            (cons nil (cadr term)))))))))

;walk through hyps until we find (unique BLAH), then try to show ... what exactly??
(defun find-remove-bag-instance-hyps (y z hyps)
  (declare (type t hyps))
  (and (consp hyps)
       (or (let ((hyp (car hyps)))
             (and (consp hyp)  ; (not (unique ..))
                  (equal (car hyp) 'not)
                  (consp (cdr hyp))
                  (let ((term (cadr hyp))) ; (unqiue list)
                    (and (consp term)
                         (equal (car term) 'unique)
                         (consp (cdr term))
                         (find-remove-bag-instance-unique y z (cadr term))))))
           (find-remove-bag-instance-hyps y z (cdr hyps)))))

(defun bind-remove-bag-instance-fn (y z which val mfc state)
  (declare (xargs :stobjs (state)
                  :verify-guards t)
           (ignore state))
  (let ((hyps (mfc-clause mfc)))
    (let ((zed nil)); (cw "y = ~p0 ~%" y)))
      (declare (ignore zed))
      (let ((zed nil)); (cw "z = ~p0 ~%" z)))
        (declare (ignore zed))
        (let ((x (find-remove-bag-instance-hyps y z hyps)))
          (and x
               `((,which . (quote ,(car x)))
                 (,val   . ,(cdr x)))))))))

;add guard?
(defun disjoint-other-hyp (which x y z)
  (if which
      (disjoint (append x (remove-bag x y))
                z)
    (disjoint (append x (remove-bag x z)) y)))

(defthm disjoint-other-memberp
  (implies (and (bind-remove-bag-instance y z which x)
                (disjoint-other-hyp which x y z))
           (disjoint y z)))

;add guard?
(defun collect-list (term)
  (if (and (consp term)
           (equal (car term) 'remove-1))
      `(cons ,(cadr term)
             ,(collect-list (caddr term)))
    `(quote nil)))

;add guard?
(defun collect-rest (term)
  (if (and (consp term)
           (equal (car term) 'remove-1))
      (collect-rest (caddr term))
    term))

;add guard?
(defun bind-list (list rest term)
  `((,list . ,(collect-list term))
    (,rest . ,(collect-rest term))))

;this could be expensive?  could we just change syntax-subbagp to consider
;(remove-1 a y) to be a subset of x whenever y is a subset of x?

(defthm bind-subbagp-remove-bag
  (implies (and (subbagp x term)
                (bind-free (bind-list 'list 'rest term) (list rest))
                (equal y rest)
                (equal term (remove-bag list rest)))
           (subbagp x y))
  :hints (("goal" :in-theory (enable subbagp-remove-bag))))

(defthm bind-memberp-remove-bag
  (implies (and (memberp sblk term)
                (bind-free (bind-list 'list 'rest term) (list rest))
                (equal y rest)
                (equal term (remove-bag list rest)))
           (memberp sblk y)))

;;
;; a little rule to show not unique of a nest of appends when a term appears
;; twice in the nest and is known to represent a non-empty bag
;;

;bzo ;could do the same with repeated elements
(defun find-repeated-subbag (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (consp term)
      (if (equal 'cons (car term))
          (find-repeated-subbag (caddr term))
        (if (equal 'binary-append (car term))
            (if (consp (caddr term))
                (if (and ;(consp (cdr term))

                     (equal 'binary-append (car (caddr term)))
    ;(consp (cdaddr term))
                     (equal (cadr term)
                            (cadr (caddr term))))
                    (cadr term) ;found two indentical adjacent bag terms being appended
                  (find-repeated-subbag (caddr term)))
              (if (equal (caddr term) (cadr term))
                  (cadr term)
                nil))
          nil))
    nil))

(defun bind-x-to-repeated-subbag (term)
  (declare (xargs :guard (pseudo-termp term)))
  (let* ((bag (find-repeated-subbag term)))
    (if bag
        (acons 'x bag nil)
      nil)))


;local becasue the :meta rules that come later will be able to get this
(local
 (defthm not-unique-doublet
   (not (bag::unique (list x x)))))

;bzo move?
(defthm show-not-unique-1
  (implies (and (bind-free (bind-x-to-repeated-subbag y) (x))
                (consp x))
           (equal (bag::unique y)
                  (if (bag::subbagp (append x x) y) ;subbagp :meta rule should get this...
                      nil
                    (hide (bag::unique y)))))
  :hints (("Goal" :in-theory (disable ;not-unique-doublet
                                      ;bag::meta-rule-to-show-unique
                                      )
           :expand (hide (bag::unique y))
           :use (:instance not-unique-doublet (x (car x))))))

;; Test it out...
(local
 (defthm test-of-show-not-unique-1
   (implies (consp x)
            (not (bag::unique (append x x y))))))
;When we're rewriting a term, it may be one of the top-level literals in the goal, may be a subterm of a top-level
;literal, or may not even appear in the goal at all (because it arose during backchaining). This function tests
;whether the term is a top-level literal in the goal which has the "parity" of a hypothesis (or a negated
;conclusion, I guess).  Recall that a clause is the disjunction of the conclusion with the negations of all the
;hyps.  So a hypothesis H appears in the clause as (not H).
(defun hypothesis-parity (term mfc state)
  (declare (ignore state) (type t term mfc state) (xargs :guard-hints (("Goal" :in-theory (enable mfc-clause)))))
  (member-equal (list 'not term) (mfc-clause mfc)))

;This function tests whether the term is a top-level literal in the goal which has the "parity" of the conclusion
;(or a negated hypothesis, I guess).  Recall that a clause is the disjunction of the conclusion with the negations
;of all the hyps.  So a hypothesis H appears in the clause as just H.
(defun conclusion-parity (term mfc state)
  (declare (ignore state) (type t term mfc state) (xargs :guard-hints (("Goal" :in-theory (enable mfc-clause)))))
  (member-equal term (mfc-clause mfc)))

; verify gaurds?
;returns a list of equalities equivalent to the claim (equal CONS-NEST1 CONS-NEST2)
;perhaps don't include equalities that are trivially true?
(defun cons-equal-meta-function-helper (cons-nest1 cons-nest2)
  (declare (type t cons-nest1 cons-nest2))
  (if (and (consp cons-nest1)
           (consp (cdr cons-nest1))
           (consp (cddr cons-nest1))
           (equal (car cons-nest1) 'cons)
           (consp cons-nest2)
           (consp (cdr cons-nest2))
           (consp (cddr cons-nest2))
           (equal (car cons-nest2) 'cons))
      (if (equal (cadr cons-nest1) (cadr cons-nest2))
          (cons-equal-meta-function-helper (caddr cons-nest1) (caddr cons-nest2)) ;skip syntactically equal stuff
        (list
         'if
         (list 'equal (cadr cons-nest1) (cadr cons-nest2))
         (cons-equal-meta-function-helper (caddr cons-nest1) (caddr cons-nest2))
         ''nil
         ))
    ; if syntactically equal, take advantage of that fact
;    (if (equal cons-nest1 cons-nest2)
 ;       ''t
      (list 'equal cons-nest1 cons-nest2) ;at least one of them is not a cons
      ))


(defthm cons-equal-smart-meta-helper
  (equal (cons-ev (cons-equal-meta-function-helper nest1 nest2) a)
         (cons-ev (list 'equal nest1 nest2) a))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defun cons-equal-meta-function (term mfc state)
  (declare (type t  mfc state) (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
          ; (consp (cdr term)) ;how was I able to comment this out?
           (consp (cadr term))  ;(cadr term) should be of the form (cons blah blah2)
           (equal (car (cadr term)) 'cons)
           (consp (cddr term))
           (consp (caddr term))
           (equal (car (caddr term)) 'cons)  ;(caddr term) should be of the form (cons blah3 blah4)

           (equal (car term) 'equal)

;           (consp (cdr (cadr term))) ;check the arities:
 ;          (consp (cddr (cadr term)))
  ;         (consp (cdr (caddr term)))
   ;        (consp (cddr (caddr term)))
           (not (conclusion-parity term mfc state))
           )
      (cons-equal-meta-function-helper (cadr term) (caddr term))
    term))

(in-theory (disable HYPothesis-PARITY MFC-CLAUSE))

(defthmd cons-equal-smart-meta
  (equal (cons-ev term a)
         (cons-ev (cons-equal-meta-function term mfc state) a))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (equal))))

#|
; this one should fire first?
;this one takes two cons nests which are claimed to be equal and removes corresponding items which are syntactically equal, yielding a two possibly-smaller cons nests
;for efficiency, before creating the new nests (which might be the same as the old ones), we check whether we will make any changes and save the creation of the cons cells if we don't
;or pass a flag indicating whether we've changed anything?
(defun cons-equal-meta-function-helper2 (cons-nest1 cons-nest2)
  (declare (type t cons-nest1 cons-nest2))
  (if (and (consp cons-nest1)
           (consp (cdr cons-nest1))
           (consp (cddr cons-nest1))
           (equal (car cons-nest1) 'cons)
           (consp cons-nest2)
           (consp (cdr cons-nest2))
           (consp (cddr cons-nest2))
           (equal (car cons-nest2) 'cons))
      (if (equal (cadr cons-nest1) (cadr cons-nest2))
          (cons-equal-meta-function-helper2 (caddr cons-nest1) (caddr cons-nest2)) ;skip syntactically equal stuff
        (met ((result1 result2) (cons-equal-meta-function-helper2 (caddr cons-nest1) (caddr cons-nest2)))
             (mv (list 'cons (cadr cons-nest1) result1)
                 (list 'cons (cadr cons-nest2) result2))))
    (mv cons-nest1 cons-nest2) ;at least one of them is not a cons
    ))

;things that might be slow
;checking every time we rewrite and equal that the rule should fire.
;consing up the new term even in the case where nothing changes..
;checking whether a change was made when we just return term.

(defun cons-equal-meta-function2 (term)
  (declare (type t term))
  (if (and (consp term)
           (consp (cdr term))
           (consp (cadr term))  ;(cadr term) should be of the form (cons blah blah2)
           (equal (car (cadr term)) 'cons)
           (consp (cddr term))
           (consp (caddr term))
           (equal (car (caddr term)) 'cons)  ;(caddr term) should be of the form (cons blah3 blah4)

           (equal (car term) 'equal)

;           (consp (cdr (cadr term))) ;check the arities:
 ;          (consp (cddr (cadr term)))
  ;         (consp (cdr (caddr term)))
   ;        (consp (cddr (caddr term)))
;           (hypothesis-parity term mfc state)  ;TERM appears as a hypothesis (or a negated conclusion)
           )
      (met ((result1 result2) (cons-equal-meta-function-helper2 (cadr term) (caddr term)))
           (list 'equal result1 result2))
    term))

(defthm cons-equal-smart-meta2-helper-one
  (implies (equal (cons-ev (v0 (cons-equal-meta-function-helper2 nest1 nest2)) a)
                  (cons-ev (v1 (cons-equal-meta-function-helper2 nest1 nest2)) a))
           (cons-ev (list 'equal nest1 nest2) a))
  :hints (("Goal" :induct t
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm cons-equal-smart-meta2-helper-two
  (implies (cons-ev (list 'equal nest1 nest2) a)
           (equal (cons-ev (v0 (cons-equal-meta-function-helper2 nest1 nest2)) a)
                  (cons-ev (v1 (cons-equal-meta-function-helper2 nest1 nest2)) a)))
  :hints (("Goal" :induct t
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(defthm cons-equal-smart-meta2-helper-three
  (equal (equal (cons-ev (v0 (cons-equal-meta-function-helper2 nest1 nest2)) a)
                (cons-ev (v1 (cons-equal-meta-function-helper2 nest1 nest2)) a))
         (cons-ev (list 'equal nest1 nest2) a))
  :hints (("Goal" :induct t
           :do-not-induct t
           :do-not '(generalize eliminate-destructors))))

(in-theory (disable mv-nth))

(defthmd cons-equal-smart-meta2
  (equal (cons-ev term a)
         (cons-ev (cons-equal-meta-function2 term) a))
  :hints (("Goal" :in-theory (enable cons-equal)
           :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (equal))))

|#

#|

(in-theory (disable cons-equal))

|#

#|
(defund cons-equal-dummy (a b c d)
  (equal (cons a b) (cons c d)))

(defthmd cons-equal-introduce-dummy
  (implies (syntaxp (hypothesis-parity (list 'equal (list 'cons a b) (list 'cons c d)) mfc state))
           (equal (equal (cons a b) (cons c d))
                  (cons-equal-dummy a b c d)))
  :hints (("Goal" :in-theory (enable cons-equal-dummy))))

(defun cons-equal-dummy-meta-function (term)
  (declare (type t term))
  (if (and; (hypothesis-parity term mfc state) ;TERM appears as a hypothesis (or a negated conclusion)
           (consp term)
           (consp (cdr term))
           (consp (cddr term))
           (consp (cdddr term))
           (consp (cddddr term))
           (equal (car term) 'cons-equal-dummy)
           )
      (cons-equal-meta-function-helper (list 'cons (cadr term) (caddr term))
                                       (list 'cons (cadddr term) (car (cddddr term)))
                                       )
    term))


(defthm cons-equal-smart-meta-helper-2
  (equal (cons-ev2 (cons-equal-meta-function-helper nest1 nest2) a)
         (cons-ev2 (list 'equal nest1 nest2) a))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

(defthm cons-equal-dummy-meta
  (equal (cons-ev2 term a)
         (cons-ev2 (cons-equal-dummy-meta-function term) a))
  :hints (("Goal" :in-theory (enable cons-equal CONS-EQUAL-DUMMY)
           :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (cons-equal-dummy))))

(defthmd cons-equal-introduce-dummy-into-non-conclusion
  (implies (syntaxp (not (conclusion-parity (list 'equal (list 'cons a b) (list 'cons c d)) mfc state)))
           (equal (equal (cons a b) (cons c d))
                  (cons-equal-dummy a b c d)))
  :hints (("Goal" :in-theory (enable cons-equal-dummy))))

(in-theory (enable cons-equal-introduce-dummy-into-non-conclusion))
(in-theory (disable cons-equal)) ;we'll use our rule instead.
|#
;don't forget about the built-in axiom CONS-EQUAL

#|
(defthmd equal-cons-cases ;trying disabled...
  (implies (consp x)
           (equal (equal (cons y z) x)
                  (and (equal y (car x))
                       (equal z (cdr x))))))


;do i need both equal-cons-cases-2 and equal-true-list-cases?
(defthm equal-cons-cases-2
  (equal (equal x (cons y z))
         (and (consp x)
              (equal (car x) y)
              (equal (cdr x) z))))
|#

(defthmd cons-equal-rewrite ;trying disabled..
  (equal (equal (cons a x) y)
         (and (consp y)
              (equal a (car y))
              (equal x (cdr y)))))

(defthm cons-onto-cdr-equals-all-rewrite
  (equal (equal (cons a (cdr x))
                x)
         (and (consp x)
              (equal a (car x)))))

(defthm list-car-equal-all-rewrite
  (equal (equal (list (car x)) x)
         (and (consp x)
              (equal nil (cdr x))))
  :hints (("Goal" :in-theory (enable cons-equal-rewrite))))

(defthm cons-equal-cons-same-rewrite-one
  (equal (equal (cons a x) (cons a y))
         (equal x y)))

(defthm cons-equal-cons-same-rewrite-two
  (equal (equal (cons a x) (cons b x))
         (equal a b)))


(in-theory (disable cons-equal))
(in-theory (enable cons-equal-smart-meta))


(in-theory (disable mfc-clause))
(in-theory (disable acl2::mfc-type-alist))
(in-theory (disable acl2::unsigned-byte-p))
(in-theory (disable pseudo-termp pseudo-term-listp))

(local (in-theory (disable acl2-count)))
(local (in-theory (enable member-to-memberp)))

(defthm ACL2-COUNT-NTH
  (implies
   (AND
    (consp list)
    (NOT (ZP I)))
   (< (ACL2-COUNT (SYN::NTH I LIST))
      (ACL2-COUNT LIST)))
  :HINTS (("goal" :IN-THEORY (enable syn::nth))))

;bzo some of the comments in this book may be out of date

;This book contains Eric's :meta rules for bags.  The rules in this book can
;replace most of the rules in bind-free-rules.lisp.  The :meta rules in this
;book "extended" in that they access the meta-function context (or mfc).  Each
;rules rewrites a term based on information in the type-alist and generates a
;hypothesis containing exactly the information that the rule relied upon.

;; This books contains :meta rules to establish the following:
;; (subbagp x y)
;; (unique x)
;; (disjoint x y)
;; (memberp a x)
;; (not (memberp a x))
;; (not (equal a b))

;;Each of the six rules in this file is very similar. See the comments for the
;;first rule (about subbagp) for more information.


;This doesn't do much consing (bzo what about the call to syntax-subbagp?),
;but hyp-for-syntax-subbagp-from-facts does.  Try to show that X is a subbagp
;of y, given the facts in CLAUSE (currently, we pay attention to only the
;subbagp facts in CLAUSE).  CLAUSE is a clause, and so facts that come from
;hypotheses are negated in CLAUSE.  The flag PERFORM-SYNTAX-SUBBAGP-TEST
;indicates whether we should test whether (syntax-subbagp x y).  Note that we
;need not do this on each recursive call, only on calls where x or y has
;changed.  The flag perform-syntax-subbagp-test should always be t for
;top-level calls. bzo better type guard on the flag (it's a boolean) So for
;the usual case (we're just walking down the clause, skipping literals that
;aren't subbagp calls), we don't keep redoing the syntax-subbagp test.
;perform-syntax-subbagp-test is a single 0 or 1 (so we can declare it to have
;type "bit"); maybe this is silly and we should just use t or nil...

;the parameter N represents the number of additional facts we are allowed to
;use and is used mostly for termination.  (I guess if there are cycles among
;the subbagp facts in the clause, then we might actually hit the case where we
;test for N.  prevents loops and is okay because, given a clause with n
;literals, we'll never need to use more than n facts to make a subbagp chain I
;wanted to move the test of N right before the recrusive call, so that we
;don't have to bother checking N in the usual case (namely, when entry is not
;a subbagp claim), but that didn't work because ACL2 only uses the top-level
;IF structure to determine termination. :-(

;We currently don't make use of the polarity of the term being rewritten to
;decide what to do for it.  We could, for example, try to rewrite hypotheses
;to false and conclusions to true. It's probably okay to not refrain from
;trying a rewrite due to polarity, since doing so can help get rid of
;redundant information; if, say, a hyp is implied by the other hyps, maybe we
;do want to get rid of it (by rewriting it to t) since it might just distract
;the user.  We also don't know a quick and easy way to tell the polarity of a
;term.

;;
;; Lemmas about allvars1 (this closely follows the material in :doc MUTUAL-RECURSION-PROOF-EXAMPLE)
;;

(defun symbol-listp-all-vars1-induction (flg x ans)
    ; Flg is non-nil (or t) if we are ``thinking'' of a single term.
  (if (atom x)
      (list x ans)
    (if flg
        (symbol-listp-all-vars1-induction nil (cdr x) ans)
      (list (symbol-listp-all-vars1-induction t (car x) ans)
            (symbol-listp-all-vars1-induction nil (cdr x) (all-vars1 (car x) ans))))))

(defthm symbol-listp-all-vars1-flg
  (if flg
      (implies (and (pseudo-termp x)
                    (symbol-listp ans))
               (symbol-listp (all-vars1 x ans)))
    (implies (and (pseudo-term-listp x)
                  (symbol-listp ans))
             (symbol-listp (all-vars1-lst x ans))))
  :hints (("Goal" :in-theory (enable pseudo-termp)
           :induct (symbol-listp-all-vars1-induction flg x ans)))
  :rule-classes nil)

(defthm symbol-listp-all-vars1
  (implies (and (pseudo-termp x)
                (symbol-listp ans))
           (symbol-listp (all-vars1 x ans)))
  :hints (("Goal" :by (:instance symbol-listp-all-vars1-flg
                                 (flg t)))))

(defthm symbol-listp-all-vars1-lst
  (implies (and (pseudo-term-listp x)
                (symbol-listp ans))
           (symbol-listp (all-vars1-lst x ans)))
  :hints (("Goal" :by (:instance symbol-listp-all-vars1-flg (flg nil)))))

(defun true-listp-all-vars1-induction (flg x ans)
    ; Flg is non-nil (or t) if we are ``thinking'' of a single term.
  (if (atom x)
      (list x ans)
    (if flg
        (true-listp-all-vars1-induction nil (cdr x) ans)
      (list (true-listp-all-vars1-induction t (car x) ans)
            (true-listp-all-vars1-induction nil (cdr x) (all-vars1 (car x) ans))))))

(defthm true-listp-all-vars1-flg
  (if flg
      (implies (and (pseudo-termp x)
                    (true-listp ans))
               (true-listp (all-vars1 x ans)))
    (implies (and (pseudo-term-listp x)
                  (true-listp ans))
             (true-listp (all-vars1-lst x ans))))
  :hints
  (("Goal" :induct (true-listp-all-vars1-induction flg x ans)))
  :rule-classes nil)

(defthm true-listp-all-vars1
  (implies (and (pseudo-termp x)
                (true-listp ans))
           (true-listp (all-vars1 x ans)))
  :hints (("Goal" :by (:instance true-listp-all-vars1-flg
                                 (flg t)))))

(defthm true-listp-all-vars1-lst
  (implies (and (pseudo-term-listp x)
                (true-listp ans))
           (true-listp (all-vars1-lst x ans)))
  :hints (("Goal" :by (:instance true-listp-all-vars1-flg (flg nil)))))

(in-theory (disable all-vars1 all-vars1-lst))


;;
;; lemmas about type-alistp
;;


(in-theory (disable acl2::type-alistp acl2::type-alist-entryp))

(defthm type-alistp-forward-to-true-listp
  (implies (acl2::type-alistp x)
           (true-listp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alistp))))

(defthm type-alistp-forward-to-pseudo-termp-of-caar
  (implies (and (acl2::type-alistp x)
                x)
           (pseudo-termp (caar x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alistp
                                     acl2::type-alist-entryp))))
(defthm type-alistp-of-cdr
  (implies (acl2::type-alistp type-alist)
           (acl2::type-alistp (cdr type-alist)))
  :hints (("Goal" :in-theory (enable acl2::type-alistp))))

(defthm type-alistp-fw-to-bound-1
  (implies (acl2::type-alistp type-alist)
           (<= (cadar type-alist) 8191))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alist-entryp ACL2::TYPE-ALISTP))))

(defthm type-alistp-fw-to-bound-2
  (implies (acl2::type-alistp type-alist)
           (<= -8192 (CADAR TYPE-ALIST)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alist-entryp ACL2::TYPE-ALISTP))))

(defthm type-alistp-fw-to-integerp-of-cadar
  (implies (and (acl2::type-alistp type-alist)
                type-alist)
           (integerp (cadar type-alist)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable acl2::type-alist-entryp ACL2::TYPE-ALISTP))))

;;
;;
;; stuff about types
;;
;;
;Checks that TS represents a non-nil type.
;was a macro...
(defund ts-non-nil (ts)
  (declare (xargs :guard (and (INTEGERP ts)
                              (<= -8192 ts)
                              (<= ts 8191))))
  (not (acl2::ts-intersectp ts acl2::*ts-nil*)))

;Checks that TS represents the type nil.
;was a macro...
(defund ts-nil (ts)
  (declare (xargs :guard (and (INTEGERP ts)
                              (<= -8192 ts)
                              (<= ts 8191))))
  (acl2::ts= ts acl2::*ts-nil*))




;;
;; stuff about unsigned-bytep
;;


;move this to a book about unsigned-byte-p?
;this broke something in push-gacc. why?  so i disabled it.
(defthmd unsigned-byte-p-from-bounds
  (implies (and (syntaxp (quotep bits))
                (< x (expt 2 bits))
                (integerp x)
                (<= 0 x)
                (integerp bits)
                (<= 0 bits))
           (acl2::unsigned-byte-p bits x))
  :hints (("Goal" :in-theory (enable acl2::unsigned-byte-p))))

(local (in-theory (enable unsigned-byte-p-from-bounds)))

(defthm unsigned-byte-p-of-one-less
  (implies (and (acl2::unsigned-byte-p 16 n)
                (< 0 n)
                (integerp n)
                )
           (acl2::unsigned-byte-p 16 (+ -1 n)))
  :hints (("Goal" :in-theory (enable acl2::unsigned-byte-p))))

;Making this local, since we have the same rule in super-ihs, and we don't need both.
;If you need rules about unsigned-byte-p, get them from super-ihs...
(local
 (defthm usb-linear-rewrite
   (implies (and (acl2::unsigned-byte-p n x)
                 (<= (expt 2 n) v))
            (< x v))
   :rule-classes (:rewrite)
   :hints (("goal" :in-theory (enable acl2::unsigned-byte-p)))))

(defund usb16-fix (x)
  (declare (type t x))
  (if (and (integerp x)
           (<= 0 x)
           (< x 65536))
      x
    65535))

(defthm usb16-usb16-fix
  (acl2::unsigned-byte-p 16 (usb16-fix x))
  :hints (("goal" :in-theory (enable usb16-fix))))

(defthm usb16-implies-usb16-fix-identity
  (implies
   (acl2::unsigned-byte-p 16 x)
   (equal (usb16-fix x) x))
  :hints (("goal" :in-theory (enable usb16-fix)
           :cases ((equal x 65535)))))

;;
;;
;; make-conjunction, etc.
;;
;;

;Returns a term representing the conjunctionof TERM1 and TERM2.
(defund make-conjunction (term1 term2)
  (declare (type t term1 term2))
  (if (equal term1 ''t)
      term2 ;conjoining something with "true" has no effect
    (if (equal term2 ''t)
        term1 ;conjoining something with "true" has no effect
      `(if ,term1 ,term2 'nil))))

(defthm make-conjunction-of-t-two
  (equal (make-conjunction x ''t)
         x)
  :hints (("Goal" :in-theory (enable make-conjunction))))

(defthm make-conjunction-of-t-one
  (equal (make-conjunction ''t x)
         x)
  :hints (("Goal" :in-theory (enable make-conjunction))))

(defthm make-conjunction-equal--quote-t-rewrite
  (equal (equal ''t (make-conjunction term1 term2))
         (and (equal ''t term1)
              (equal ''t term2)))
  :hints (("Goal" :in-theory (enable make-conjunction))))

(defthm syntax-ev-of-make-conjunction
  (iff (syntax-ev (make-conjunction term1 term2) alist)
       (and (syntax-ev term1 alist)
                (syntax-ev term2 alist)))
  :hints (("Goal" :in-theory (enable make-conjunction))))

(defthm pseudo-termp-of-make-conjunction
  (equal (pseudo-termp (make-conjunction term1 term2))
         (and (pseudo-termp term1)
                  (pseudo-termp term2)))
  :hints (("Goal" :in-theory (enable make-conjunction pseudo-termp))))

;could check whether term1 is ''t, but I think that'll never happen (we only negate stuff we find typed to nil in the type-alist).
;we don't need to check whether term2 is 't, because we'd still generate essentially `(if ,term1 'nil ,term2)
(defund make-conjunction-with-arg1-negated (term1 term2)
  (declare (type t term1 term2))
  `(if ,term1 'nil ,term2))

(defthm syntax-ev-of-make-conjunction-with-arg1-negated
  (iff (syntax-ev (make-conjunction-with-arg1-negated term1 term2) alist)
       (and (not (syntax-ev term1 alist))
            (syntax-ev term2 alist)))
  :hints (("Goal" :in-theory (enable make-conjunction-with-arg1-negated))))

(defthm pseudo-termp-of-make-conjunction-with-arg1-negated
  (equal  (pseudo-termp (make-conjunction-with-arg1-negated term1 term2))
          (and (pseudo-termp term1)
               (pseudo-termp term2)))
  :hints (("Goal" :in-theory (enable make-conjunction-with-arg1-negated))))

;;
;;
;; stuff to support binding all the vars in our hyps to themselves
;;
;;

;; Essay on hypothesis metafunctions and changes recently made to ACL2.
;;
;; If a hypothesis metafunction generates a hypothesis which mentions variables not in the term being rewritten,
;; those variables are considered free when ACL2 relieves the generated hypothesis.  This was a big surprise to us!
;; Furthermore, :meta rules behave as if they have :match-free :once. We had a small example in which a :meta rule
;; failed because a spurious match was found, preventing the right match from being found.  That was annoying, since
;; we know exactly what we want the variables in our hyp to be bound to (namely, themselves!)  Recall that everything
;; in our generated hyps comes straight from the type-alist.  We solve the free variables problem by binding to
;; itself each variable from the hyp which is not also in the term being rewritten.  (A recent change to ACL2 allows
;; this. Previously, the hyps generated by hypothesis metafunctions could not include calls to SYNP (which is what
;; BIND-FREE expands into.)  We also add a backchain limit of 0 to our :meta rules, because nothing more than type
;; reasoning should be needed to relieve the hyps, since they can straight from the type-alist.  Having a backchain
;; limit also ensures that the rule won't loop by finding in the generated hypothesis the very term bring rewritten.
;; (A change to ACL2 allowed the use of backchain limits with :meta rules.)


;; This generates what is essentially a call to bind-free that binds each var in VARS to themselves.  (Actually,
;; bind-free is a macro, and we must generate a term, so we generate a call to SYNP, which is what the call to
;; bind-free would expans into.)
;; NOTE! If VARS is nil, you probably don't want to call this function, since it will
;; return what is essentially a call to bind-free with a nil, and returning nil is how a bind-free function signals
;; failure.
;;  bzo add a guard that  vars is not nil?

;This partly follows a defun from Matt Kaufmann.
(defund bind-vars-to-selves (vars)
  (declare (xargs :guard t))
; The following can be figured out by running
; :trans1 (bind-free (pairlis$ '(a b c) '(a b c)) (a b c))
  `(SYNP ',vars
         '(BIND-FREE (PAIRLIS$ ',vars ',vars)
                     ,vars)
         '(PAIRLIS$ ',vars ',vars)))

(defun bind-extra-vars-in-hyp (hyp term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp hyp)
                              )))
  (if hyp ;bzo do we even need to check this?
      (let* ((hyp-vars (all-vars hyp))
             (lhs-vars (all-vars term))
             (extra-vars (acl2::set-difference-eq hyp-vars lhs-vars)))
        (if extra-vars ;if there are no extra vars, we can't just have "bind-free" return an empty alist, since that's how bind-free indicates failure.
            (make-conjunction (bind-vars-to-selves extra-vars) hyp)
          hyp))
    ''nil))

;; jcd - speed hack !!
;;
;; these rules seem to slow down the proofs in this book after this point, and
;; don't seem to be needed.  so, I am locally disabling them.
(local (in-theory (disable default-car default-cdr)))

(defthm show-subbagp-from-type-alist-iff-hyp-for-show-subbagp-from-type-alist
  (iff (show-subbagp-from-type-alist x y n type-alist whole-type-alist flg)
       (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg))
  :hints (("Goal" :in-theory (enable show-subbagp-from-type-alist-fn
                                     hyp-for-show-subbagp-from-type-alist-fn))))


(defthm show-subbagp-from-type-alist-works-right
  (implies (and (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg)
                (syntax-ev (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg) a))
           (subbagp (syntax-ev x a)
                    (syntax-ev y a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-subbagp-from-type-alist-fn
                            )
                           ())))
  :rule-classes (:rewrite :forward-chaining))

;; ;do we need this?
;; ;use this more?
;; (defthm show-subbagp-from-type-alist-works-right-2
;;   (implies (equal (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg)
;;                   ''t)
;;            (subbagp (syntax-ev x alist)
;;                     (syntax-ev y alist)))
;;   :hints (("Goal" :in-theory (disable show-subbagp-from-type-alist-works-right)
;;            :use (:instance show-subbagp-from-type-alist-works-right))))

(defthm hyp-for-show-subbagp-from-type-alist-equal-t-rewrite
  (equal (equal (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist flg)
                ''t)
         (and (equal 1 flg) (syntax-subbagp x y)))
  :hints (("Goal" :expand ((HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-fn a X Y N TYPE-ALIST WHOLE-TYPE-ALIST FLG))
           :in-theory (enable hyp-for-show-subbagp-from-type-alist-fn))))


(defthm pseudo-termp-of-hyp-for-show-subbagp-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-subbagp-from-type-alist x y n type-alist whole-type-alist perform-syntax-test)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-FN))))

;This is the metafunction.

;(We could count the number of subbagp facts and use that value for len.  This
;might be a good idea if we think cycles might exist among our subbagp facts.)
;(Or We could consider using the length of the clause, not the type-alist for
;len.)

(defun show-subbagp-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (equal (car term) 'subbagp) ;needed for the guard stuff..
           (let* ((type-alist (acl2::mfc-type-alist mfc))
                  (len (usb16-fix (len type-alist))))
             (show-subbagp-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist 1)))
      ''t
    term))

;This is the hypothesis metafunction

;This partly follows something from Matt Kaufmann.
(defun hyp-for-show-subbagp-from-mfc (term mfc state)
  (declare (type t term mfc state)
           (ignore state)
           (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (equal (car term) 'subbagp) ;needed for the guard stuff..
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (bind-extra-vars-in-hyp
         (hyp-for-show-subbagp-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist 1) term))
    ''nil))


;; This is the :meta rule for (subbagp x y).

(defthm meta-rule-to-show-subbagp
  (implies (syntax-ev (hyp-for-show-subbagp-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-subbagp-from-mfc term mfc state) a)))
  :otf-flg t
  :rule-classes ((:meta :trigger-fns (subbagp)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable HYP-FOR-SHOW-SUBBAGP-FROM-TYPE-ALIST-irrelevant)
           :do-not '(generalize eliminate-destructors))))

(in-theory (disable subbagp-computation)) ;we will use my rule instead
;(in-theory (disable meta-rule-to-show-subbagp))
(defthm show-unique-from-type-alist-iff-hyp-for-show-unique-from-type-alist
  (iff (show-unique-from-type-alist x n type-alist whole-type-alist)
       (hyp-for-show-unique-from-type-alist x n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-unique-from-type-alist-fn
                                     hyp-for-show-unique-from-type-alist-fn))))

(defthm show-unique-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-unique-from-type-alist x n type-alist whole-type-alist ) a)
                (hyp-for-show-unique-from-type-alist x n type-alist whole-type-alist ))
           (unique (syntax-ev x a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-unique-from-type-alist-fn)
                           ())))
  :rule-classes (:rewrite :forward-chaining))

(defthm pseudo-termp-of-hyp-for-show-unique-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-unique-from-type-alist x n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable hyp-for-show-unique-from-type-alist-fn))))

(defthm syntax-show-common-members-implies-not-unique
  (implies
   (syntax-show-common-members list)
   (not (unique (syntax-ev list a))))
  :hints (("goal" :in-theory (enable SYN::NTH unique)))
  :rule-classes (:rewrite :forward-chaining))


(defun show-unique-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;should always succeed
           (equal 'unique (car term)))
      (if (let* ((type-alist (acl2::mfc-type-alist mfc))
                 (len (usb16-fix (len type-alist))))
            (show-unique-from-type-alist-fn nil (cadr term) len type-alist type-alist))
          (syn::true)
        (if (syntax-show-common-members-fn nil (cadr term))
            (syn::nil)
          term))
    term))

(defun hyp-for-show-unique-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;should always succeed
           (equal 'unique (car term)) ;should always succeed, included for guard proof
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (let ((hyp (hyp-for-show-unique-from-type-alist-fn nil (cadr term) len type-alist type-alist)))
          (or (and hyp
                   (bind-extra-vars-in-hyp hyp term))
              (if (syntax-show-common-members-fn nil (cadr term))
                  (syn::true)
                (syn::nil)))))
    (syn::nil)))

(defthm meta-rule-to-show-unique
  (implies (syntax-ev (hyp-for-show-unique-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-unique-from-mfc term mfc state) a)))
  :rule-classes ((:meta :trigger-fns (unique)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable
                       hyp-for-show-unique-from-type-alist-irrelevant
                       syntax-show-common-members-irrelevant
                       )
           :do-not '(generalize eliminate-destructors))))

(in-theory (disable unique-computation))

(defthm show-unique-subbagps-from-type-alist-iff-hyp-for-show-unique-from-type-alist
  (iff (show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg)
       (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg))
  :hints (("Goal" :in-theory (enable show-unique-subbagps-from-type-alist-fn
                                     hyp-for-show-unique-subbagps-from-type-alist-fn
                                     ))))

;bzo make a meta rule to conclude unique-subbagps
;get rid of some hints?
;really slow proof!

; jcd - i looked at speeding this up by disabling rules from accumulated
; persistence, but I didn't get very far at all.  it uses the definition
; hyp-for-show-unique-subbagps-from-type-alist-fn a lot but you can't just
; disable it, or the proof fails.  so, i didn't change anything, since i didn't
; have anything to show for it.

(defthm show-unique-subbagps-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg) a)
                (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg)
                (equal v (syntax-ev x a))
                (equal w (syntax-ev y a))
                )
           (unique-subbagps v w (syntax-ev bag a)))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable hyp-for-show-unique-subbagps-from-type-alist-fn)))
  :rule-classes (:rewrite :forward-chaining))

(defthmd show-unique-subbagps-from-type-alist-works-right-2
  (implies
   (and (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg)
        (equal (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg) ''t))
   (unique-subbagps (syntax-ev x a)
                    (syntax-ev y a)
                    (syntax-ev bag a)))
  :hints (("Goal" :use (:instance  show-unique-subbagps-from-type-alist-works-right
                                   (v (syntax-ev x a))
                                   (w (syntax-ev y a)))
           :in-theory (disable  show-unique-subbagps-from-type-alist-works-right)))
  :rule-classes (:rewrite :forward-chaining))

;bzo any tests for this? go ahead and make the :meta rule?
(defthm pseudo-termp-of-hyp-for-show-unique-subbagps-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-unique-subbagps-from-type-alist x y bag n type-alist whole-type-alist flg)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-UNIQUE-SUBBAGPS-FROM-TYPE-ALIST-fn))))

;;
;;
;; disjoint
;;
;;


;old stuff
(in-theory (disable unique-subbagps-from-unique-subbagps-and-subbagp))


(defthm show-disjoint-from-type-alist-iff-hyp-for-show-disjoint-from-type-alist
  (iff (show-disjoint-from-type-alist x y n type-alist whole-type-alist)
       (hyp-for-show-disjoint-from-type-alist x y n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-disjoint-from-type-alist-fn
                                     hyp-for-show-disjoint-from-type-alist-fn
                                     ))))

(defthm show-disjoint-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-disjoint-from-type-alist x y n type-alist whole-type-alist) a)
                (hyp-for-show-disjoint-from-type-alist x y n type-alist whole-type-alist))
           (disjoint (syntax-ev x a)
                     (syntax-ev y a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-disjoint-from-type-alist-fn
                            *TRIGGER*-UNIQUE-SUBBAGPS-IMPLIES-DISJOINTNESS
                            show-unique-subbagps-from-type-alist-works-right
;                            show-subbagp-from-type-alist-works-right-2
                            )
                           ())))
  :rule-classes (:rewrite :forward-chaining))

(defthm pseudo-termp-of-hyp-for-show-disjoint-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-disjoint-from-type-alist x y n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-DISJOINT-FROM-TYPE-ALIST-fn))))

(defun show-disjoint-from-mfc (term mfc state)
  (declare (type t term mfc state)
           (ignore state)
           (xargs :guard (pseudo-termp term)
                  ))
  (if (and (consp term)    ;well-formedness checks, should always succeed
           (equal (car term) 'disjoint)
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (if (show-disjoint-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist)
            ''t
          term))
    term))

(defun hyp-for-show-disjoint-from-mfc (term mfc state)
  (declare (type t term mfc state)
           (xargs :guard (pseudo-termp term))
           (ignore state))
  (if (and (consp term) ;well-formedness checks, should always succeed
           (equal (car term) 'disjoint)
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (bind-extra-vars-in-hyp (hyp-for-show-disjoint-from-type-alist-fn
                                 nil (cadr term) (caddr term) len type-alist type-alist) term))
    ''nil))

(defthm meta-rule-to-show-disjoint
  (implies (syntax-ev (hyp-for-show-disjoint-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-disjoint-from-mfc term mfc state) a)))
  :hints (("goal" :in-theory (enable
                              hyp-for-show-disjoint-from-type-alist-irrelevant
                              )))
  :rule-classes ((:meta :trigger-fns (disjoint)
                        :backchain-limit-lst 0 ;just in case...
                        )))

(in-theory (disable disjoint-computation))
(in-theory (disable subbagp-disjoint))
;(in-theory (disable meta-rule-to-show-disjoint))

(defthm show-memberp-from-type-alist-iff-hyp-for-show-memberp-from-type-alist
  (iff (show-memberp-from-type-alist x y n type-alist whole-type-alist flg)
       (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg))
  :hints (("Goal" :in-theory (enable show-memberp-from-type-alist-fn
                                     hyp-for-show-memberp-from-type-alist-fn
                                     ))))

(defthm pseudo-termp-of-hyp-for-show-memberp-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-MEMBERP-FROM-TYPE-ALIST-fn))))

(defthm show-memberp-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg) a)
                (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg)
                )
           (memberp (syntax-ev x a)
                    (syntax-ev y a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-memberp-from-type-alist-fn
                            )
                           ()))))

(defthm hyp-for-show-memberp-from-type-alist-equal-t-rewrite
  (equal (equal (hyp-for-show-memberp-from-type-alist x y n type-alist whole-type-alist flg)
                ''t)
         (and (equal 1 flg) (syntax-memberp x y)))
  :hints (("Goal" :in-theory (enable hyp-for-show-memberp-from-type-alist-fn))))

(defun show-memberp-from-mfc (term mfc state)
  (declare (ignore state)
           (type t term mfc state)
           (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
               (equal (car term) 'acl2::member-equal))
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (if (show-memberp-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist 1)
            ''t
          term))
    term))

(defun hyp-for-show-memberp-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
               (equal (car term) 'acl2::member-equal))
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist))))
        (bind-extra-vars-in-hyp (hyp-for-show-memberp-from-type-alist-fn
                                 nil (cadr term) (caddr term) len type-alist type-alist 1) term))
    ''nil))

(defthm meta-rule-to-show-memberp
  (implies (syntax-ev (hyp-for-show-memberp-from-mfc term mfc state) a)
           (iff (syntax-ev term a)
                (syntax-ev (show-memberp-from-mfc term mfc state) a)))
  :rule-classes ((:meta :trigger-fns (acl2::member list::memberp)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :in-theory (enable
                              hyp-for-show-memberp-from-type-alist-irrelevant
                              )
           :do-not-induct t :do-not '(generalize eliminate-destructors))))

(in-theory (disable memberp-computation))

;;
;;
;; rule to show non-memberp
;;
;;



(local
 (defthm cons-iff
   (iff (cons x y)
        t)))

(defthm show-non-memberp-from-type-alist-iff-hyp-for-show-non-memberp-from-type-alist
  (iff (show-non-memberp-from-type-alist v x n type-alist whole-type-alist)
       (hyp-for-show-non-memberp-from-type-alist v x n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-non-memberp-from-type-alist-fn
                                     hyp-for-show-non-memberp-from-type-alist-fn
                                     ))))


(local (in-theory (enable not-memberp-from-disjointness-two
                          not-memberp-from-disjointness-one
                          not-memberp-from-unique-subbagps-of-something-unique-alt
                          not-memberp-from-unique-subbagps-of-something-unique)))

(defthm show-non-memberp-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-non-memberp-from-type-alist v x n type-alist whole-type-alist) a)
                (hyp-for-show-non-memberp-from-type-alist v x n type-alist whole-type-alist)
                )
           (not (memberp (syntax-ev v a)
                         (syntax-ev x a))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (
          ("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-non-memberp-from-type-alist-fn
                            )
                           ()))))

#+joe
(defthm show-non-memberp-from-type-alist-works-right-2
  (implies (equal (hyp-for-show-non-memberp-from-type-alist a x n type-alist whole-type-alist)
                 ''t)
           (not (memberp (syntax-ev a alist)
                         (syntax-ev x alist))))
  :hints (("Goal" :in-theory (disable show-non-memberp-from-type-alist-works-right)
           :use (:instance show-non-memberp-from-type-alist-works-right))))

(defthm pseudo-termp-of-hyp-for-show-non-memberp-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-non-memberp-from-type-alist v x n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-NON-MEMBERP-FROM-TYPE-ALIST))))

(defun show-non-memberp-from-mfc (term mfc state)
  (declare (ignore state)
           (type t term mfc state)
           (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
               (equal (car term) 'acl2::member-equal))
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
            (len  (usb16-fix (len type-alist))))
        (if (show-non-memberp-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist)
            ''nil ;we're rewriting a call to memberp to nil
          term))
    term))

(defun hyp-for-show-non-memberp-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
               (equal (car term) 'acl2::member-equal))
           )
      (let* ((type-alist (acl2::mfc-type-alist mfc))
            (len  (usb16-fix (len type-alist))))
        (bind-extra-vars-in-hyp (hyp-for-show-non-memberp-from-type-alist-fn
                                 nil (cadr term) (caddr term) len type-alist type-alist) term))
    ''nil))

(defthm meta-rule-to-show-non-memberp
  (implies (syntax-ev (hyp-for-show-non-memberp-from-mfc term mfc state) a)
           (iff (syntax-ev term a)
                (syntax-ev (show-non-memberp-from-mfc term mfc state) a)))
  :rule-classes ((:meta :trigger-fns (list::memberp acl2::member)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :in-theory (enable
                              hyp-for-show-non-memberp-from-type-alist-irrelevant
                              )
           :do-not-induct t :do-not '(generalize eliminate-destructors))))


(in-theory (disable non-memberp-computation))

(in-theory (disable hide-subbagp-forward
                    hide-subbagp-z-z
                    hide-unique-forward
                    hide-disjoint-forward
                    subbagp-pair-x-x-y-y
                    hide-memberp-forward
                    *trigger*-syntax-ev-syntax-subbagp
                    syntactic-membership-meta-rule
                    ;run-remove-1-helper2
                    ))

(defthm syntax-unique-memberps-implies-unique-memberps
  (implies (syntax-unique-memberps v b bag)
           (unique-memberps (syntax-ev v a)
                            (syntax-ev b a)
                            (syntax-ev bag a)))
  :hints (("Goal" :in-theory (enable unique-memberps
                                     syntax-unique-memberps-fn
                                     )))
  :rule-classes (:rewrite :forward-chaining))

;move
(defthm subbagp-from-syntax-remove-bag
  (implies (and (val 0 (syntax-remove-bag x z))               ;z is a free var
                (equal ''nil (val 1 (syntax-remove-bag x z)))
                (subbagp (syntax-ev z a) y))
           (subbagp (syntax-ev x a)
                    y))
  :hints (("Goal" :use (:instance subbagp-chaining (x (syntax-ev x a)) (y y) (z (syntax-ev z a)))))
  :rule-classes (:rewrite :forward-chaining))

(defthm syntax-unique-memberp-and-subbagp-implies-unique-memberp-and-subbagp
  (implies (syntax-unique-memberp-and-subbagp v x bag)
           (unique-memberp-and-subbagp (syntax-ev v a)
                                       (syntax-ev x a)
                                       (syntax-ev bag a)))
  :hints (("Goal" :in-theory (enable unique-memberp-and-subbagp
                                     syntax-unique-memberp-and-subbagp)))
  :rule-classes (:rewrite :forward-chaining))

(defun show-unique-memberp-and-subbagp-from-type-alist-memberp-case (a v x bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist type-alist)
           (xargs :guard  (and (acl2::type-alistp type-alist)
                               (acl2::type-alistp whole-type-alist)
                               (not (endp type-alist))
                               (consp fact)
                               (equal entry (car type-alist))
                               (equal fact (car entry))
                               (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                   (equal (car fact) 'acl2::member-equal))
                               (pseudo-termp v)
                               (pseudo-termp x)
                               (pseudo-termp bag)
                               (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and (equal v (cadr fact))
       (ts-non-nil (cadr entry))
       (show-unique-subbagps-from-type-alist
        x (caddr fact) bag w whole-type-alist whole-type-alist 1)
       (equal nil (cdddr fact))))

(defun hyp-for-show-unique-memberp-and-subbagp-from-type-alist-subbagp-case-1 (a v x bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist entry)
           (xargs :guard  (and (acl2::type-alistp type-alist)
                               (acl2::type-alistp whole-type-alist)
                               (not (endp type-alist))
                               (consp fact)
                               (equal entry (car type-alist))
                               (equal fact (car entry))
                               (equal (car fact) 'subbagp)

                               (pseudo-termp v)
                               (pseudo-termp x)
                               (pseudo-termp bag)
                               (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and (syntax-memberp v (cadr fact))
       (conjoin-fact-and-hyp
        fact (hyp-for-show-unique-subbagps-from-type-alist
              x (caddr fact) bag w whole-type-alist whole-type-alist 1))))

(defun hyp-for-show-unique-memberp-and-subbagp-from-type-alist-memberp-case (a v x bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist type-alist)
           (xargs :guard  (and (acl2::type-alistp type-alist)
                               (acl2::type-alistp whole-type-alist)
                               (not (endp type-alist))
                               (consp fact)
                               (equal entry (car type-alist))
                               (equal fact (car entry))
                               (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                   (equal (car fact) 'acl2::member-equal))
                               (pseudo-termp v)
                               (pseudo-termp x)
                               (pseudo-termp bag)
                               (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and (equal v (cadr fact))
       (ts-non-nil (cadr entry))
       (equal nil (cdddr fact))
       (conjoin-fact-and-hyp
        fact (hyp-for-show-unique-subbagps-from-type-alist
              x (caddr fact) bag w whole-type-alist whole-type-alist 1))))


(defthm show-unique-memberp-and-subbagp-from-type-alist-memberp-case-iff
  (iff (show-unique-memberp-and-subbagp-from-type-alist-memberp-case a v x bag entry fact type-alist w whole-type-alist)
       (hyp-for-show-unique-memberp-and-subbagp-from-type-alist-memberp-case a v x bag entry fact type-alist w whole-type-alist)))

;(in-theory (disable show-unique-memberp-and-subbagp-from-type-alist-memberp-case
;                    hyp-for-show-unique-memberp-and-subbagp-from-type-alist-memberp-case))


(defthm show-unique-memberp-and-subbagp-from-type-alist-iff-hyp-for-show-unique-from-type-alist
  (iff (show-unique-memberp-and-subbagp-from-type-alist v x bag n type-alist w whole-type-alist flg)
       (hyp-for-show-unique-memberp-and-subbagp-from-type-alist v x bag n type-alist w whole-type-alist flg))
  :hints (("Goal" :in-theory (enable show-unique-memberp-and-subbagp-from-type-alist
                                     hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                     ))))

(defthm UNIQUE-MEMBERP-AND-SUBBAGP-WHEN-UNIQUE-SUBBAGPS-AND-MEMBERP-ALT-trigger
  (IMPLIES
   (AND
    (MEMBERP A X)
    (UNIQUE-SUBBAGPS Y X BAG))
   (UNIQUE-MEMBERP-AND-SUBBAGP A Y BAG)))

(defthmd unique-memberp-and-subbagp-subbagp-trigger
  (implies
   (and
    (subbagp b1 b2)
    (memberp v b1)
    (unique-subbagps x b2 bag))
   (unique-memberp-and-subbagp v x bag)))

(defthm show-unique-memberp-and-subbagp-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                            v x bag n type-alist w whole-type-alist flg) a)
                (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                 v x bag n type-alist w whole-type-alist flg))
           (unique-memberp-and-subbagp (syntax-ev v a)
                                       (syntax-ev x a)
                                       (syntax-ev bag a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors preprocess
                                       )
           :in-theory (e/d (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                            unique-memberp-and-subbagp-subbagp-trigger)
                           ())))
  :rule-classes (:rewrite :forward-chaining))


#+joe
(defthm show-unique-memberp-and-subbagp-from-type-alist-works-right-2
  (implies
   (and (equal ''t (hyp-for-show-unique-memberp-and-subbagp-from-type-alist a x bag n type-alist w whole-type-alist flg))
        (hyp-for-show-unique-memberp-and-subbagp-from-type-alist a x bag n type-alist w whole-type-alist flg))
   (unique-memberp-and-subbagp (syntax-ev a alist)
                               (syntax-ev x alist)
                               (syntax-ev bag alist)))
  :hints (("Goal" :use (:instance show-unique-memberp-and-subbagp-from-type-alist-works-right)
           :in-theory (disable  show-unique-memberp-and-subbagp-from-type-alist-works-right))))

;bzo any tests for this? go ahead and make the :meta rule?

(defthm pseudo-termp-of-hyp-for-show-unique-memberp-and-subbagp-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-unique-memberp-and-subbagp-from-type-alist x y bag n type-alist w whole-type-alist flg)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-UNIQUE-MEMBERP-AND-SUBBAGP-FROM-TYPE-ALIST))))


;;meta rule goes here

;;tests go here...















;; Ways to show (unique-memberps a b bag)
;;   Easy case: Discover that (syntax-unique-memberps a b bag).
;;   Find (subbagp BLAH1 BLAH2) where (syntax-memberp a BLAH1), and then show (unique-memberp-and-subbagp b BLAH2 bag).
;;   Find (subbagp BLAH1 BLAH2) where (syntax-memberp b BLAH1), and then show (unique-memberp-and-subbagp a BLAH2 bag).
;;   Find (subbagp BLAH1 BLAH2) where (syntax-subbagp BLAH2 bag), and then show (unique-memberps a b BLAH1).
;;   Find (memberp a BLAH), and then show (unique-memberp-and-subbagp b BLAH bag).
;;   Find (memberp b BLAH), and then show (unique-memberp-and-subbagp a BLAH bag).

(defun show-unique-memberps-from-type-alist-memberp-case (a v b bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist)
           (type (unsigned-byte 16) w)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (equal entry (car type-alist))
                              (consp fact)
                              (equal fact (car entry))
                              (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                  (equal (car fact) 'acl2::member-equal))
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and(ts-non-nil (cadr entry))
      (or (and (equal v (cadr fact))
               (show-unique-memberp-and-subbagp-from-type-alist
                b (caddr fact) bag w whole-type-alist w whole-type-alist 1))
          (and (equal b (cadr fact))
               (show-unique-memberp-and-subbagp-from-type-alist
                v (caddr fact) bag w whole-type-alist w whole-type-alist 1)))
      (equal nil (cdddr fact))))

(defun hyp-for-show-unique-memberps-from-type-alist-memberp-case (a v b bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist)
           (type (unsigned-byte 16) w)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (equal entry (car type-alist))
                              (consp fact)
                              (equal fact (car entry))
                              (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                  (equal (car fact) 'acl2::member-equal))
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (and (ts-non-nil (cadr entry))
       (equal nil (cdddr fact))
       (or (and (equal v (cadr fact))
                (conjoin-fact-and-hyp fact
                                      (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                       b (caddr fact) bag w whole-type-alist w whole-type-alist 1)))
           (and (equal b (cadr fact))
                (conjoin-fact-and-hyp fact
                                      (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                       v (caddr fact) bag w whole-type-alist w whole-type-alist 1))))))


(defthm hyp-for-show-unique-memberps-from-type-alist-memberp-case-iff
  (iff (hyp-for-show-unique-memberps-from-type-alist-memberp-case a v b bag entry fact type-alist w whole-type-alist)
       (show-unique-memberps-from-type-alist-memberp-case a v b bag entry fact type-alist w whole-type-alist)))

(defun hyp-for-show-unique-memberps-from-type-alist-subbagp-case-1 (a v b bag entry fact type-alist w whole-type-alist)
  (declare (ignore type-alist entry)
           (type (unsigned-byte 16) w)
           (xargs :guard (and (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (equal entry (car type-alist))
                              (consp fact)
                              (equal fact (car entry))
                              (equal (car fact) 'subbagp)
                              (acl2::type-alistp whole-type-alist)
                              (pseudo-termp v)
                              (pseudo-termp b)
                              (pseudo-termp bag)
                              (equal w (usb16-fix (len whole-type-alist))))
                  :guard-hints  (("Goal" :do-not '(preprocess)))))
  (or (and (syntax-memberp v (cadr fact))
           (conjoin-fact-and-hyp fact
                                 (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                  b (caddr fact) bag w whole-type-alist w whole-type-alist 1)))
      (and (syntax-memberp b (cadr fact))
           (conjoin-fact-and-hyp fact
                                 (hyp-for-show-unique-memberp-and-subbagp-from-type-alist
                                  v (caddr fact) bag w whole-type-alist w whole-type-alist 1)))
      ))

(defthm pseudo-termp-of-hyp-for-show-unique-memberps-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-unique-memberps-from-type-alist v b bag n type-alist w whole-type-alist flg)))
  :hints (("Goal" :in-theory (enable hyp-for-show-unique-memberps-from-type-alist))))


;;
(defthm show-unique-memberps-from-type-alist-iff-hyp-for-show-unique-from-type-alist
  (iff (show-unique-memberps-from-type-alist x y bag n type-alist w whole-type-alist flg)
       (hyp-for-show-unique-memberps-from-type-alist x y bag n type-alist w whole-type-alist flg))
  :hints (("Goal" :in-theory (e/d (show-unique-memberps-from-type-alist
                                     hyp-for-show-unique-memberps-from-type-alist
                                     ) (;HYP-FOR-SHOW-UNIQUE-MEMBERPS-FROM-TYPE-ALIST-MEMBERP-CASE
                                        )))))

;drop some hints?
(defthm show-unique-memberps-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-unique-memberps-from-type-alist v b bag n type-alist w whole-type-alist flg) a)
                (hyp-for-show-unique-memberps-from-type-alist v b bag n type-alist w whole-type-alist flg)
                )
           (unique-memberps (syntax-ev v a)
                            (syntax-ev b a)
                            (syntax-ev bag a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (hyp-for-show-unique-memberps-from-type-alist
                            default-car default-cdr
                            )
                           (;for efficiency:

                            DEFAULT-CAR
                            ;;LIST::EQUAL-OF-BOOLEANS-REWRITE
                            acl2::iff-reduction
                            ))))
  :rule-classes (:rewrite :forward-chaining))

(defun show-unique-memberps-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'unique-memberps)
           (consp (cdr term))
           (consp (cddr term))
           (consp (cdddr term))
           (null  (cddddr term))
           (let* ((type-alist (acl2::mfc-type-alist mfc))
                  (len (usb16-fix (len type-alist)))
                  )
             (show-unique-memberps-from-type-alist-fn
              nil (cadr term) (caddr term) (cadddr term) len type-alist len type-alist 1)))
      ''t
    term))

(defun hyp-for-show-unique-memberps-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'unique-memberps)
           (consp (cdr term))
           (consp (cddr term))
           (consp (cdddr term))
           (null  (cddddr term)))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist)))
             )
        (bind-extra-vars-in-hyp
         (hyp-for-show-unique-memberps-from-type-alist-fn
          nil (cadr term) (caddr term) (cadddr term) len type-alist len type-alist 1) term))
    ''nil))

(defthm meta-rule-to-show-unique-memberps
  (implies (syntax-ev (hyp-for-show-unique-memberps-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-unique-memberps-from-mfc term mfc state) a)))
  :otf-flg t
  :rule-classes ((:meta :trigger-fns (unique-memberps)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable
                       hyp-for-show-unique-memberps-from-type-alist-irrelevant
                       ))))

;;
;;
;; Eric's rule for not equal
;;
;;

;Ways to show (not (equal x y)):
; Find (not (memberp x BLAH)) and show (memberp y BLAH), or vice-versa.
; Find (memberp x BLAH) and show (not (memberp y BLAH)), or vice-versa.
; Find (disjoint BLAH1 BLAH2) and show that a is a memberp of BLAH1 and b is a memberp of BLAH2, or vice versa.  (perhaps subset chains will intervene...)

; Find (unique BLAH) and show a and b are unique-memberps of BLAH. or that (list a) and (list b) are unique-subbagps of BLAH?? no? won't catch memberp facts?

;skip these for now?
; Find (subbagp BLAH1 BLAH2) where BLAH1 syntactically contains a, and show that b is not a memberp of BLAH2. - bzo do the memberp rules cover this case?
; Find (subbagp BLAH1 BLAH2) where BLAH1 syntactically contains b, and show that a is not a memberp of BLAH2.


;note that we actually look for something of the form (memberp b BLAH) which types to nil?

;bzo if they're constants, just call equal?  do we need to do that?  can other metafunctions call this one?
;unused?
;; (defun make-negation (term)
;;   (declare (type t term))
;;   `(if ,term 'nil 't))

;newly pulled out (doing so speed the guard conjecture for
;show-not-equal-from-type-alist-fn up by a ton (at the expense of perhaps
;slightly slower metafunction execution, but i bet that effect is minimal, and
;I'm sick of waiting for eric-meta to certify)
(defun show-not-equal-from-type-alist-member-case (a x y n entry fact type-alist whole-type-alist)
  (declare (ignore  type-alist)
           (xargs :guard (and (acl2::type-alistp whole-type-alist)
                              (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (consp fact)
                              (equal entry (car type-alist))
;                              (memberp entry whole-type-alist)
                              (equal fact (car entry))
                              (acl2::unsigned-byte-p 16 n)
                              (equal n (usb16-fix (len whole-type-alist)))
                              (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                  (equal (car fact) 'acl2::member-equal)))
                  :guard-hints (("Goal"

                                 :do-not '(generalize eliminate-destructors)))))
  (or (and (ts-nil (cadr entry))
           (or (and (equal x (cadr fact))
                    (show-memberp-from-type-alist
                     y (caddr fact) n whole-type-alist whole-type-alist 1)
                    (equal nil (cdddr fact)))
               (and (equal y (cadr fact))
                    (show-memberp-from-type-alist
                     x (caddr fact) n whole-type-alist whole-type-alist 1)
                    (equal nil (cdddr fact)))))
      (and (ts-non-nil (cadr entry))
           (or (and (equal x (cadr fact))
                    (show-non-memberp-from-type-alist
                     y (caddr fact) n whole-type-alist whole-type-alist)
                    (equal nil (cdddr fact)))
               (and (equal y (cadr fact))
                    (show-non-memberp-from-type-alist
                     x (caddr fact) n whole-type-alist whole-type-alist)
                    (equal nil (cdddr fact)))))))

;pulling this stuff out into a separate function
;  one more function call would be done when member or memberp facts are found in the type-alist
;  but now the guard conjecture for hyp-for-show-not-equal-from-type-alist takes 3 seconds instead of 145.
;  also, isn't the hyp fun only called when the metafunction succeeds?
;bzo - it's kind of gross to
;pass in the ignored type-alist, but it made the guard conjecture very close
;to what it was before this stuff was pulled out into a function
(defun hyp-for-show-not-equal-from-type-alist-member-case (a x y n entry fact type-alist whole-type-alist)
  (declare (ignore  type-alist)
           (xargs :guard (and (acl2::type-alistp whole-type-alist)
                              (acl2::type-alistp type-alist)
                              (not (endp type-alist))
                              (pseudo-termp x)
                              (pseudo-termp y)
                              (consp fact)
                              (equal entry (car type-alist))
;                              (memberp entry whole-type-alist)
                              (equal fact (car entry))
                              (acl2::unsigned-byte-p 16 n)
                              (equal n (usb16-fix (len whole-type-alist)))
                              (or (equal (car fact) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                                  (equal (car fact) 'acl2::member-equal)))
                  :guard-hints (("Goal"

                                 :do-not '(generalize eliminate-destructors)))))
  (or (and (ts-nil (cadr entry))
           (equal nil (cdddr fact))
           (or (and (equal x (cadr fact))
                    (conjoin-negated-fact-and-hyp
                     fact
                     (hyp-for-show-memberp-from-type-alist y (caddr fact) n whole-type-alist whole-type-alist 1)))
               (and (equal y (cadr fact))
                    (conjoin-negated-fact-and-hyp
                     fact
                     (hyp-for-show-memberp-from-type-alist x (caddr fact) n whole-type-alist whole-type-alist 1)))))
      (and (ts-non-nil (cadr entry))
           (equal nil (cdddr fact))
           (or (and (equal x (cadr fact))
                    (conjoin-fact-and-hyp
                     fact (hyp-for-show-non-memberp-from-type-alist
                           y (caddr fact) n whole-type-alist whole-type-alist)))
               (and (equal y (cadr fact))
                    (conjoin-fact-and-hyp
                     fact (hyp-for-show-non-memberp-from-type-alist
                           x (caddr fact) n whole-type-alist whole-type-alist)))))))

(defthm show-not-equal-from-type-alist-iff-hyp-for-show-not-equal-from-type-alist
  (iff (show-not-equal-from-type-alist x y n type-alist whole-type-alist)
       (hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist))
  :hints (("Goal" :in-theory (enable show-not-equal-from-type-alist
                                     hyp-for-show-not-equal-from-type-alist
                                     ))))

(defthm show-not-equal-from-type-alist-works-right
  (implies (and (syntax-ev (hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist) a)
                (hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist)
                )
           (not (equal (syntax-ev x a)
                       (syntax-ev y a))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( not-equal-when-unique-and-unique-memberps
                             hyp-for-show-not-equal-from-type-alist
                             not-equal-from-member-of-disjoint-facts
                             not-equal-from-member-of-disjoint-facts-alt
                             )
                           ()))))

(defthm pseudo-termp-of-hyp-for-show-not-equal-from-type-alist
  (implies (and (acl2::type-alistp type-alist)
                (acl2::type-alistp whole-type-alist)
                )
           (pseudo-termp (hyp-for-show-not-equal-from-type-alist x y n type-alist whole-type-alist)))
  :hints (("Goal" :in-theory (enable HYP-FOR-SHOW-NOT-EQUAL-FROM-TYPE-ALIST))))

(defun show-not-equal-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term) ;should always succeed
           (equal (car term) 'equal) ;should always succeed
           (let* ((type-alist (acl2::mfc-type-alist mfc))
                  (len (usb16-fix (len type-alist)))
                  )
             (show-not-equal-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist))
           (equal (cdddr term) nil))
      ''nil
    term))

(defun hyp-for-show-not-equal-from-mfc (term mfc state)
  (declare (ignore state)
           (xargs :guard (pseudo-termp term))
           (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'equal)
           (equal (cdddr term) nil))
      (let* ((type-alist (acl2::mfc-type-alist mfc))
             (len (usb16-fix (len type-alist)))
             )
        (bind-extra-vars-in-hyp (hyp-for-show-not-equal-from-type-alist-fn nil (cadr term) (caddr term) len type-alist type-alist) term))
    ''nil))


;This rule is hung on equal; is it expensive?  I've tried to write my
;metafunctions efficiently.  If this rule proves too expensive, we
;could introduce a new function, neq, for inequality.  But that seems
;unfortunate...

(defthm meta-rule-to-show-not-equal
  (implies (syntax-ev (hyp-for-show-not-equal-from-mfc term mfc state) a)
           (equal (syntax-ev term a)
                  (syntax-ev (show-not-equal-from-mfc term mfc state) a)))
  :otf-flg t
  :rule-classes ((:meta :trigger-fns (equal)
                        :backchain-limit-lst 0 ;just in case...
                        ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable
                       hyp-for-show-not-equal-from-type-alist-irrelevant
                       ))))

;wrapping this around the equal calls I want to rewrite keeps acl2
;from using substitution, etc. to prove the goal, thus making for a
;better test of my :meta rules.

(local (defstub foo-eric (x) t))


;;  Bbzo this is incomplete

;; ;bzo new stuff. remove skip--proofs.  replace unique-subbagps?

;; ;this all is written in an out-of-date style;compare it to the other stuff in this file

;; (defund show-subbagp2-from-type-alist (x y n type-alist whole-type-alist
;;                                          perform-syntax-test)
;;   (declare (type t x y type-alist whole-type-alist)
;;            (type (unsigned-byte 16) n)
;;            (type bit perform-syntax-test)
;;            (xargs :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
;;                   :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
;;   (if (and (equal 1 perform-syntax-test)
;;            (syntax-subbagp x y) ;we can tell just by looking at x and y that x is a subbagp of y
;;            )
;;       t
;;     (if (zp n) ;prevents loops and is okay because, given a type-alist with n things in it, we'll never need to use more than n facts to make a subbagp chain ; bzo should n be the len of the clause of type-alist?
;;         nil
;;       (if (consp type-alist)
;;           (let ((entry (car type-alist)))
;;             (if (consp entry)
;;                 (let ((fact (car entry)))
;;                   (or (and (consp fact)
;;                            (equal (car fact) 'subbagp)
;; ;                           (consp (cdr entry))
;;                            (ts-non-nil (cadr entry)) ;check that the type is either t or non-nil
;;  ;                          (consp (cdr fact))
;;   ;                         (consp (cddr fact))

;;                            (syntax-subbagp (cadr fact) x)
;;                            (syntax-subbagp (caddr fact) y)

;;                            (met ((hit smaller-cadr smaller-x) (syntax-remove-bag (cadr fact) x))
;;                                 (declare (ignore hit smaller-cadr))
;;                                 (met ((hit2 smaller-caddr smaller-y) (syntax-remove-bag (caddr fact) y))
;;                                      (declare (ignore hit2 smaller-caddr))
;;                                      (show-subbagp2-from-type-alist smaller-x
;;                                                                     smaller-y
;;                                                                     (+ -1 n) whole-type-alist whole-type-alist
;;                                                                     1)))
;;                                         ;we've found success; now we just need to check the arities of some stuff:
;;                            (equal nil (cdddr fact))
;;                            )
;;                       (show-subbagp2-from-type-alist x y n (cdr type-alist) whole-type-alist
;;                                                     0)))
;;               (show-subbagp2-from-type-alist x y n (cdr type-alist) whole-type-alist
;;                                             0)))
;;         nil))))

;;   bzo fix up make conjunction, etc.
;; (defund hyp-for-show-subbagp2-from-type-alist (x y n type-alist whole-type-alist
;;                                                  perform-syntax-test)
;;   (declare (type t x y type-alist whole-type-alist)
;;            (type (unsigned-byte 16) n)
;;            (type bit perform-syntax-test)
;;            (xargs :measure `((1 . ,(+ 1 (nfix n))) . ,(len type-alist))
;;                   :hints (("Goal" :do-not '(generalize eliminate-destructors)))))
;;   (if (and (equal 1 perform-syntax-test)
;;            (syntax-subbagp x y) ;we can tell just by looking at x and y that x is a subbagp of y
;;            )
;;       ''t
;;     (if (zp n) ;prevents loops and is okay because, given a type-alist with n things in it, we'll never need to use more than n facts to make a subbagp chain ; bzo should n be the len of the clause of type-alist?
;;         nil
;;       (if (consp type-alist)
;;           (let ((entry (car type-alist)))
;;             (if (consp entry)
;;                 (let ((fact (car entry)))
;;                   (or (and (consp fact)
;;                            (equal (car fact) 'subbagp)
;;    ;                        (consp (cdr entry))
;;                            (ts-non-nil (cadr entry)) ;check that the type is either t or non-nil
;;     ;                       (consp (cdr fact))
;;      ;                      (consp (cddr fact))

;;                            (syntax-subbagp (cadr fact) x)
;;                            (syntax-subbagp (caddr fact) y)

;;                            (met ((hit smaller-cadr smaller-x) (syntax-remove-bag (cadr fact) x))
;;                                 (declare (ignore hit smaller-cadr))
;;                                 (met ((hit2 smaller-caddr smaller-y) (syntax-remove-bag (caddr fact) y))
;;                                      (declare (ignore hit2 smaller-caddr))
;;                                      (let ((hyp (hyp-for-show-subbagp2-from-type-alist
;;                                                  smaller-x
;;                                                  smaller-y
;;                                                  (+ -1 n) whole-type-alist whole-type-alist
;;                                                  1)))
;;                                        (if (and hyp
;;                                                 (equal nil (cdddr fact)))
;;                                            (make-conjunction fact hyp)
;;                                          nil))))

;;                            )
;;                       (hyp-for-show-subbagp2-from-type-alist x y n (cdr type-alist) whole-type-alist
;;                                                              0)))
;;               (hyp-for-show-subbagp2-from-type-alist x y n (cdr type-alist) whole-type-alist
;;                                                      0)))
;;         nil))))


;; (defthm show-subbagp2-from-type-alist-iff-hyp-for-show-subbagp2-from-type-alist
;;   (iff (show-subbagp2-from-type-alist x y n type-alist whole-type-alist flg)
;;        (hyp-for-show-subbagp2-from-type-alist x y n type-alist whole-type-alist flg))
;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;;            :in-theory (enable show-subbagp2-from-type-alist
;; ;                                     MAKE-CONJUNCTION
;;                                      hyp-for-show-subbagp2-from-type-alist
;;                                      ))))


;; ;; (defthm syntax-remove-bag-1-yields-a-subbagp
;; ;;   (subbagp (syntax-ev2 (val 1 (syntax-remove-bag-1 x y))
;; ;;                        a)
;; ;;            (syntax-ev2 y a))
;; ;;   :hints (("Goal" :in-theory (enable syntax-remove-bag-1))))

;; ;; (defthm syntax-remove-1-yields-a-subbagp
;; ;;   (subbagp (SYNTAX-EV2 (VAL 1 (SYNTAX-REMOVE-1 b Y)) A)
;; ;;            (syntax-ev2 y a))
;; ;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;;            :in-theory (enable syntax-remove-1))))

;; ;; (defthm syntax-remove-bag-yields-a-subbagp
;; ;;   (subbagp (syntax-ev2 (val 2 (syntax-remove-bag x y)) a)
;; ;;            (syntax-ev2 y a))
;; ;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;;            :in-theory (enable syntax-remove-bag syntax-remove-bag-1))))

;; ;; (defthm show-subbagp2-from-type-alist-works-right
;; ;;   (implies
;; ;;    (and (syntax-ev2 (hyp-for-show-subbagp2-from-type-alist x y n type-alist whole-type-alist flg) a)
;; ;;         (hyp-for-show-subbagp2-from-type-alist x y n type-alist whole-type-alist flg)
;; ;;         )
;; ;;    (subbagp (syntax-ev2 x a)
;; ;;             (syntax-ev2 y a)))
;; ;;   :hints (("Goal" :do-not '(generalize eliminate-destructors)
;; ;;            :in-theory (e/d (hyp-for-show-subbagp2-from-type-alist
;; ;;                             )
;; ;;                            ()))
;; ;; ))

;; (defun hyp-for-show-subbagp2-from-mfc (term mfc state)
;;   (declare (ignore state)
;;            (type t term mfc state)
;;            (xargs :guard (pseudo-termp term)))

;;   (if (and (consp term)
;;            (equal (car term) 'subbagp)
;;            (consp (cdr term))
;;            (consp (cddr term)))
;;       (let* ((type-alist (acl2::mfc-type-alist mfc))
;;              (len (usb16-fix (len type-alist)))
;;              )
;;         (bind-extra-vars-in-hyp (hyp-for-show-subbagp2-from-type-alist (cadr term) (caddr term) len type-alist type-alist 1) term))
;;     ''nil))


;; ;We could count the number of subbagp facts and use that count instead of (len clause).  This might be a good idea if we think cycles might exist among our subbagp facts.
;; ;We don't let LEN be more than 65535, so that it can be a fix-num in show-subbagp2-from-clause.
;; ;I can't imagine needing to make a chain of more than 65535 subbagp facts!
;; ;bzo what if we're rewriting a subbagp claim that's not the atom of a top-level literal?  then we're okay because or rules won't use that fact?
;; ;it would be nice to know that mfc-ts returns a valid type.
;; (defun show-subbagp2-from-mfc (term mfc state)
;;   (declare (ignore state)
;;            (xargs :guard (pseudo-termp term))
;;            (type t term mfc state))
;;   (if (and (consp term)  ;well-formedness checks, should always succeed
;; ;           (consp (cdr term))
;;  ;          (consp (cddr term))
;;            )
;;       (let* ((type-alist (acl2::mfc-type-alist mfc))
;;              (len (usb16-fix (len type-alist)))
;;              )
;;         (if (and (show-subbagp2-from-type-alist (cadr term) (caddr term) len type-alist type-alist 1)
;;                  (equal (car term) 'subbagp) ;well-formedness check, should always succeed)
;;                  )
;;             term ;''t Bbzo put this back
;;           term))
;;     term))




;; ;I never got around to proving this
;; ;add the SYNP treatment to this!  see the other rules in this file
;; (defthm meta-rule-to-show-subbagp2
;;    (implies (syntax-ev (hyp-for-show-subbagp2-from-mfc term mfc state) alist)
;;             (equal (syntax-ev term alist)
;;                    (syntax-ev (show-subbagp2-from-mfc term mfc state) alist)))
;;    :otf-flg t
;;    :rule-classes ((:meta :trigger-fns (subbagp)
;;                          :backchain-limit-lst 0 ;just in case...
;;                          ))
;;    :hints (("Goal" :do-not-induct t
;;             :in-theory (enable TYPE-REASONING-ONLY)
;;             :expand ((:free (x) (hide x)))
;;             :do-not '(generalize eliminate-destructors))))

;; ;If hyp is non-nil and check is also non-nil, then make a conjunction of fact and hyp.
;; (defun conjoin-fact-to-hyp-given-check (fact hyp check)
;;   (if (and hyp check)
;;       (make-conjunction fact hyp)))

;bzo where should this go?
(defthm find-index-of-cdr
  (implies (bag::unique key-names)
           (equal (list::find-index key (cdr key-names))
                  (if (list::memberp key (cdr key-names))
                      (+ -1 (list::find-index key key-names))
                    (len (cdr key-names)))))
  :hints (("Goal" :induct t
           :in-theory (enable list::find-index)
           :do-not '(generalize eliminate-destructors))))

(defthmd member-to-memberp
  (iff (acl2::member a x)
       (list::memberp a x))
  :hints (("goal" :in-theory (enable acl2::member list::memberp))))

(local (in-theory (enable member-to-memberp)))

;eventually, move the any-subbagp meta rule below to a different book?

#|
(defun implies-if (a term)
  (declare (type t a term))
  (if a t term))
|#

;trying disabled...
(defund meta-subbagp (list1 list2)
  (declare (type t list1 list2))
  (subbagp list1 list2))

;trying disabled...
(defund meta-memberp (x list)
  (declare (type t x list))
  (memberp x list))

;We expect TERM to be of the form (memberp x y).  If not, we do nothing.
;If so, we call syntax-memberp.  If that function returns t, that means we can show
;syntactically that X is a memberp of Y.  If that function returns nil, we don't know whether
;X is a memberp of Y; in this case, we must return something equivalent to TERM,
;so we return TERM itself !
(defun syntax-memberp-wrapper (term)
  (declare (type t term)
           (xargs :guard (pseudo-termp term)))
  (if (not (and (equal 3 (len term))
                (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                    (equal (car term) 'acl2::member-equal))))
      term
    (if (syntax-memberp-fn nil (cadr term) (caddr term))
        ''t
      term
      )))

(defthm syntax-memberp-implies-memberp
  (implies (syntax-memberp x y)
           (memberp (evaluator-for-memberp-cons-and-append x a)
                    (evaluator-for-memberp-cons-and-append y a)))
  :hints (("Goal" :in-theory (enable memberp)))
  :rule-classes (:rewrite :forward-chaining))


(defthm syntactic-membership-meta-rule
  (iff (evaluator-for-memberp-cons-and-append term a)
       (evaluator-for-memberp-cons-and-append (syntax-memberp-wrapper term) a))
  :hints (("Goal" :in-theory (enable  syntax-memberp-irrelevant)
           :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (acl2::member list::memberp))))

(defund subbagp-pair (x1 x2 list1 list2)
  (declare (type t x1 x2 list1 list2))
  (or (and (subbagp x1 list1)
           (subbagp x2 list2))
      (and (subbagp x1 list2)
           (subbagp x2 list1))))



;; jcd - changed so that it list::fixes its result
;like remove-1, but this returns (mv hit result), where hit indicates whether anything was actually removed.
(defun run-remove-1 (a x)
  (declare (type t a x))
  (if (consp x)
      (if (equal a (car x))
          (mv t (list::fix (cdr x))) ;we removed (car x)
          (met ((hit result) (run-remove-1 a (cdr x)))
               (mv hit (cons (car x) result))))
      (mv nil nil)))

(defthm v1-run-remove-1
  (equal (val 1 (run-remove-1 a x))
         (remove-1 a x)))

(defthm v0-run-remove-1
  (equal (val 0 (run-remove-1 a x))
         (memberp a x)))

(defthm not-v0-no-change-syntax-remove-1
  (implies (not (v0 (syntax-remove-1 elem term)))
           (equal (v1 (syntax-remove-1 elem term))
                      term))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn))))

(defthm booleanp-of-mv-nth-0-of-syntax-remove-bag-1
  (booleanp (val 0 (syntax-remove-bag-1 term1 term2)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable syntax-remove-bag-1-fn))))

(defthm not-v0-no-change-syntax-remove-bag-1
  (implies (not (v0 (syntax-remove-bag-1 x y)))
           (equal (v1 (syntax-remove-bag-1 x y))
                      y))
  :hints (("goal" :in-theory (enable syntax-remove-bag-1-fn))))

(defthm pseudo-termp-of-v1-of-syntax-remove-bag-1
  (implies (and (pseudo-termp term1)
                (pseudo-termp term2))
           (pseudo-termp (val 1 (syntax-remove-bag-1 term1 term2)))))

(defthm pseudo-termp-of-v1-of-syntax-remove-1
  (implies (and (pseudo-termp term1)
                (pseudo-termp term2))
           (pseudo-termp (val 1 (syntax-remove-1 term1 term2))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn))))

(defthm unchanged-syntax-remove-bag
  (implies
   (not (v0 (syntax-remove-bag term1 term2)))
   (and
    (equal (v1 (syntax-remove-bag term1 term2))
           term1)
    (equal (v2 (syntax-remove-bag term1 term2))
           term2)))
  :hints (("goal" :in-theory (enable syntax-remove-bag-fn))))

(defthm pseudo-termp-quote
  (pseudo-termp (list 'quote anything)))

;(syntax-remove-bag '(cons 2 '(3 4)) '(cons 2 (cons 3 (cons 4 c))))
;(syntax-subbagp '(cons 2 '(3 4)) '(cons 2 (cons 3 (cons 4 c))))

;I think both parts of this had to be proved together
(defthm pseudo-termp-of-syntax-remove-bag
  (implies (and (pseudo-termp term1)
                (pseudo-termp term2))
           (and (pseudo-termp (val 1 (syntax-remove-bag term1 term2)))
                (pseudo-termp (val 2 (syntax-remove-bag term1 term2)))))
  :hints (("Goal" :induct t
           :in-theory (e/d (syntax-remove-bag-fn) (TRUE-LISTP PSEUDO-TERMP PSEUDO-TERM-listp)))))

#|
old version:
;Returns non-nil iff we can tell just by looking at list1 and list2 that list1 is a subbagp of list2.
;perhaps make this a separate :meta rule? <-- huh?
;We syntactically try to remove everything in list2 from list1.  If doing so removes everything from list1, then
;list1 must have been a subbagp of list2.
;This seems inefficient, since it can't fail before syntax-remove-bag has completely finished.

(defun syntax-subbagp (list1 list2)
  (declare (type t list1 list2))
  (met ((hit newlist2 newlist1) (syntax-remove-bag list2 list1))
       (declare (ignore newlist2))
       (and hit ;syntax-remove-bag did something
            (equal newlist1 '(quote nil)) ;syntax-remove-bag removed everything from newlist1
            )))
|#

(defthm pseudo-termp-syntax-subbagp-helper
  (implies
   (and
    (pseudo-termp term1)
    (pseudo-termp term2))
   (pseudo-termp (v1 (syntax-subbagp-helper term1 term2))))
  :hints (("goal" :in-theory (enable syntax-subbagp-helper-fn))))

(defthm booleanp-of-mv-nth-0-of-syntax-subbagp-helper
  (booleanp (val 0 (syntax-subbagp-helper x2 y2)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable syntax-subbagp-helper-fn))))

(defthm booleanp-of-syntax-subbagp
  (booleanp (syntax-subbagp x2 y2))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable syntax-subbagp-fn))))

;add guard?
(defund meta-remove-bag (x y)
  (remove-bag x y))

#|
;drop?
(defund meta-remove-1 (x list)
  (remove-1 x list))
|#

;remove this?
;add guard?
(defun any-subbagp (term list)
  (declare (type t term list))
  (if (consp list)
      (or (subbagp term (car list))
          (any-subbagp term (cdr list)))
    nil))





;add guard?
(defund hide-disjoint (x y)
  (disjoint x y))

(defthm hide-disjoint-forward
  (implies (disjoint x y)
           (hide-disjoint x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hide-disjoint))))


;add guard?
(defund hide-unique (list)
  (unique list))

(defthm hide-unique-forward
  (implies (unique x)
           (hide-unique x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hide-unique))))


;add guard?
(defund hide-subbagp (x y)
  (subbagp x y))

(defthm hide-subbagp-forward
  (implies (subbagp x y)
           (hide-subbagp x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hide-subbagp))))

(defthm hide-subbagp-z-z
  (hide-subbagp z z)
  :hints (("Goal" :in-theory (enable hide-subbagp))))

;add guard?
(defund hide-memberp (x y)
  (memberp x y))

(defthm hide-memberp-forward
  (implies (memberp x y)
           (hide-memberp x y))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable hide-memberp))))

;If syntax-remove-1 signals a hit, ELEM must have been found (and removed) in TERM.
(defthm syntax-remove-1-implements-memberp
  (implies (v0 (syntax-remove-1 elem term))
           (memberp (syntax-ev elem a) (syntax-ev term a)))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn)))
  :rule-classes (:rewrite :forward-chaining))

(defthm syntax-remove-bag-1-implements-subbagp
  (implies (and (v0 (syntax-remove-bag-1 list1 list2))
                (equal (v1 (syntax-remove-bag-1 list1 list2))
                       '(quote nil)))
           (subbagp (syntax-ev list2 a) (syntax-ev list1 a)))
  :rule-classes (:rewrite :forward-chaining))

;the new TERM returned by syntax-remove-1 represents a term which is a subbag
;of the original TERM.
(defthm v1-syntax-remove-1-subbagp
  (subbagp (syntax-ev (v1 (syntax-remove-1 x list1)) a)
           (syntax-ev list1 a))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-1-fn))))

(defthm v1-syntax-remove-bag-1-subbagp
  (subbagp (syntax-ev (v1 (syntax-remove-bag-1 x list1)) a)
           (syntax-ev list1 a)))

#|
(defthm syntax-remove-bag-1-not
  (implies (and (v0 (syntax-remove-bag-1 list1 list2))
                (not (syntax-ev (v1 (syntax-remove-bag-1 list1 list2)) alist)))
           (subbagp (syntax-ev list2 alist)
                    (syntax-ev list1 alist)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))
|#

(defthm v0-remove-1-subbagp
  (implies
   (v0 (syntax-remove-bag-1 list1 list2))
   (subbagp (syntax-ev list1 a) (syntax-ev list2 a)))
  :rule-classes (:rewrite :forward-chaining))

;think more about the proof of this?? how should we handle remove-1 and
;append?  If syntax-remove-1 signals a hit, then the new term it returns
;represents a bag which is a permutation of the bag resulting from the removal
;of ELEM from the bag represented by TERM.

(defthm v1-syntax-remove-1-perm-remove-1
  (implies (v0 (syntax-remove-1 elem term))
           (perm (syntax-ev (v1 (syntax-remove-1 elem term)) a)
                 (remove-1 (syntax-ev elem a) (syntax-ev term a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;remove-1
                            syntax-remove-1-fn
                            REMOVE-1-APPEND
                            ;APPEND-OF-REMOVE-1-TWO
                            PERM-CONS-REDUCTION
                            ;APPEND-OF-REMOVE-1-TWO
                            )
                           (APPEND-REMOVE-1-REDUCTION
                            PERM-OF-REMOVE-1-ONE
                            ;PERM-CONSP-REMOVE-1 ;bzo looped! when mv-nth was enabled.
                            ;PERM-OF-REMOVE-1-ONE
                            ;PERM-OF-CONS
                            ;PERM-OF-CONS-MEMBERP-CASE
                            ;PERM-COMMUTATIVE
                            )))))


(defthm v1-syntax-remove-bag-1-perm-remove-bag
  (implies (v0 (syntax-remove-bag-1 list1 list2))
           (perm (syntax-ev (v1 (syntax-remove-bag-1 list1 list2)) a)
                 (remove-bag (syntax-ev list1 a) (syntax-ev list2 a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors))))

;theorem we are interested in
(defthm syntax-remove-bag-1-subbagp-append
  (implies (and (v0 (syntax-remove-bag-1 x list2))
                (subbagp (syntax-ev (v1 (syntax-remove-bag-1 x list2)) a)
                         (syntax-ev y a)))
           (subbagp (syntax-ev list2 a)
                    (append (syntax-ev x a)
                            (syntax-ev y a)))))


;make local?
(defthmd not-v1-syntax-remove-1
  (implies (and (v0 (syntax-remove-1 x list2))
                (not (syntax-ev (v1 (syntax-remove-1 x list2)) a)))
           (not (consp (remove-1 (syntax-ev x a) (syntax-ev list2 a)))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn)))
  :rule-classes (:rewrite :forward-chaining))


(defthm syntax-remove-bag-adds-no-elements
  (implies (memberp elem (syntax-ev (val 2 (syntax-remove-bag term1 term2)) a))
           (memberp elem (syntax-ev term2 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn))))





;we don't really use this?  maybe someday...
(defund syntax-count (elem term)
  (declare (type t elem term)
           (xargs :guard (pseudo-termp term))
           )
  (if (consp term)
      (if (and (equal (car term) 'binary-append) ;; '(binary-append arg1 arg2)
;               (consp (cdr term))
 ;              (consp (cddr term))
               (null  (cdddr term)))
          (+ (syntax-count elem (cadr term))
             (syntax-count elem (caddr term)))
        (if (and (equal (car term) 'cons) ;; '(cons arg1 arg2)
;                 (consp (cdr term))
 ;                (consp (cddr term))
                 (null  (cdddr term)))
            (if (equal (cadr term) elem)
                (+ 1 (syntax-count elem (caddr term)))
              (syntax-count elem (caddr term)))
          0))
    0))

(defthm syntax-count-of-non-consp
  (implies (not (consp term1))
           (equal (syntax-count elem term1) 0))
 :hints (("Goal" :in-theory (enable syntax-count))))


(defthm count-in-SYNTAX-REMOVE-1-linear
  (<= (COUNT ELEM (SYNTAX-EV (VAL 1 (SYNTAX-REMOVE-1 x Y)) a))
      (COUNT ELEM (SYNTAX-EV Y a)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-1-fn))))

(defthm count-in-SYNTAX-REMOVE-bag-1-linear
  (>= (COUNT ELEM (SYNTAX-EV (VAL 1 (SYNTAX-REMOVE-bag-1 x Y)) a))
      (- (COUNT ELEM (SYNTAX-EV Y a))
         (COUNT ELEM (SYNTAX-EV x a))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable SYNTAX-REMOVE-bag-1-fn))))

(defthm booleanp-of-VAL-of-SYNTAX-REMOVE-1
  (booleanp (VAL 0 (SYNTAX-REMOVE-1 ELEM TERM)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-1-fn))))

(defthm count-of-syntax-remove-1
  (equal (count (syntax-ev x a)
                (syntax-ev (val 1 (syntax-remove-1 x y)) a))
         (if (syntax-memberp x y)
             (+ -1 (count (syntax-ev x a)
                          (syntax-ev y a)))
           (count (syntax-ev x a)
                  (syntax-ev y a))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn)
           :do-not '(generalize eliminate-destructors))))

(defthm count-of-syntax-remove-1-better
  (equal (count elem (syntax-ev (val 1 (syntax-remove-1 x y)) a))
         (if (equal elem (syntax-ev x a))
             (if (syntax-memberp x y)
                 (+ -1 (count (syntax-ev x a)
                              (syntax-ev y a)))
               (count (syntax-ev x a)
                      (syntax-ev y a)))
           (count elem (syntax-ev y a))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn)
           :do-not '(generalize eliminate-destructors))))

(defthm count-in-syntax-remove-bag-linear
  (>= (count elem (syntax-ev (val 2 (syntax-remove-bag x y)) a))
     (- (count elem (syntax-ev y a))
        (count elem (syntax-ev x a))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn))))

;trying
(local (in-theory (disable SYNTAX-REMOVE-BAG-1-FN SYNTAX-MEMBERP-FN)))

(defthm memberp-of-syntax-remove-bag-one
  (implies (memberp elem (remove-bag (syntax-ev x a) (syntax-ev y a)))
           (memberp elem (syntax-ev (val 2 (syntax-remove-bag x y)) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn memberp))))

(defthm syntax-intersection-is-nil-when-syntax-remove-bag-does-nothing
  (implies (not (val 0 (syntax-remove-bag term1 term2)))
           (equal (syntax-intersection term1 term2)
                  ''nil))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct t
           :expand ((SYNTAX-INTERSECTION TERM1 TERM2))
           :in-theory (e/d (syntax-remove-bag-fn
                              ;syntax-remove-bag-1-fn
                              syntax-intersection-fn
                              ) (syntax-remove-bag-1-fn
                                 SYNTAX-MEMBERP-FN
                                 )))))


(defthm kingoftown
  (implies (not (syntax-memberp elem term))
           (not (syntax-memberp elem (val 1 (syntax-remove-bag-1 other-term term)))))
  :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-BAG-1-FN SYNTAX-MEMBERP-FN))))

(defthm kingoftown2
  (IMPLIES
   (NOT (SYNTAX-MEMBERP ELEM TERM))
   (NOT
    (SYNTAX-MEMBERP ELEM
                       (VAL 1
                                  (SYNTAX-REMOVE-1 OTHER-TERM TERM)))))
  :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-1-fn
                                     SYNTAX-REMOVE-BAG-1-FN SYNTAX-MEMBERP-FN))))

(defthm smith-blah
  (IMPLIES (NOT (SYNTAX-MEMBERP elem term))
           (NOT (SYNTAX-MEMBERP elem (VAL 2 (SYNTAX-REMOVE-BAG other-term term)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable SYNTAX-REMOVE-BAG-fn
                              SYNTAX-MEMBERP-fn))))


#|

;really want the -alt form?
(defthm not-syntax-memberp-means-not-in-syntactic-intersection
  (implies (not (syntax-memberp x y))
           (not (syntax-memberp x (syntax-intersection y other-term))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-intersection syntax-memberp))))
|#


(in-theory (disable SYNTAX-MEMBERP-FN))

(defthm hack-eric
  (implies (and (val 0 (syntax-remove-bag-1 other-term y))
                (not (syntax-memberp x y))
                )
           (not (syntax-memberp x other-term)))
  :hints (("Goal" :in-theory (enable syntax-memberp-fn SYNTAX-REMOVE-BAG-1-FN)
           :do-not '(generalize eliminate-destructors))))


(defthm not-syntax-memberp-means-not-syntax-memberp-of-syntax-remove-1
  (implies (not (syntax-memberp x y))
           (not (syntax-memberp x (val 1 (syntax-remove-1 elem y)))))
  :hints (("Goal" :in-theory (enable syntax-remove-1-fn syntax-memberp-fn))))


#|
;could show that syntactic-intersection is a syntactic subset of each arg?
(defthm not-syntax-memberp-means-not-in-syntactic-intersection-alt
  (implies (not (syntax-memberp x y))
           (not (syntax-memberp x (syntax-intersection other-term y))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (syntax-intersection syntax-memberp
                              )
                           (poopsmith
                            (:induction  syntax-memberp))))))

|#


;bzo change names!
(defthm syntax-remove-bag-cannot-increase-count-one
  (equal (< (count elem (syntax-ev term1 a))
            (count elem (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)))
         nil)
 :hints (("Goal" :in-theory (enable syntax-remove-bag-fn))))

(defthm syntax-remove-bag-1-cannot-increase-count
  (equal (< (count elem (syntax-ev term2 a))
            (count elem (syntax-ev (val 1 (syntax-remove-bag-1 term1 term2)) a)))
         nil))

(defthm syntax-remove-bag-cannot-increase-count-two
  (equal (< (count elem (syntax-ev term2 a))
            (count elem (syntax-ev (val 2 (syntax-remove-bag term1 term2)) a)))
         nil)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn))))


(defthm bubs
  (<= (count elem (syntax-ev (val 2 (syntax-remove-bag (val 1 (syntax-remove-bag term1 term2)) term3)) a))
      (count elem (syntax-ev term3 a)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (disable syntax-remove-bag-cannot-increase-count-two)
           :use (:instance syntax-remove-bag-cannot-increase-count-two (term1 (val 1 (syntax-remove-bag term1 term2))) (term2 term3)))))

(defthm checkinemail
  (<= (count (syntax-ev elem a)
             (syntax-ev (syntax-intersection term1 term2) a))
      (count (syntax-ev elem a)
             (syntax-ev term1 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-intersection-fn))))

(defthm syntax-remove-bag-does-the-right-thing-helper
  (equal (- (count elem (syntax-ev term1 a))
            (count elem (syntax-ev term2 a)))
         (- (count elem (syntax-ev (v1 (syntax-remove-bag term1 term2)) a))
            (count elem (syntax-ev (v2 (syntax-remove-bag term1 term2)) a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (syntax-remove-bag-fn)
                           (v1-syntax-remove-1-perm-remove-1
                            ;for efficiency:
                            SYNTAX-REMOVE-BAG-1-FN
                            MEMBERP-OF-SYNTAX-REMOVE-BAG-ONE
                            COUNT-WHEN-NON-MEMBER
                            COUNT-IN-SYNTAX-REMOVE-BAG-LINEAR
                            )))))

(defthm not-syntax-memberp-means-syntax-remove-1-does-nothing
  (implies (not (syntax-memberp elem term))
           (equal (val 1 (syntax-remove-1 elem term))
                  term)))


(in-theory (disable SYNTAX-REMOVE-BAG-1-fn SYNTAX-MEMBERP-fn))

(in-theory (disable SUBBAGP-OF-REMOVE-1-FROM-SUBBAGP)) ;why needed?

;bzo make equal
(defthm syntax-remove-bag-does-the-right-thing
  (implies (subbagp (syntax-ev term1 alist) (syntax-ev term2 alist))
           (subbagp (syntax-ev (v1 (syntax-remove-bag term1 term2)) alist)
                    (syntax-ev (v2 (syntax-remove-bag term1 term2)) alist)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag; subbagp
                              ))))



    (implies (and (v0 (syntax-remove-bag list1 list2))
                  (equal (syntax-ev
                          (v2 (syntax-remove-bag list1 list2)) alist)
                         nil)
                  )
             (subbagp (syntax-ev list2 alist) (syntax-ev list1 alist)))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;             :induct (SYNTAX-REMOVE-BAG LIST1 LIST2)
 ;            :do-not-induct t
             :in-theory (e/d (SUBBAGP-CONS-TO-SUBBAGP-REMOVE-1
                              syntax-remove-bag
                              not-v1-syntax-remove-1)
                             (
                              (:REWRITE SUBBAGP-OF-CONS)
                              SUBBAGP-OF-REMOVE-1-BOTH
                              ))))

(local
  (defthm syntax-subbagp-implements-subbagp-syntax-ev-nil
    (implies (and (v0 (syntax-remove-bag list1 list2))
                  (equal (syntax-ev (v2 (syntax-remove-bag list1 list2)) alist)
                         nil)
                  )
             (subbagp (syntax-ev list2 alist) (syntax-ev list1 alist)))
    :hints (("Goal" :do-not '(generalize eliminate-destructors)
;             :induct (SYNTAX-REMOVE-BAG LIST1 LIST2)
 ;            :do-not-induct t
             :in-theory (e/d (SUBBAGP-CONS-TO-SUBBAGP-REMOVE-1
                              syntax-remove-bag
                              not-v1-syntax-remove-1)
                             (
                              (:REWRITE SUBBAGP-OF-CONS)
                              SUBBAGP-OF-REMOVE-1-BOTH
                              )))
            ))

  )

|#



(defthm *trigger*-syntax-ev-syntax-subbagp
  (implies (and (unique list2)
                (meta-subbagp list1 list2)
                )
           (unique list1))
  :hints (("Goal" :in-theory (enable meta-subbagp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;--------------------- SUBBAGP-PAIR --------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;A main lemma...
;To show disjointness of x1 and x2, we can find two other bags, list1 and list2, which we know are disjoint and
;which we can tell (syntactcally) are supersets of x1 and x2 (either x1 is a subset of list1 and x2 is a subset of
;list2, or vice versa).
(defthm *trigger*-subbagp-pair-disjoint
  (implies (and (disjoint list1 list2) ;list1 and list2 are free variables
                (subbagp-pair x1 x2 list1 list2))
           (disjoint x1 x2))
  :hints (("goal" :in-theory (enable subbagp-pair))))


(defthm v1-syntax-remove-bag-1-implication-lemma
  (implies (and (v0 (syntax-remove-bag-1 u y))
                (subbagp (syntax-ev v a)
                         (syntax-ev (v1 (syntax-remove-bag-1 u y)) a))
                (equal (v1 (syntax-remove-bag v (v1 (syntax-remove-bag-1 u y))))
                       ''nil))
           (subbagp (append (syntax-ev u a)
                            (syntax-ev v a))
                    (syntax-ev y a))))


(defthm v2-subbagp-remove-bag
  (implies (and (v0 (syntax-remove-bag x list))
                (equal (v1 (syntax-remove-bag x list))
                       ''nil))
           (perm (syntax-ev (v2 (syntax-remove-bag x list)) a)
                 (remove-bag (syntax-ev x a) (syntax-ev list a))))
  :hints (("Goal" :in-theory (enable syntax-remove-bag-fn))))

(defthm syntax-memberp-quoted-implies-memberp
  (implies (syntax-memberp (list 'quote elem) term)
           (memberp elem (syntax-ev term a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable SYNTAX-MEMBERP-fn))))

(defthm subbagp-when-cdr-is-non-consp
  (implies (and (not (consp (cdr x)))
                (consp x) ;move to conclusion?
                )
           (equal (subbagp x y)
                  (memberp (car x) y))))

;key lemma for subgoal 2 of syntax-unique-subbagps-implies-unique-subbagps
(defthm v1-syntax-remove-bag-implication
  (implies (and (v0 (syntax-remove-bag x y))
                (equal (v1 (syntax-remove-bag x y))
                       '(quote nil)))
           (subbagp (syntax-ev x a)
                    (syntax-ev y a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag-fn))))




;disable stuff like this?
(defthm v2-syntax-remove-bag-implication-lemma
  (implies
   (and
    (subbagp (syntax-ev x a) (syntax-ev list a))
    (subbagp (syntax-ev y a) (syntax-ev (v2 (syntax-remove-bag x list)) a))
    (perm (syntax-ev (v2 (syntax-remove-bag x list)) a)
          (remove-bag (syntax-ev x a) (syntax-ev list a)))
    )
   (subbagp (syntax-ev y a)
            (remove-bag (syntax-ev x a)
                        (syntax-ev list a)))))

(defthm v2-syntax-remove-bag-implication
  (implies
   (and
    (v0 (syntax-remove-bag x list))
    (equal (v1 (syntax-remove-bag x list))
           ''nil)
    (v0 (syntax-remove-bag y (v2 (syntax-remove-bag x list))))
    (equal (v1 (syntax-remove-bag y (v2 (syntax-remove-bag x list))))
           ''nil)
    )
   (subbagp (syntax-ev y a)
           (remove-bag (syntax-ev x a)
                        (syntax-ev list a))))
  :hints (("Goal'" :in-theory (disable v1-syntax-remove-bag-implication
                                       v2-subbagp-remove-bag)
           :use ((:instance v1-syntax-remove-bag-implication (y list))
                 (:instance v1-syntax-remove-bag-implication (x y)
                            (y (v2 (syntax-remove-bag x list))))
                 (:instance v2-subbagp-remove-bag)
                 ))))

;this is the key lemma for the meta rule
(defthm syntax-unique-subbagps-implies-unique-subbagps
  (implies (syntax-unique-subbagps x y list)
           (unique-subbagps (syntax-ev x a)
                            (syntax-ev y a)
                            (syntax-ev list a)))
  :hints (("Goal" :in-theory (enable syntax-unique-subbagps-fn
                                     unique-subbagps))))

(defun syntax-unique-subbagps-wrapper (term)
  (declare (type t term)
           (xargs :guard (pseudo-termp term))
           )
  (if (and (consp term)
           (equal (car term) 'unique-subbagps) ;; (unique-subbagps x y list)
           (consp (cdr term))
           (consp (cddr term))
           (consp (cdddr term))
           (null  (cddddr term)))
      (let ((x (cadr term))
            (y (caddr term))
            (list (cadddr term)))
        (let ((hit (syntax-unique-subbagps-fn nil x y list)))
          (if hit
              `(quote t)
            term)))
    term))

;is this no longer used?
(defthm *meta*-syntax-ev-syntax-unique-subbagps
  (equal (syntax-ev term a)
         (syntax-ev (syntax-unique-subbagps-wrapper term) a))
  :rule-classes ((:meta :trigger-fns (unique-subbagps)))
  :hints (("goal" :in-theory (enable syntax-unique-subbagps-irrelevant))))

;If list is unique and is big enough to contain both x and y, then x and y must be disjoint.
(defthm *trigger*-unique-subbagps-implies-disjointness
  (implies (and (unique list) ;list is a free variable
                (unique-subbagps x y list))
           (disjoint x y))
  :hints (("goal" :in-theory (enable unique-subbagps remove-bag disjoint)
           :do-not '(generalize eliminate-destructors))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;-------------------------- MEMBERP ------------------------
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
(defthm syntax-memberp-implements-memberp
  (implies (syntax-memberp x list)
           (memberp (syntax-ev x alist) (syntax-ev list alist))))

(defun syntax-memberp-wrapper (term)
  (declare (type t term))
  (if (and (consp term)
           (equal (car term) 'meta-memberp) ;; (meta-memberp x list)
;           (consp (cdr term))
        ;   (consp (cddr term))
           (null  (cdddr term)))
      (let ((x (cadr term))
            (list (caddr term)))
        (let ((hit (syntax-memberp x list)))
          (if hit
              '(quote t)
            term)))
    term))

;replace this with eric's rule?
(defthm *meta*-syntax-ev-syntax-memberp
  (equal (syntax-ev term alist)
         (syntax-ev (syntax-memberp-wrapper term) alist))
  :rule-classes ((:meta :trigger-fns (meta-memberp)))
  :hints (("Goal" :in-theory (enable meta-memberp))))

|#

#|
(defthmd non-memberp-eric
  (implies (and (not (memberp a y)) ;y is a free variable
                (subbagp x y))
           (equal (memberp a x)
                  nil)))


;bzo ti of REMOVE-BAG-OVER-REMOVE-1 and REMOVE-1-OF-REMOVE-BAG
;bzo REMOVE-BAG-REMOVE-1 and REMOVE-BAG-OVER-REMOVE-1 !

#|
PUTBACK
(defthm v2-syntax-remove-bag-is-remove-bag
   (implies (and (unique (syntax-ev list a))
                 (true-listp (syntax-ev list a))
                 (v0 (syntax-remove-bag x list))
                 (equal (v1 (syntax-remove-bag x list))
                        ''nil))
            (equal (syntax-ev (v2 (syntax-remove-bag x list)) a)
                   (remove-bag (syntax-ev x a) (syntax-ev list a))))
   :hints (("Goal" :in-theory (enable syntax-remove-bag))))
|#

;bzo it would be nice if this returned a simplified term even if the first arg didn't simplify to nil.
(defun syntax-meta-remove-bag-wrapper (term)
   (declare (type t term)
            (xargs :guard (pseudo-termp term)))
   (if (and (consp term)
            (equal (car term) 'meta-remove-bag)
;            (consp (cdr term))
 ;           (consp (cddr term))
            (null  (cdddr term)))
       (met ((hit v1 v2) (syntax-remove-bag-fn nil (cadr term) (caddr term)))
            (if (and hit
                     (equal v1 '(quote nil))
                     )
                ;bzo consider remove-bag here?
                ;`(meta-remove-bag ,v1 ,v2)
                v2
              term))
     term))

#|

(defthm hhelperh
  (implies t;(val 0 (syntax-remove-bag term1 term2))
           (perm (syntax-ev (val 1 (syntax-remove-bag term1 term2)) a)
                 (remove-bag (syntax-ev (syntax-intersection term1 term1) a)
                             (syntax-ev term1 a))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag syntax-intersection))))


   (PERM (REMOVE-BAG (SYNTAX-EV TERM3 a)
                     (SYNTAX-EV TERM5 a))
         (REMOVE-BAG (SYNTAX-EV (VAL 1 (SYNTAX-REMOVE-BAG TERM3 TERM5)) a)
                     (SYNTAX-EV (VAL 2 (SYNTAX-REMOVE-BAG TERM3 TERM5)) a)))

|#

(defthm *meta*-syntax-ev-meta-remove-bag-perm
   (perm (syntax-ev term a)
         (syntax-ev (syntax-meta-remove-bag-wrapper term) a))
   :hints (("goal" :in-theory (enable meta-remove-bag
                                      syntax-remove-bag-irrelevant)))
   :rule-classes ((:meta :trigger-fns (meta-remove-bag))))

;trying a change where this handles remove-1 instead of meta-remove-1
(defun syntax-remove-1-wrapper (term)
   (declare (type t term)
            (xargs :guard (pseudo-termp term)))
   (if (and (consp term)
            (equal (car term) 'remove-1) ;(equal (car term) 'meta-remove-1)
;            (consp (cdr term))
 ;           (consp (cddr term))
            (null  (cdddr term)) ;why?
            )
       (met ((hit v1) (syntax-remove-1-fn nil (cadr term) (caddr term)))
            (if hit ;if we succeeded, then
                v1 ;return the resulting term
              term ;else, do nothing
              ))
     term))

#|
(defthm *meta*-syntax-ev-meta-remove-1-perm
  (perm (syntax-ev term a)
        (syntax-ev (syntax-meta-remove-1-wrapper term) a))
  :hints (("goal" :in-theory (enable meta-remove-1)))
  :rule-classes ((:meta :trigger-fns (meta-remove-1))))
 |#

(defthm *meta*-syntax-ev-remove-1-perm
  (perm (syntax-ev term a)
        (syntax-ev (syntax-remove-1-wrapper term) a))
  :hints (("goal" :in-theory (enable remove-1
                                     SYNTAX-MEMBERP-irrelevant
                                     syntax-remove-1-irrelevant)))
  :rule-classes ((:meta :trigger-fns (remove-1))))




(defun which-subbagp (x list1 list2 key)
  (declare (type t x list1 list2 key)
           (xargs :guard (and (pseudo-termp x)
                              (pseudo-termp list1)
                              (pseudo-termp list2)
                              (pseudo-termp key))))
  (or (and (syntax-subbagp-fn nil x list1)
           `((,key . (quote t))))
      (and (syntax-subbagp-fn nil x list2)
           `((,key . (quote nil))))))

(defthm perm-free-substitution
  (implies (and (perm x y)
                (bind-free (which-subbagp x list1 list2 'in1) (in1))
                (meta-subbagp x (if in1 list1 list2))
                (equal in2 (not in1))
                )
           (equal (perm list1 list2)
                  (perm (replace-perm in1 x y list1)
                        (replace-perm in2 x y list2))))
  :hints (("Goal" :in-theory (enable meta-subbagp meta-remove-bag))))

#|
;bzo wrong value on (common-elements '(cons b nil) '(cons a (cons b nil)))?
;should we just write a function for the syntactic intersection of two terms, instead of calling syntax-remove-bag?
(defun common-elements (term1 term2)
  (declare (type t term1 term2))
  (met ((hit xterm1 xterm2) (syntax-remove-bag term1 term2))
       (declare (ignore xterm2))
       (if (not hit)
           (mv nil nil)
         (met ((hit xterm1 sub) (syntax-remove-bag xterm1 term1))
              (declare (ignore xterm1))
              (mv
               hit ;should this be t?  what if xterm1 is nil?
               sub)))))

(defun bind-common-elements (term1 term2 key)
  (declare (type t term1 term2 key))
  (met ((hit common) (common-elements term1 term2))
       (if (not hit) nil
         `((,key . ,common)))))


;cancel common stuff from both sides of a perm.
;bzo consider doing the same for a subbagp and a remove-bag?
(defthm perm-common-elimination
  (implies (and (bind-free (bind-common-elements list1 list2 'x) (x))
                (meta-subbagp x list1)
                (meta-subbagp x list2))
           (equal (perm list1 list2)
                  (perm (meta-remove-bag x list1)
                        (meta-remove-bag x list2))))
  :hints (("Goal" :in-theory (enable meta-subbagp;bzo why did I have to enable this?
                                     meta-remove-bag))))
|#

;   (in-theory (disable perm-consp-remove-1))

;; I don't know how expensive these rules are in practice.
;; For now, I disable them until needed.

(in-theory
 (disable
  perm-free-substitution
;  perm-common-elimination
  ))

;; Nonetheless, perm-common-elimination should be used in
;; place of such hack rules as these ..

(in-theory
 (disable
;; jcd- removed this  perm-cons-x-y-z
;; jcd- removed this  perm-append-x-y-z
  ;perm-append-y-z-a
  perm-append-x-a-y-append-a-z
  ))

;; This comment is probably not entirely correct:
;; I think I know more about congruence based rewriting now.  I don't
;; think we need the meta rules stated above to do effective perm
;; reasoning.
;;
;; I think proving congruence and associative rules for append/cons/
;; etc should be enough .. we are close even now. I'm not sure how
;; destructors factor in (remove-1, remove-bag, etc), but I bet there
;; is a good strategy somewhere.
;;
;; So, in the future we may want to transition to rules of this form
;; to do perm reasoning:

;;
;; Try to clean up the perm mess a bit ..
;;

(in-theory
 (disable
;  perm-not-consp-nil
 ; perm-remove-bag-x-x
;  perm-append
  perm-cons-append
  perm-append-remove-1
;  perm-remove-1
 ; perm-remove-bag
  subbagp-perm-append-remove-bag
  perm-cons-reduction
  perm-nil-y
;  perm-remove-bag-2
;;jcd- removed this  perm-consp-remove-1
  perm-subbagp-subbagp
  remove-1-cons
  ))


;;
;; Some meta trigger functions we need to keep around
;;

(in-theory
 (disable
;  meta-remove-bag
 ;meta-remove-1
  ))

;returns the list of all BLAH such that mfc contains a literal of the form (not (memberp x BLAH)).
;doesn't allow BLAH to be Z, though.
;a hyp of the form (not (memberp x lst)) will appear negated in the clause as (memberp x lst)
;bzo this should use the type-alist, not the clause
(defun get-irrel-list-from-clause (x z clause)
  (declare (type t x clause)
;           (xargs :guard (pseudo-termp term))
           )
  (if (not (consp clause))
      nil
    (let ((literal (car clause)))
      (if (and (consp literal)
               (or (equal (car literal) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                   (equal (car literal) 'acl2::member-equal))
               (consp (cdr literal))
               (equal x (cadr literal))
               (consp (cddr literal))
               (not (equal z (caddr literal))) ;skip this case...
               )
          (cons (caddr literal) (get-irrel-list-from-clause x z (cdr clause)))
        (get-irrel-list-from-clause x z (cdr clause))))))


;pass in x?  have a case to handle constants like the meta rule above does?
;write this more efficiently?  bzo make this more efficient can we avoid some
;consing by adding a passing a flag which indicates whether the recursive
;calls changed anything?  bzo don't depend on append nest being associated?

(defun simplify-cons-and-append-nest-given-irrelevant-lists (nest irrel-list)
  (declare (type t nest irrel-list))
  (if (not (equal 3 (len nest))) ;calls to cons and binary-append have length 3
      ;we've hit a leaf; check whether it is something in the irrelevant list.
      (if (memberp nest irrel-list)
          ''nil
        nest)
    (if (equal (car nest) 'cons)
        (list 'cons (cadr nest) (simplify-cons-and-append-nest-given-irrelevant-lists (caddr nest) irrel-list))
      (if (equal (car nest) 'binary-append)
       ;We don't have to recur on (cadr nest) because we know it won't be an append or a cons, because of how
       ;nests of those functions get normalized?
          (if (memberp (cadr nest) irrel-list) ;we're appending something irrelevant, so drop it
              (simplify-cons-and-append-nest-given-irrelevant-lists (caddr nest) irrel-list)
            (list 'binary-append (cadr nest)
                  (simplify-cons-and-append-nest-given-irrelevant-lists (caddr nest) irrel-list)))
       ;We've found something that is neither a cons nor an append.
        (if (memberp nest irrel-list)
            ''nil
          nest))
      )
    ))

(set-state-ok t)


(defun simplify-cons-and-append-nest (term mfc state)
  (declare (ignore state) (type t term mfc state))
  (if (not (and (equal 3 (len term))
                (or (equal (car term) 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                    (equal (car term) 'acl2::member-equal))))
      term
    (let ((irrel-list (get-irrel-list-from-clause (cadr term) (caddr term) (mfc-clause mfc))))
      (if (not (consp irrel-list))
          term
        (list 'list::memberp
              (cadr term)
              (simplify-cons-and-append-nest-given-irrelevant-lists (caddr term) irrel-list))))))

(defun make-not-memberp-claim (x term)
  (declare (type t x term))
  `(not (memberp ,x ,term)))

(defun hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists (x nest irrel-list)
  (declare (type t x nest irrel-list))
  (if (not (equal 3 (len nest))) ;calls to cons and binary-append have length 3
       ;we've hit a leaf:
      (if (memberp nest irrel-list)
          (make-not-memberp-claim x nest) ;we dropped nest
        ''nil ;no hyps necessary
        )
    (if (equal (car nest) 'cons)
        (hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists x (caddr nest) irrel-list)
      (if (equal (car nest) 'binary-append)
       ;We don't have to recur on (cadr nest) because we know it won't be an append or a cons, because of how
       ;nests of those functions get normalized?
          (if (memberp (cadr nest) irrel-list) ;we're appending something irrelevant, so drop it
              (list 'if (make-not-memberp-claim x (cadr nest))
                    (hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists x (caddr nest) irrel-list)
                    ''nil)
            (hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists x (caddr nest) irrel-list))
       ;We've found something that is neither a cons nor an append.
        (if (memberp nest irrel-list)
            (make-not-memberp-claim x nest) ;we dropped nest
          ''nil ;no hyps necessary
          )
        )
      )))


(defun hyp-fun-simplify-cons-and-append-nest (term mfc state)
  (declare (ignore state)  (type t term mfc state))
  (if (not (and (equal 3 (len term))
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
                (or (equal (car term) 'acl2::member-equal)
                    (equal (car term) 'list::memberp))))
      'nil
    (let ((irrel-list (get-irrel-list-from-clause (cadr term) (caddr term) (mfc-clause mfc))))
      (if (not (consp irrel-list))
          'nil
        (hyp-fun-simplify-cons-and-append-nest-given-irrelevant-lists (cadr term) (caddr term) irrel-list)))))

(defun syntax-subbagp-wrapper (term)
  (declare (type t term)
           (xargs :guard (pseudo-termp term))
           )
  (if (and (consp term)
           (equal (car term) 'meta-subbagp) ;; (meta-subbagp list1 list2)
;           (consp (cdr term))
        ;   (consp (cddr term))
           (null  (cdddr term)))
      (let ((list1 (cadr term))
            (list2 (caddr term)))
        (let ((hit (syntax-subbagp-fn nil list1 list2)))
          (if hit
              '(quote t)
            term)))
    term))


(defun syntax-subbagp-pair-wrapper (term)
  (declare (type t term)
           (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (equal (car term) 'subbagp-pair) ;; (subbagp-pair x1 x2 list1 list2)
;           (consp (cdr term))
        ;   (consp (cddr term))
         ;  (consp (cdddr term))
          ; (consp (cddddr term))
           (null  (cdddddr term)))
      (let ((x1    (cadr term))
            (x2    (caddr term))
            (list1 (cadddr term))
            (list2 (caddddr term)))
        (let ((hit (syntax-subbagp-pair-fn nil x1 x2 list1 list2)))
          (if hit
              `(quote t)
            term)))
    term))



;(my-syntax-subbagp '(cons a x) '(cons b (cons a x)))
;(my-syntax-subbagp '(cons a x) '(cons a x))

#|

;key lemma for *meta*-syntax-ev-syntax-subbagp
;bzo rename
 (defthm syntax-subbagp-implements-subbagp
   (implies (and (v0 (syntax-remove-bag list1 list2))
                 (equal (v2 (syntax-remove-bag list1 list2))
                        '(quote nil))
                 )
            (subbagp (syntax-ev list2 a) (syntax-ev list1 a)))
   :hints (("Goal" :in-theory (enable meta-subbagp)))))



|#

(defthm hhelper
  (implies (val 0 (syntax-subbagp-helper term1 term2))
           (perm (syntax-ev (val 1 (syntax-subbagp-helper term1 term2)) a)
                 (remove-bag (syntax-ev term1 a) (syntax-ev term2 a))))
  :hints (("Goal" :in-theory (enable syntax-subbagp-helper-fn))))

(defthm syntax-subbagp-helper-implements-subbagp
  (implies (v0 (syntax-subbagp-helper term1 term2))
           (subbagp (syntax-ev term1 a) (syntax-ev term2 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-subbagp-helper-fn
                              meta-subbagp)))
  :rule-classes (:rewrite :forward-chaining))

(defthm syntax-subbagp-implements-subbagp
  (implies (syntax-subbagp term1 term2)
           (subbagp (syntax-ev term1 a) (syntax-ev term2 a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (meta-subbagp syntax-subbagp-fn) (syntax-subbagp-helper-fn))))
  :rule-classes (:rewrite :forward-chaining))

;do we need this rule? previously, meta-subbagp was enabled (!), and so this rule probably didn't fire.
;yet we seem to have gotten by without it??
(defthm *meta*-syntax-ev-syntax-subbagp
  (equal (syntax-ev term a)
         (syntax-ev (syntax-subbagp-wrapper term) a))
  :rule-classes ((:meta :trigger-fns (meta-subbagp)))
  :hints (("Goal" :in-theory (enable syntax-subbagp-irrelevant meta-subbagp))))

(defthm syntax-subbagp-pair-implies-subbagp-pair-x
  (implies (syntax-subbagp-pair x1 x2 list1 list2)
           (subbagp-pair (syntax-ev x1 a)
                         (syntax-ev x2 a)
                         (syntax-ev list1 a)
                         (syntax-ev list2 a)))
  :hints (("Goal" :in-theory (enable subbagp-pair syntax-subbagp-pair-fn)))
  :rule-classes (:rewrite :forward-chaining))

(defthm *meta*-syntax-ev-subbagp-pair
  (equal (syntax-ev term a)
         (syntax-ev (syntax-subbagp-pair-wrapper term) a))
  :hints (("goal" :in-theory (enable SYNTAX-SUBBAGP-PAIR-irrelevant)))
  :rule-classes ((:meta :trigger-fns (subbagp-pair))))

;If we can tell syntactically that term1 and term2 have stuff in common,
;return an alist binding the name indicated by key to that stuff.  Otherwise,
;return nil.

(defun my-bind-common-elements (term1 term2 key)
  (declare (type t term1 term2 key)
           (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2)
                              (pseudo-termp key))))
  (let ((common (bag::syntax-intersection-fn nil term1 term2)))
    (if (equal common ''nil)
        nil
      `((,key . ,common)))))


;trying with this enabled...
;bzo consider replacing this with a :meta rule that calls syntax-remove-bag?
(defthm my-perm-common-elimination
  (implies (and (bind-free (my-bind-common-elements list1 list2 'x) (x))
                (bag::meta-subbagp x list1)
                (bag::meta-subbagp x list2))
           (equal (perm list1 list2)
                  (perm (bag::meta-remove-bag x list1)
                        (bag::meta-remove-bag x list2))))
  :hints (("Goal" :in-theory (enable bag::meta-subbagp       ;bzo why did I have to enable this?
                                     bag::meta-remove-bag))))


#|
(defun perm-cancel-metafunction (term)
  (declare (type t term))
  (if (and (consp term)
           (equal 'perm (car term))
           (consp (cdr term))
           (consp (cddr term))
           (null (cdddr term)))
      (met ((hit newarg1 newarg2) (syntax-remove-bag (cadr term) (caddr term)))
           (if hit
               `(perm ,newarg1 ,newarg2)
             term))
    term))

;expensive?
(defthm subbagp-other-way
  (implies (subbagp y x)
           (equal (subbagp x y)
                  (perm x y)))
  :hints (("Goal" :in-theory (enable subbagp perm))))


(defthm meta-perm-cancel
  (equal (syntax-ev term a)
         (syntax-ev (perm-cancel-metafunction term) a))
  :rule-classes ((:meta :trigger-fns (perm))))




|#

#|


(defthm SYNTAX-REMOVE-BAG-kills-all-of-term1-means-subbagp
  (IMPLIES (EQUAL (VAL 1 (SYNTAX-REMOVE-BAG TERM1 TERM2))
                  ''NIL)
           (subbagp (SYNTAX-EV TERM1 a)
                    (SYNTAX-EV TERM2 a)
                    ))
  :hints (("Goal" :in-theory (enable SYNTAX-REMOVE-BAG))))

(defthm syntax-remove-bag-kills-all-of-term1-means-subbagp
  (implies (equal (val 1 (syntax-remove-bag term1 term2))
                  ''nil)
           (mv-nth 0 (syntax-subbagp-helper term1 term2)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag syntax-subbagp-helper))))


|#

#|

(defthm REMOVE-1-car-remove-bag-under-perm
  (PERM
   (REMOVE-1 (CAR y) (REMOVE-BAG x y))
   (REMOVE-BAG x (CDR y))))

;sheesh.  do we really need a notion of syntactic perm?
(defthm not-syntax-memberp-means-not-in-syntactic-intersection-alt
  (equal (syntax-memberp elem (syntax-intersection x y))
         (syntax-memberp elem (syntax-intersection y x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-intersection syntax-memberp))))




(defthm subbagp-from-subbagp-of-append-1
  (implies (subbagp (append x y) z)
           (subbagp x z))
  :hints (("Goal" :in-theory (enable subbagp))))

(defthm subbagp-from-subbagp-of-append-two
  (implies (subbagp (append x y) z)
           (subbagp x z))
  :hints (("Goal" :use subbagp-from-subbagp-of-append-1
           :in-theory (disable subbagp-from-subbagp-of-append-1))))

(defthm syntax-remove-bag-does-the-right-thing
  (implies (subbagp (syntax-ev term1 a) (syntax-ev term2 a))
           (subbagp (syntax-ev (v1 (syntax-remove-bag term1 term2)) a)
                    (syntax-ev (v2 (syntax-remove-bag term1 term2)) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag;
                              ;subbagp
                              ))))


(defthm syntax-remove-bag-does-the-right-thing
  (equal (subbagp (syntax-ev term1 a) (syntax-ev term2 a))
         (subbagp (syntax-ev (v1 (syntax-remove-bag term1 term2)) a)
                  (syntax-ev (v2 (syntax-remove-bag term1 term2)) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag ;
;subbagp
                              ))))

(defthm syntax-remove-bag-does-the-right-thing-helper1
  (equal (count elem (syntax-ev (v1 (syntax-remove-bag term1 term2)) a))
         (- (count elem (syntax-ev term1 a))
            (min (syntax-count elem term1)
                 (syntax-count elem term2))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag))))


  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable syntax-remove-bag; subbagp
                              ))))





prove these about remove-bag-1
(defthm count-of-syntax-remove-bag-1
  (equal (count (syntax-ev x a)
                (syntax-ev (val 1 (syntax-remove-bag-1 x y)) a))
         (if (syntax-memberp x y)
             (+ -1 (count (syntax-ev x a)
                          (syntax-ev y a)))
           (count (syntax-ev x a)
                  (syntax-ev y a))))
  :hints (("Goal" :in-theory (enable syntax-remove-1)
           :do-not '(generalize eliminate-destructors))))

(defthm count-of-syntax-remove-1-better
  (equal (count elem (syntax-ev (val 1 (syntax-remove-1 x y)) a))
         (if (equal elem (syntax-ev x a))
             (if (syntax-memberp x y)
                 (+ -1 (count (syntax-ev x a)
                              (syntax-ev y a)))
               (count (syntax-ev x a)
                      (syntax-ev y a)))
           (count elem (syntax-ev y a))))
  :hints (("Goal" :in-theory (enable syntax-remove-1)
           :do-not '(generalize eliminate-destructors))))

to handle

(IMPLIES
  (AND (NOT (CONSP TERM1))
       (VAL 0 (SYNTAX-REMOVE-BAG-1 TERM1 TERM2)))
  (EQUAL (+ (COUNT ELEM (SYNTAX-EV TERM1 a))
            (COUNT ELEM
                   (SYNTAX-EV (VAL 1 (SYNTAX-REMOVE-BAG-1 TERM1 TERM2)) a)))
         (COUNT ELEM (SYNTAX-EV TERM2 a))))
|#



;odd proof?
;move some of this stuff?
(defthm syntax-memberp-implements-memberp
  (implies (syntax-memberp v x)
           (memberp (syntax-ev v a)
                    (syntax-ev x a)))
  :rule-classes (:rewrite :forward-chaining))

(defthm memberp-of-syntax-ev-helper
  (implies (and (syntax-memberp x blah)
                (subbagp (syntax-ev blah a) y))
           (memberp (syntax-ev x a) y))
  :hints (("Goal" :use (:instance syntax-memberp-implements-memberp (v x) (x blah) (a a))
           :in-theory (e/d ( non-memberp-eric) (syntax-memberp-implements-memberp)))))

(defun neq (x y)
  (not (equal x y)))

;Look through the clause for a (non-negated) literal of the form
;(memberp a BLAH) where BLAH syntactically contains b.
;or a (non-negated) literal of the form:
;(memberp b BLAH) where BLAH syntactically contains a.
;If such a literal is found, return it.  The (non-negated) presence of that literal in the clause
;essentially means that we have a hypotheses which is the negation of that literal, e.g., (not (memberp a BLAH)).
;where BLAH syntactically contains b. In this case, a and b can't be equal.
;If not such literal is found, return nil.

(defun member-symbol (x)
  (declare (type t x))
  (or (equal x 'list::memberp)
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced member by member-equal).]
      (equal x 'acl2::member-equal)))

;TERM has the form (equal a b)
(defun metafunction-to-rewrite-equal-to-nil (term mfc state)
  (declare (ignore state)
           (type t term mfc state)
           (xargs :guard (pseudo-termp term)
                  ))
  (if (and (consp term)
           (equal (car term) 'equal)
           (consp (cdr term))
           (consp (cddr term))
           (find-memberp-literal-that-shows-a-and-b-differ-fn
            nil (cadr term) (caddr term) (mfc-clause mfc))
           (null (cdddr term))
           )
      ''nil
    term))

(defun hyp-for-metafunction-to-rewrite-equal-to-nil (term mfc state)
  (declare (ignore state)
           (type t term mfc state)
           (xargs :guard (pseudo-termp term)
                  ))
  (if (and (consp term)
           (equal (car term) 'equal)
           (consp (cdr term))
           (consp (cddr term))
           (null (cdddr term))
           )
      `(not ,(find-memberp-literal-that-shows-a-and-b-differ-fn
              nil (cadr term) (caddr term) (mfc-clause mfc)))
    ''nil))

(local
 (defthm syntactic-membership-meta-rule-helper
   (implies (syntax-memberp x y)
            (memberp (ev3 x a)
                     (ev3 y a)))
   :rule-classes (:forward-chaining)
   :hints (("Goal" :in-theory (enable memberp
                                      syntax-memberp
                                      )))))

(local
 (defthm helper-bzo
   (implies (and (find-memberp-literal-that-shows-a-and-b-differ x y clause)
                 (not (ev3 (find-memberp-literal-that-shows-a-and-b-differ x y clause)
                           a)))
            (not (equal (ev3 x a) (ev3 y a))))
   :hints (("Goal" :in-theory (enable
                               find-memberp-literal-that-shows-a-and-b-differ
                               )
            :do-not '(generalize eliminate-destructors)))))

;Rewrite (equal a b) to nil when either the clause contains (not
;(memberp a BLAH)) and BLAH syntactically contains b.  or the clause
;contains (not (memberp b BLAH)) and BLAH syntactically contains a.

(defthm meta-rule-to-rewrite-equal-to-nil
  (implies (ev3 (hyp-for-metafunction-to-rewrite-equal-to-nil term mfc state) a)
           (equal (ev3 term a)
                  (ev3 (metafunction-to-rewrite-equal-to-nil term mfc state) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable
                       find-memberp-literal-that-shows-a-and-b-differ-irrelevant
                       )))
  :rule-classes ((:meta :trigger-fns (equal))))

;Looks for a negated literal (roughly, a hypothesis) of the form  (memberp a x))
;Returns the literal if it finds one.  Else, returns nil.
(defun find-negated-memberp-literal-in-clause (a x clause)
  (declare (type t a x clause))
  (if (consp clause)
      (let ((lit (car clause)))  ;testing whether lit is (not (memberp a x))
        (if (and (consp lit)
                 (equal 'not (car lit))
                 (consp (cdr lit)))
            (let ((inner-lit (cadr lit)))
              (if (and (consp inner-lit)
                       (member-symbol (car inner-lit))
                       (consp (cdr inner-lit))
                       (equal a (cadr inner-lit))
                       (consp (cddr inner-lit))
                       (equal x (caddr inner-lit))
;check arities?
                       )
                  inner-lit
                (find-negated-memberp-literal-in-clause a x (cdr clause))))
          (find-negated-memberp-literal-in-clause a x (cdr clause))))
    nil))

;Look through the clause for literals of the form:
;(memberp a BLAH)
;and
;(not (memberp b BLAH))
;or vice versa
;This function looks for the (memberp a BLAH) literal and then calls a helper function to find the
;(not (memberp b BLAH)) literal.
;This function returns a term representing the conjunction of the literals, or else nil.
;We choose to have the outer loop (this function, rather than the one it calls) look for literals of the form (memberp a BLAH) or (memberp b BLAH)
;instead of literals of the form (not (memberp b BLAH)) or (not (memberp a BLAH)) for two reasons:
;1. In the cases where this rule won't hit, it's cheaper to not strip off the enclosiing NOTs from the literals
;2. We expect memberp to appear less often in the clause than not-memberp, since not-memberp appears less often as a hyp .. do we??  bzo ask greve!
;what if a equals b?
(defun find-two-memberp-literals-that-tell-you-that-a-and-b-differ (a b clause whole-clause)
  (declare (type t a b clause whole-clause))
  (if (consp clause)
      (let ((lit (car clause)))
        (if (and (consp lit)
                 (member-symbol (car lit)) ;the fact (not (memberp a x)) appears un-negated in the clause
                 (consp (cdr lit)))
            (if (and (equal a (cadr lit))
                     (consp (cddr lit)) ;necessary?
                     )
                (let ((result (find-negated-memberp-literal-in-clause b (caddr lit) whole-clause)))
                  (if result
                      `(if (not ,lit) ; `(and (not ,lit) ,result)
                           ,result
                         'nil)
                    (find-two-memberp-literals-that-tell-you-that-a-and-b-differ a b (cdr clause) whole-clause)))
              (if (and (equal b (cadr lit))
                       (consp (cddr lit)) ;necessary?
                       )
                  (let ((result (find-negated-memberp-literal-in-clause a (caddr lit) whole-clause)))
                    (if result
                        `(if (not ,lit); `(and (not ,lit) ,result)
                             ,result
                           'nil)
                      (find-two-memberp-literals-that-tell-you-that-a-and-b-differ a b (cdr clause) whole-clause)))
                (find-two-memberp-literals-that-tell-you-that-a-and-b-differ a b (cdr clause) whole-clause)))
          (find-two-memberp-literals-that-tell-you-that-a-and-b-differ a b (cdr clause) whole-clause)))
    nil))

;TERM has the form (equal a b)
(defun metafunction-for-two-memberp-literals-blah (term mfc state)
  (declare (ignore state) (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'equal)
           (consp (cdr term))
           (consp (cddr term))
           (null (cdddr term))
           (find-two-memberp-literals-that-tell-you-that-a-and-b-differ (cadr term) (caddr term) (mfc-clause mfc) (mfc-clause mfc))
           )
      ''nil
    term))

(defun hyp-metafunction-for-two-memberp-literals-blah (term mfc state)
  (declare (ignore state) (type t term mfc state))
  (if (and (consp term)
           (equal (car term) 'equal)
           (consp (cdr term))
           (consp (cddr term))
           (null (cdddr term))
           )
      (let ((hyp (find-two-memberp-literals-that-tell-you-that-a-and-b-differ (cadr term) (caddr term) (mfc-clause mfc) (mfc-clause mfc))))
        (if hyp
            hyp
          ''nil))
    ''nil))

(local
 (defthm cons-iff
   (iff (cons a b) t)))

(local (defthm helper3
 (implies (and (ev3 (find-negated-memberp-literal-in-clause x list clause) a)
               (find-negated-memberp-literal-in-clause x list clause))
          (memberp (ev3 x a) (ev3 list a )))))


(local
 (defthm syntactic-membership-meta-rule-helper-2
   (implies (and (find-two-memberp-literals-that-tell-you-that-a-and-b-differ x y clause clause2)
                 (ev3 (find-two-memberp-literals-that-tell-you-that-a-and-b-differ x y clause clause2)
                      a))
            (not (equal (ev3 x a)
                        (ev3 y a))))
   :hints (("Goal" :do-not '(generalize eliminate-destructors)
            :in-theory (e/d (memberp) (;FIND-NEGATED-MEMBERP-LITERAL-IN-CLAUSE
                                              ))))))

; ; Greve almost considers this a special case.
(defthm meta-rule-for-two-memberp-literals
  (implies (ev3 (hyp-metafunction-for-two-memberp-literals-blah term mfc state) a)
           (equal (ev3 term a)
                  (ev3 (metafunction-for-two-memberp-literals-blah term mfc state) a)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)))
  :rule-classes ((:meta :trigger-fns (equal))))

#|
;too expensive?!
(defthm disjoint-singletons-means-not-equal
  (implies (disjoint (list a) (list b))
           (not (equal a b))))


;  Ones that could (at least in part) hijack the disjoint code:

;why does this work but not the disj version?
(defthm neq-test-3-foo
  (implies (unique (list a b c d e f))
           (equal (foo (equal b e))
                  (foo nil)))
  :hints (("Goal" :in-theory (disable UNIQUE-OF-CONS)))
;  :hints (("Goal" :in-theory (enable unique-of-cons)))
  )


;could this be failing because the disjoint claims gets rewritten when we are neither backchaining nor rewriting a top-level literal in the clause
(defthm neq-test-3-foo-disj
  (implies (unique (list a b c d e f))
           (equal (foo (disjoint (list b) (list e)))
                  (foo t)))
  :hints (("Goal" :in-theory (disable UNIQUE-OF-CONS
                                      DISJOINT-OF-CONS-TWO
                                      DISJOINT-OF-CONS-ONE
                                      DISJOINT-OF-SINGLETON-ONE
                                      DISJOINT-OF-SINGLETON-TWO)))
;  :hints (("Goal" :in-theory (enable unique-of-cons)))
  )


(defthm neq-test-3-foo-disj2
  (implies (unique (list a b c d e f))
           (equal (disjoint (list b) (list e))
                  t))
  :hints (("Goal" :in-theory (disable UNIQUE-OF-CONS
                                      DISJOINT-OF-CONS-TWO
                                      DISJOINT-OF-CONS-ONE
                                      DISJOINT-OF-SINGLETON-ONE
                                      DISJOINT-OF-SINGLETON-TWO)))
;  :hints (("Goal" :in-theory (enable unique-of-cons)))
  )

(defthm neq-test-4-foo
  (implies (disjoint (list a b c) (list d e f))
           (equal (foo (equal b e)) (foo nil))))

;bzo why can't we get this!? now we can!
;on the one hand, we'd like to tie the neq rules to the disjointness rules. on the other hands, disjointness claims about singletons really should be simplified away.
;maybe i need to figure out all the ways we can conclude disjoint and write similar rules for neq (or for (note equal)).
(defthm neq-test-5-foo-aux
  (implies (and (disjoint x (list b c d))
                (memberp a x))
           (equal (foo (disjoint (list a) (list b)))
                  (foo t)))
  :hints (("Goal" :in-theory (disable DISJOINT-OF-CONS-TWO
                                      DISJOINT-OF-SINGLETON-TWO
                                      DISJOINT-OF-SINGLETON-one))))


(defthm neq-test-5-foo
  (implies (and (disjoint x (list b c d))
                (memberp a x))
           (equal (foo (equal a b))
                  (foo nil)))
  :hints (("Goal" :in-theory (disable DISJOINT-OF-CONS-TWO

                                      DISJOINT-OF-SINGLETON-TWO
                                      DISJOINT-OF-SINGLETON-ONE))))




(defthm blah
  (implies (

  (not (equal a b))

;why doesn't hijacking the disjoint rule work for this?
(defthm neq-test-5-foo
  (implies (and (disjoint x (list b c d))
                (memberp a x))
           (equal (foo (equal a b)) (foo nil))))

(defthm neq-test-6
 (implies
  (and
    (unique (append x (list c d e f)))
    (memberp a x))
  (neq a d)))

(defthm neq-test-6-foo
  (implies (and (unique (append x (list c d e f)))
                (memberp a x))
           (equal (foo (neq a d)) (foo t))))

(defthm neq-test-7
  (implies
   (and
    (disjoint x y)
    (memberp a x)
    (memberp b y))
   (neq a b)))

(defthm neq-test-7-foo
  (implies (and (disjoint x y)
                (memberp a x)
                (memberp b y))
           (equal (foo (neq a b)) (foo t))))




In general:

  I would suggest: if neither a nor b appear as
an argument to member in the hypothesis,
wrap them in a list and pass them to the
disjoint computation.

  If one does appear as an argument to a member
in the hypothesis (memberp a x), try to establish the
disjointness of the other from the list argument of
member.
|#

;; THE DOUBLE CONTAINMENT PERM STRATEGY
;;
;; A related idea in the set theory library is the notion that, if you want to
;; prove that two sets are equal, you should just prove that they are mutual
;; subsets of one another.  (And, by extension of the pick a point strategy,
;; you should just prove that they have the same elements).
;;
;; We can come up with a similar strategy for perm.  In other words, if we want
;; to prove that two bags are perm, we should just show that they are mutual
;; subbags of one another.  We can then use our multiplicity strategy to reduce
;; the "perm" to a question of membership.
;;
;; In the set theory library, we have a double-containment rule that can be
;; relatively automatic, because we have hypotheses requiring x and y to be
;; sets.  In this case, we have no nice hypotheses that can guide the
;; application of this rule, so we just leave this disabled and expect you to
;; :use it when appropriate.

(defthmd perm-by-double-containment
  (equal (perm x y)
         (and (subbagp x y)
              (subbagp y x)))
  :hints(("Goal" :in-theory (enable perm))))


(in-theory (disable LIST::memberp-of-cons)) ;can introduce an if
(in-theory (disable remove-1-of-cons-both))
(in-theory (disable remove-1-of-non-consp))
(in-theory (disable subbagp-of-remove-1-implies-subbagp))

(in-theory (disable (:forward-chaining subbagp-disjoint))) ;trying...

(in-theory (disable ;; jcd - removed unique-if-perm-of-something-unique
                    subbagp-false-from-witness
                    non-unique-not-subbagp-of-unique))

(in-theory (disable disjoint-of-append-one
                    disjoint-of-append-two)) ;trying
(in-theory (disable subbagp-remove-bag-append)) ;trying
(in-theory (disable subbagp-remove-bag-subbagp-append)) ;trying
(in-theory (disable non-uniqueness-implications))
(in-theory (disable subbagp-disjoint
                    subbagp-disjoint-commute))
(in-theory (disable subbagp-not-disjoint))
(in-theory (disable subbagp-append-2))
(in-theory (disable subbagp-implies-subbagp-append-rec))
(in-theory (disable unique-of-cons))
(in-theory (disable disjoint-of-cons-one
                    disjoint-of-cons-two
                    unique-of-append
                    subbagp-implies-subbagp-append-car
                    unique-despite-remove-bag
;                    subbagp-uniqueness
                    subbagp-memberp-remove-1
                    subbagp-cdr-remove-1-rewrite
                    subbagp-remove-bag
                    subbagp-remove
                    subbagp-remove-1 ;leave enabled?
                    subbagp-of-non-consp-one ;??
                    subbagp-of-non-consp-two
                    subbagp-chaining
                    subbagp-cons ;improve this?
;                    unique-remove-1
                    unique-memberp-remove
                    subbagp-cons-car-memberp
                    not-memberp-implies-not-memberp-remove-1
                    memberp-false-from-disjointness
                    subbagp-implies-membership
                    remove-bag-adds-no-terms
                    LIST::memberp-of-append
                    memberp-subbagp
                    memberp-x-remove-x-implies-memberp-x-remove-1-y
                    memberp-of-remove-bag-means-memberp
                    memberp-of-remove-1
                    remove-bag-of-non-consp
                    memberp-car-when-disjoint
                    remove-bag-does-nothing
                    append-commutative-inside-perm
                    disjoint-cdr-from-disjoint
                    ))

;(in-theory (disable append-associative)) ;try

(defund any-subbagp (term list)
  (declare (type t term list))
  (if (consp list)
      (or (subbagp term (car list))
          (any-subbagp term (cdr list)))
    nil))

(defund flat (zlist)
  (if (consp zlist)
      (append (car zlist)
              (flat (cdr zlist)))
    nil))

(defthm true-listp-flat
  (true-listp (flat list))
  :hints (("Goal" :in-theory (enable flat))))

(defthm flat-append
  (equal (flat (append x y))
         (append (flat x) (flat y)))
  :hints (("goal" :in-theory (enable binary-append flat))))

(defthm flat-of-non-consp-cheap
  (implies (not (consp x))
           (equal (flat x)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable flat))))

(defthm flat-of-singleton
  (equal (flat (cons x nil))
         (list::fix x))
  :hints (("Goal" :in-theory (enable flat list::fix))))

(defthmd flat-of-cons
  (equal (flat (cons a x))
         (append a (flat x)))
  :hints (("Goal" :in-theory (enable flat))))

;could we just say that TERM is disjoint from (flat LIST) ?
(defund disjoint-list (term list)
  (declare (type t term list))
  (if (consp list)
      (and (disjoint term (car list))
           (disjoint-list term (cdr list)))
    t))

;disable?
;rename?
(defthm not-consp-disjoint-list
  (implies (not (consp list))
           (disjoint-list x list))
  :hints (("goal" :in-theory (enable disjoint-list flat))))

(defthm open-disjoint-list
  (and
   (equal (disjoint-list term (cons entry rest))
          (and (disjoint term entry)
               (disjoint-list term rest)))
   (equal (disjoint-list term nil) t))
  :hints (("Goal" :in-theory (enable disjoint-list))))

(defthm any-subbagp-implies-subbagp-flat
  (implies (any-subbagp term list)
           (subbagp term (flat list)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable flat any-subbagp))))

(defthm disjoint-list-implies-disjoint-flat
  (implies (disjoint-list term list)
           (disjoint term (flat list)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable flat))))

;bzo
(defthm memberp-implies-subbagp-flat
  (implies (memberp x xx)
           (subbagp x (flat xx)))
  :hints (("goal" :in-theory (enable memberp flat))))

;eric's version:
;rename
(defthm subbagp-append-reduction
  (implies (memberp sblk list)
           (equal (subbagp sblk (append x (flat list)))
                  t))
  :hints (("goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (memberp) (CONS-CAR-ONTO-REMOVE-1-OF-CDR ;why?
                                             )))))

;bzo
(defthm flat-perm
  (implies (perm x y)
           (equal (perm (flat x) (flat y))
                  t))
  :hints (("goal" :in-theory (enable perm memberp remove-1 flat))))

(defthm disjoint-list-reduction
  (equal (disjoint-list x list)
         (disjoint x (flat list)))
  :hints (("goal" :in-theory (enable disjoint-list flat))))


;bzo
(defthm flat-remove-1
  (implies (memberp x y)
           (perm (flat (remove-1 x y))
                 (remove-bag x (flat y))))
  :hints (("goal" :in-theory (enable LIST::memberp-of-cons remove-bag remove-1 flat)
           :induct (remove-1 x y))))

(defthm subbagp-flat-backchain
  (implies (subbagp f1 f2)
           (subbagp (flat f1) (flat f2)))
  :otf-flg t
  :hints (("goal" :do-not '(generalize eliminate-destructors)
;           :do-not-induct t
;           :induct (REMOVE-BAG F2 F1)
           :in-theory (e/d (subbagp
                            remove-bag flat)
                           (;SUBBAGP-OF-REMOVE-1-BOTH
                            SUBBAGP-CDR-REMOVE-1-REWRITE
                            ;SUBBAGP-APPEND-2
                            )))))

(defthm flat-remove-bag
  (implies (subbagp x y)
           (perm (flat (remove-bag x y))
                 (remove-bag (flat x) (flat y))))
  :hints (("Goal" :in-theory (enable flat remove-bag
                                     ))))

(defthmd disjoint-of-flat-helper
  (implies (memberp lst lst-of-lsts)
           (equal (disjoint (flat lst-of-lsts) lst)
                  (not (consp lst))
                  ))
  :hints (("Goal"
           :do-not '(generalize eliminate-destructors))))

(defthmd disjoint-of-flat-helper-2
  (implies (memberp lst lst-of-lsts)
           (equal (disjoint lst (flat lst-of-lsts))
                  (not (consp lst))
                  ))
  :hints (("Goal" :in-theory (disable disjoint-of-flat-helper)
           :use  disjoint-of-flat-helper
           :do-not '(generalize eliminate-destructors))))


;bzo name should mention flat
(defthmd subbagp-membership-fwd ;trying disabled..
  (implies (memberp x list1)
           (subbagp x (flat list1)))
  :rule-classes (:forward-chaining))



#|

(DEFTHM APPEND-of-flat-and-flat
  (EQUAL (APPEND (FLAT X) (FLAT Y))
         (FLAT (APPEND X Y)))
  :HINTS
  (("goal" :IN-THEORY (ENABLE BINARY-APPEND))))

(in-theory (disable flat-append))


|#

(defthm any-subbagp-subbagp
  (implies (and (any-subbagp pair list)
                (subbagp x pair))
           (any-subbagp x list))
  :hints (("goal" :in-theory (enable any-subbagp SUBBAGP-CHAINING))))

(defthm disjoint-list-append-reduction
  (equal (disjoint-list (append x y) list)
         (and (disjoint-list x list)
              (disjoint-list y list)))
  :hints (("goal" :in-theory (enable ;disjoint-of-append
;disjoint-list-reduction
                              ))))


;add flat to name
(defthmd memberp-not-disjoint-free
  (implies (and (memberp x list1)
                (consp x)
                (subbagp (flat list1) list2))
           (equal (disjoint x list2)
                  nil))
  :hints (("Goal" :use (:instance DISJOINT-OF-FLAT-HELPER-2 (lst x) (lst-of-lsts list1)))))


(defthm disjoint-from-disjoint-of-flat-one
  (implies (and (disjoint x (flat a))
                (memberp y a))
           (equal (disjoint x y)
                  t)))

(defthm disjoint-from-disjoint-of-flat-two
  (implies (and (disjoint y (flat a))
                (memberp x a))
           (equal (disjoint x y)
                  t)))

(defthm disjoint-from-disjoint-of-flat-three
  (implies (and (disjoint (flat a) x)
                (memberp y a))
           (equal (disjoint x y)
                  t)))

(defthm disjoint-from-disjoint-of-flat-four
  (implies (and (disjoint (flat a) y)
                (memberp x a))
           (equal (disjoint x y)
                  t)))

(defun syntax-deconsp (list)
  (declare (type t list))
  (if (and (consp list)
           (equal (car list) 'cons)
           (consp (cdr list))
           (consp (cddr list))
           (null  (cdddr list)))
      (mv t (cadr list) (caddr list))
    (mv nil nil nil)))

(defun syntax-subbagp-list-wrapper (term)
  (declare (type t term)
           (xargs :guard (pseudo-termp term)
                  ))
  (if (and (consp term)
           (equal (car term) 'any-subbagp)
           (consp (cdr term))
           (consp (cddr term))
           (null  (cdddr term))
           (syntax-subbagp-list-fn nil (cadr term) (caddr term)))
      '(quote t)
    term))

(defthm syntax-subbagp-implies-any-subbagp
  (implies (syntax-subbagp-list term1 term2)
           (any-subbagp (syntax-ev term1 a) (syntax-ev term2 a)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable syntax-subbagp-list any-subbagp))))

(defthm *meta*-subbagp-list
  (equal (syntax-ev term a)
         (syntax-ev (syntax-subbagp-list-wrapper term) a))
  :hints (("goal" :in-theory (enable syntax-subbagp-list-irrelevant)))
  :rule-classes ((:meta :trigger-fns (any-subbagp))))
