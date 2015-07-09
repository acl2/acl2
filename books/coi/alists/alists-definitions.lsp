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
;; alists-definitions.lisp
;; John D. Powell
;(in-package "ALIST")

;;
;; This file isolates alists definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the alists book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(defthm alist::use-equivp-id
  (alist::use-equivp domain x x))

; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
; (defthm assoc-eq-is-assoc
;   (equal (assoc-eq key list)
;          (assoc key list)))

(defthm assoc-equiv-rewrite-order
  (implies
   (syntaxp (acl2::good-rewrite-order y x))
   (equal (alist::assoc-equiv domain x y)
          (alist::assoc-equiv domain y x))))

(in-theory (disable ALIST::ASSOC-EQUIV-COMMUTE))

(defthm assoc-equiv-substitution
  (implies
   (and
    (alist::assoc-equiv d1 x y)
    (subsetp d2 d1))
   (alist::use-equiv :lhs x
                     :rhs y
                     :domain d2)))

(defthm assoc-use-cong
  (implies
   (and
    (equal domain (list a))
    (acl2::bind-contextp ((b1 (equal b2 (alist::use-ctx b1 :domain domain))))))
   (alist::cons-equiv (assoc a b1)
                      (assoc a b2))))

(defthm alist::use-equivp-self-characterization
  (implies
   (acl2::bind-contextp ((x (equal a (alist::use-ctx x :domain domain)))
                         (y (equal b (alist::use-ctx y :domain domain)))))
   (equal (alist::use-equivp domain x y)
          (alist::use-equivp domain a b))))

(defthm use-equiv-cons-not-member-reduction
  (implies
   (not (list::memberp (car a) domain))
   (alist::use-equiv :lhs (cons a list)
                     :rhs list
                     :domain domain)))

(defthm use-equiv-cons-normal-form
  (implies
   (and
    (syntaxp (acl2::<< (car b) (car a)))
    (not (equal (car a) (car b))))
   (alist::use-equiv :lhs (cons a (cons b x))
                     :rhs (cons b (cons a x)))))

(defthm use-equiv-append-normal-form
  (implies
   (and
    (syntaxp (acl2::<< y x))
    (bag::disjoint (alist::keys x) (alist::keys y)))
   (alist::use-equiv :lhs (append x y)
                     :rhs (append y x))))

;; ===========================================================================
;;
;; This was the easy property ..  dropping the first argument to
;; append will be tougher.
;;
;; ===========================================================================

(defthm use-equiv-append-reduction-2
  (implies
   (subsetp domain (alist::keys x))
   (alist::use-equiv :lhs (append x y)
                     :rhs x
                     :domain domain)))


;; ===========================================================================
;;
;; assoc-transparent: either the keys are disjoint or the bound values
;; are equal.
;;
;; ===========================================================================


(defun assoc-transparent (key value alist)
  (if (consp alist)
      (and (implies (equal key (caar alist)) (equal value (cdar alist)))
           (assoc-transparent key value (cdr alist)))
    t))

(defthm assoc-transparent-append
  (equal (assoc-transparent key value (append x y))
         (and (assoc-transparent key value x)
              (assoc-transparent key value y))))

(defthm assoc-transparent-implies-cons-equiv-assoc
  (implies
   (assoc-transparent key value x)
   (alist::cons-equiv (assoc key x)
                      (and (list::memberp key (alist::keys x)) (cons key value))))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthm assoc-transparent-implies-cons-equiv-assoc-2
  (implies
   (and
    (assoc-transparent key (cdr (assoc key x)) y)
    (list::memberp key (alist::keys y)))
   (alist::cons-equiv (assoc key x)
                      (and (list::memberp key (alist::keys x)) (assoc key y))))
  :hints (("Goal" :induct (assoc key y)
           :in-theory (enable alist::keys))))

(defthm assoc-transparent-non-memberp
  (implies
   (not (list::memberp key (alist::keys x)))
   (assoc-transparent key nil x))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthm use-equiv-cons-assoc-transparent-reduction
  (implies
   (and
    (assoc-transparent (car a) (cdr a) list)
    (list::memberp (car a) (alist::keys list)))
   (alist::use-equiv :lhs (cons a list)
                     :rhs list
                     :domain domain))
  :hints (("Goal" :in-theory (enable alist::keys))))

;; ===========================================================================
;;
;; unified-domain-binding: the alist is self-assoc-transparent.
;;
;; cross-domain-binding: the glue that combines two parts of a
;; unified-domain-binding.
;;
;; ===========================================================================


(defun unified-domain-binding (domain alist)
  (if (consp domain)
      (and (assoc-transparent (car domain) (cdr (assoc (car domain) alist)) alist)
           (unified-domain-binding (cdr domain) alist))
    t))

(defun cross-domain-binding (domain x y)
  (if (consp domain)
      (let ((key (car domain)))
        (and (implies (list::memberp key (alist::keys x))
                      (assoc-transparent key (cdr (assoc key x)) y))
             (cross-domain-binding (cdr domain) x y)))
    t))

(defthm disjoint-cross-domain-binding
  (implies
   (bag::disjoint (alist::keys x) (alist::keys y))
   (cross-domain-binding domain x y))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthm cross-domain-binding-replacement
  (implies
   (and
    (cross-domain-binding domain x y)
    (list::memberp key domain)
    (list::memberp key (alist::keys y)))
   (alist::cons-equiv (assoc key x)
                      (and (list::memberp key (alist::keys x)) (assoc key y)))))


(defthmd cross-domain-binding-cons
  (implies
   (and
    (consp x)
    (unified-domain-binding domain x))
   (equal (cross-domain-binding domain x y)
          (and (implies (list::memberp (caar x) domain)
                        (assoc-transparent (caar x) (cdar x) y))
               (cross-domain-binding domain (cdr x) y))))
  :hints (("Goal" :induct (cross-domain-binding domain x y)
           :in-theory (enable alist::keys))))

(defthmd cross-domain-binding-not-cons
  (implies
   (not (consp x))
   (cross-domain-binding domain x y))
  :hints (("Goal" :in-theory (enable alist::keys))))

(defthmd unified-domain-binding-cons
  (implies
   (consp x)
   (equal (unified-domain-binding domain x)
          (and (implies (list::memberp (caar x) domain)
                        (assoc-transparent (caar x) (cdar x) (cdr x)))
               (unified-domain-binding domain (cdr x)))))
  :hints (("Goal" :induct (unified-domain-binding domain x)
           :in-theory (enable alist::keys))))

(defthmd unified-domain-binding-non-cons
  (implies
   (not (consp x))
   (unified-domain-binding domain x)))

(defthm unified-domain-binding-append
  (equal (unified-domain-binding domain (append x y))
         (and (unified-domain-binding domain x)
              (unified-domain-binding domain y)
              (cross-domain-binding domain x y)))
  :hints (("Goal" :induct (append x y)
           :in-theory (enable append
                              unified-domain-binding-cons
                              unified-domain-binding-non-cons
                              cross-domain-binding-cons
                              cross-domain-binding-not-cons
                              ))))

(defthm use-equiv-append-reduction-1
  (implies
   (and
    (cross-domain-binding d1 x y)
    (subsetp domain d1)
    (subsetp domain (alist::keys y)))
   (alist::use-equiv :lhs (append x y)
                     :rhs y
                     :domain domain))
  :hints (("Goal" :in-theory (disable ASSOC-EQUIV-SUBSTITUTION)))
  :otf-flg t)

;; ===========================================================================
;;
;; unified-binding: the alist is self-consistent w/to unified-domain-bindings
;;
;; ===========================================================================

(defund unified-binding (alist)
  (unified-domain-binding (alist::keys alist) alist))

(defun equiv-domain-binding (domain x y)
  (and (cross-domain-binding domain x y)
       (cross-domain-binding domain y x)))

(defthm unified-domain-binding-subsetp
  (implies
   (and
    (unified-domain-binding y a)
    (subsetp x y))
   (unified-domain-binding x a)))

(defund clearkey (k x)
  (declare (xargs :guard (alistp x)))
  (if (consp x)
      (if (equal k (caar x))
          (clearkey k (cdr x))
        (cons (consfix (car x))
              (clearkey k (cdr x))))
    nil))

(defthm alistp-of-clearkey
  (alistp (clearkey k x))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-of-cons
  (equal (clearkey k (cons a x))
         (if (equal k (car a))
             (clearkey k x)
           (cons (consfix a) (clearkey k x))))
  :hints(("Goal" :in-theory (enable clearkey))))

; no theorem about car-of-clearkey, too hard to describe
; no theorem about cdr-of-clearkey, too hard to describe

(defthm len-of-clearkey-bound-tight
  (implies (memberp k (strip-cars x))
           (< (len (clearkey k x))
              (len x)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm len-of-clearkey-bound-tight-rewrite
  (implies (memberp k (strip-cars x))
           (equal (< (len (clearkey k x)) (len x))
                  t)))

(defthm len-of-clearkey-bound-weak
  (<= (len (clearkey k x))
      (len x))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm len-of-clearkey-bound-weak-rewrite
  (equal (< (len x) (len (clearkey k x)))
         nil))

;; no theorem about clearkey-of-firstn, too awkward to describe
;; no theorem about clearkey-of-nthcdr, too awkward to describe

(defthm clearkey-of-append
  (equal (clearkey k (append x y))
         (append (clearkey k x)
                 (clearkey k y)))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-reorder
  (equal (clearkey k1 (clearkey k2 r))
         (clearkey k2 (clearkey k1 r)))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-when-non-memberp
  (implies (not (memberp key (strip-cars x)))
           (equal (clearkey key x)
                  (alistfix x)))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-caar-when-unique
  (implies (and (consp x)
                (BAG::unique (strip-cars x)))
           (equal (clearkey (caar x) (cdr x))
                  (alistfix (cdr x)))))

(defthm strip-cars-of-clearkey
  (equal (strip-cars (clearkey k x))
         (BAG::remove-all k (strip-cars x)))
  :hints(("Goal" :in-theory (enable clearkey))))

(defthm clearkey-idempotent
  (equal (clearkey k (clearkey k r))
         (clearkey k r)))

(defthm not-memberp-of-strip-cdrs-of-clearkey
  (implies (not (memberp val (strip-cdrs x)))
           (not (memberp val (strip-cdrs (clearkey key x)))))
  :hints(("Goal" :in-theory (enable clearkey))))

;; bzo move to bags library
(defthm count-of-remove-all-diff
  (implies (not (equal a b))
           (equal (BAG::count a (BAG::remove-all b x))
                  (BAG::count a x)))
  :hints(("Goal" :in-theory (enable BAG::remove-all))))

(defund deshadow (x)
  (declare (xargs :guard (alistp x)
                  :measure (len x)))
  (if (consp x)
      (cons (consfix (car x))
            (deshadow (clearkey (caar x) (cdr x))))
    nil))

(defthm deshadow-type-1
  (implies (not (consp x))
           (equal (deshadow x) nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-type-2
  (implies (consp x)
           (consp (deshadow x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-of-non-consp
  (implies (not (consp x))
           (equal (deshadow x)
                  nil)))

(defthm consp-of-deshadow
  (equal (consp (deshadow x))
         (consp x)))

(defthm deshadow-of-cons
  (equal (deshadow (cons x y))
         (cons (consfix x)
               (deshadow (clearkey (car x) y))))
  :hints(("Goal" :in-theory (enable deshadow clearkey))))

(defthm car-of-deshadow
  (equal (car (deshadow x))
         (if (consp x)
             (consfix (car x))
           nil)))

;; no rules about cdr-of-deshadow, it is weird



(defthm len-of-deshadow-weak
  (<= (len (deshadow x))
      (len x))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm len-of-deshadow-weak-rewrite
  (equal (< (len x) (len (deshadow x)))
         nil))

;; Even though we will shortly prove deshadow-when-strip-cars-unique, we will
;; go ahead and prove both :linear rules below, so that we can backchain to
;; the unique of strip cars hypothesis when necessary.

(defthm len-of-deshadow-when-strip-cars-not-unique
  (implies (not (BAG::unique (strip-cars x)))
           (< (len (deshadow x))
              (len x)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm len-of-deshadow-when-strip-cars-unique
  (implies (BAG::unique (strip-cars x))
           (equal (len (deshadow x))
                  (len x)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm len-of-deshadow-decreases-rewrite
  (equal (< (len (deshadow x)) (len x))
         (not (BAG::unique (strip-cars x)))))
(defthm alistp-of-deshadow
  (alistp (deshadow x))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-of-clearkey
  (equal (deshadow (clearkey key x))
         (clearkey key (deshadow x)))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm unique-of-strip-cars-of-deshadow
  (BAG::unique (strip-cars (deshadow x)))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-when-strip-cars-unique
  (implies (BAG::unique (strip-cars x))
           (equal (deshadow x)
                  (alistfix x)))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm deshadow-idempotent
  (equal (deshadow (deshadow x))
         (deshadow x)))

(defthm memberp-of-strip-cars-of-deshadow
  (equal (memberp key (strip-cars (deshadow x)))
         (memberp key (strip-cars x)))
  :hints(("Goal" :in-theory (enable deshadow))))

(defthm count-of-strip-cars-of-deshadow
  (<= (BAG::count key (strip-cars (deshadow x)))
      (BAG::count key (strip-cars x)))
  :hints(("Goal" :in-theory (enable deshadow))))

;; There is probably an equivalent rule for strip-cdrs, but I haven't tried
;; to prove it yet.

(defthm not-memberp-of-strip-cdrs-of-deshadow
  (implies (not (memberp val (strip-cdrs x)))
           (equal (memberp val (strip-cdrs (deshadow x)))
                  nil))
  :hints(("Goal" :in-theory (enable deshadow))))

;; Interpreting Objects as Conses (consfix)
;;
;; We can think of a mapping between all ACL2 objects and conses, so that any
;; atom is mapped to (nil . nil) and any cons is mapped to itself.  The
;; function consfix applies this mapping for us, i.e., it interprets any ACL2
;; object as a cons.  Because this is how car and cdr interpret their
;; arguments, there are some very nice properties that we can prove about this
;; operation.

(defund consfix (x)
  (declare (type t x))
  (if (consp x)
      x
    (cons nil nil)))

(defthm consfix-when-non-consp
  (implies (not (consp x))
           (equal (consfix x)
                  (cons nil nil)))
  :hints(("Goal" :in-theory (enable consfix))))

(defthm consfix-when-consp
  (implies (consp x)
           (equal (consfix x)
                  x))
  :hints(("Goal" :in-theory (enable consfix))))

(defthm consfix-does-nothing
  (equal (equal x (consfix x))
         (consp x))
  :hints(("Goal" :in-theory (enable consfix))))

(defthm consfix-of-cons
  (equal (consfix (cons a b))
         (cons a b)))



;; Note (jcd): Do not add the following rules.  They are trivial consequences
;; of the congruence rules under cons-equiv below, so adding them is not
;; necessary.
;;
;; (defthm consfix-of-car
;;   (equal (car (consfix a))
;;          (car a)))
;;
;; (defthm consfix-of-cdr
;;   (equal (cdr (consfix a))
;;          (cdr a)))





;; The Cons Equivalence Relation (cons-equiv)
;;
;; Given that (with consfix) we can now think of any object as a cons, the next
;; natural step is to define an equivalence relation wherein objects are
;; considered to be equivalent when their interpretations as conses are the
;; same.

(defund cons-equiv (x y)
  (declare (type t x y))
  (equal (consfix x)
         (consfix y)))

(defthm consfix-in-cons-equiv
  (cons-equiv (consfix x)
              x)
  :hints(("Goal" :in-theory (enable cons-equiv))))

(defthm equal-of-consfixes
  (equal (equal (consfix x) (consfix y))
         (cons-equiv x y))
  :hints (("Goal" :in-theory (enable cons-equiv))))

;; Interpreting Objects as Alists (alistfix)
;;
;; An alist is a list of pairs.  Since we can now interpret any ACL2 object as
;; a pair using consfix, it is straightforward to interpet any ACL2 object as
;; an alist: any atom is interpreted as the empty alist, and any list is fixed
;; by pair-fixing each of its elements.
;;
;; An alternate definition that I considered was to simply interpret any
;; non-alistp object as the empty alist, and any alist as itself.  But, I think
;; the current approach gives us many nice rules.  In particular, our approach
;; allows alist-equiv to be a refinement of list::equiv, giving us a lot of
;; rewrite rules "for free" (e.g., the lengths are the same).  Other rules work
;; nicely (the keys are the same, the values are the same, etc.)  Finally, we
;; also get to provide very nice congruence rules, e.g., the cars of alist
;; interpretations are cons-equiv.

(defund alistfix (x)
  (declare (type t x))
  (if (consp x)
      (cons (consfix (car x))
            (alistfix (cdr x)))
    nil))

(defthm alistfix-type-consp
  (implies (consp x)
           (consp (alistfix x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable alistfix))))

(defthm alistfix-type-non-consp
  (implies (not (consp x))
           (equal (alistfix x)
                  nil))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable alistfix))))


;; Note (jcd): Do not add the following rule.  It is redundant with the defcong
;; below for alist-equiv over consp.
;;
;; (defthm consp-alistfix
;;   (equal (consp (alistfix x))
;;          (consp x)))


(defthm alistfix-when-non-consp
  (implies (not (consp alist))
           (equal (alistfix alist)
                  nil)))

(defthm alistfix-when-alist
  (implies (alistp x)
           (equal (alistfix x)
                  x))
  :hints(("Goal" :in-theory (enable alistfix))))

(defthm alistfix-does-nothing
  (equal (equal x (alistfix x))
         (alistp x))
  :hints(("Goal" :in-theory (enable alistfix))))

(defthm alistp-of-alistfix
  (alistp (alistfix x))
  :hints(("Goal" :in-theory (enable alistfix))))



(defthm alistfix-of-cons
  (equal (alistfix (cons a x))
         (cons (consfix a) (alistfix x)))
  :hints(("Goal" :in-theory (enable alistfix))))

(defthm car-of-alistfix
  (equal (car (alistfix a))
         (if (consp a)
             (consfix (car a))
           nil)))

(defthm cdr-of-alistfix
  (equal (cdr (alistfix a))
         (alistfix (cdr a))))

;; Note (jcd): Do not add the following rule.  It is trivial using the
;; congruence rule of alist-equiv for len, along with alistfix-in-alist-equiv.
;;
;; (defthm len-of-alistfix
;;   (equal (len (alistfix a))
;;          (len a)))

(defthm alistfix-of-append
  (equal (alistfix (append x y))
         (append (alistfix x)
                 (alistfix y)))
  :hints(("Goal" :in-theory (enable append))))

(defthm alistfix-of-firstn
  (equal (alistfix (list::firstn n x))
         (list::firstn n (alistfix x)))
  :hints(("Goal" :in-theory (enable list::firstn))))

(defthm alistfix-of-nthcdr
  (equal (alistfix (nthcdr n x))
         (nthcdr n (alistfix x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

;; The Alist Equivalence Relation
;;
;; Given that (with alistfix) we can now think of any object as an alist, the
;; next natural step is to define an equivalence relation wherein objects are
;; considered to be equivalent when their interpretations as alists are the
;; same.
;;
;; IMPORTANT: You might think that alists should be considered to be equivalent
;; whenever "forall a, (assoc a x) = (assoc a y)."  Although equivalent alists
;; will satisfy this property, the converse is NOT true!  For example, if x and
;; y satisfy this property but x has shadowed pairs and y does not, then x and
;; y will not be considered equivalent under alist-equiv!
;;
;; Instead, you should think of alist-equiv as a "structural" relation that
;; essentially is comparing the interpretation of x and y as lists of pairs.
;; But understand that no a priori judgement is made as to how those lists of
;; pairs will be used, and we do not assume that shadowed pairs are irrelevant.

(defund alist-equiv (a b)
  (equal (alistfix a)
         (alistfix b)))

(defthm alistfix-in-alist-equiv
  (alist-equiv (alistfix a)
               a)
  :hints(("Goal" :in-theory (enable alist-equiv))))

(defthm alist-equiv-cons-cases
  (equal (alist-equiv x (cons y z))
         (and (consp x)
              (cons-equiv y (car x))
              (alist-equiv z (cdr x))))
  :hints(("Goal" :in-theory (enable alist-equiv))))

(defthm equal-of-alistfixes
  (equal (equal (alistfix x) (alistfix y))
         (alist-equiv x y))
  :hints(("Goal" :in-theory (enable alist-equiv))))

;; Interpreting Objects as Conses (consfix)
;;
;; We can think of a mapping between all ACL2 objects and conses, so that any
;; atom is mapped to (nil . nil) and any cons is mapped to itself.  The
;; function consfix applies this mapping for us, i.e., it interprets any ACL2
;; object as a cons.  Because this is how car and cdr interpret their
;; arguments, there are some very nice properties that we can prove about this
;; operation.

(defund consfix (x)
  (declare (type t x))
  (if (consp x)
      x
    (cons nil nil)))

(defthm consfix-when-non-consp
  (implies (not (consp x))
           (equal (consfix x)
                  (cons nil nil)))
  :hints(("Goal" :in-theory (enable consfix))))

(defthm consfix-when-consp
  (implies (consp x)
           (equal (consfix x)
                  x))
  :hints(("Goal" :in-theory (enable consfix))))

(defthm consfix-does-nothing
  (equal (equal x (consfix x))
         (consp x))
  :hints(("Goal" :in-theory (enable consfix))))

(defthm consfix-of-cons
  (equal (consfix (cons a b))
         (cons a b)))



;; Note (jcd): Do not add the following rules.  They are trivial consequences
;; of the congruence rules under cons-equiv below, so adding them is not
;; necessary.
;;
;; (defthm consfix-of-car
;;   (equal (car (consfix a))
;;          (car a)))
;;
;; (defthm consfix-of-cdr
;;   (equal (cdr (consfix a))
;;          (cdr a)))





;; The Cons Equivalence Relation (cons-equiv)
;;
;; Given that (with consfix) we can now think of any object as a cons, the next
;; natural step is to define an equivalence relation wherein objects are
;; considered to be equivalent when their interpretations as conses are the
;; same.

(defund cons-equiv (x y)
  (declare (type t x y))
  (equal (consfix x)
         (consfix y)))

(defthm cons-equiv-cases-fwd
  (implies
   (and (equal (car x) (car y))
        (equal (cdr x) (cdr y)))
   (cons-equiv x y))
  :hints (("Goal" :in-theory (enable cons-equiv)))
  :rule-classes (:forward-chaining))

(defthm not-cons-equiv-cases-fwd-1
  (implies
   (not (equal (car x) (car y)))
   (not (cons-equiv x y)))
  :hints (("Goal" :in-theory (enable cons-equiv)))
  :rule-classes (:forward-chaining))

(defthm not-cons-equiv-cases-fwd-2
  (implies
   (not (equal (cdr x) (cdr y)))
   (not (cons-equiv x y)))
  :hints (("Goal" :in-theory (enable cons-equiv)))
  :rule-classes (:forward-chaining))

(defthm cons-equiv-fwd
  (implies
   (cons-equiv x y)
   (and (equal (car x) (car y))
        (equal (cdr x) (cdr y))))
  :hints (("Goal" :in-theory (enable cons-equiv)))
  :rule-classes (:forward-chaining))

(defthm cons-equiv-cons-reduction-1
  (equal (cons-equiv (cons a b) c)
         (and (equal a (car c))
              (equal b (cdr c))))
  :hints (("Goal" :in-theory (enable cons-equiv))))

(defthm cons-equiv-cons-reduction-2
  (equal (cons-equiv a (cons b c))
         (and (equal (car a) b)
              (equal (cdr a) c)))
  :hints (("Goal" :in-theory (enable cons-equiv))))

(defthm consfix-in-cons-equiv
  (cons-equiv (consfix x)
              x)
  :hints(("Goal" :in-theory (enable cons-equiv))))

(defthm equal-of-consfixes
  (equal (equal (consfix x) (consfix y))
         (cons-equiv x y))
  :hints (("Goal" :in-theory (enable cons-equiv))))

(defun keys (alist)
  (declare (type t alist))
  (if (consp alist)
      (if (consp (car alist))
          (cons (caar alist)
                (keys (cdr alist)))
        (cons nil (keys (cdr alist))))
    nil))

#|
(defthm memberp-cons-keys
  (implies
   (consp alist)
   (memberp (caar alist) (keys alist))))

(defthm clrv-len-reduction
  (implies
   (memberp a (keys alist))
   (< (len (clrv a alist)) (len alist)))
  :rule-classes (:linear))

(defun element (a y)
  (if (consp y)
      (if (equal (car a) (caar y))
          (equal (cdr a) (cdar y))
        (element a (cdr y)))
    nil))

(defthm element-definition
  (equal (element a y)
         (and (memberp (car a) (keys y))
              (equal (cdr a) (cdr (getv (car a) y)))))
  :rule-classes (:definition))

(defthm element-implication
  (implies
   (element a y)
   (and (memberp (car a) (keys y))
        (equal (cdr a) (cdr (getv (car a) y)))))
  :rule-classes (:forward-chaining))

(defthm element-elements-implication
  (implies
   (and (memberp (car a) (keys y))
        (equal (cdr a) (cdr (getv (car a) y))))
   (element a y))
  :rule-classes (:forward-chaining))

(defthm not-element-elements-implication-1
  (implies
   (not (memberp (car a) (keys y)))
   (not (element a y)))
  :rule-classes (:forward-chaining))

(defthm not-element-elements-implication-2
  (implies
   (not (equal (cdr a) (cdr (getv (car a) y))))
   (not (element a y)))
  :rule-classes (:forward-chaining))

(defthm element-base
  (implies
   (not (consp x))
   (not (element a x)))
  :hints (("Goal" :in-theory (enable element))))

(defthm element-cons
  (equal (element a (cons x y))
         (if (equal (car a) (car x))
             (equal (cdr a) (cdr x))
           (element a y)))
  :hints (("Goal" :in-theory (enable element))))

(defthm element-append
  (equal (element a (append x y))
         (if (memberp (car a) (keys x))
             (element a x)
           (element a y)))
  :hints (("Goal" :induct (append x y)
           :in-theory (enable memberp append element))))

|#

(defthm assoc-append
  (equal (assoc a (append x y))
         (if (memberp a (keys x))
             (assoc a x)
           (assoc a y))))

(defthm keys-append
  (equal (keys (append x y))
         (append (keys x)
                 (keys y))))


;; pick-a-point

#|
(defthm consp-implies-memberp
  (implies
   (consp x)
   (memberp (caar x) (keys x))))
|#

(defun assoc-equiv (list x y)
  (if (consp list)
      (and (cons-equiv (assoc (car list) x)
                       (assoc (car list) y))
           (assoc-equiv (cdr list) x y))
    t))

(defthmd assoc-equiv-commute
  (equal (assoc-equiv list x y)
         (assoc-equiv list y x)))

(defthm assoc-equiv-commute-fwd
  (implies
   (assoc-equiv list x y)
   (assoc-equiv list y x))
  :hints (("Goal" :in-theory (enable assoc-equiv-commute))))

(defthm assoc-equiv-memberp
  (implies
   (and
    (memberp a list)
    (assoc-equiv list x y))
   (cons-equiv (assoc a x)
               (assoc a y)))
  :rule-classes (:forward-chaining))

(defthm assoc-equiv-subsetp-1
  (implies
   (and
    (subsetp a b)
    (assoc-equiv b x y))
   (assoc-equiv a x y))
  :rule-classes (:rewrite :forward-chaining))

(defthm assoc-equiv-subsetp-2
  (implies
   (and
    (assoc-equiv b x y)
    (subsetp a b))
   (assoc-equiv a x y))
  :rule-classes (:rewrite :forward-chaining))

(defthm assoc-equiv-chaining-1
  (implies
   (and
    (assoc-equiv a w x)
    (assoc-equiv a x y))
   (assoc-equiv a w y))
  :rule-classes (:rewrite :forward-chaining))

(defthm assoc-equiv-chaining-2
  (implies
   (and
    (assoc-equiv a x y)
    (assoc-equiv a w x))
   (assoc-equiv a w y))
  :rule-classes (:rewrite :forward-chaining))

(defun subdomain (x y)
  (and (assoc-equiv (keys x) x y)
       (subsetp (keys x) (keys y))))

(defun keyquiv (x y)
  (and (list::setequiv (keys x) (keys y))
       (assoc-equiv (keys x) x y)
       (assoc-equiv (keys y) y x)))

(defthm assoc-non-memberp
  (implies
   (not (memberp a (keys alist)))
   (equal (assoc a alist) nil)))

(defthm car-assoc-memberp
  (implies
   (memberp a (keys alist))
   (equal (car (assoc a alist))
          a)))

(defthm keyquiv-cons-commute
  (implies
   (not (equal (car a) (car b)))
   (keyquiv (cons a (cons b x))
            (cons b (cons a x)))))

(defthm keyquiv-cons-crush
  (implies
   (equal (car a) (car b))
   (keyquiv (cons a (cons b x))
            (cons a x))))

(in-theory (disable keyquiv))

(defun setv (a v alist)
  (cons (cons a v) alist))

(defun getv (a alist)
  (cdr (assoc a alist)))

(defthm getv-over-setv
  (equal (getv a (setv b v r))
         (if (equal a b)
             v
           (getv a r))))

(defthm setv-over-setv
  (implies
   (not (equal a b))
   (keyquiv (setv a v (setv b w r))
            (setv b w (setv a v r)))))

(defthm setv-of-setv
  (keyquiv (setv a v (setv a w r))
           (setv a v r)))

(defthm setv-of-getv
  (implies
   (memberp a (keys r))
   (keyquiv (setv a (getv a r) r)
            r))
  :hints (("Goal" :in-theory (enable keyquiv))))

(defthm keys-setv
  (equal (keys (setv a v r))
         (cons a (keys r))))

(defun clr (key alist)
  (if (consp alist)
      (if (equal key (caar alist))
          (clr key (cdr alist))
        (cons (car alist)
              (clr key (cdr alist))))
    alist))

(defthm clr-append
  (equal (clr a (append x y))
         (append (clr a x) (clr a y))))

(defthm clr-clr-commute
  (equal (clr a (clr b x))
         (clr b (clr a x))))

(defthm keys-clr
  (equal (keys (clr key alist))
         (remove key (keys alist))))

(defthm assoc-clr
  (equal (assoc a (clr key x))
         (if (equal a key) nil
           (assoc a x))))

(in-theory (disable LIST::SETEQUIV-REMOVE-DEFINITION))

(defthm getv-clr
  (equal (getv a (clr key alist))
         (if (equal a key) nil
           (getv a alist))))

(defthm clr-over-setv
  (implies
   (not (equal a b))
   (keyquiv (clr a (setv b v r))
            (setv b v (clr a r)))))

(defthm clr-of-setv
  (keyquiv (clr a (setv a v r))
           (clr a r)))

(defthm acl2-count-cdr-<=
  (<= (acl2-count (cdr x)) (acl2-count x))
  :rule-classes (:linear))

(defthm acl2-count-car-<=
  (<= (acl2-count (car x)) (acl2-count x))
  :rule-classes (:linear))

(defthm memberp-clr-non-increasing
  (<= (acl2-count (clr a alist)) (acl2-count alist))
  :hints (("goal" :induct (clr a alist)))
  :rule-classes (:linear))

(defthm memberp-clr-decreases
  (implies
   (memberp a (keys alist))
   (< (acl2-count (clr a alist)) (acl2-count alist)))
  :hints (("goal" :induct (clr a alist)))
  :rule-classes (:linear))

(defthm memberp-cons
  (implies
   (consp alist)
   (memberp (caar alist) (keys alist))))

(defthm acl2-count-assoc-<=
  (<= (acl2-count (assoc a list)) (acl2-count list))
  :hints (("Goal" :induct (assoc a list)))
  :rule-classes (:linear))

(defthm acl2-count-assoc-memberp-<
  (implies
   (memberp key (keys list))
   (< (acl2-count (assoc a list)) (acl2-count list)))
  :hints (("Goal" :induct (assoc a list)))
  :rule-classes (:linear))

(defthm acl2-count-getv-<=
  (<= (acl2-count (alist::getv key alist1)) (acl2-count alist1))
  :rule-classes (:linear))

(defthm acl2-count-getv-<
  (implies
   (memberp key (alist::keys alist1))
   (< (acl2-count (alist::getv key alist1)) (acl2-count alist1)))
  :rule-classes (:linear))

(in-theory (disable setv getv clr keys))

;; Preimage-aux scans the list looking for our value, and collects any keys it
;; finds along the way.  Note that it will collect shadowed pairs if they are
;; bound to our value.

(defund preimage-aux (val x)
  (declare (xargs :guard (alistp x)))
  (if (consp x)
      (if (equal (cdar x) val)
          (cons (caar x)
                (preimage-aux val (cdr x)))
        (preimage-aux val (cdr x)))
    nil))

(defthm preimage-aux-when-value-missing
  (implies (not (memberp val (strip-cdrs x)))
           (equal (preimage-aux val x)
                  nil))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm not-memberp-of-preimage-aux
  (implies (not (memberp key (strip-cars x)))
           (equal (memberp key (preimage-aux val x))
                  nil))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm unique-of-preimage-aux-when-unique-of-strip-cdrs
  (implies (BAG::unique (strip-cdrs x))
           (BAG::unique (preimage-aux val x)))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm unique-of-preimage-aux-when-unique-of-strip-cars
  (implies (BAG::unique (strip-cars x))
           (BAG::unique (preimage-aux val x)))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm memberp-of-caar-in-preimage-aux
  (implies (BAG::unique (strip-cars x))
           (equal (memberp (caar x) (preimage-aux a x))
                  (and (consp x)
                       (equal (cdar x) a))))
  :hints(("goal" :in-theory (enable preimage-aux))))

(defthm preimage-aux-when-not-member-of-cdr-of-strip-cdrs
  (implies (not (memberp a (cdr (strip-cdrs x))))
           (equal (preimage-aux a x)
                  (if (and (consp x)
                           (equal a (cdar x)))
                      (list (caar x))
                    nil)))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm preimage-aux-of-cdar-with-self
  (equal (preimage-aux (cdar x) x)
         (if (consp x)
             (cons (caar x) (preimage-aux (cdar x) (cdr x)))
           nil))
  :hints(("Goal" :in-theory (enable preimage-aux))))

(defthm preimage-aux-of-cdr-when-not-cdar
  (implies (not (equal (cdar x) a))
           (equal (preimage-aux a (cdr x))
                  (if (consp x)
                      (preimage-aux a x)
                    nil)))
  :hints(("Goal" :in-theory (enable preimage-aux))))




;; Preimage simply calls Preimage-aux after deshadowing x.  This produces a
;; list of keys that would actually map to the desired value when given to
;; assoc.

(defund preimage (val x)
  (declare (xargs :guard (alistp x)))
  (preimage-aux val (deshadow x)))

(defthm preimage-when-value-missing
  (implies (not (memberp val (strip-cdrs x)))
           (equal (preimage val x)
                  nil))
  :hints(("Goal" :in-theory (enable preimage))))

(defthm not-memberp-of-preimage
  (implies (not (memberp key (strip-cars x)))
           (equal (memberp key (preimage val x))
                  nil))
  :hints(("Goal" :in-theory (enable preimage))))

(defthm unique-preimage
  (BAG::unique (preimage val x))
  :hints(("Goal" :in-theory (enable preimage))))

(defthm preimage-of-deshadow
  (equal (preimage val (deshadow x))
         (preimage val x))
  :hints(("Goal" :in-theory (enable preimage))))

(defthm memberp-of-caar-in-preimage
  (equal (memberp (caar x) (preimage a x))
         (and (consp x)
              (equal (cdar x) a)))
  :hints(("Goal" :in-theory (enable preimage)
          :use (:instance memberp-of-caar-in-preimage-aux
                          (x (deshadow x))))))

(defthm preimage-when-not-member-of-cdr-of-strip-cdrs
  (implies (not (memberp a (cdr (strip-cdrs x))))
           (equal (preimage a x)
                  (if (and (consp x)
                           (equal a (cdar x)))
                      (list (caar x))
                    nil)))
  :hints(("Goal" :in-theory (enable preimage))))

(defthm preimage-of-cdar-with-self
  (equal (preimage (cdar x) x)
         (if (consp x)
             (cons (caar x)
                   (preimage (cdar x)
                             (clearkey (caar x) (cdr x))))
           nil))
  :hints(("Goal" :in-theory (e/d (preimage)
                                 (preimage-aux-of-cdar-with-self))
          :use (:instance preimage-aux-of-cdar-with-self
                          (x (deshadow x))))))

(defthm preimage-of-cdr-when-not-cdar-and-unique
  (implies (and (not (equal (cdar x) a))
                (BAG::unique (strip-cars x)))
           (equal (preimage a (cdr x))
                  (if (consp x)
                      (preimage a x)
                    nil)))
  :hints(("Goal" :in-theory (enable preimage))))

(in-theory (disable strip-cars strip-cdrs))

(defthm strip-cars-type-consp
  (implies (consp x)
           (consp (strip-cars x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strip-cars))))

(defthm strip-cars-type-non-consp
  (implies (not (consp x))
           (not (consp (strip-cars x))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strip-cars))))

(defthm consp-strip-cars
  (equal (consp (strip-cars x))
         (consp x)))

(defthm strip-cars-of-non-consp
  (implies (not (consp x))
           (equal (strip-cars x)
                  nil))
  :hints(("Goal" :in-theory (enable strip-cars))))

(defthm strip-cars-of-cons
  (equal (strip-cars (cons x y))
         (cons (car x)
               (strip-cars y)))
  :hints(("Goal" :in-theory (enable strip-cars))))

(defthm car-of-strip-cars
  (equal (car (strip-cars x))
         (car (car x))))

(defthm strip-cars-of-cdr
  (equal (strip-cars (cdr x))
         (cdr (strip-cars x))))

(defthm len-of-strip-cars
  (equal (len (strip-cars x))
         (len x))
  :hints(("Goal" :in-theory (enable len))))

(defthm strip-cars-of-append
  (equal (strip-cars (append x y))
         (append (strip-cars x)
                 (strip-cars y)))
  :hints(("Goal" :in-theory (enable append))))

(defthm strip-cars-of-firstn
  (equal (strip-cars (firstn n x))
         (firstn n (strip-cars x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm strip-cars-of-nthcdr
  (equal (strip-cars (nthcdr n x))
         (nthcdr n (strip-cars x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm memberp-caar-strip-cars
  (equal (memberp (caar x) (strip-cars x))
         (consp x)))

(defthm strip-cdrs-type-consp
  (implies (consp x)
           (consp (strip-cdrs x)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-type-non-consp
  (implies (not (consp x))
           (not (consp (strip-cdrs x))))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable strip-cdrs))))

(defthm consp-strip-cdrs
  (equal (consp (strip-cdrs x))
         (consp x)))

(defthm strip-cdrs-of-non-consp
  (implies (not (consp x))
           (equal (strip-cdrs x)
                  nil))
  :hints(("Goal" :in-theory (enable strip-cdrs))))

(defthm strip-cdrs-of-cons
  (equal (strip-cdrs (cons x y))
         (cons (cdr x)
               (strip-cdrs y)))
  :hints(("Goal" :in-theory (enable strip-cdrs))))

(defthm car-of-strip-cdrs
  (equal (car (strip-cdrs x))
         (cdr (car x))))

(defthm strip-cdrs-of-cdr
  (equal (strip-cdrs (cdr x))
         (cdr (strip-cdrs x))))

(defthm len-of-strip-cdrs
  (equal (len (strip-cdrs x))
         (len x))
  :hints(("Goal" :in-theory (enable len))))

(defthm strip-cdrs-of-append
  (equal (strip-cdrs (append x y))
         (append (strip-cdrs x)
                 (strip-cdrs y)))
  :hints(("Goal" :in-theory (enable append))))

(defthm strip-cdrs-of-firstn
  (equal (strip-cdrs (firstn n x))
         (firstn n (strip-cdrs x)))
  :hints(("Goal" :in-theory (enable firstn))))

(defthm strip-cdrs-of-nthcdr
  (equal (strip-cdrs (nthcdr n x))
         (nthcdr n (strip-cdrs x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm memberp-cdar-strip-cdrs
  (equal (memberp (cdar x) (strip-cdrs x))
         (consp x)))

