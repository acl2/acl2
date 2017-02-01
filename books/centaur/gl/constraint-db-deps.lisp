; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "GL")

(include-book "constraint-db")
(include-book "glcp-unify-thms")

(define gobj-alist-list-depends-on (k p x)
  :verify-guards nil
  (if (atom x)
      nil
    (or (gobj-alist-depends-on k p (car x))
        (gobj-alist-list-depends-on k p (cdr x))))
  ///
  (defthm gobj-alist-list-depends-on-of-append
    (equal (gobj-alist-list-depends-on k p (append a b))
           (or (gobj-alist-list-depends-on k p a)
               (gobj-alist-list-depends-on k p b)))
    :hints(("Goal" :in-theory (enable gobj-alist-list-depends-on))))
  (defthm gobj-alist-list-depends-on-nil
         (not (gobj-alist-list-depends-on k p nil))
         :hints(("Goal" :in-theory (enable gobj-alist-list-depends-on)))))

(define gbc-sigtable-depends-on (k p sigtable)
  :verify-guards nil
  (if (atom sigtable)
      nil
    (if (atom (car sigtable))
        (gbc-sigtable-depends-on k p (cdr sigtable))
      (or (gobj-alist-list-depends-on k p (cdar sigtable))
          (gbc-sigtable-depends-on k p (cdr sigtable))))))

(define gbc-tuples-depends-on (k p tuples)
  :verify-guards nil
  (if (atom tuples)
      nil
    (or (gbc-sigtable-depends-on k p (constraint-tuple->sig-table (car tuples)))
        (gbc-tuples-depends-on k p (cdr tuples)))))


(define gbc-db-depends-on (k p ccat)
  :verify-guards nil
  (if (atom ccat)
      nil
    (if (atom (car ccat))
        (gbc-db-depends-on k p (cdr ccat))
      (or (gbc-tuples-depends-on k p (cdar ccat))
          (gbc-db-depends-on k p (cdr ccat))))))


(defsection gbc-db-emptyp

  (define gbc-sigtable-emptyp (x)
    :verify-guards nil
    (if (atom x)
        t
      (and (or (atom (car x))
               (subsetp (cdar x) '(nil)))
           (gbc-sigtable-emptyp (cdr X))))
    ///
    (defthm gbc-sigtable-empty-implies-no-dependencies
      (implies (gbc-sigtable-emptyp x)
               (not (gbc-sigtable-depends-on k p x)))
      :hints(("Goal" :in-theory (enable gbc-sigtable-depends-on
                                        gobj-alist-list-depends-on)))))


  (define gbc-tuples-emptyp (x)
    :verify-guards nil
    (if (atom x)
        t
      (and (gbc-sigtable-emptyp (constraint-tuple->sig-table (car x)))
           (gbc-tuples-emptyp (cdr x))))
    ///
    (defthm gbc-tuples-empty-implies-no-dependencies
      (implies (gbc-tuples-emptyp x)
               (not (gbc-tuples-depends-on k p x)))
      :hints(("Goal" :in-theory (enable gbc-tuples-depends-on)))))

  (define gbc-db-emptyp (x)
    :verify-guards nil
    (if (atom x)
        t
      (and (or (atom (car x))
               (gbc-tuples-emptyp (cdar x)))
           (gbc-db-emptyp (cdr x))))
    ///
    (defthm gbc-db-emptyp-implies-no-dependencies
      (implies (gbc-db-emptyp x)
               (not (gbc-db-depends-on k p x)))
      :hints(("Goal" :in-theory (enable gbc-db-depends-on))))))



(defthm gbc-extend-substs-dependencies
  (implies (and (not (gobj-alist-depends-on k p lit-subst))
                (not (gobj-alist-list-depends-on k p partial-substs)))
           (not (gobj-alist-list-depends-on k p (gbc-extend-substs lit-subst
                                                                   partial-substs))))
  :hints(("Goal" :in-theory (enable gobj-alist-list-depends-on))))

(local (in-theory (enable alist-vals)))

(defthm gbc-substs-check-syntaxp-dependencies
  (implies (not (gobj-alist-list-depends-on k p substs))
           (not (gobj-alist-list-depends-on
                 k p (alist-vals (gbc-substs-check-syntaxp substs thmname syntaxp
                                                           state)))))
  :hints(("Goal" :in-theory (enable gbc-substs-check-syntaxp
                                    gobj-alist-list-depends-on))))

(defthm dependencies-of-sigtable-lookup
  (implies (not (gbc-sigtable-depends-on k p sigtable))
           (not (gobj-alist-list-depends-on k p (cdr (hons-assoc-equal sig
                                                                       sigtable)))))
  :hints(("Goal" :in-theory (enable gbc-sigtable-depends-on
                                    gobj-alist-list-depends-on))))

(defthm gbc-sort-substs-into-sigtable-dependencies
  (implies (and (not (gobj-alist-list-depends-on k p substs))
                (not (gbc-sigtable-depends-on k p sigtable)))
           (not (gbc-sigtable-depends-on
                 k p (gbc-sort-substs-into-sigtable substs common-vars
                                                    sigtable))))
  :hints(("Goal" :in-theory (enable gobj-alist-list-depends-on
                                    gbc-sigtable-depends-on))))

(defthm gbc-unbound-lits-add-to-existing-tuple-dependencies
  (implies (and (not (gobj-alist-list-depends-on k p substs))
                (not (gbc-tuples-depends-on k p tuples)))
           (not (gbc-tuples-depends-on
                 k p (mv-nth 1 (gbc-unbound-lits-add-to-existing-tuple
                                rule existing-lits lit substs tuples)))))
  :hints(("Goal" :in-theory (enable gbc-tuples-depends-on))))

(defthm gbc-unbound-lits-add-tuples-dependencies
  (implies (and (not (gobj-alist-list-depends-on k p substs))
                (not (gbc-db-depends-on k p ccat)))
           (not (gbc-db-depends-on k p (gbc-unbound-lits-add-tuples
                                        litvars rule existing-lits
                                        existing-vars substs ccat))))
  :hints(("Goal" :in-theory (enable gbc-db-depends-on
                                    gbc-tuples-depends-on))))


;; (local (defthm gobj-alist-depends-on-nil
;;          (not (gobj-alist-depends-on k p nil))
;;          :hints(("Goal" :in-theory (enable gobj-alist-depends-on)))))

(defthm dependencies-of-gbc-db-lookup
  (implies (not (gbc-db-depends-on k p sigtable))
           (not (gbc-tuples-depends-on k p (cdr (hons-assoc-equal sig sigtable)))))
  :hints(("Goal" :in-theory (enable gbc-db-depends-on))))

(defthm gbc-process-new-lit-tuple-dependencies
  (implies (and (not (gobj-depends-on k p lit))
                (not (gbc-sigtable-depends-on k p (constraint-tuple->sig-table
                                                   tuple)))
                (not (gbc-db-depends-on k p ccat)))
           (mv-let (substs ccat)
             (gbc-process-new-lit-tuple lit tuple ccat state)
             (and (not (gobj-alist-list-depends-on k p (alist-vals substs)))
                  (not (gbc-db-depends-on k p ccat)))))
  :hints (("goal" :expand ((:free (a b) (gbc-db-depends-on k p (cons a b)))
                           (:free (a b) (gbc-tuples-depends-on k p (cons a
                                                                         b)))))))

(local (defthm alist-vals-of-append
         (equal (alist-vals (append a b))
                (append (alist-vals a) (alist-vals b)))))



(defthm gbc-process-new-lit-tuples-dependencies
  (implies (and (not (gobj-depends-on k p lit))
                (not (gbc-tuples-depends-on k p tuples))
                (not (gbc-db-depends-on k p ccat)))
           (mv-let (substs ccat)
             (gbc-process-new-lit-tuples lit tuples ccat state)
             (and (not (gobj-alist-list-depends-on k p (alist-vals substs)))
                  (not (gbc-db-depends-on k p ccat)))))
  :hints(("Goal" :in-theory (e/d (gbc-tuples-depends-on)
                                 (gbc-process-new-lit-tuple)))))

(defthm gbc-process-new-lit-dependencies
  (implies (and (not (gobj-depends-on k p lit))
                (not (gbc-db-depends-on k p ccat)))
           (mv-let (substs ccat)
             (gbc-process-new-lit lit ccat state)
             (and (not (gobj-alist-list-depends-on k p (alist-vals substs)))
                  (not (gbc-db-depends-on k p ccat)))))
  :hints(("Goal" :in-theory (enable gbc-process-new-lit))))



(defund parametrize-gobj-alists (p alists)
  (declare (xargs :guard t))
  (if (atom alists)
      nil
    (cons (gobj-alist-to-param-space (car alists) p)
          (parametrize-gobj-alists p (cdr alists)))))

(defund parametrize-sig-table (p sig-table)
  (declare (xargs :guard t))
  (if (atom sig-table)
      nil
    (if (atom (car sig-table))
        (parametrize-sig-table p (cdr sig-table))
      (hons-acons (gobj-list-to-param-space (caar sig-table) p)
                  (parametrize-gobj-alists p (cdar sig-table))
                  (parametrize-sig-table p (cdr sig-table))))))


(defund parametrize-constraint-db-tuples (p tuples)
  (declare (xargs :guard t))
  (b* (((when (atom tuples)) nil)
       ((unless (constraint-tuple-p (car tuples)))
        (parametrize-constraint-db-tuples p (cdr tuples)))
       ((constraint-tuple x) (car tuples))
       (sig-table (parametrize-sig-table p x.sig-table)))
    (fast-alist-free x.sig-table)
    (cons (constraint-tuple x.rule x.existing-lits x.matching-lit x.common-vars
                            x.existing-vars sig-table)
          (parametrize-constraint-db-tuples p (cdr tuples)))))

(defund parametrize-constraint-db (p ccat)
  (declare (xargs :guard t))
  (b* (((when (atom ccat)) nil)
       ((when (atom (car ccat)))
        (parametrize-constraint-db p (cdr ccat))))
    (hons-acons (caar ccat)
                (parametrize-constraint-db-tuples p (cdar ccat))
                (parametrize-constraint-db p (cdr ccat)))))





(defsection gobj-alist-list-vars-bounded
  (defund gobj-alist-list-vars-bounded (k p x)
    (if (atom x)
        t
      (and (gobj-alist-vars-bounded k p (car x))
           (gobj-alist-list-vars-bounded k p (cdr x)))))

  (defund gobj-alist-list-vars-bounded-witness (k p x)
    (if (atom x)
        nil
      (or (gobj-alist-vars-bounded-witness k p (car x))
          (gobj-alist-list-vars-bounded-witness k p (cdr x)))))

  (local (in-theory (enable gobj-alist-list-vars-bounded
                            gobj-alist-list-vars-bounded-witness)))

  (local (in-theory (disable nfix)))

  (defthm gobj-alist-list-vars-bounded-implies-not-depends-on
    (implies (and (gobj-alist-list-vars-bounded k p x)
                  (let ((n (bfr-varname-fix n)))
                    (or (not (natp n))
                        (<= (nfix k) n))))
             (not (gobj-alist-list-depends-on n p x)))
    :hints(("Goal" :in-theory (e/d (gobj-alist-list-depends-on)))))

  (defthm gobj-alist-list-vars-bounded-incr
    (implies (and (gobj-alist-list-vars-bounded m p x)
                  (<= (nfix m) (nfix n)))
             (gobj-alist-list-vars-bounded n p x)))

  (defthm gobj-alist-list-vars-bounded-witness-under-iff
    (iff (gobj-alist-list-vars-bounded-witness k p x)
         (not (gobj-alist-list-vars-bounded k p x))))

  (defthmd gobj-alist-list-vars-bounded-in-terms-of-witness
    (implies (acl2::rewriting-positive-literal
              `(gobj-alist-list-vars-bounded ,k ,p ,x))
             (equal (gobj-alist-list-vars-bounded k p x)
                    (let ((n (bfr-varname-fix (gobj-alist-list-vars-bounded-witness k p x))))
                      (implies (or (not (natp n))
                                   (<= (nfix k) n))
                               (not (gobj-alist-list-depends-on n p x))))))
    :hints(("Goal" :in-theory (enable gobj-alist-list-depends-on
                                      gobj-alist-vars-bounded-in-terms-of-witness))))

  (defthm gobj-alist-list-vars-bounded-of-cons
    (equal (gobj-alist-list-vars-bounded k p (cons a b))
           (and (gobj-alist-vars-bounded k p a)
                (gobj-alist-list-vars-bounded k p b))))

  (defthm gobj-alist-list-vars-bounded-of-atom
    (implies (not (consp x))
             (equal (gobj-alist-list-vars-bounded k p x) t))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm gobj-alist-list-vars-bounded-of-parametrize-gobj-alists
    (implies (gobj-alist-list-vars-bounded k t x)
             (gobj-alist-list-vars-bounded
              k p (parametrize-gobj-alists p x)))
    :hints(("Goal" :in-theory (enable gobj-alist-list-vars-bounded
                                      parametrize-gobj-alists)))))


(defsection gbc-sigtable-vars-bounded
  (defund gbc-sigtable-vars-bounded (k p x)
    (if (atom x)
        t
      (and (or (atom (car x))
               (gobj-alist-list-vars-bounded k p (cdar x)))
           (gbc-sigtable-vars-bounded k p (cdr x)))))

  (defund gbc-sigtable-vars-bounded-witness (k p x)
    (if (atom x)
        nil
      (or (and (consp (car x))
               (gobj-alist-list-vars-bounded-witness k p (cdar x)))
          (gbc-sigtable-vars-bounded-witness k p (cdr x)))))

  (local (in-theory (enable gbc-sigtable-vars-bounded
                            gbc-sigtable-vars-bounded-witness)))

  (local (in-theory (disable nfix)))

  (defthm gbc-sigtable-vars-bounded-implies-not-depends-on
    (implies (and (gbc-sigtable-vars-bounded k p x)
                  (let ((n (bfr-varname-fix n)))
                    (or (not (natp n))
                        (<= (nfix k) n))))
             (not (gbc-sigtable-depends-on n p x)))
    :hints(("Goal" :in-theory (e/d (gbc-sigtable-depends-on)))))

  (defthm gbc-sigtable-vars-bounded-incr
    (implies (and (gbc-sigtable-vars-bounded m p x)
                  (<= (nfix m) (nfix n)))
             (gbc-sigtable-vars-bounded n p x)))

  (defthm gbc-sigtable-vars-bounded-witness-under-iff
    (iff (gbc-sigtable-vars-bounded-witness k p x)
         (not (gbc-sigtable-vars-bounded k p x))))

  (defthmd gbc-sigtable-vars-bounded-in-terms-of-witness
    (implies (acl2::rewriting-positive-literal
              `(gbc-sigtable-vars-bounded ,k ,p ,x))
             (equal (gbc-sigtable-vars-bounded k p x)
                    (let ((n (bfr-varname-fix (gbc-sigtable-vars-bounded-witness k p x))))
                      (implies (or (not (natp n))
                                   (<= (nfix k) n))
                               (not (gbc-sigtable-depends-on n p x))))))
    :hints(("Goal" :in-theory (enable gbc-sigtable-depends-on
                                      gobj-alist-list-vars-bounded-in-terms-of-witness))))

  (defthm gbc-sigtable-vars-bounded-of-cons
    (equal (gbc-sigtable-vars-bounded k p (cons a b))
           (and (or (atom a)
                    (gobj-alist-list-vars-bounded k p (cdr a)))
                (gbc-sigtable-vars-bounded k p b))))

  (defthm gbc-sigtable-vars-bounded-of-atom
    (implies (not (consp x))
             (equal (gbc-sigtable-vars-bounded k p x) t))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))


  (defthm gbc-sigtable-vars-bounded-of-parametrize-sig-table
    (implies (gbc-sigtable-vars-bounded k t x)
             (gbc-sigtable-vars-bounded
              k p (parametrize-sig-table p x)))
    :hints(("Goal" :in-theory (enable gbc-sigtable-vars-bounded
                                      parametrize-sig-table)))))


(defsection gbc-tuples-vars-bounded
  (defund gbc-tuples-vars-bounded (k p x)
    (if (atom x)
        t
      (and (gbc-sigtable-vars-bounded k p (constraint-tuple->sig-table (car x)))
           (gbc-tuples-vars-bounded k p (cdr x)))))

  (defund gbc-tuples-vars-bounded-witness (k p x)
    (if (atom x)
        nil
      (or (gbc-sigtable-vars-bounded-witness k p (constraint-tuple->sig-table (car x)))
          (gbc-tuples-vars-bounded-witness k p (cdr x)))))

  (local (in-theory (enable gbc-tuples-vars-bounded
                            gbc-tuples-vars-bounded-witness)))

  (local (in-theory (disable nfix)))

  (defthm gbc-tuples-vars-bounded-implies-not-depends-on
    (implies (and (gbc-tuples-vars-bounded k p x)
                  (let ((n (bfr-varname-fix n)))
                    (or (not (natp n))
                        (<= (nfix k) n))))
             (not (gbc-tuples-depends-on n p x)))
    :hints(("Goal" :in-theory (e/d (gbc-tuples-depends-on)))))

  (defthm gbc-tuples-vars-bounded-incr
    (implies (and (gbc-tuples-vars-bounded m p x)
                  (<= (nfix m) (nfix n)))
             (gbc-tuples-vars-bounded n p x)))

  (defthm gbc-tuples-vars-bounded-witness-under-iff
    (iff (gbc-tuples-vars-bounded-witness k p x)
         (not (gbc-tuples-vars-bounded k p x))))

  (defthmd gbc-tuples-vars-bounded-in-terms-of-witness
    (implies (acl2::rewriting-positive-literal
              `(gbc-tuples-vars-bounded ,k ,p ,x))
             (equal (gbc-tuples-vars-bounded k p x)
                    (let ((n (bfr-varname-fix (gbc-tuples-vars-bounded-witness k p x))))
                      (implies (or (not (natp n))
                                   (<= (nfix k) n))
                               (not (gbc-tuples-depends-on n p x))))))
    :hints(("Goal" :in-theory (enable gbc-tuples-depends-on
                                      gbc-sigtable-vars-bounded-in-terms-of-witness))))

  (defthm gbc-tuples-vars-bounded-of-cons
    (equal (gbc-tuples-vars-bounded k p (cons a b))
           (and (gbc-sigtable-vars-bounded k p (constraint-tuple->sig-table a))
                (gbc-tuples-vars-bounded k p b))))

  (defthm gbc-tuples-vars-bounded-of-atom
    (implies (not (consp x))
             (equal (gbc-tuples-vars-bounded k p x) t))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm gbc-tuples-vars-bounded-of-parametrize-constraint-db-tuples
    (implies (gbc-tuples-vars-bounded k t x)
             (gbc-tuples-vars-bounded
              k p (parametrize-constraint-db-tuples p x)))
    :hints(("Goal" :in-theory (enable gbc-tuples-vars-bounded
                                      parametrize-constraint-db-tuples)))))



(defsection gbc-db-vars-bounded
  (defund gbc-db-vars-bounded (k p x)
    (if (atom x)
        t
      (and (or (atom (car x))
               (gbc-tuples-vars-bounded k p (cdar x)))
           (gbc-db-vars-bounded k p (cdr x)))))

  (defund gbc-db-vars-bounded-witness (k p x)
    (if (atom x)
        nil
      (or (and (consp (car x))
               (gbc-tuples-vars-bounded-witness k p (cdar x)))
          (gbc-db-vars-bounded-witness k p (cdr x)))))

  (local (in-theory (enable gbc-db-vars-bounded
                            gbc-db-vars-bounded-witness)))

  (local (in-theory (disable nfix)))

  (defthm gbc-db-vars-bounded-implies-not-depends-on
    (implies (and (gbc-db-vars-bounded k p x)
                  (let ((n (bfr-varname-fix n)))
                    (or (not (natp n))
                        (<= (nfix k) n))))
             (not (gbc-db-depends-on n p x)))
    :hints(("Goal" :in-theory (e/d (gbc-db-depends-on)))))

  (defthm gbc-db-vars-bounded-incr
    (implies (and (gbc-db-vars-bounded m p x)
                  (<= (nfix m) (nfix n)))
             (gbc-db-vars-bounded n p x)))

  (defthm gbc-db-vars-bounded-witness-under-iff
    (iff (gbc-db-vars-bounded-witness k p x)
         (not (gbc-db-vars-bounded k p x))))

  (defthmd gbc-db-vars-bounded-in-terms-of-witness
    (implies (acl2::rewriting-positive-literal
              `(gbc-db-vars-bounded ,k ,p ,x))
             (equal (gbc-db-vars-bounded k p x)
                    (let ((n (bfr-varname-fix (gbc-db-vars-bounded-witness k p x))))
                      (implies (or (not (natp n))
                                   (<= (nfix k) n))
                               (not (gbc-db-depends-on n p x))))))
    :hints(("Goal" :in-theory (enable gbc-db-depends-on
                                      gbc-tuples-vars-bounded-in-terms-of-witness))))

  (defthm gbc-db-vars-bounded-of-cons
    (equal (gbc-db-vars-bounded k p (cons a b))
           (and (or (atom a)
                    (gbc-tuples-vars-bounded k p (cdr a)))
                (gbc-db-vars-bounded k p b))))

  (defthm gbc-db-vars-bounded-of-atom
    (implies (not (consp x))
             (equal (gbc-db-vars-bounded k p x) t))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))


  (defthm gbc-db-vars-bounded-of-parametrize-constraint-db
    (implies (gbc-db-vars-bounded k t x)
             (gbc-db-vars-bounded
              k p (parametrize-constraint-db p x)))
    :hints(("Goal" :in-theory (enable gbc-db-vars-bounded
                                      parametrize-constraint-db)))))


(defthm-gobj-flag gobj-depends-on-congruence
  (defthm bfr-varname-equiv-implies-equal-gobj-depends-on
    (implies (bfr-varname-equiv k1 k2)
             (equal (gobj-depends-on k1 p x)
                    (gobj-depends-on k2 p x)))
    :hints ('(:expand ((:free (k) (gobj-depends-on k p x)))
              :in-theory (disable bfr-varname-equiv)))
    :rule-classes :congruence
    :flag gobj)

  (defthm bfr-varname-equiv-implies-equal-gobj-list-depends-on
    (implies (bfr-varname-equiv k1 k2)
             (equal (gobj-list-depends-on k1 p x)
                    (gobj-list-depends-on k2 p x)))
    :hints ('(:expand ((:free (k) (gobj-list-depends-on k p x)))
              :in-theory (disable bfr-varname-equiv)))
    :rule-classes :congruence
    :flag list))

(defcong bfr-varname-equiv equal (gobj-alist-depends-on k p x) 1
  :hints(("Goal" :in-theory (e/d (gobj-alist-depends-on) (bfr-varname-equiv)))))

(defcong bfr-varname-equiv equal (gobj-alist-list-depends-on k p x) 1
  :hints(("Goal" :in-theory (e/d (gobj-alist-list-depends-on) (bfr-varname-equiv)))))

(defcong bfr-varname-equiv equal (gbc-sigtable-depends-on k p x) 1
  :hints(("Goal" :in-theory (e/d (gbc-sigtable-depends-on) (bfr-varname-equiv)))))

(defcong bfr-varname-equiv equal (gbc-tuples-depends-on k p x) 1
  :hints(("Goal" :in-theory (e/d (gbc-tuples-depends-on) (bfr-varname-equiv)))))

(defcong bfr-varname-equiv equal (gbc-db-depends-on k p x) 1
  :hints(("Goal" :in-theory (e/d (gbc-db-depends-on) (bfr-varname-equiv)))))





(defthm gbc-process-new-lit-bounded
  (implies (and (gobj-vars-bounded k p lit)
                (gbc-db-vars-bounded k p ccat))
           (mv-let (substs ccat)
             (gbc-process-new-lit lit ccat state)
             (and (gobj-alist-list-vars-bounded k p (alist-vals substs))
                  (gbc-db-vars-bounded k p ccat))))
  :hints (("goal" :in-theory (e/d
                              (gobj-alist-list-vars-bounded-in-terms-of-witness
                              gbc-db-vars-bounded-in-terms-of-witness)
                              (nfix)))))




(defthm gbc-db-vars-bounded-of-incr
  (implies (and (gbc-db-vars-bounded n p x)
                (<= (nfix n) (nfix k)))
           (gbc-db-vars-bounded k p x))
  :hints (("goal" :in-theory (e/d (gbc-db-vars-bounded-in-terms-of-witness)
                                  (nfix)))))



(defthmd gbc-db-empty-implies-gbc-db-vars-bounded
  (implies (gbc-db-emptyp x)
           (gbc-db-vars-bounded k p x))
  :hints(("Goal" :in-theory (enable gbc-db-vars-bounded-in-terms-of-witness))))


