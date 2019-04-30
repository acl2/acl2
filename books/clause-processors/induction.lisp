; Induction Clause Processor
; Copyright (C) 2013 Centaur Technology
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

(in-package "ACL2")

(include-book "tools/defevaluator-fast" :dir :system)
(include-book "ev-theoremp")
(include-book "unify-subst")
(include-book "tools/def-functional-instance" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "std/basic/arith-equivs" :dir :System)

(defevaluator-fast
  indev indev-lst
  ((if a b c)
   (o-p x)
   (o< a b)
   (not a)
   (binary-+ a b)
   (cons a b))
  :namedp t)

(def-ev-theoremp indev)


(defun pseudo-term-alist-listp (x)
  (declare (Xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (pseudo-term-val-alistp (car x))
         (pseudo-term-alist-listp (cdr X)))))

(defun induction-step-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (pseudo-termp (caar x))            ;; predicate
         (pseudo-term-alist-listp (cdar x)) ;; substitutions
         (induction-step-listp (cdr x)))))



;; (defun pseudo-term-alist-list-listp (x)
;;   (declare (Xargs :guard t))
;;   (if (atom x)
;;       (eq x nil)
;;     (and (pseudo-term-alist-listp (car x))
;;          (pseudo-term-alist-list-listp (cdr X)))))
(local
 (defthm pseudo-term-val-alistp-implies-alistp
   (implies (pseudo-term-val-alistp x)
            (alistp x))
   :hints(("Goal" :in-theory (enable pseudo-term-val-alistp)))
   :rule-classes :forward-chaining))



;; Applies each substitution to the clause; returns the list of resulting clauses
(defun substitute-list-into-clause (subs clause)
  (declare (xargs :guard (and (pseudo-term-alist-listp subs)
                              (pseudo-term-listp clause))))
  (if (atom subs)
      nil
    (cons (substitute-into-list clause (car subs))
          (substitute-list-into-clause (cdr subs) clause))))

(defthm substitute-list-into-clause-of-cons
  (equal (substitute-list-into-clause
          (cons a b) clause)
         (cons (substitute-into-list clause a)
               (substitute-list-into-clause b clause))))

(defthm substitute-list-into-clause-of-atom
  (implies (not (consp x))
           (equal (substitute-list-into-clause x clause)
                  nil))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))


;; for each induction, produces a clause meaning basically
;;      (implies (implies ind-condition
;;                        ...ind-hyps...)
;;               clause)
(defun induction-steps (clause inductions)
  (declare (xargs :guard (and (pseudo-term-listp clause)
                              (induction-step-listp inductions))))
  (if (atom inductions)
      nil
    (cons (cons `(not (if ,(caar inductions)   ;; condition
                          ,(conjoin-clauses
                            (substitute-list-into-clause
                             (cdar inductions) ;; substitutions
                             clause))
                        'nil))
                clause)
          (induction-steps clause (cdr inductions)))))

(defun measure-decrs-subs (meas pred subs orig-clause)
  (declare (xargs :guard (and (pseudo-termp meas)
                              (pseudo-termp pred)
                              (pseudo-term-alist-listp subs)
                              (pseudo-term-listp orig-clause))))
  (if (atom subs)
      nil
    (cons `(,@orig-clause
            (not ,pred)
            (o< ,(substitute-into-term meas (car subs))
                ,meas))
          (measure-decrs-subs meas pred (cdr subs) orig-clause))))

(defun measure-decrs (meas inductions orig-clause)
  (declare (xargs :guard (and (pseudo-termp meas)
                              (induction-step-listp inductions)
                              (pseudo-term-listp orig-clause))))
  (if (atom inductions)
      nil
    (append (measure-decrs-subs meas (caar inductions) (cdar inductions) orig-clause)
            (measure-decrs meas (cdr inductions) orig-clause))))

(local
 (progn

   (defthm o-first-expt-of-make-ord
     (equal (o-first-expt (make-ord a b c))
            a))

   (defthm o-first-coeff-of-make-ord
     (equal (o-first-coeff (make-ord a b c))
            b))

   (defthm o-rst-of-make-ord
     (equal (o-rst (make-ord a b c))
            c))

   (defthm o-finp-of-make-ord
     (not (o-finp (make-ord a b c))))

   (defthm o-p-of-make-ord
     (implies (and (o-p a)
                   (o-p n)
                   (posp c)
                   (o< (o-first-expt n) a))
              (o-p (make-ord a c n))))

   (defthm o<-self
     (not (o< a a)))

   (local (in-theory (disable o-first-expt
                              o-first-coeff
                              o-rst
                              make-ord)))

   (defthm o<-of-make-ord
     (equal (o< (make-ord a b c) d)
            (and (not (o-finp d))
                 (or (o< a (o-first-expt d))
                     (and (equal a (o-first-expt d))
                          (or (< b (o-first-coeff d))
                              (and (equal b (o-first-coeff d))
                                   (o< c (o-rst d))))))))
     :hints (("goal" :do-not-induct t)))


   (defthm acl2-count-of-o-rst
     (implies (not (o-finp x))
              (< (acl2-count (o-rst x)) (acl2-count x)))
     :hints(("Goal" :in-theory (enable o-finp o-rst))))


   (defun o-fin-part (x)
     (declare (xargs :guard (o-p x)))
     (if (o-finp x)
         (nfix x)
       (o-fin-part (o-rst x))))

   (defun replace-o-fin-part (x n)
     (declare (xargs :guard (and (o-p x) (natp n))
                     :verify-guards nil))
     (if (o-finp x)
         (nfix n)
       (make-ord (o-first-expt x)
                 (o-first-coeff x)
                 (replace-o-fin-part (o-rst x) n))))

   (defthm o-first-expt-of-replace-o-fin-part
     (equal (o-first-expt (replace-o-fin-part x n))
            (o-first-expt x))
     :hints (("goal" :induct t)
             (and stable-under-simplificationp
                  '(:in-theory (enable o-first-expt)))))

   (defthm o-finp-of-replace-o-fin-part
     (equal (o-finp (replace-o-fin-part x n))
            (o-finp x))
     :hints(("Goal" :in-theory (enable o-finp))))

   (local (in-theory (disable o-finp)))

   (defthm o-first-coeff-of-replace-o-fin-part
     (equal (o-first-coeff (replace-o-fin-part x n))
            (if (o-finp x)
                (nfix n)
              (o-first-coeff x)))
     :hints (("goal" :expand ((replace-o-fin-part x n))
              :do-not-induct t)
             (and stable-under-simplificationp
                  '(:in-theory (enable o-first-coeff o-finp)))))

   (defthm o-p-of-first-expt-when-o-p
     (implies (o-p x)
              (o-p (o-first-expt x)))
     :hints(("Goal" :in-theory (enable o-p))
            (and stable-under-simplificationp
                 '(:in-theory (enable o-first-expt)))))

   (defthm posp-of-first-coeff-when-o-p
     (implies (and (o-p x)
                   (not (o-finp x)))
              (posp (o-first-coeff x)))
     :hints(("Goal" :in-theory (enable o-p))
            (and stable-under-simplificationp
                 '(:in-theory (enable o-first-coeff))))
     :rule-classes :type-prescription)

   (defthm o-p-nfix
     (o-p (nfix n))
     :hints(("Goal" :in-theory (enable o-p))))

   (defthm first-<-rst-when-o-p
     (implies (and (o-p x)
                   (not (o-finp x)))
              (o< (o-first-expt (o-rst x))
                  (o-first-expt x))))

   (defthm o-p-of-o-rst
     (implies (and (o-p x)
                   (not (o-finp x)))
              (o-p (o-rst x)))
     :hints(("Goal" :in-theory (enable o-p))))

   (defthm o-p-replace-o-fin-part
     (implies (o-p x)
              (o-p (replace-o-fin-part x n)))
     :hints(("Goal" :in-theory (disable o< o-p))))

   (verify-guards replace-o-fin-part
     :hints(("Goal" :in-theory (e/d ()
                                    (replace-o-fin-part
                                     o-rst))
             :expand ((o-p x)))))

   (defthm o-finp-of-plus
     (o-finp (+ x y))
     :hints(("Goal" :in-theory (enable o-finp))))

   (defthm o-finp-of-nfix
     (o-finp (nfix x))
     :hints(("Goal" :in-theory (enable o-finp))))

   (defthm o<-when-o-finp
     (implies (o-finp x)
              (equal (o< x y)
                     (or (not (o-finp y))
                         (< x y))))
     :hints(("Goal" :in-theory (enable o<))))

   (defthm replace-o-fin-part-rel
     (implies (and (o-p x) (o-p y))
              (equal (o< (replace-o-fin-part x (+ 1 (o-fin-part x)))
                         (replace-o-fin-part y (+ 1 (o-fin-part y))))
                     (o< x y))))

   (defthm replace-o-fin-part-nonzero
     (implies (posp fp)
              (and (o< 0 (replace-o-fin-part x fp))
                   (implies (o-finp x)
                            (< 0 (replace-o-fin-part x fp))))))


   (local (in-theory (disable make-ord o-finp o-rst o-first-coeff o-first-expt
                              o-p o<)))

   (defthm o-first-expt-of-nfix
     (equal (o-first-expt (nfix n)) 0)
     :hints(("Goal" :in-theory (enable o-first-expt))))))

;; (defthm o-<-of-make-ord-case1
;;   (implies (o< a b)
;;            (o< (make-ord a 1 n)
;;                (make-ord b 1 n))))

;; (defthm o-<-of-make-ord-case2
;;   (implies (and (natp n)
;;                 (natp m)
;;                 (< n m))
;;            (o< (make-ord a 1 n)
;;                (make-ord a 1 m)))
;;   :hints(("Goal" :in-theory (enable o-finp))))


(defun indev-alist (x al)
  (if (atom x)
      nil
    (cons (cons (caar x) (indev (cdar x) al))
          (indev-alist (cdr x) al))))

(def-functional-instance
  indev-substitute-into-term
  substitute-into-term-correct
  ((unify-ev indev)
   (unify-ev-lst indev-lst)
   (unify-ev-alist indev-alist))
  :hints ((and stable-under-simplificationp
               '(:use indev-of-fncall-args))))

(defthm len-equal-0
  (equal (equal (len x) 0)
         (not (consp x))))










(defthm nthcdr-nil
  (equal (nthcdr n nil) nil))

(defthm nthcdr-open
  (implies (< (nfix n) (len x))
           (equal (nthcdr n x)
                  (cons (nth n x)
                        (nthcdr (+ 1 (nfix n)) x)))))

(defthm nthcdr-end
  (implies (<= (len x) (nfix n))
           (and (equal (consp (nthcdr n x))
                       nil)
                (equal (car (nthcdr n x))
                       nil)
                (equal (cdr (nthcdr n x))
                       nil))))

;; ;; This is basically a mutual-recursion based on flg, but we check
;; ;; o-p of the measure before we split into the separate "functions."
;; (defun induction-cp-ind (flg meas n preds subs a)
;;   (declare (xargs :measure (if (o-p (indev meas a))
;;                                (let ((o (indev meas a)))
;;                                  (if top-flg
;;                                      (if (equal 0 o)
;;                                          (+ 1 (len preds))
;;                                        (make-ord o 1 (+ 1 (len preds))))
;;                                    (if (equal 0 o)
;;                                        (nfix (- (len preds) (nfix n)))
;;                                      (make-ord o 1 (nfix (- (len preds) (nfix n)))))))
;;                              0)
;;                   :ruler-extenders :all
;;                   :hints(("Goal" :in-theory (enable o-finp)
;;                           :do-not-induct t))))
;;   (if (not (o-p (indev meas a)))
;;       (list meas preds subs a)
;;     (case flg
;;       (top
;;        ;; (top meas preds subs a)
;;        ;; Iterate over
;;        (if (indev (disjoin preds) a)
;;            (induction-cp-ind nil meas 0 preds subs a)
;;          (list meas preds subs a))
;;       (if (zp (- (len preds) (nfix n)))
;;           (list meas preds subs a)
;;         (if (indev (nth n preds) a)
;;             (let* ((aa (indev-alist (nth n subs) a))
;;                    (meas-eval (indev meas a))
;;                    (meas1-eval (indev meas aa)))
;;               (and (o-p meas1-eval)
;;                    (o< meas1-eval meas-eval)
;;                    (induction-cp-ind t meas 0 preds subs aa)))
;;           (induction-cp-ind nil meas (1+ (nfix n)) preds subs a))))))

;; (in-theory (disable nthcdr nth))

(local
 (defun induction-cp-ind (flg meas nstep nsub inductions a)
   (declare (ignorable flg meas nstep nsub inductions a)
            (xargs :measure
                   (let* ((o (indev meas a))
                          (o (if (o-p o)
                                 (replace-o-fin-part o (+ 1 (o-fin-part o)))
                               1)))
                     (case flg
                       (steps (make-ord o 2
                                        (nfix (- (len inductions) (nfix nstep)))))
                       (t     (make-ord o 1
                                        (nfix (- (len (cdr (nth nstep inductions)))
                                                 (nfix nsub)))))))
                   :ruler-extenders (cons)))

   (case flg
     (steps
      ;; Iterating over the predicates.  When we find the predicate that
      ;; applies, iterate over all its substitutions.
      (cond ((zp (- (len inductions) (nfix nstep)))              nil)
            ((indev (car (nth nstep inductions)) a)
             (induction-cp-ind 'subs meas nstep 0 inductions a))
            (t
             (induction-cp-ind 'steps meas (+ 1 (nfix nstep)) 0 inductions a))))
     (t ;; induction-hyps
      ;; Iterating over the substitutions of (nth nstep subs).
      (let* ((psubs (cdr (nth nstep inductions))))
        (if (zp (- (len psubs) (nfix nsub)))
            nil
          (let* ((aa (indev-alist (nth nsub psubs) a))
                 (meas-eval (indev meas a))
                 (meas1-eval (indev meas aa)))
            (list (and (o-p meas-eval)
                       (o-p meas1-eval)
                       (o< meas1-eval meas-eval)
                       (induction-cp-ind 'steps meas 0 0 inductions aa))
                  (induction-cp-ind 'subs meas nstep (+ 1 (nfix nsub)) inductions a)))))))))




(defthm o-p-when-theoremp
  (implies (o-p (indev meas (indev-falsify (list 'o-p meas))))
           (o-p (indev meas a)))
  :hints (("goal" :use ((:instance indev-falsify
                         (x (list 'o-p meas))
                         (a a))))))

(defthm measure-decr-when-measure-decrs-subs
  (implies (and (indev-theoremp
                 (conjoin-clauses (measure-decrs-subs meas pred subs orig-clause)))
                (< (nfix n) (len subs))
                (indev pred a)
                (pseudo-termp meas)
                (not (indev (disjoin orig-clause) a)))
           (o< (indev meas (indev-alist (nth n subs) a))
               (indev meas a)))
  :hints (("goal" :induct (nth n subs)
           :in-theory (enable nth))
          (and stable-under-simplificationp
               '(:expand ((measure-decrs-subs meas pred subs orig-clause))
                 :use ((:instance indev-falsify
                        (x (disjoin `(,@orig-clause
                                      (not ,pred)
                                      (o< ,(substitute-into-term meas (car
                                                                       subs))
                                          ,meas))))
                        (a a)))))))


(defthm measure-decr-when-measure-decrs
  (implies (and (indev-theoremp
                 (conjoin-clauses (measure-decrs meas inductions orig-clause)))
                (< (nfix nstep) (len inductions))
                (indev (car (nth nstep inductions)) a)
                (< (nfix nsub) (len (cdr (nth nstep inductions))))
                (pseudo-termp meas)
                (not (indev (disjoin orig-clause) a)))
           (o< (indev meas (indev-alist (nth nsub (cdr (nth nstep inductions))) a))
               (indev meas a)))
  :hints (("Goal" :induct (nth nstep inductions)
           :in-theory (enable nth))
          (and stable-under-simplificationp
               '(:expand ((measure-decrs meas inductions orig-clause))))))

(defthm o-p-with-clause-when-theoremp
  (implies (and (not (indev (disjoin clause) a))
                (not (o-p (indev meas a))))
           (and (not (indev (disjoin clause)
                            (indev-falsify (disjoin (Append clause (list (list 'o-p meas)))))))
                (not (o-p (indev meas
                                 (indev-falsify (disjoin (Append clause (list (list 'o-p meas))))))))))
  :hints (("goal" :use ((:instance indev-falsify
                         (x (disjoin (Append clause (list (list 'o-p meas)))))
                         (a a))))))


(defthm induction-step-right
  (implies (and (indev
                 (conjoin-clauses (induction-steps clause inductions))
                 (indev-falsify (conjoin-clauses (induction-steps clause inductions))))
                (indev (car (nth n inductions)) a)
                (not (indev (disjoin clause) a))
                (< (nfix n) (len inductions)))
           (not (indev (conjoin-clauses
                        (substitute-list-into-clause
                         (cdr (nth n inductions)) clause))
                       a)))
  :hints(("Goal" :in-theory (enable nth)
          :induct (nth n inductions))
          (and stable-under-simplificationp
               '(:expand ((induction-steps clause inductions))
                 :use ((:instance indev-falsify
                        (x (disjoin `((not (if ,(caar inductions)
                                               ,(conjoin-clauses
                                                 (substitute-list-into-clause
                                                  (cdar inductions) clause))
                                             'nil))
                                      . ,clause)))
                        (a a)))))))


(defthm indev-disjoin-substitute
  (implies (pseudo-term-listp clause)
           (iff (indev (disjoin (substitute-into-list clause subst)) a)
                (indev (substitute-into-term (disjoin clause) subst) a)))
  :hints (("goal" :induct (len clause))))




(local (defthm indev-disjoin-atom-no-bc
         (IMPLIES (NOT (CONSP X))
                  (EQUAL (INDEV (DISJOIN X) A) NIL))))

(defthm nthcdr-0
  (equal (nthcdr 0 x) x)
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm induction-cp-correct-rec-with-orig-clause
  (implies
   (and (indev-theoremp (disjoin (append clause `((o-p ,meas)))))
        (pseudo-termp meas)
        (pseudo-term-listp clause)
        (indev-theoremp (conjoin-clauses
                         (measure-decrs meas inductions clause)))
        ;; this says that the base case holds, i.e. if no induction step
        ;; condition is true then the clause is true
        (indev-theoremp (disjoin (cons (disjoin (strip-cars inductions)) clause)))
        (indev-theoremp (conjoin-clauses
                         (induction-steps clause inductions))))
   (if (eq flg 'steps)
       (implies (indev (disjoin (strip-cars (nthcdr nstep inductions))) a)
                (indev (disjoin clause) a))
     (implies (and (indev (car (nth nstep inductions)) a)
                   (not (indev (disjoin clause) a))
                   (< (nfix nstep) (len inductions)))
              (indev (conjoin-clauses (substitute-list-into-clause
                                       (nthcdr nsub (cdr (nth nstep inductions)))
                                       clause))
                     a))))
  :hints (("goal" :induct (induction-cp-ind flg meas nstep nsub inductions a)
           :in-theory (disable nth measure-decrs substitute-into-term
                               indev-alist induction-steps
                               substitute-list-into-clause
                               pseudo-termp nthcdr))
          '(:use ((:instance indev-falsify
                   (x (disjoin (cons (disjoin (strip-cars inductions)) clause)))
                   (a a))))
          (and stable-under-simplificationp
               '(:use ((:instance indev-falsify
                        (x (disjoin (cons (disjoin (strip-cars inductions)) clause)))
                        (a (indev-alist (nth nsub (cdr (nth nstep inductions))) a)))))))
  :rule-classes nil)

(defthm induction-cp-correct-rec-without-orig-clause
  (implies
   (and (indev-theoremp `(o-p ,meas))
        (pseudo-termp meas)
        (pseudo-term-listp clause)
        (indev-theoremp (conjoin-clauses
                         (measure-decrs meas inductions nil)))
        ;; this says that the base case holds, i.e. if no induction step
        ;; condition is true then the clause is true
        (indev-theoremp (disjoin (cons (disjoin (strip-cars inductions)) clause)))
        (indev-theoremp (conjoin-clauses
                         (induction-steps clause inductions))))
   (if (eq flg 'steps)
       (implies (indev (disjoin (strip-cars (nthcdr nstep inductions))) a)
                (indev (disjoin clause) a))
     (implies (and (indev (car (nth nstep inductions)) a)
                   ;; (not (indev (disjoin clause) a))
                   (< (nfix nstep) (len inductions)))
              (indev (conjoin-clauses (substitute-list-into-clause
                                       (nthcdr nsub (cdr (nth nstep inductions)))
                                       clause))
                     a))))
  :hints (("goal" :induct (induction-cp-ind flg meas nstep nsub inductions a)
           :in-theory (disable nth measure-decrs substitute-into-term
                               indev-alist induction-steps
                               substitute-list-into-clause
                               pseudo-termp nthcdr))
          '(:use ((:instance indev-falsify
                   (x (disjoin (cons (disjoin (strip-cars inductions)) clause)))
                   (a a))))
          (and stable-under-simplificationp
               '(:use ((:instance indev-falsify
                        (x (disjoin (cons (disjoin (strip-cars inductions)) clause)))
                        (a (indev-alist (nth nsub (cdr (nth nstep inductions))) a)))))))
  :rule-classes nil)



(defun induction-cp (clause hint)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (b* (((mv ok meas inductions extra-args)
        (case-match hint
          ((meas inductions . extra-args) (mv t meas inductions extra-args))
          (& (mv nil nil nil nil))))
       (apply-orig-clause (equal extra-args '(t)))
       (ok (and ok
                (pseudo-termp meas)
                (induction-step-listp inductions)))
       ((unless ok)
        (cw "bad hints~%")
        (list clause)))
    (list* `(,@(and apply-orig-clause clause)
             (o-p ,meas))
           ;; base-case
           (cons (disjoin (strip-cars inductions)) clause)
           ;; induction steps
           (append (induction-steps clause inductions)
                   (measure-decrs meas inductions (and apply-orig-clause clause))))))

(defthm disjoin-singleton
  (equal (disjoin (list x)) x)
  :hints(("Goal" :in-theory (enable disjoin))))

(defthm indev-theorem-disjoin-clause
  (implies (indev-theoremp (disjoin clause))
           (indev (disjoin clause) a))
  :hints (("goal" :use ((:instance indev-falsify
                         (x (disjoin clause)) (a a))))))

(defthm indev-theorem-disjoin-cons
  (implies (and (indev-theoremp (disjoin (cons x y)))
                (not (indev x a)))
           (indev (disjoin y) a))
  :hints (("goal" :use ((:instance indev-falsify
                         (x (disjoin (cons x y)))))
           :in-theory (disable indev-theorem-disjoin-clause))))

(defthm induction-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (indev-theoremp (conjoin-clauses (induction-cp clause hint))))
           (indev (disjoin clause) a))
  :hints (("goal" :use ((:instance induction-cp-correct-rec-with-orig-clause
                         (meas (car hint))
                         (inductions (cadr hint))
                         (flg 'steps)
                         (nstep 0))
                        (:instance induction-cp-correct-rec-without-orig-clause
                         (meas (car hint))
                         (inductions (cadr hint))
                         (flg 'steps)
                         (nstep 0))
                        (:instance indev-falsify
                         (x (disjoin (cons (disjoin (strip-cars (cadr hint))) clause)))
                         (a a)))
           :in-theory (disable measure-decrs induction-steps
                               pseudo-termp
                               pseudo-term-listp
                               pseudo-term-val-alistp
                               indev-disjoin-cons
                               indev-of-o-p-call
                               indev-of-variable
                               indev-of-quote
                               INDEV-DISJOIN-APPEND
                               INDEV-THEOREMP-DISJOIN-CONS-UNLESS-THEOREMP)
           :do-not-induct t))
  :rule-classes :clause-processor
  :otf-flg t)


(local
 (progn
   (encapsulate
     (((fib *) => *))
     (local (defun fib (x)
              (cond ((or (zp x) (eql x 1)) 1)
                    (t (+ (fib (- x 1))
                          (fib (- x 2)))))))

     (defthm fib-of-x+2
       (implies (natp x)
                (equal (fib (+ 2 x))
                       (+ (fib (+ 1 x))
                          (fib x)))))

     (defthm fib-of-0-and-1
       (and (equal (fib 0) 1)
            (equal (fib 1) 1))))


   (defthm fib-positive
     (implies (natp x)
              (< 0 (fib x)))
     :hints ('(:clause-processor
               (induction-cp
                clause
                '((nfix x) ;; measure

                  ;; induction step: when x > 1, assume true of x-1, x-2
                  (((< '1 (nfix x))     ((x . (binary-+ '-1 x)))
                                        ((x . (binary-+ '-2 x))))))))
             (and stable-under-simplificationp
                  '(:cases ((equal x 0))
                    :use ((:instance fib-of-x+2
                           (x (- x 2))))))))))

(defxdoc induction-cp
  :short "A clause processor to prove a goal by induction."
  :long "<p>Mostly not very practical, just an exercise.</p>
<p>This replicates ACL2's built-in induction principle (sec. 6.5 of Computer
Aided Reasoning: An Approach).  This clause processor should be able to do
anything that ACL2's induction can do.  However, every time this clause
processor is used to perform an induction, we must prove the associated measure
conjecture, i.e. that the induction scheme is legal.</p>

<p>Induction-cp must be given a hint object specifying the induction scheme.
This object must be a two-element list containing:
<ul>
<li>a term specifying the measure that justifies the induction,</li>
<li>a list of pairs (condition . substitutions), where condition is a term
giving the ruler of an induction step, and substitutions are a list of
 (variable . term) alists giving the substitutions for that induction step.</li>
</ul></p>

<p>For example, the following hint:
@({
 :clause-processor
    (induction-cp
     clause
     '((nfix x) ;; measure

       ;; induction step: when x > 1, assume true of x-1, x-2
       (((< '1 (nfix x))     ((x . (binary-+ '-1 x)))
                             ((x . (binary-+ '-2 x)))))

       ;; extra option: if t, weaken the measure proof obligations by
       ;; disjoining them with the original clause
       t))
 })
will cause the current goal to be attempted with a base case in for x<=1, and
an induction step for x > 1 where the property is assumed true of x-1 and
x-2.</p>")

