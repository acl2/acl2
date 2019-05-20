
; Centaur Miscellaneous Books
; Copyright (C) 2012 Centaur Technology
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
;
; Includes tweaks made by Mihir Mehta 4/2019 for a change to the
; definition of take.

(in-package "ACL2")

;; This book defines def-tr, which is similar to Greve's defminterm.  See the
;; local form at the bottom for a usage example.

; cert_param: (non-acl2r)

(include-book "std/util/bstar" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "clause-processors/generalize" :dir :system)
(local (include-book "std/lists/take" :dir :system))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/sets" :dir :system))

;; Part 1: Generic theory showing that a tail-recursive function can be defined
;; regardless of its termination, along with an induction scheme that can be
;; used when termination is assumed.

(encapsulate
  ((pf-next (st) st)
   (pf-done (st) flg)
   (pf-retval (st) res)
   (pf-diverge () fail))

  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)

  (local
   (progn

     (defun pf-next (st)
       (list (+ 1 (car st)) (not (cadr st))))

     (defun pf-done (st)
       (equal (car st) 100))

     (defun pf-retval (st)
       (- st (if (cadr st) 100 0)))

     (defun pf-diverge () (list :pf-diverge)))))


(defun pf-steps-clk (clk st)
  (declare (xargs :measure (nfix clk)
                  :hints (("goal" :in-theory
                           '(nfix zp o-p o-finp natp o<)))
                  :guard (natp clk)))
  (cond ((zp clk) nil)
        ((pf-done st)     0)
        (t (let ((res (pf-steps-clk (1- clk)
                              (pf-next st))))
             (and res (+ 1 res))))))

(local
 (defthm pf-steps-clk-equal
   (equal (equal (pf-steps-clk clk1 st)
                 (pf-steps-clk clk2 st))
          (iff (pf-steps-clk clk1 st)
               (pf-steps-clk clk2 st)))))

(defun-sk pf-terminates (st)
  (exists (clk)
          (pf-steps-clk (nfix clk) st)))

(verify-guards pf-terminates)

(local
 (defthm pf-terminates-implies-natp-pf-terminates-witness
   (implies (pf-terminates st)
            (and (integerp (pf-terminates-witness st))
                 (<= 0  (pf-terminates-witness st))))
   :rule-classes (:rewrite :type-prescription)))

(in-theory (disable pf-terminates-suff))

(local
 (progn
   (defthm pf-terminates-sufficient
     (implies (pf-steps-clk clk st)
              (pf-terminates st))
     :hints (("goal" :use pf-terminates-suff
              :in-theory (disable pf-terminates))))

   (defthm pf-terminates-when-pf-done
     (implies (pf-done st)
              (equal (pf-terminates st) 0))
     :hints (("goal" :use ((:instance pf-terminates-sufficient
                            (clk 1)))
              :in-theory (disable pf-terminates-sufficient
                                  pf-terminates-suff))))))

(defun pf-measure (st)
  (declare (xargs :guard t))
  (or (pf-terminates st) 0))

(local
 (defthm natp-of-pf-measure
   (natp (pf-measure st))
   :rule-classes (:type-prescription :rewrite)))




(encapsulate
  nil
  (local (defthm pf-steps-clk-of-next
           (implies (and (pf-steps-clk (pf-terminates-witness st) st)
                         (not (pf-done st)))
                    (equal (pf-steps-clk (pf-terminates-witness st) st)
                           (+ 1 (pf-steps-clk (pf-terminates-witness (pf-next st))
                                              (pf-next st)))))
           :hints (("goal" :use ((:instance pf-terminates-sufficient
                                  (st (pf-next st))
                                  (clk (1- (pf-terminates-witness st)))))
                    :in-theory (disable pf-terminates-sufficient)
                    :expand ((pf-steps-clk (pf-terminates-witness st) st))))))

  (local (defthm pf-terminates-implies-next
           (implies (and (pf-terminates st)
                         (not (pf-done st)))
                    (pf-terminates (pf-next st)))
           :hints (("goal" :expand ((pf-steps-clk (pf-terminates-witness st) st)
                                    (pf-terminates st))
                    :in-theory (disable pf-terminates)))))

  (local (defthm not-pf-terminates-implies-next
           (implies (and (not (pf-terminates st))
                         (not (pf-done st)))
                    (not (pf-terminates (pf-next st))))
           :hints (("goal" :expand ((pf-terminates (pf-next st))
                                    (:free (clk) (pf-steps-clk clk st)))
                    :use ((:instance pf-terminates-sufficient
                           (clk (+ 1 (pf-terminates-witness (pf-next st))))))
                    :in-theory (disable pf-terminates)))))

  (local (defthm pf-terminates-next
           (implies (not (pf-done st))
                    (iff (pf-terminates (pf-next st))
                         (pf-terminates st)))
           :hints(("Goal" :in-theory (disable pf-terminates)))))

  (defthm pf-terminates-redef
    (equal (pf-terminates st)
           (if (pf-done st)
               0
             (let ((next (pf-terminates (pf-next st))))
               (and next (1+ next)))))
    :hints (("goal" :in-theory (disable pf-terminates))
            (and stable-under-simplificationp
                 '(:in-theory (enable pf-terminates))))
    :rule-classes ((:definition :clique (pf-terminates)
                    :controller-alist ((pf-terminates t))))))


(defthm pf-measure-redef
  (equal (pf-measure st)
         (if (or (not (pf-terminates st))
                 (pf-done st))
             0
           (1+ (pf-measure (pf-next st)))))
  :rule-classes ((:definition :clique (pf-measure)
                  :controller-alist ((pf-measure t)))))

(in-theory (disable pf-measure pf-terminates))

(defun pf-run (st)
  (declare (xargs :measure (pf-measure st)))
  (mbe :logic
       (if (pf-terminates st)
           (if (pf-done st)
               (pf-retval st)
             (pf-run (pf-next st)))
         (pf-diverge))
       :exec
       (if (pf-done st)
           (pf-retval st)
         (pf-run (pf-next st)))))

(defthm pf-run-is-loop
  (equal (pf-run st)
         (if (pf-done st)
           (pf-retval st)
         (pf-run (pf-next st))))
  :rule-classes nil)

(verify-guards pf-run)






;; Part 2.  Decompose an arbitrary tail-recursive definition into done, retval,
;; next so that it fits the form above, and prove this decomposition correct.
;; Here we're working toward done-retval-next-from-body and partial-norm-body,
;; but we need a bunch of meta-level stuff to lead up.


(defun mk-list-term (terms)
  (if (atom terms)
      *nil*
    `(cons ,(car terms)
           ,(mk-list-term (cdr terms)))))

(defun get-mv-nths (start n term)
  (declare (xargs :guard (and (natp start) (natp n)
                              (pseudo-termp term))))
  (if (zp n)
      nil
    (cons `(mv-nth ',start ,term)
          (get-mv-nths (+ 1 start) (1- n) term))))



(defevaluator partial-ev partial-ev-lst
  ((if a b c)
   (cons a b)
   (mv-nth n x)
   (equal x y)
   (use-by-hint x)
   (not x)
   (use-these-hints x)))


(defun normalize-sym-alist (keys x)
  (declare (Xargs :guard (symbol-alistp x)))
  (if (atom keys)
      nil
    (let ((look (assoc (car keys) x)))
      (if look
          (cons look
                (normalize-sym-alist (cdr keys) x))
        (normalize-sym-alist (cdr keys) x)))))

(local
 (progn

   (encapsulate nil
     (defthm car-assoc-equal
       (implies (assoc-equal key x)
                (equal (car (assoc-equal key x))
                       key)))

     (local (defthm not-assoc-normalize
              (implies (not (assoc key x))
                       (not (assoc key (normalize-sym-alist keys x))))))

     (defthm assoc-normalize-sym-alist
       (equal (assoc key (normalize-sym-alist keys x))
              (and (member key keys)
                   (assoc key x)))))


   (defthm subsetp-equal-append
     (iff (subsetp-equal (append a b) c)
          (and (subsetp-equal a c)
               (subsetp-equal b c))))

   (defthm-simple-term-vars-flag
     (defthm normalize-sym-alist-eval
       (implies (and (subsetp-equal (simple-term-vars x) keys)
                     (pseudo-termp x))
                (equal (partial-ev x (normalize-sym-alist keys al))
                       (partial-ev x al)))
       :hints ('(:expand ((simple-term-vars x)))
               (and stable-under-simplificationp
                    '(:in-theory (enable partial-ev-constraint-0))))
       :flag simple-term-vars)

     (defthm normalize-sym-alist-eval-lst
       (implies (and (subsetp-equal (simple-term-vars-lst x) keys)
                     (pseudo-term-listp x))
                (equal (partial-ev-lst x (normalize-sym-alist keys al))
                       (partial-ev-lst x al)))
       :hints ('(:expand (simple-term-vars-lst x)))
       :flag simple-term-vars-lst))

   (defthm subsetp-cons
     (implies (subsetp x y)
              (subsetp x (cons a y))))

   (defthm subsetp-x-x
     (subsetp x x))

   ;; (in-theory (disable normalize-sym-alist-eval normalize-sym-alist-eval-lst))

   (defthm symbol-alistp-pairlis$
     (implies (symbol-listp vars)
              (symbol-alistp (pairlis$ vars args))))

   (local (defthm symbol-listp-impl-eqlable-listp
            (implies (symbol-listp x)
                     (eqlable-listp x))))

   (defthm alistp-normalize-sym-alist
     (implies (alistp alist)
              (alistp (normalize-sym-alist keys alist))))

   (defthm alistp-pairlis$
     (alistp (pairlis$ a b)))))

(defun clean-lambda1 (vars body args)
  (declare (xargs :guard (and (symbol-listp vars)
                              (pseudo-termp body)
                              (pseudo-term-listp args))))
  (b* ((bound-vars (remove-duplicates (simple-term-vars body)))
       (alist (pairlis$ vars args))
       (alist (normalize-sym-alist bound-vars alist)))
    (mv (strip-cars alist) body (strip-cdrs alist))))

(defun clean-lambda2 (vars body args)
  (declare (xargs :guard (and (pseudo-termp body)
                              (symbol-listp vars))))
  (if (and (equal vars args)
           (subsetp-equal (simple-term-vars body) vars))
      body
    `((lambda ,vars ,body) . ,args)))

(defun clean-lambda (vars body args)
  (declare (xargs :guard (and (symbol-listp vars)
                              (pseudo-termp body)
                              (pseudo-term-listp args))
                  :verify-guards nil))
  (b* (((mv vars body args) (clean-lambda1 vars body args)))
    (clean-lambda2 vars body args)))


(local
 (progn
   (defthm member-remove-duplicates
     (iff (member x (remove-duplicates-equal y))
          (member x y)))

   (defthm subsetp-equal-remove-duplicates
     (subsetp-equal x (remove-duplicates-equal x)))

   (defthm assoc-pairlis$
     (implies (assoc x (pairlis$ a b))
              (assoc x (pairlis$ a c))))

   (defthm assoc-pairlis$-partial-ev-lst
     (implies (assoc-equal key (pairlis$ vars args))
              (equal (assoc key (pairlis$ vars (partial-ev-lst args alist)))
                     (cons key (partial-ev (cdr (assoc key (pairlis$ vars args))) alist)))))


   (defthm pairlist-partial-ev-strip-normalize
     (equal (pairlis$
             (strip-cars (normalize-sym-alist keys (pairlis$ vars args)))
             (partial-ev-lst (strip-cdrs (normalize-sym-alist keys (pairlis$ vars args)))
                             al))
            (normalize-sym-alist keys (pairlis$ vars (partial-ev-lst args al))))
     :hints (("goal" :induct (len keys))))


   (defthm clean-lambda1-correct
     (implies (pseudo-termp body)
              (equal (mv-let (vars body args)
                       (clean-lambda1 vars body args)
                       (partial-ev body (pairlis$ vars (partial-ev-lst args alist))))
                     (partial-ev body (pairlis$ vars (partial-ev-lst args alist))))))

   (defthm-simple-term-vars-flag
     (defthm eval-under-identity-alist-containing-all-vars
       (implies (and (subsetp-equal (simple-term-vars x) keys)
                     (pseudo-termp x))
                (equal (partial-ev x (pairlis$ keys (partial-ev-lst keys al)))
                       (partial-ev x al)))
       :hints ('(:expand (simple-term-vars x))
               (and stable-under-simplificationp
                    '(:in-theory (enable partial-ev-constraint-0))))
       :flag simple-term-vars)

     (defthm eval-list-under-identity-alist-containing-all-vars
       (implies (and (subsetp-equal (simple-term-vars-lst x) keys)
                     (pseudo-term-listp x))
                (equal (partial-ev-lst x (pairlis$ keys (partial-ev-lst keys al)))
                       (partial-ev-lst x al)))
       :hints ('(:expand (simple-term-vars-lst x)))
       :flag simple-term-vars-lst))

   (defthm clean-lambda2-correct
     (implies (pseudo-termp body)
              (equal (partial-ev (clean-lambda2 vars body args) alist)
                     (partial-ev body (pairlis$ vars (partial-ev-lst args alist))))))



   (defthm len-strip-cdrs
     (equal (len (strip-cdrs x)) (len x)))

   (defthm len-strip-cars
     (equal (len (strip-cars x)) (len x)))

   (defthm symbol-listp-strip-cars-normalize-sym-alist
     (implies (symbol-listp vars)
              (symbol-listp (strip-cars (normalize-sym-alist (remove-duplicates-equal vars) al)))))

   (defthm pseudo-term-listp-strip-cdrs-normalize-sym-alist
     (implies (pseudo-term-listp args)
              (pseudo-term-listp
               (strip-cdrs (normalize-sym-alist keys (pairlis$ vars args))))))

   (defthm pseudo-termp-clean-lambda1
     (mv-let (vars body args)
       (clean-lambda1 vars1 body1 args1)
       (implies (pseudo-termp body1)
                (and (pseudo-termp body)
                     (implies (pseudo-term-listp args1)
                              (and (symbol-listp vars)
                                   (pseudo-term-listp args)
                                   (equal (len vars) (len args))))))))

   (defthm pseudo-termp-clean-lambda2
     (implies (and (pseudo-termp body)
                   (symbol-listp vars)
                   (pseudo-term-listp args)
                   (equal (len vars) (len args)))
              (pseudo-termp (clean-lambda2 vars body args))))

   (in-theory (disable clean-lambda1 clean-lambda2))

   (defthm clean-lambda-correct
     (implies (pseudo-termp body)
              (equal (partial-ev (clean-lambda vars body args) alist)
                     (partial-ev body (pairlis$ vars (partial-ev-lst args alist)))))
     :hints (("goal" :do-not-induct t)))

   (defthm pseudo-termp-clean-lambda
     (implies (and (pseudo-termp body)
                   (pseudo-term-listp args))
              (pseudo-termp (clean-lambda vars body args))))))

(verify-guards clean-lambda)

(in-theory (disable clean-lambda))

(mutual-recursion
 (defun clean-lambdas (x)
   (declare (xargs :guard (pseudo-termp x)
                   :verify-guards nil))
   (cond ((atom x) x)
         ((quotep x) x)
         (t (b* ((args (clean-lambdas-list (rest x)))
                 ((when (atom (first x)))
                  (cons (first x) args))
                 (body (clean-lambdas (third (first x)))))
              (clean-lambda (second (first x)) body args)))))
 (defun clean-lambdas-list (x)
   (declare (Xargs :guard (pseudo-term-listp x)))
   (if (atom x)
       nil
     (cons (clean-lambdas (car x))
           (clean-lambdas-list (cdr x))))))

(local
 (progn
   (flag::make-flag clean-lambdas-flag clean-lambdas
                    :flag-mapping ((clean-lambdas . term)
                                   (clean-lambdas-list . list)))


   (defthm-clean-lambdas-flag
     (defthm pseudo-termp-clean-lambdas
       (implies (pseudo-termp x)
                (pseudo-termp (clean-lambdas x)))
       :flag term
       :hints ('(:expand ((pseudo-termp x))) ))
     (defthm pseudo-term-listp-clean-lambdas-list
       (implies (pseudo-term-listp x)
                (pseudo-term-listp (clean-lambdas-list x)))
       :flag list))))

(verify-guards clean-lambdas
  :hints(("Goal" :expand (pseudo-termp x))))

(set-irrelevant-formals-ok t)

(mutual-recursion
 (defun term-ev-ind (x a)
   (b* (((when (or (atom x) (quotep x))) x)
        (arg-res (term-ev-list-ind (rest x) a))
        ((when (atom (first x))) arg-res)
        (args-ev (partial-ev-lst (rest x) a))
        (alist (pairlis$ (second (first x)) args-ev)))
     (term-ev-ind (third (first x)) alist)))

 (defun term-ev-list-ind (x a)
   (if (atom x)
       nil
     (cons (term-ev-ind (car x) a)
           (term-ev-list-ind (cdr x) a)))))

(local
 (progn
   (flag::make-flag term-ev-flag term-ev-ind
                    :flag-mapping ((term-ev-ind . term)
                                   (term-ev-list-ind . list)))

   (defthm-term-ev-flag
     (defthm clean-lambdas-correct
       (implies (pseudo-termp x)
                (equal (partial-ev (clean-lambdas x) a)
                       (partial-ev x a)))
       :flag term
       :hints ('(:expand ((pseudo-termp x)))
               (and stable-under-simplificationp
                    '(:in-theory (enable partial-ev-constraint-0)))))
     (defthm clean-lambdas-list-correct
       (implies (pseudo-term-listp x)
                (equal (partial-ev-lst (clean-lambdas-list x) a)
                       (partial-ev-lst x a)))
       :flag list))))






;; Splits the function body x into done, retval, next such that
;; (eval x al)
;; = (eval `(if ,done ,retval (,fnname . ,(get-nths arity next))) al).

(defun done-retval-next-from-body (fnname arity x)
  (declare (xargs :guard (pseudo-termp x)
                  :verify-guards nil))
  (cond ((atom x)           (mv nil *t* (or x *nil*) *nil*))
        ((quotep x)         (mv nil *t* x *nil*))
        ((equal (first x) fnname)
         (if (equal (len (rest x)) arity)
             (mv nil *nil* nil (if (= 1 arity)
                                   (car (rest x))
                                 (mk-list-term (rest x))))
           (mv "arity" nil nil nil)))
        ((eq (first x) 'if)
         (b* (((mv err then-done then-ret then-next)
               (done-retval-next-from-body fnname arity (third x)))
              ((when err) (mv err nil nil nil))
              ((mv err else-done else-ret else-next)
               (done-retval-next-from-body fnname arity (fourth x)))
              ((when err) (mv err nil nil nil))
              (test (second x))
              (done (if (equal then-done else-done)
                        then-done
                      `(if ,test ,then-done ,else-done)))
              ;;(- (and (equal done *t*)
              ;;        (or then-next else-next)
              ;;        (er hard 'done-retval-next-from-body
              ;;            "Mismatch: done is t but next is non-nil")))
              ;;(- (and (equal done *nil*)
              ;;        (or then-ret else-ret)
              ;;        (er hard 'done-retval-next-from-body
              ;;            "Mismatch: done is nil but ret is non-nil")))
              (ret (cond ((equal done *nil*) *nil*)
                         ((equal then-done *nil*) else-ret)
                         ((equal else-done *nil*) then-ret)
                         (t `(if ,test ,then-ret ,else-ret))))
              (next (cond ((equal done *t*) *nil*)
                          ((equal then-done *t*) else-next)
                          ((equal else-done *t*) then-next)
                          (t `(if ,test ,then-next ,else-next)))))
           (mv nil done ret next)))
        ((atom (first x))   (mv nil *t* x *nil*))
        (t ;; lambda
         (b* ((vars (second (first x)))
              (body (third (first x)))
              (args (rest x))
              ((mv err body-done body-ret body-next)
               (done-retval-next-from-body fnname arity body))
              ((when err) (mv err nil nil nil))
              ;;(- (and (equal body-done *t*)
              ;;        body-next
              ;;        (er hard 'done-retval-next-from-body
              ;;            "Mismatch: done is t but next is non-nil")))
              ;;(- (and (equal body-done *nil*)
              ;;        body-ret
              ;;        (er hard 'done-retval-next-from-body
              ;;            "Mismatch: done is nil but ret is non-nil")))
              )
           (mv nil
               (cond ((equal body-done *t*) *t*)
                     ((equal body-done *nil*) *nil*)
                     (t (clean-lambda vars body-done args)))
               (cond ((equal body-done *nil*) *nil*)
                     (t (clean-lambda vars body-ret args)))
               (cond ((equal body-done *t*) *nil*)
                     (t (clean-lambda vars body-next args))))))))

(defun done-retval-next-from-body-ind (fnname x al)
  (declare (ignorable al))
  (cond ((atom x)           nil)
        ((quotep x)         nil)
        ((eq (first x) fnname) nil)
        ((eq (first x) 'if)
         (list (done-retval-next-from-body-ind fnname (third x) al)
               (done-retval-next-from-body-ind fnname (fourth x) al)))
        ((atom (first x))   nil)
        (t ;; lambda
         (b* ((vars (second (first x)))
              (body (third (first x)))
              (args (rest x)))
           (done-retval-next-from-body-ind
            fnname body
            (pairlis$ vars
                      (partial-ev-lst args al)))))))


(local
 (progn
   (defthm pseudo-termp-mk-list-term
     (implies (pseudo-term-listp x)
              (pseudo-termp (mk-list-term x))))



   (defthm pseudo-termp-done-retval-next-from-body
     (implies
      (pseudo-termp x)
      (and (pseudo-termp (mv-nth 1 (done-retval-next-from-body fname arity x)))
           (pseudo-termp (mv-nth 2 (done-retval-next-from-body fname arity x)))
           (pseudo-termp (mv-nth 3 (done-retval-next-from-body fname arity x)))))
     :hints (("goal" :induct (done-retval-next-from-body-ind fname x nil)
              :in-theory (disable done-retval-next-from-body default-cdr
                                  default-car default-+-1
                                  default-+-2 symbol-listp not length len
                                  mk-list-term
                                  (:type-prescription pseudo-termp)
                                  (:type-prescription pseudo-term-listp))
              :expand ((:free (fnname arity)
                        (done-retval-next-from-body fnname arity x))))
             (and stable-under-simplificationp
                  '(:expand ((pseudo-termp x))))))



   (local
    (encapsulate nil
      (local (defthm car-nthcdr
               (equal (car (nthcdr n x))
                      (mv-nth n x))
               :hints(("Goal" :in-theory (enable nthcdr mv-nth)))))
      (local (defthm cdr-nthcdr
               (equal (cdr (nthcdr n x))
                      (nthcdr n (cdr x)))
               :hints(("Goal" :in-theory (enable nthcdr mv-nth)))))
      (defthm get-mv-nths-correct
        (implies (and (natp start) (natp n))
                 (equal (partial-ev-lst (get-mv-nths start n term) al)
                        (take n (nthcdr start (partial-ev term al)))))
        :hints(("Goal" :in-theory (enable take nthcdr)
                :induct (get-mv-nths start n term)
                :expand ((:free (x) (nthcdr (+ 1 start) x))))))))


   (defthm partial-ev-constraint-0-rewrite
     (implies
      (and (consp x)
           (syntaxp (and (not (equal a ''nil))
                         (equal (car x) 'cons)
                         (equal (cadr x) 'fnname)))
           (not (equal (car x) 'quote)))
      (equal
       (partial-ev x a)
       (partial-ev (cons (car x)
                         (kwote-lst (partial-ev-lst (cdr x) a)))
                   nil)))
     :hints
     (("goal" :in-theory (enable partial-ev-constraint-0))))

   (defthm partial-ev-mk-list-term
     (equal (partial-ev (mk-list-term x) al)
            (partial-ev-lst x al)))

   (defthm partial-ev-lst-type
     (true-listp (partial-ev-lst x al))
     :hints (("goal" :induct (len x)))
     :rule-classes :type-prescription)

   (defthm partial-ev-lst-len
     (equal (len (partial-ev-lst x al))
            (len x))
     :hints (("goal" :induct (len x))))

   (defthmd partial-ev-lst-when-len-1
     (implies (equal (len x) 1)
              (equal (partial-ev-lst x al)
                     (list (partial-ev (car x) al))))
     :hints (("goal" :expand ((len x)
                              (len (cdr x))))))


   (encapsulate nil
     (local (in-theory (e/d (partial-ev-lst-when-len-1)
                            (default-car default-cdr mv-nth-cons-meta
                              len mk-list-term kwote-lst get-mv-nths
                              pairlis$ true-listp
                              done-retval-next-from-body
                              partial-ev-constraint-10
                              partial-ev-constraint-9
                              symbol-listp pseudo-termp
                              (:type-prescription kwote-lst)
                              (:type-prescription pseudo-termp)
                              (:type-prescription pseudo-term-listp)))))
     (defthm done-retval-next-from-body-correct
       (b* (((mv err done ret next)
             (done-retval-next-from-body fnname arity x)))
         (implies (and (not err)
                       (not (eq fnname 'quote))
                       (pseudo-termp x)
                       (natp arity))
                  (equal (partial-ev
                          `(if ,done
                               ,ret
                             ((lambda (mv)
                                (,fnname . ,(if (equal arity 1)
                                                '(mv)
                                              (get-mv-nths 0 arity 'mv))))
                              ,next))
                          al)
                         (partial-ev x al))))
       :hints (("goal" :induct (done-retval-next-from-body-ind
                                fnname x al)
                :expand ((:free (fnname arity)
                          (done-retval-next-from-body fnname arity x))
                         (:free (a b c)
                          (pairlis$ (cons a b) c))
                         (pseudo-termp x))
                :do-not '(generalize fertilize eliminate-destructors))
               (and stable-under-simplificationp
                    '(:in-theory (enable partial-ev-constraint-0))))
       :rule-classes nil))))

(verify-guards mk-list-term)
(verify-guards done-retval-next-from-body)



(defun partial-norm-body (fnname formals x donefn retfn nextfn)
  (declare (xargs :guard (pseudo-termp x)))
  (b* ((arity (len formals))
       ((mv err done ret next)
        (done-retval-next-from-body fnname arity x))
       ((when err) (mv err x nil)))
    (mv nil `(if (,donefn . ,formals)
                 (,retfn . ,formals)
               ((lambda (mv)
                  (,fnname . ,(if (equal arity 1)
                                  '(mv)
                                (get-mv-nths 0 arity 'mv))))
                (,nextfn . ,formals)))
        `(((not (use-by-hint ',donefn))
           (equal (,donefn . ,formals) ,done))
          ((not (use-by-hint ',retfn))
           (equal (,retfn . ,formals) ,ret))
          ((not (use-by-hint ',nextfn))
           (equal (,nextfn . ,formals) ,next))))))

(local
 (progn
   (def-join-thms partial-ev)



   (defthm partial-norm-body-correct
     (b* (((mv & term clauses)
           (partial-norm-body fnname formals x
                              donefn retfn
                              nextfn)))
       (implies (and (pseudo-termp x)
                     (not (eq fnname 'quote))
                     (partial-ev (conjoin-clauses clauses) al))
                (equal (partial-ev term al)
                       (partial-ev x al))))
     :hints (("goal" :use ((:instance done-retval-next-from-body-correct
                            (arity (len formals))))
              :in-theory (e/d (use-by-hint)
                              (done-retval-next-from-body
                               kwote-lst default-car default-cdr
                               pseudo-termp))
              :do-not-induct t))
     :otf-flg t)

   (defthm pseudo-term-listp-get-mv-nths
     (implies (pseudo-termp term)
              (pseudo-term-listp (get-mv-nths start by term))))))



(defun tr-decomp-clause-proc (clause hints)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (b* (((unless (equal (len hints) 6))
        (cw "wrong shape of clause proc hints~%")
        (list clause))
       ((list fn formals body donefn retfn nextfn) hints)
       ((unless (and (not (eq fn 'quote))
                     (pseudo-termp body)
                     ;;(symbolp donefn)
                     (not (eq donefn 'quote))
                     ;;(symbolp retfn)
                     (not (eq retfn 'quote))
                     ;;(symbolp nextfn)
                     (not (eq nextfn 'quote))))
        (cw "wrong types of clause proc hints~%")
        (list clause))
       ((mv err new-body clauses)
        (partial-norm-body fn formals body donefn retfn nextfn))
       ((when err) (cw err) (list clause)))
    (cons (replace-subterms-list
           clause (list (cons body new-body)))
          clauses)))

(defun partial-ev-equal-term-alistp (x a)
  (if (atom x)
      t
    (and (equal (partial-ev (caar x) a)
                (partial-ev (cdar x) a))
         (partial-ev-equal-term-alistp (cdr x) a))))

(local
 (progn
   (defthm assoc-in-equal-term-alistp
     (implies (and (partial-ev-equal-term-alistp alist a)
                   (assoc-equal x alist))
              (equal (partial-ev (cdr (assoc-equal x alist)) a)
                     (partial-ev x a))))

   (defthm-replace-subterms-flag
     (defthm replace-subterms-when-equal-term-alists
       (implies (partial-ev-equal-term-alistp alist al)
                (equal (partial-ev (replace-subterms x alist) al)
                       (partial-ev x al)))
       :flag term
       :hints ((and stable-under-simplificationp
                    '(:in-theory (enable partial-ev-constraint-0)
                      :expand ((replace-subterms x alist))))))
     (defthm replace-subterms-when-equal-term-alists-list
       (implies (partial-ev-equal-term-alistp alist al)
                (equal (partial-ev-lst (replace-subterms-list x alist) al)
                       (partial-ev-lst x al)))
       :hints ('(:expand ((replace-subterms-list x alist))))
       :flag list))



   (defthm partial-ev-of-disjoin
     (iff (partial-ev (disjoin x) a)
          (or-list (partial-ev-lst x a)))
     :hints (("goal" :induct (len x))))))

(defthm tr-decomp-clause-proc-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (partial-ev (conjoin-clauses
                           (tr-decomp-clause-proc clause hints))
                          a))
           (partial-ev (disjoin clause) a))
  :hints (("goal" :do-not-induct t
           :in-theory (disable partial-norm-body)))
  :otf-flg t
  :rule-classes :clause-processor)


;; Functional substitution into a recursive structure
;; (eval (fsubst-into-tail-recursion basefn tailfn fnname formals extras x) al)
;; = (eval `(if ,done ,basefn (,tailfn . ,(get-nths arity next))) al)
;; (approximately) where done and next are from done-retval-next-from-body.
;; base -- term to return in the base case, may use the extras
;; tailfn -- function to apply on tail recursive calls
;; fnname -- name of the original function
;; formals -- original formals of the recursion
;; extras -- additional formals used by the new function
;; returns: body, recp -- where recp says whether there was a tail call
(defun fsubst-into-tail-recursion (base tailfn fnname extras x)
  (declare (xargs :guard (and (pseudo-termp x)
                              (symbol-listp extras))))
  (cond ((or (atom x)
             (eq (car x) 'quote)
             (and (not (consp (car x)))
                  (not (eq (car x) 'if))
                  (not (equal (car x) fnname))))
         (mv base nil))
        ((equal (first x) fnname)
         (mv `(,tailfn ,@extras . ,(cdr x)) t))
        ((eq (first x) 'if)
         (b* (((mv then-body then-recp)
               (fsubst-into-tail-recursion base tailfn fnname extras
                                           (third x)))
              ((mv else-body else-recp)
               (fsubst-into-tail-recursion base tailfn fnname extras
                                           (fourth x)))
              (test (second x))
              ((when (and (not then-recp)
                          (not else-recp)))
               (mv base nil)))
           (mv `(if ,test ,then-body ,else-body) t)))
        (t
         ;; lambda.  substitute into the body.
         (b* (((mv body recp)
               (fsubst-into-tail-recursion
                base tailfn fnname extras (third (car x))))
              ((when (not recp)) (mv base nil)))
           (mv `((lambda ,(append extras (second (car x)))
                   ,body)
                 ,@extras . ,(cdr x))
               t)))))


(local
 (progn
   (defun has-tail-call (fnname x)
     (declare (xargs :guard (pseudo-termp x)))
     (cond ((or (atom x)
                (eq (car x) 'quote)
                (and (not (consp (car x)))
                     (not (eq (car x) 'if))
                     (not (equal (car x) fnname))))
            nil)
           ((equal (first x) fnname) t)
           ((eq (first x) 'if)
            (or (has-tail-call fnname (third x))
                (has-tail-call fnname (fourth x))))
           (t (has-tail-call fnname (third (car x))))))

   (defthm fsubst-into-tail-recursion-is-has-tail-call
     (equal (mv-nth 1 (fsubst-into-tail-recursion base tailfn fnname extras x))
            (has-tail-call fnname x)))

   (defun fsubst-into-tail-recursion-body (base tailfn fnname extras x)
     (declare (xargs :guard (and (pseudo-termp x)
                                 (symbol-listp extras))))
     (cond ((not (has-tail-call fnname x))
            base)
           ((equal (first x) fnname)
            `(,tailfn ,@extras . ,(cdr x)))
           ((eq (first x) 'if)
            (b* ((then-body
                  (fsubst-into-tail-recursion-body base tailfn fnname extras
                                                   (third x)))
                 (else-body
                  (fsubst-into-tail-recursion-body base tailfn fnname extras
                                                   (fourth x)))
                 (test (second x)))
              `(if ,test ,then-body ,else-body)))
           (t
            ;; lambda.  substitute into the body.
            (b* ((body
                  (fsubst-into-tail-recursion-body
                   base tailfn fnname extras (third (car x)))))
              `((lambda ,(append extras (second (car x)))
                  ,body)
                ,@extras . ,(cdr x))))))

   (defthm fsubst-into-tail-recursion-is-fsubst-body
     (equal (mv-nth 0 (fsubst-into-tail-recursion base tailfn fnname extras x))
            (fsubst-into-tail-recursion-body base tailfn fnname extras x)))

   (in-theory (disable fsubst-into-tail-recursion))

   (defun fsubst-into-tail-ind (fnname extras x al)
     (declare (ignorable al))
     (cond ((atom x)           nil)
           ((quotep x)         nil)
           ((eq (first x) fnname) nil)
           ((eq (first x) 'if)
            (list (fsubst-into-tail-ind fnname extras (third x) al)
                  (fsubst-into-tail-ind fnname extras (fourth x) al)))
           ((atom (first x))   nil)
           (t ;; lambda
            (b* ((vars (second (first x)))
                 (body (third (first x)))
                 (args (rest x)))
              (fsubst-into-tail-ind
               fnname extras body
               (pairlis$ (append extras vars)
                         (partial-ev-lst (append extras args) al)))))))

   (defthm-simple-term-vars-flag
     (defthm eval-under-identity-alist-containing-all-vars1
       (implies (and (subsetp-equal (simple-term-vars x) keys)
                     (pseudo-termp x))
                (equal (partial-ev x (pairlis$ (append keys vars)
                                               (partial-ev-lst (append keys vals) al)))
                       (partial-ev x al)))
       :hints ('(:expand (simple-term-vars x))
               (and stable-under-simplificationp
                    '(:in-theory (enable partial-ev-constraint-0))))
       :flag simple-term-vars)

     (defthm eval-list-under-identity-alist-containing-all-vars1
       (implies (and (subsetp-equal (simple-term-vars-lst x) keys)
                     (pseudo-term-listp x))
                (equal (partial-ev-lst x (pairlis$ (append keys vars)
                                                   (partial-ev-lst (append keys vals) al)))
                       (partial-ev-lst x al)))
       :hints ('(:expand (simple-term-vars-lst x)))
       :flag simple-term-vars-lst))))


;; clause processor for the terminates-redef proof.
;; clause is of the form:
;; `((equal (,terminates . ,formals)
;;         ,(fsubst-into-tail-recursion-body
;;            ''0
;;            `(lambda ,formals
;;               ((lambda (termp) (if termp (binary-+ '1 termp) 'nil))
;;                (terminates . ,formals)))
;;             fn
;;             nil fn-body)
;; We produce clauses:
;;  ((not (use-these-hints '(:functional-instance ...)))
;;   (equal (terminates . formals)
;;          (if (,done . ,formals)
;;              '0
;;            ((lambda (mv)
;;              ((lambda ,formals
;;                ((lambda (termp) (if termp (binary-+ '1 termp) 'nil))
;;                  (terminates . ,formals)))
;;               . ,(get-mv-nths 0 (len formals) 'mv)))
;;             (,next . ,formals)))))
;;
;;  ((not (use-by-hint ',done))
;;   (equal (,done . ,formals) ,done-term)
;;
;;  ((not (use-by-hint ',next))
;;   (equal (,next . ,formals) ,next-term))


;;;; collects all used vars, not just free ones
;;(mutual-recursion
;; (defun used-vars (x)
;;   (declare (Xargs :guard (pseudo-termp x)))
;;   (cond ((atom x) (list x))
;;         ((eq (car x) 'quote) nil)
;;         ((consp (car x))
;;          (append (used-vars (third (car x)))
;;                  (used-vars-list (cdr x))))
;;         (t (used-vars-list (cdr x)))))

;; (defun used-vars-list (x)
;;   (declare (Xargs :guard (pseudo-term-listp x)))
;;   (if (atom x)
;;       nil
;;     (append (used-vars (car x))
;;             (used-vars-list (cdr x))))))

;;(local (defthm member-append
;;         (iff (member a (append b c))
;;              (or (member a b)
;;                  (member a c)))))

;;(defthm intersectp-append
;;  (iff (intersectp a (append b c))
;;       (or (intersectp a b)
;;           (intersectp a c))))

;;(defthm used-vars-of-clean-lambdas
;;  (subsetp-equal (used-vars (clean-lambda vars body args))
;;                 (append (used-vars body)
;;                         (used-vars-list args)))
;;  :hints(("Goal" :in-theory (enable clean-lambda clean-lambda1 clean-lambda2))))

;;(defthm done-retval-next-from-body-used-vars
;;  (b* (((mv err done retval next)
;;        (done-retval-next-from-body fn arity x)))
;;    (implies (not err)
;;             (and (subsetp-equal (used-vars done) (used-vars x))
;;                  (subsetp-equal (used-vars retval) (used-vars x))
;;                  (subsetp-equal (used-vars next) (used-vars x))))))

(local
 (progn
   (defthm-simple-term-vars-flag
     (defthm eval-when-simple-term-vars-empty
       (implies (and (syntaxp (not (equal al ''nil)))
                     (atom (simple-term-vars x)))
                (equal (partial-ev x al)
                       (partial-ev x nil)))
       :hints ('(:expand (simple-term-vars x))
               (and stable-under-simplificationp
                    '(:in-theory (enable partial-ev-constraint-0
                                         partial-ev-constraint-6)
                      :use ((:instance partial-ev-constraint-0 (a nil))))))
       :flag simple-term-vars)

     (defthm eval-list-when-simple-term-vars-empty
       (implies (and (syntaxp (not (equal al ''nil)))
                     (atom (simple-term-vars-lst x)))
                (equal (partial-ev-lst x al)
                       (partial-ev-lst x nil)))
       :hints ('(:expand (simple-term-vars-lst x)))
       :flag simple-term-vars-lst))

   (defthm len-is-0-rw
     (equal (equal (len x) 0)
            (atom x)))

   (defthm kwote-lst-of-partial-ev-lst-when-len-1
     (implies (equal (len x) 1)
              (equal (kwote-lst (partial-ev-lst x al))
                     (list (list 'quote (partial-ev (car x) al))))))

   (defthm fsubst-into-tail-recursion-body-when-no-tail-call
     (implies (not (has-tail-call fnname x))
              (equal (fsubst-into-tail-recursion-body
                      base tailfn fnname extras x)
                     base)))

   (defthm done-retval-next-from-body-when-no-tail-call
     (implies (and (not (has-tail-call fnname x))
                   (not (mv-nth 0 (done-retval-next-from-body fnname arity x))))
              (equal (mv-nth 1 (done-retval-next-from-body fnname arity x))
                     *t*)))

   (encapsulate nil
     (local (in-theory (disable fsubst-into-tail-recursion-body
                                done-retval-next-from-body
                                partial-ev-constraint-11
                                partial-ev-constraint-10
                                partial-ev-constraint-9
                                partial-ev-constraint-13
                                partial-ev-constraint-12
                                partial-ev-constraint-0-rewrite
                                default-car default-cdr len
                                append-to-nil
                                default-coerce-1
                                default-coerce-2
                                not
                                (:type-prescription pseudo-termp)
                                (:type-prescription simple-term-vars)
                                (:type-prescription has-tail-call)
                                (:type-prescription pseudo-term-listp)
                                get-mv-nths
                                symbol-listp
                                has-tail-call
                                (:type-prescription
                                 fsubst-into-tail-recursion-body))))

     (defthm fsubst-into-tail-recursion-correct
       (b* (((mv err done ?ret next)
             (done-retval-next-from-body fnname arity x))
            (new-body (fsubst-into-tail-recursion-body base tailfn fnname extras
                                                       x)))
         (implies (and (not err)
                       (not (eq fnname 'quote))
                       (not (eq tailfn 'quote))
                       (pseudo-termp x)
                       (natp arity)
                       (not (simple-term-vars base))
                       (equal extras nil)
                       (pseudo-termp base))
                  (equal (partial-ev new-body al)
                         (partial-ev `(if ,done
                                          ,base
                                        ((lambda (mv)
                                           (,tailfn ,@extras
                                                    . ,(if (equal arity 1)
                                                           '(mv)
                                                         (get-mv-nths 0 arity
                                                                      'mv))))
                                         ,next))
                                     al))))
       :hints (("goal" :induct (fsubst-into-tail-ind fnname extras x al)
                :do-not-induct t)
               '(:cases ((has-tail-call fnname x)))
               (and stable-under-simplificationp
                    '(:expand ((:free (fnname arity) (done-retval-next-from-body fnname arity x))
                               (:free (base tailfn fnname)
                                (fsubst-into-tail-recursion-body base tailfn fnname nil
                                                                 x)))))
               (and stable-under-simplificationp
                    '(:in-theory (e/d (partial-ev-constraint-0))))
               (and stable-under-simplificationp
                    '(:in-theory (enable has-tail-call))))))))





(defun terminates-redef-cp (clause hints)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (b* (((unless (= (len hints) 7))
        (er hard? 'terminates-redef-cp "wrong number of hints")
        (list clause))
       ((list body formals terminates-fn done-fn next-fn fn finst-hint) hints)
       ((unless (and (pseudo-termp body)
                     (symbol-listp formals)
                     (symbolp terminates-fn) (not (eq terminates-fn 'quote))
                     (symbolp done-fn) (not (eq done-fn 'quote))
                     (symbolp next-fn) (not (eq next-fn 'quote))
                     (symbolp fn) (not (eq fn 'quote))))
        (er hard? 'terminates-redef-cp "bad hints")
        (list clause))
       (term-lambda
        `(lambda ,formals
           ((lambda (termp)
              (if termp (binary-+ '1 termp) 'nil))
            (,terminates-fn . ,formals))))
       ((mv termp-body &)
        (fsubst-into-tail-recursion ''0 term-lambda fn nil body))
       ((mv err done & next)
        (done-retval-next-from-body fn (len formals) body))
       ((when err)
        (er hard? 'terminates-redef-cp err)
        (list clause))
       (clause-should-be `((equal (,terminates-fn . ,formals) ,termp-body)))
       ((unless (equal clause clause-should-be))
        (er hard? 'terminates-redef-cp "bad clause: ~x0~%should be:~%~x1~%"
            clause clause-should-be)
        (list clause)))
    (list `((not (use-these-hints ',finst-hint))
            (equal (,terminates-fn . ,formals)
                   (if (,done-fn . ,formals)
                       '0
                     ((lambda (mv)
                        (,term-lambda
                         . ,(if (equal (len formals) 1)
                                '(mv)
                              (get-mv-nths 0 (len formals) 'mv))))
                      (,next-fn . ,formals)))))
          `((not (use-by-hint ',next-fn))
            (equal (,next-fn . ,formals)
                   ,next))
          `((not (use-by-hint ',done-fn))
            (equal (,done-fn . ,formals)
                   ,done)))))


(defthm terminates-redef-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (partial-ev (conjoin-clauses
                             (terminates-redef-cp clause hints))
                            a))
           (partial-ev (disjoin clause) a))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (use-by-hint use-these-hints)
                           ( done-retval-next-from-body
                             has-tail-call
                             fsubst-into-tail-recursion-body
                             default-car default-cdr))))
  :rule-classes :clause-processor)



(defun measure-redef-cp (clause hints)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (b* (((unless (= (len hints) 8))
        (er hard? 'measure-redef-cp "wrong number of hints")
        (list clause))
       ((list body formals measure-fn terminates-fn done-fn next-fn fn finst-hint) hints)
       ((unless (and (pseudo-termp body)
                     (symbol-listp formals)
                     (symbolp measure-fn) (not (eq measure-fn 'quote))
                     (symbolp terminates-fn) (not (eq terminates-fn 'quote))
                     (symbolp done-fn) (not (eq done-fn 'quote))
                     (symbolp next-fn) (not (eq next-fn 'quote))
                     (symbolp fn) (not (eq fn 'quote))))
        (er hard? 'measure-redef-cp "bad hints")
        (list clause))
       (measure-lambda
        `(lambda ,formals
           (binary-+ '1 (,measure-fn . ,formals))))
       ((mv measure-body &)
        (fsubst-into-tail-recursion ''0 measure-lambda fn nil body))
       ((mv err done & next)
        (done-retval-next-from-body fn (len formals) body))
       ((when err)
        (er hard? 'measure-redef-cp err)
        (list clause))
       (clause-should-be `((equal (,measure-fn . ,formals)
                                  (if (,terminates-fn . ,formals)
                                      ,measure-body
                                    '0))))
       ((unless (equal clause clause-should-be))
        (er hard? 'measure-redef-cp "bad clause: ~x0~%should be:~%~x1~%"
            clause clause-should-be)
        (list clause)))
    (list `((not (use-these-hints ',finst-hint))
            (equal (,measure-fn . ,formals)
                   (if (,terminates-fn . ,formals)
                       (if (,done-fn . ,formals)
                           '0
                         ((lambda (mv)
                            (,measure-lambda
                             . ,(if (equal (len formals) 1)
                                    '(mv)
                                  (get-mv-nths 0 (len formals) 'mv))))
                          (,next-fn . ,formals)))
                     '0)))
          `((not (use-by-hint ',next-fn))
            (equal (,next-fn . ,formals)
                   ,next))
          `((not (use-by-hint ',done-fn))
            (equal (,done-fn . ,formals)
                   ,done)))))

(defthm measure-redef-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (partial-ev (conjoin-clauses
                             (measure-redef-cp clause hints))
                            a))
           (partial-ev (disjoin clause) a))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (use-by-hint use-these-hints)
                           (done-retval-next-from-body
                            has-tail-call
                            fsubst-into-tail-recursion-body
                            default-car default-cdr))))
  :otf-flg t
  :rule-classes :clause-processor)





(defun subset-mask (subset lst)
  (declare (xargs :guard (eqlable-listp subset)))
  (if (atom lst)
      nil
    (cons (if (member (car lst) subset) t nil)
          (subset-mask subset (cdr lst)))))


(defun dtr-sym (fn rest)
  (declare (xargs :guard (and (symbolp fn) (stringp rest))))
  (intern-in-package-of-symbol
   (concatenate 'string (symbol-name fn) rest)
   fn))

;; produces an alist mapping each keyword to its arg, and puts the
;; non-keyword/value elements into a separate list
(defun extract-keyword-alist (lst)
  (if (or (atom lst) (atom (cdr lst)))
      nil
    (if (keywordp (car lst))
        (cons (cons (car lst) (cadr lst))
              (extract-keyword-alist (cddr lst)))
      (extract-keyword-alist (cdr lst)))))

(defun remove-keyword-pairs (lst)
  (if (atom lst)
      nil
    (if (and (consp (cdr lst))
             (keywordp (car lst)))
        (remove-keyword-pairs (cddr lst))
      (cons (car lst) (remove-keyword-pairs (cdr lst))))))

(defun mv-binding-list (n formals obj)
  (if (atom formals)
      nil
    (cons `(,(car formals) (mv-nth ,n ,obj))
          (mv-binding-list (1+ n) (cdr formals) obj))))


(defun denormalize-thm-fn (fn thmname rest world)
  (b* ((unnorm-body (getprop fn 'unnormalized-body nil 'current-acl2-world
                             world))
       (formals (getprop fn 'formals nil 'current-acl2-world world)))
    `(defthm ,thmname
       (equal (,fn . ,formals)
              ,unnorm-body)
       :hints (("goal" :by ,fn))
       . ,rest)))

(defun def-tr-fn (fn formals decl-body state)
  (declare (xargs :mode :program :stobjs state))
  (flet ((bind (formals obj body)
               (if (< 1 (len formals))
                   `(mv-let ,formals ,obj
                      ,body)
                 `(let ((,(car formals) ,obj))
                    ,body)))
         (fget (formals) (if (< 1 (len formals))
                             `(mv . ,formals)
                           (car formals))))
    (b* ((world (w state))
         (keyal (extract-keyword-alist decl-body))
         (decl-body (remove-keyword-pairs decl-body))
         (tuple (list (list* fn formals decl-body)))
         ((er (list (list fn formals ?doc ?decls orig-body)))
          (chk-defuns-tuples tuple nil 'def-tr-fn world state))
         ;; Using chk-acceptable-defuns will fail if we're doing this
         ;; redundantly and redefinition is disallowed.  So we temporarily set
         ;; the ld-redefinition-action and then set it back to its original
         ;; value.
         (redef-action (ld-redefinition-action state))
         ((er &) (set-ld-redefinition-action '(:doit! . :overwrite) state))
         ((er (list & ;; 'chk-acceptable-defuns
                    & ;; fn names
                    & ;; fn formals
                    ?docs
                    & ;; pairs?
                    (list ?guard)
                    & ;; measures
                    & ;; ruler-extenders
                    & ;; measure-p
                    & ;; well-founded relation
                    ?hints
                    ?guard-hints
                    ?std-hints ;; ?
                    ?otf-flgs
                    (list body)
                    symbol-class ;; symbol-class
                    & ;; normalizeps
                    & ;; reclassifying
                    & ;; world
                    non-execp
                    guard-debug
                    ?measure-debug
                    ?split-types-terms
                    ?lambda$-stuff
                    guard-simplify))
          (chk-acceptable-defuns tuple 'def-tr-fn world state))
         ((er &) (set-ld-redefinition-action redef-action state))
         (- (cw "symbol-class: ~x0~%" symbol-class))
         ((mv err done-term ret-term next-term)
          (done-retval-next-from-body fn (len formals) body))
         ((when err)
          (mv "wrong number of formals" nil state))
         (verify-guardsp (eq symbol-class :common-lisp-compliant))
         (diverge (cdr (assoc :diverge keyal)))
         (done (dtr-sym fn "-DONE"))
         (ret  (dtr-sym fn "-RET"))
         (next (dtr-sym fn "-NEXT"))
         (steps-clk  (dtr-sym fn "-STEPS"))
         (terminates (dtr-sym fn "-TERMINATES"))
         (terminates-witness (dtr-sym fn "-TERMINATES-WITNESS"))
         (terminates-suff (dtr-sym terminates "-SUFF"))
         (terminates-sufficient (dtr-sym terminates "-SUFFICIENT"))
         (measure    (dtr-sym fn "-MEASURE"))
         (controllers (or (cdr (assoc :controllers keyal))
                          (subset-mask (all-vars done-term)
                                       formals)))
         (terminates-lambda
          `(lambda ,formals
             ((lambda (termp)
                (if termp (binary-+ '1 termp) 'nil))
              (,terminates . ,formals))))
         (measure-lambda
          `(lambda ,formals
             (binary-+ '1 (,measure . ,formals))))
         (fn-body `(if (,terminates . ,formals)
                       ,orig-body
                     ,diverge))
         (simp-body `(if (,terminates . ,formals)
                         (if (,done . ,formals)
                             (,ret . ,formals)
                           ,(bind formals
                                  `(,next . ,formals)
                                  `(,fn . ,formals)))
                       ,diverge))
         (func-inst `((pf-next       (lambda (st) ,(bind formals 'st `(,next . ,formals))))
                      (pf-done       (lambda (st) ,(bind formals 'st `(,done . ,formals))))
                      (pf-retval     (lambda (st) ,(bind formals 'st `(,ret . ,formals))))
                      (pf-diverge    (lambda ()   ,diverge))
                      (pf-steps-clk
                       (lambda (clk st) ,(bind formals 'st `(,steps-clk clk . ,formals))))
                      (pf-terminates
                       (lambda (st) ,(bind formals 'st `(,terminates . ,formals))))
                      (pf-terminates-witness
                       (lambda (st) ,(bind formals 'st `(,terminates-witness . ,formals))))
                      (pf-measure
                       (lambda (st) ,(bind formals 'st `(,measure . ,formals)))))))
      (value
       `(encapsulate
          nil
          (set-ignore-ok t)
          (set-irrelevant-formals-ok t)

          (defun-nx ,done ,formals
            ,done-term)

          (defund-nx ,ret ,formals
            ,ret-term)

          (defun-nx ,next ,formals
            ,next-term)

          (local (in-theory (disable ,next ,done)))


          (defun-nx ,steps-clk (tr-clk . ,formals)
            (declare (xargs :measure (nfix tr-clk)
                            :hints (("goal" :in-theory
                                     '(nfix zp o-p o-finp natp o<)))))
            ;;(if (zp tr-clk)
            ;;    nil
            ;;  (let ((tr-clk (1- tr-clk)))
            ;;    ,(subst `(lambda
            ;;               ,formals
            ;;               (let ((__def-tr-steps__
            ;;                      (,steps-clk tr-clk . ,formals)))
            ;;                 (and __def-tr-steps__
            ;;                      (+ 1 __def-tr-steps__))))
            ;;            fn orig-body))))
            (cond ((zp tr-clk)           nil)
                  ((,done . ,formals)    0)
                  (t ,(bind formals
                            `(,next . ,formals)
                            `(let ((__def-tr-steps__
                                    (,steps-clk (1- tr-clk) . ,formals)))
                               (and __def-tr-steps__
                                    (+ 1 __def-tr-steps__)))))))

          (defun-sk ,terminates ,formals
            (exists (tr-clk)
                    (,steps-clk (nfix tr-clk) . ,formals)))

          (defthm ,(dtr-sym terminates "-IMPLIES-NATP-WITNESS")
            (implies (,terminates . ,formals)
                     (natp (,terminates-witness . ,formals)))
            :rule-classes (:rewrite :type-prescription))

          (in-theory (disable ,terminates-suff))

          (defthm ,terminates-sufficient
            (implies (,steps-clk tr-clk . ,formals)
                     (,terminates . ,formals))
            :hints (("goal" :use ,terminates-suff
                     :in-theory (disable ,terminates))))

          (defun-nx ,measure ,formals
            (or (,terminates . ,formals)
                0))

          (defthm ,(dtr-sym measure "-NATP")
            (natp (,measure . ,formals))
            :rule-classes
            (:type-prescription :rewrite))

          ;;(local (defthm steps-clk-functional-instance
          ;;         t
          ;;         :rule-classes nil
          ;;         :hints (("goal" :use ((:functional-instance
          ;;                                pf-steps-clk
          ;;                                . ,func-inst;; (pf-steps-clk (lambda (clk st)
          ;;                               ;;                ,(bind formals 'st
          ;;                                ;;                       `(,steps-clk
          ;;                                ;;                         clk . ,formals))))
          ;;                                ;;(pf-done (lambda (st) ,(bind formals 'st `(,done . ,formals))))
          ;;                                ;;(pf-next (lambda (st) ,(bind formals 'st `(,next . ,formals))))
          ;;                                ))
          ;;                  :in-theory '(my-run2-steps)))))

          (defthm ,(dtr-sym terminates "-REDEF")
            (equal (,terminates . ,formals)
                   ,(b* (((mv body &)
                          (fsubst-into-tail-recursion
                           ''0 terminates-lambda fn nil body)))
                      body)
                   ;;,(untranslate1
                   ;;  (b* (((mv body &)
                   ;;        (fsubst-into-tail-recursion
                   ;;         ''0 terminates-lambda fn nil body)))
                   ;;    body)
                   ;;  nil (untrans-table world) nil nil)
                   )
                   ;;(if (,done . ,formals)
                   ;;    0
                   ;;  ,(bind formals `(,next . ,formals)
                   ;;         `(let ((next (,terminates . ,formals)))
                   ;;            (and next (1+ next))))))
            :hints (("goal"
                     :clause-processor
                     (terminates-redef-cp
                      clause
                      '(,body ,formals ,terminates ,done ,next ,fn
                              ('(:use ((:instance
                                        (:functional-instance
                                         pf-terminates-redef
                                         . ,func-inst)
                                        (st ,(fget formals))))))))
                     :in-theory nil)
                    (use-by-computed-hint clause)
                    (use-these-hints-hint clause)
                    (and stable-under-simplificationp
                         '(:in-theory '(,terminates ,steps-clk ,terminates-suff)))
                     ;; :use ((:instance
                    ;;               (:functional-instance
                    ;;                pf-terminates-redef
                    ;;                . ,func-inst)
                    ;;               (st ,(fget formals))))
                    ;; :do-not-induct t
                    ;; :in-theory '(,terminates-suff))
                    ;;(and stable-under-simplificationp
                    ;;     '(:in-theory '(,terminates)))
                    ;;(and stable-under-simplificationp
                    ;;     '(:in-theory (theory 'minimal-theory)
                    ;;       :expand ((:free ,formals
                    ;;                 (,steps-clk clk . ,formals)))))
                    )
            :otf-flg t
            :rule-classes ((:definition
                            :clique (,terminates)
                            :controller-alist ((,terminates . ,controllers)))))

          (defthm ,(dtr-sym measure "-REDEF")
            (equal (,measure . ,formals)
                   (if (,terminates . ,formals)
                       ,(b* (((mv body &)
                              (fsubst-into-tail-recursion
                               ''0 measure-lambda fn nil body)))
                          body)
                     0))
            :hints (("goal"
                     :clause-processor
                     (measure-redef-cp
                      clause
                      '(,body ,formals ,measure ,terminates ,done ,next ,fn
                              ('(:use ((:instance
                                        (:functional-instance
                                         pf-measure-redef
                                         . ,func-inst)
                                        (st ,(fget formals))))))))
                     :in-theory nil)
                    (use-by-computed-hint clause)
                    (use-these-hints-hint clause)
                    (and stable-under-simplificationp
                         '(:in-theory '(,measure)))
                     ;; :use ((:instance
                    ;;               (:functional-instance
                    ;;                pf-terminates-redef
                    ;;                . ,func-inst)
                    ;;               (st ,(fget formals))))
                    ;; :do-not-induct t
                    ;; :in-theory '(,terminates-suff))
                    ;;(and stable-under-simplificationp
                    ;;     '(:in-theory '(,terminates)))
                    ;;(and stable-under-simplificationp
                    ;;     '(:in-theory (theory 'minimal-theory)
                    ;;       :expand ((:free ,formals
                    ;;                 (,steps-clk clk . ,formals)))))
                    )
            :otf-flg t
            :rule-classes ((:definition
                            :clique (,measure)
                            :controller-alist ((,measure . ,controllers)))))


          ;;(defthm ,(dtr-sym measure "-REDEF")
          ;;  (equal (,measure . ,formals)
          ;;         (if (or (not (,terminates . ,formals))
          ;;                 (,done . ,formals))
          ;;             0
          ;;           ,(bind formals `(,next . ,formals)
          ;;                  `(1+ (,measure . ,formals)))))
          ;;  :hints (("goal" :use ((:instance
          ;;                         (:functional-instance
          ;;                          pf-measure-redef
          ;;                          . ,func-inst)
          ;;                         (st ,(fget formals))))
          ;;           :do-not-induct t
          ;;           :in-theory '(,measure)))
          ;;  :otf-flg t
          ;;  :rule-classes ((:definition
          ;;                  :clique (,measure)
          ;;                  :controller-alist ((,measure . ,controllers)))))

          (in-theory (disable ,measure ,terminates))

          (,(if non-execp 'defun-nx 'defun) ,fn ,formals
            (declare (xargs :measure (,measure . ,formals)
                            :hints (("goal" :in-theory '(,(dtr-sym measure "-NATP")
                                                         o< o-finp o-p natp);; )
                                   ;;(and stable-under-simplificationp
                                    ;;     '(
                                     :expand ((:with ,(dtr-sym measure "-REDEF")
                                               (,measure . ,formals))
                                              (:with ,(dtr-sym terminates "-REDEF")
                                               (,terminates . ,formals)))))
                            :verify-guards nil))
            (declare . ,decls)
            (mbe :logic ,fn-body
                 :exec
                 ,orig-body))

          (local (make-event (denormalize-thm-fn
                              ',fn
                              ',(dtr-sym fn "-DENORM")
                              '(:rule-classes nil)
                              (w state))))
          (local (defthm ,(dtr-sym fn "-SIMPLE-TR")
                   (equal (,fn . ,formals)
                          ,simp-body)
                   :hints (("goal" :use ,(dtr-sym fn "-DENORM")
                            :in-theory nil)
                           '(:clause-processor
                             (tr-decomp-clause-proc
                              clause
                              '(,fn ,formals ,body ,done ,ret ,next))
                             :do-not-induct t)
                           (use-by-computed-hint clause))
                   :rule-classes nil))
          (defthm ,(dtr-sym fn "-REDEF")
            (equal (,fn . ,formals)
                   ,orig-body)
            :hints (("goal" :clause-processor
                      (tr-decomp-clause-proc
                       clause
                       '(,fn ,formals ,body ,done ,ret ,next))
                      :do-not-induct t
                     :in-theory nil)
                    (use-by-computed-hint clause)
                    '(:use ((:instance
                                   (:functional-instance
                                    pf-run-is-loop
                                    (pf-run (lambda (st)
                                              ,(bind formals 'st `(,fn . ,formals))))
                                    . ,func-inst)
                                   (st ,(fget formals)))))
                    (and (= (len clause) 1)
                         (consp (car clause))
                         (eq (caar clause) 'equal)
                         '(:use ((:instance ,(dtr-sym fn "-SIMPLE-TR")
                                  . ,(if (< 1 (len formals))
                                         (mv-binding-list 0 formals 'st)
                                       `((,(car formals) st)))))))
                    ;;'(:clause-processor
                    ;;  (tr-decomp-clause-proc
                    ;;   clause
                    ;;   '(,fn ,formals ,body ,done ,ret ,next))
                    ;;  :do-not-induct t)
                    )
            :rule-classes ((:definition :clique (,fn)
                            :controller-alist ((,fn . ,controllers)))))

          ,@(and verify-guardsp
                 `((verify-guards ,fn
                     :hints ,(cons `'(:use ,(dtr-sym fn "-REDEF")
                                      :in-theory (disable ,(dtr-sym fn "-REDEF")))
                                   guard-hints)
                     :guard-simplify ,guard-simplify
                     :guard-debug ,guard-debug)))

          (in-theory (disable (:definition ,fn))))))))

(defmacro def-tr (fn formals &rest decl-body)
  `(make-event
    (def-tr-fn ',fn ',formals ',decl-body state)))


(local
 (progn
   (defstobj sta (regs :type (array t (0)) :resizable t))

   (defun-nx mk-sta ()
     (create-sta))

   (defun my-step (pc prog sta)
     (declare (xargs :guard (and (natp pc) (true-listp prog))
                     :stobjs sta))
     (let ((instr (nth pc prog)))
       (if (atom instr)
           (mv pc sta)
         (case (car instr)
           (incr (let* ((sta (if (and (natp (cdr instr))
                                      (< (cdr instr) (regs-length sta)))
                                 (update-regsi (cdr instr) (+ 1 (nfix (regsi (cdr instr) sta))) sta)
                               sta)))
                   (mv (+ 1 pc) sta)))
           (t (mv pc sta))))))


   (def-tr my-run (pc prog sta)
     (declare (xargs :guard (and (natp pc) (true-listp prog))
                     :stobjs sta
                     :guard-simplify nil
                     :guard-debug t))
     (if (< (len prog) pc)
         sta
       (mv-let (pc sta)
         (my-step pc prog sta)
         (my-run pc prog sta)))
     :diverge (mk-sta))

   (def-tr my-run2 (pc prog sta)
     (declare (xargs :guard (and (natp pc) (true-listp prog))
                     :guard-hints ('(:in-theory (disable my-run2 my-run2-redef)
                                     :expand ((:with my-run2 (my-run2 pc prog sta)))))
                     :stobjs sta))
     (if (< (len prog) pc)
         sta
       (let ((instr (nth pc prog)))
         (if (atom instr)
             sta
           (case (car instr)
             (incr (let* ((sta (if (and (natp (cdr instr))
                                        (< (cdr instr) (regs-length sta)))
                                   (update-regsi (cdr instr) (+ 1 (nfix (regsi (cdr instr) sta))) sta)
                                 sta)))
                     (my-run2 (1+ pc) prog sta)))
             (decr (let* ((sta (if (and (natp (cdr instr))
                                        (< (cdr instr) (regs-length sta)))
                                   (update-regsi (cdr instr) (- 1 (nfix (regsi (cdr instr) sta))) sta)
                                 sta)))
                     (my-run2 (1+ pc) prog sta)))
             (zero (let* ((sta (if (and (natp (cdr instr))
                                        (< (cdr instr) (regs-length sta)))
                                   (update-regsi (cdr instr) 0 sta)
                                 sta)))
                     (my-run2 (1+ pc) prog sta)))
             (one (let* ((sta (if (and (natp (cdr instr))
                                       (< (cdr instr) (regs-length sta)))
                                  (update-regsi (cdr instr) 1 sta)
                                sta)))
                    (my-run2 (1+ pc) prog sta)))
             (jmp (let* ((pc (if (natp (cdr instr)) (cdr instr) (1+ pc))))
                    (my-run2 pc prog sta)))
             (jmpz (let* ((pc (if (and (natp (cdr instr))
                                       (or (<= (regs-length sta) (cdr instr))
                                           (= 0 (nfix (regsi (cdr instr) sta)))))
                                  (1+ pc)
                                (+ 2 pc))))
                     (my-run2 pc prog sta)))
             (otherwise (prog2$ (cw "bad instruction: ~x0~%" (car instr))
                                sta))))))
     :diverge (mk-sta))))
