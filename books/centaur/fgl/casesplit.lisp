; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(in-package "FGL")

(include-book "arith-base")
(include-book "centaur/meta/term-vars" :dir :system)
(include-book "clause-processors/generalize" :dir :system) ;; for make-n-vars
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "std/alists/alist-defuns" :dir :System)

(fty::defmap casesplit-alist :val-type pseudo-termp :true-listp t)

(defevaluator fcs-ev fcs-ev-lst
  ((implies a b)
   (if a b c)
   (not a)
   (equal a b)
   (if* a b c)
   (fgl-sat-check params x)
   (fgl-pathcond-fix x)
   (show-counterexample params msg))
  :namedp t)

(acl2::def-join-thms fcs-ev)

(acl2::def-ev-pseudo-term-fty-support fcs-ev fcs-ev-lst)




(define disjoin* ((x pseudo-term-listp))
  :returns (new-x pseudo-termp)
  (cond ((atom x) ''nil)
        ((atom (cdr x)) (pseudo-term-fix (car x)))
        (t `(if* ,(pseudo-term-fix (car x)) 't ,(disjoin* (cdr x)))))
  ///
  (local (in-theory (disable pseudo-term-listp symbol-listp
                             pseudo-termp acl2::pseudo-termp-opener)))
  (defthm fcs-ev-of-disjoin*
    (iff (fcs-ev (disjoin* x) a)
         (fcs-ev (disjoin x) a))))

(define fgl-casesplit-solve ((params pseudo-termp)
                             msg
                             (x pseudo-termp))
  :returns (solve pseudo-termp)
  `((lambda (x msg params)
      ((lambda (x params msg ignore)
         ((lambda (ans params msg)
            (if ans 't (show-counterexample params msg)))
          (not (fgl-sat-check params (not x)))
          params
          msg))
       x params msg
       (FMT-TO-COMMENT-WINDOW '"Checking case ~@0~%"
                       (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                                 (CONS MSG 'NIL))
                       '0
                       'NIL
                       'NIL)))
    ,(pseudo-term-fix x)
    ',msg
    ,(pseudo-term-fix params))
  ///
  (defthm fcs-ev-of-fgl-casesplit-solve
    (iff (fcs-ev (fgl-casesplit-solve params msg x) a)
         (fcs-ev x a))
    :hints(("Goal" :in-theory (enable fgl-sat-check)))))


(define fgl-casesplit-solve-cases ((params pseudo-termp)
                                   (messages true-listp)
                                   (cases pseudo-term-listp)
                                   (result pseudo-termp))
  :returns (term pseudo-termp)
  (if (atom cases)
      ''t
    `(if* ,(fgl-casesplit-solve params (car messages)
                                `(if ,(car cases) ,result 't))
          ,(fgl-casesplit-solve-cases params (cdr messages) (cdr cases) result)
          'nil))
  ///
  (local (defthm result-implies-fcs-ev-of-fgl-casesplit-solve-cases
           (implies (fcs-ev result a)
                    (fcs-ev (fgl-casesplit-solve-cases params messages cases result) a))))

  (defthm fcs-ev-of-fgl-casesplit-solve-cases
    (implies (fcs-ev (disjoin cases) a)
             (iff (fcs-ev (fgl-casesplit-solve-cases params messages cases result) a)
                  (fcs-ev result a)))
    :hints(("Goal" :in-theory (enable fcs-ev-disjoin-when-consp)))))
          

(define termlist-apply-fgl-pathcond-fix ((x pseudo-term-listp))
  :returns (new-x pseudo-term-listp)
  (if (atom x)
      nil
    (cons `(fgl-pathcond-fix ,(pseudo-term-fix (car x)))
          (termlist-apply-fgl-pathcond-fix (cdr x))))
  ///
  (defret fcs-ev-list-of-<fn>
    (equal (fcs-ev-lst new-x a)
           (fcs-ev-lst x a)))

  (defret len-of-<fn>
    (equal (len new-x) (len x))))

(local (defthm pseudo-term-listp-when-pseudo-var-listp
         (implies (pseudo-var-list-p x)
                  (pseudo-term-listp x))
         :hints(("Goal" :in-theory (enable pseudo-term-listp pseudo-var-list-p)))))

(local (defthm len-of-append
         (Equal (len (append a b))
                (+ (len a) (len b)))))

(local (defthm symbol-listp-of-append
         (implies (and (Symbol-listp x)
                       (symbol-listp y))
                  (symbol-listp (append x y)))))

(local (defthm symbol-listp-of-set-diff
         (implies (Symbol-listp x)
                  (symbol-listp (set-difference-eq x y)))))

;; (local (defthm pseudo-term-listp-of-append
;;          (implies (and (pseudo-term-listp x)
;;                        (pseudo-term-listp y))
;;                   (pseudo-term-listp (append x y)))))

(local (defthm pseudo-term-listp-of-set-diff
         (implies (pseudo-term-listp x)
                  (pseudo-term-listp (set-difference-eq x y)))))

(local (defthm pseudo-var-list-p-of-set-diff
         (implies (pseudo-var-list-p x)
                  (pseudo-var-list-p (set-difference-eq x y)))))

(local (defthm symbol-listp-when-pseudo-var-list-p
         (implies (pseudo-var-list-p x)
                  (symbol-listp x))))

(local (defthm fcs-ev-lst-of-append
         (equal (fcs-ev-lst (append x y) a)
                (append (fcs-ev-lst x a)
                        (fcs-ev-lst y a)))))

(local (defthm len-of-fcs-ev-lst
         (equal (len (fcs-ev-lst x a))
                (len x))))

(local (defthm lookup-in-pairlis$-append-1
         (implies (and (equal (len k1) (len v1))
                       (case-split (member x k1)))
                  (equal (hons-assoc-equal x (pairlis$ (append k1 k2) (append v1 v2)))
                         (hons-assoc-equal x (pairlis$ k1 v1))))))

(local (defthm len-equal-0
         (equal (Equal 0 (len x))
                (atom x))))

(local (defthm lookup-in-pairlis$-append-2
         (implies (and (equal (len k1) (len v1))
                       (not (member x k1)))
                  (equal (hons-assoc-equal x (pairlis$ (append k1 k2) (append v1 v2)))
                         (hons-assoc-equal x (pairlis$ k2 v2))))
         :hints(("Goal" :in-theory (enable append)
                 :induct (pairlis$ k1 v1)))))

(local (defthm lookup-in-pairlis-vars-fcs-ev-lst
         (implies (and (pseudo-var-list-p vars)
                       (member v vars))
                  (equal (hons-assoc-equal v (pairlis$ vars (fcs-ev-lst vars a)))
                         (cons v (cdr (hons-assoc-equal v a)))))))

(local (defthm member-set-diff
         (implies (and (member x a) (not (member x b)))
                  (member x (set-difference-eq a b)))))

(local (defthm eval-alists-agree-for-wrap-fgl-pathcond-fix-vars
         (implies (and (pseudo-var-list-p vars)
                       (pseudo-var-list-p term-vars))
                  (acl2::eval-alists-agree term-vars
                                           (pairlis$ (append vars (set-difference-equal term-vars vars))
                                                     (append (fcs-ev-lst vars a)
                                                             (fcs-ev-lst (set-difference-equal term-vars vars) a)))
                                           a))
         :hints(("Goal" :in-theory (enable acl2::eval-alists-agree-by-bad-guy)
                 :do-not-induct t))))

(local
 (defthm fcs-ev-when-agree-on-term-vars
   (implies (acl2::eval-alists-agree (term-vars x) a b)
            (equal (fcs-ev x a)
                   (fcs-ev x b)))
   :hints (("goal" :use ((:functional-instance cmr::base-ev-when-agree-on-term-vars
                          (cmr::base-ev fcs-ev)
                          (cmr::base-ev-list fcs-ev-lst)))))))

(define wrap-fgl-pathcond-fix-vars ((vars pseudo-var-list-p)
                                    (x pseudo-termp))
  :returns (new-x pseudo-termp)
  (b* ((vars (pseudo-var-list-fix vars))
       (fixes (termlist-apply-fgl-pathcond-fix vars))
       (free-vars (term-free-vars x vars)))
    `((lambda (,@vars . ,free-vars)
        ,(pseudo-term-fix x))
      ,@fixes . ,free-vars))
  ///
  (defret fcs-ev-of-<fn>
    (equal (fcs-ev new-x a)
           (fcs-ev x a))
    :hints (("goal" :use ((:instance eval-alists-agree-for-wrap-fgl-pathcond-fix-vars
                           (vars (pseudo-var-list-fix vars))
                           (term-vars (term-vars x))))
             :in-theory (disable eval-alists-agree-for-wrap-fgl-pathcond-fix-vars)))))


(define fgl-casesplit-core ((hyp pseudo-termp)
                            (concl pseudo-termp)
                            (split-params)
                            (solve-params)
                            (cases casesplit-alist-p))
  :prepwork ((local (defthm pseudo-term-listp-when-symbol-listp
                      (implies (symbol-listp x)
                               (pseudo-term-listp x))))
             (local (defthm pseudo-term-listp-alist-vals-of-casesplit-alist
                      (implies (casesplit-alist-p x)
                               (pseudo-term-listp (alist-vals x)))
                      :hints(("Goal" :in-theory (enable alist-vals))))))
  :returns (thm pseudo-termp)
  (b* ((cases (casesplit-alist-fix cases))
       (case-msgs (alist-keys cases))
       (cases (alist-vals cases))
       (cases-vars (acl2::make-n-vars (len cases) 'fgl-case 0 '(result))))
    `(if ,(pseudo-term-fix hyp)
         ((lambda (result solve-params . ,cases-vars)
            (if* ,(fgl-casesplit-solve (list 'quote split-params) "Case split completeness" (disjoin* cases-vars))
                 ,(fgl-casesplit-solve-cases 'solve-params case-msgs cases-vars 'result)
                 'nil))
          ,(wrap-fgl-pathcond-fix-vars (term-vars hyp) concl)
          ',solve-params
          . ,cases)
       't))
  ///
  (defthm fcs-ev-of-fgl-casesplit-core
    (implies (and (fcs-ev hyp a)
                  (not (fcs-ev concl a)))
             (not (fcs-ev (fgl-casesplit-core hyp concl split-params solve-params cases) a)))))

(local (in-theory (disable pseudo-termp
                           acl2::pseudo-termp-opener)))

(local (defthm pseudo-term-listp-of-take
         (implies (pseudo-term-listp x)
                  (pseudo-term-listp (take n x)))))

(local (defthm pseudo-termp-of-nth
         (implies (pseudo-term-listp x)
                  (pseudo-termp (nth n x)))))

(local (defthm fcs-ev-disjoin-clause-when-disjoin-take
         (implies (not (fcs-ev (disjoin clause) a))
                  (not (fcs-ev (disjoin (take n clause)) a)))))

(local (defthm fcs-ev-disjoin-clause-when-disjoin-take-pseudo-term-list-fix
         (implies (not (fcs-ev (disjoin clause) a))
                  (not (fcs-ev (disjoin (take n (pseudo-term-list-fix clause))) a)))
         :hints(("Goal" :induct (take n clause)
                 :in-theory (disable pseudo-term-listp)
                 :expand ((pseudo-term-list-fix clause))))))

(local (defthm fcs-ev-disjoin-clause-when-nth-pseudo-term-list-fix
         (implies (not (fcs-ev (disjoin clause) a))
                  (not (fcs-ev (nth n (pseudo-term-list-fix clause)) a)))
         :hints(("Goal" :induct (take n clause)
                 :in-theory (disable pseudo-term-listp)
                 :expand ((pseudo-term-list-fix clause))))))

(local (defthm fcs-ev-disjoin-clause-when-nth
         (implies (not (fcs-ev (disjoin clause) a))
                  (not (fcs-ev (nth n clause) a)))
         :hints(("Goal" :induct (nth n clause)))))

(local (defthm fcs-ev-disjoin-of-pseudo-term-list-fix
         (iff (fcs-ev (disjoin (pseudo-term-list-fix x)) a)
              (fcs-ev (disjoin x) a))
         :hints(("Goal" :in-theory (enable pseudo-term-list-fix)
                 :induct (len x)))))

(define fgl-casesplit-hyp/concl (split-concl-p
                                 (clause pseudo-term-listp))
  :returns (mv (hyp pseudo-termp
                    :hints ((and stable-under-simplificationp
                                 `(:expand ((:free (x) (pseudo-termp `(not ,x))))))))
               (concl pseudo-termp))
  :guard-debug t
  (b* ((clause (pseudo-term-list-fix clause))
       ((when (atom clause)) (mv ''t ''nil)))
    (case-match clause
      ((('implies hyp concl)) (mv hyp concl))
      (& (if split-concl-p
             (mv `(not ,(disjoin (take (+ -1 (len clause)) clause)))
                 (nth (+ -1 (len clause)) clause))
           (mv ''t (disjoin clause))))))
  ///
  (defret fcs-ev-of-fgl-casesplit-hyp/concl
    (implies (not (fcs-ev (disjoin clause) a))
             (and (fcs-ev hyp a)
                  (not (fcs-ev concl a))))
    :hints (("goal" :use ((:instance fcs-ev-disjoin-of-pseudo-term-list-fix (x clause)))
             :in-theory (e/d (fcs-ev-disjoin-when-consp)
                             (fcs-ev-disjoin-of-pseudo-term-list-fix
                              fcs-ev-pseudo-term-equiv-congruence-on-x
                              fcs-ev-of-pseudo-term-fix-x))))))

(defprod fgl-casesplit-config
  ((split-params)
   (solve-params)
   (split-concl-p)
   (cases casesplit-alist-p)))

(define fgl-casesplit-clause-proc ((clause pseudo-term-listp) config)
  :returns (res pseudo-term-list-listp)
  (b* ((clause (pseudo-term-list-fix clause))
       ((unless (fgl-casesplit-config-p config))
        (cw "fgl-casesplit-clause-proc error: bad config~%")
        (list clause))
       ((fgl-casesplit-config config))
       ((mv hyp concl) (fgl-casesplit-hyp/concl config.split-concl-p clause)))
    (list (list (fgl-casesplit-core hyp concl config.split-params config.solve-params config.cases))))
  ///
  (defthm fgl-casesplit-clause-proc-correct
    (implies (and (pseudo-term-listp clause)
                  (alistp a)
                  (fcs-ev (conjoin-clauses (fgl-casesplit-clause-proc clause config)) a))
             (fcs-ev (disjoin clause) a))
    :hints (("goal" :use ((:instance fcs-ev-disjoin-of-pseudo-term-list-fix (x clause)))
             :in-theory (e/d (fcs-ev-disjoin-when-consp)
                             (fcs-ev-disjoin-of-pseudo-term-list-fix
                              fcs-ev-pseudo-term-equiv-congruence-on-x
                              fcs-ev-of-pseudo-term-fix-x))))
    :rule-classes :clause-processor))

(set-state-ok t)
(define fgl-casesplit-translate-cases (cases state)
  :mode :program
  (b* (((when (atom cases)) (value nil))
       ((unless (and (consp (car cases))
                     (consp (cdar cases))
                     (not (cddar cases))))
        (er soft 'fgl-casesplit-translate-cases
            "Bad casesplit syntax -- must be a pair (\"case-name\" term): ~x0" (car cases)))
       ((er trans) (acl2::translate (cadar cases) t t t 'fgl-casesplit-translate-cases (w state) state))
       ((er rest) (fgl-casesplit-translate-cases (cdr cases) state)))
    (value (cons (cons (caar cases) trans) rest))))
    
       
  
(define fgl-casesplit-hint-fn (cases split-params solve-params split-concl-p state)
  :mode :program
  (b* (((er cases-trans) (fgl-casesplit-translate-cases cases state))
       (config (make-fgl-casesplit-config :split-params (or split-params
                                                            (fgl-toplevel-sat-check-config))
                                          :solve-params (or solve-params
                                                            (fgl-toplevel-sat-check-config))
                                          :split-concl-p split-concl-p
                                          :cases cases-trans)))
    (value `(:clause-processor (fgl-casesplit-clause-proc clause ',config)))))

(defmacro fgl-casesplit (&key cases split-params solve-params split-concl-p)
  `(fgl-casesplit-hint-fn ,cases ,split-params ,solve-params ,split-concl-p state))




(define expand-an-implies ((x pseudo-termp))
  :returns (new-x pseudo-termp)
  :measure (pseudo-term-count x)
  :verify-guards nil
  (pseudo-term-case x
    :const (pseudo-term-fix x)
    :var (pseudo-term-fix x)
    :fncall (if (and (eq x.fn 'implies)
                     (eql (len x.args) 2))
                (pseudo-term-fncall 'if
                                    (list (car x.args)
                                          (wrap-fgl-pathcond-fix-vars
                                           (term-vars (car x.args))
                                           (cadr x.args))
                                          ''t))
              (pseudo-term-fix x))
    :lambda (pseudo-term-lambda
             x.formals
             (expand-an-implies x.body)
             x.args))
  ///
  (verify-guards expand-an-implies)

  (local (defun-sk fcs-ev-of-expand-an-implies-cond (x)
           (forall a
                   (iff (fcs-ev (expand-an-implies x) a)
                        (fcs-ev x a)))
           :rewrite :direct))
  (local (in-theory (disable fcs-ev-of-expand-an-implies-cond)))

  (local (defthm fcs-ev-of-expand-an-implies-lemma
           (fcs-ev-of-expand-an-implies-cond x)
           :hints (("goal" :induct (expand-an-implies x))
                   (and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))

  (defret fcs-ev-of-expand-an-implies
    (iff (fcs-ev (expand-an-implies x) a)
         (fcs-ev x a))))

(define expand-an-implies-cp ((x pseudo-term-listp))
  (if (and (consp x)
           (not (cdr x)))
      (list (list (expand-an-implies (car x))))
    (list x))
  ///
  (defthm expand-an-implies-cp-correct
    (implies (and (pseudo-term-listp x)
                  (alistp a)
                  (fcs-ev (conjoin-clauses (expand-an-implies-cp x)) a))
             (fcs-ev (disjoin x) a))
    :rule-classes :clause-processor))
