; FGL - A Symbolic Simulation Framework for ACL2
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
(include-book "syntax-bind")
(include-book "centaur/meta/term-vars" :dir :system)
(include-book "clause-processors/generalize" :dir :system) ;; for make-n-vars
(include-book "clause-processors/pseudo-term-fty" :dir :system)
(include-book "std/alists/alist-defuns" :dir :System)
(include-book "centaur/meta/bindinglist" :dir :system)
(include-book "tools/def-functional-instance" :dir :system)
(include-book "std/lists/index-of" :dir :system)

(fty::defmap casesplit-alist :val-type pseudo-termp :true-listp t)

(defevaluator fcs-ev fcs-ev-list
  ((implies a b)
   (if a b c)
   (not a)
   (equal a b)
   (if* a b c)
   (fgl-sat-check params x)
   (fgl-pathcond-fix x)
   (show-counterexample params msg)
   (cons x y)
   (car x)
   (cdr x)
   ;; (syntax-bind-fn x y z)
   )
  :namedp t)

(acl2::def-join-thms fcs-ev)

(acl2::def-ev-pseudo-term-fty-support fcs-ev fcs-ev-list)

(local (defthm alistp-of-pairlis$
         (alistp (pairlis$ x y))))

(local (defthm alistp-of-append
         (implies (and (alistp x) (alistp y))
                  (alistp (append x y)))))

(local (defthm true-listp-of-fcs-ev-list
         (true-listp (fcs-ev-list x a))
         :hints (("goal" :induct (len x)))
         :rule-classes :type-prescription))

(define fcs-ev-bindinglist ((x cmr::bindinglist-p) (a alistp))
  ;; Returns the alist for evaluating a body term nested inside all the
  ;; bindings.
  :returns (final-alist alistp)
  (b* (((when (atom x)) (acl2::alist-fix a))
       ((cmr::binding x1) (car x))
       (new-bindings (pairlis$ x1.formals (fcs-ev-list x1.args a))))
    (fcs-ev-bindinglist (cdr x) (append new-bindings a))))

(acl2::def-functional-instance
  fcs-ev-bindinglist-to-lambda-nest-correct
  cmr::bindinglist-to-lambda-nest-correct
  ((acl2::base-ev fcs-ev)
   (acl2::base-ev-list fcs-ev-list)
   (cmr::base-ev-bindinglist fcs-ev-bindinglist))
  :hints(("Goal" :in-theory (enable fcs-ev-bindinglist))))

(acl2::def-functional-instance
  fcs-ev-when-agree-on-term-vars
  cmr::base-ev-when-agree-on-term-vars
  ((acl2::base-ev fcs-ev)
   (acl2::base-ev-list fcs-ev-list))
  :hints(("Goal" :in-theory (enable fcs-ev-bindinglist))))
  

(local (defthm assoc-when-nonnil
         (implies k
                  (equal (assoc k x)
                         (hons-assoc-equal k x)))))

(define bind-vars-to-list-elems ((vars pseudo-var-list-p)
                                 (tmp pseudo-var-p))
  :returns (bindings cmr::bindinglist-p)
  :measure (len vars)
  (b* (((when (atom vars)) nil)
       (vars (pseudo-var-list-fix vars))
       (tmp (pseudo-var-fix tmp))
       ((when (atom (cdr vars)))
        (list (cmr::binding vars `((car ,tmp))))))
    (cons (cmr::binding (list (car vars) tmp) `((car ,tmp) (cdr ,tmp)))
          (bind-vars-to-list-elems (cdr vars) tmp)))
  ///
  (local (defun fcs-ev-bindinglist-of-bind-vars-to-list-elems-ind (vars tmp a)
           (Declare (Xargs :measure (len vars)))
           (if (atom (cdr vars))
               (list tmp a)
             (fcs-ev-bindinglist-of-bind-vars-to-list-elems-ind
              (pseudo-var-list-fix (cdr vars))
              (pseudo-var-fix tmp)
              (append (pairlis$ (list (pseudo-var-fix (car vars))
                                      (pseudo-var-fix tmp))
                                (list (cadr (assoc (pseudo-var-fix tmp) a))
                                      (cddr (assoc (pseudo-var-fix tmp) a))))
                      a)))))
             
  (local (defthm cdr-of-pseudo-var-list-fix
           (equal (cdr (pseudo-var-list-fix x))
                  (pseudo-var-list-fix (cdr x)))
           :hints(("Goal" :in-theory (enable pseudo-var-list-fix)))))

  (local (in-theory (disable cons-equal not no-duplicatesp-equal)))

  (defthm fcs-ev-bindinglist-of-bind-vars-to-list-elems
    (implies (and (no-duplicatesp-equal (pseudo-var-list-fix vars))
                  (not (member (pseudo-var-fix tmp) (pseudo-var-list-fix vars)))
                  ;; (alistp a)
                  )
             (equal (hons-assoc-equal v (fcs-ev-bindinglist (bind-vars-to-list-elems vars tmp) a))
                    (cond ((member v (pseudo-var-list-fix vars))
                           (cons v (nth (acl2::index-of v (pseudo-var-list-fix vars))
                                        (cdr (hons-assoc-equal (pseudo-var-fix tmp)
                                                               a)))))
                          ((equal v (pseudo-var-fix tmp))
                           (if (consp (cdr vars))
                               (cons (pseudo-var-fix tmp)
                                     (nthcdr (+ -1 (len vars)) (cdr (hons-assoc-equal (pseudo-var-fix tmp) a))))
                             (hons-assoc-equal (pseudo-var-fix tmp) a)))
                          (t (hons-assoc-equal v a)))))
    :hints(("Goal" :in-theory (enable fcs-ev-bindinglist
                                      acl2::index-of
                                      hons-assoc-equal
                                      ;; no-duplicatesp-equal
                                      ;; cmr::remove-non-pseudo-vars
                                      ;; cmr::remove-corresp-non-pseudo-vars
                                      )
            :expand ((pseudo-var-list-fix vars)
                     (:free (a b) (no-duplicatesp-equal (cons a b))))
            :induct (fcs-ev-bindinglist-of-bind-vars-to-list-elems-ind vars tmp a))))

  (local
   (defthm nth-index-of-in-fcs-ev-list
     (implies (and (member v vars)
                   (pseudo-var-list-p vars))
              (equal (nth (acl2::index-of v vars) (fcs-ev-list vars a))
                     (cdr (hons-assoc-equal v a))))
     :hints(("Goal" :in-theory (enable acl2::index-of member pseudo-var-list-p nth)))))

  (defthm eval-alists-agree-of-fcs-ev-bindinglist-of-bind-vars-to-list-elems
    (implies (and (no-duplicatesp-equal vars)
                  (not (member tmp vars))
                  (pseudo-var-list-p vars)
                  (pseudo-var-p tmp))
             (acl2::eval-alists-agree vars (fcs-ev-bindinglist (bind-vars-to-list-elems vars tmp)
                                                               (cons (cons tmp (fcs-ev-list vars a))
                                                                     a))
                                      a))
    :hints(("Goal" :in-theory (enable ACL2::EVAL-ALISTS-AGREE-BY-BAD-GUY)))))

(define construct-list-term ((x pseudo-term-listp))
  :returns (list-term pseudo-termp)
  (if (atom x)
      ''nil
    `(cons ,(pseudo-term-fix (car x))
           ,(construct-list-term (cdr x))))
  ///
  (defret fcs-ev-of-<fn>
    (equal (fcs-ev (construct-list-term x) a)
           (fcs-ev-list x a))))


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
    (equal (fcs-ev-list new-x a)
           (fcs-ev-list x a)))

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

(local (defthm fcs-ev-list-of-append
         (equal (fcs-ev-list (append x y) a)
                (append (fcs-ev-list x a)
                        (fcs-ev-list y a)))))

(local (defthm len-of-fcs-ev-list
         (equal (len (fcs-ev-list x a))
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

(local (defthm lookup-in-pairlis-vars-fcs-ev-list
         (implies (and (pseudo-var-list-p vars)
                       (member v vars))
                  (equal (hons-assoc-equal v (pairlis$ vars (fcs-ev-list vars a)))
                         (cons v (cdr (hons-assoc-equal v a)))))))

(local (defthm member-set-diff
         (implies (and (member x a) (not (member x b)))
                  (member x (set-difference-eq a b)))))

(local (defthm eval-alists-agree-for-wrap-fgl-pathcond-fix-vars
         (implies (and (pseudo-var-list-p vars)
                       (pseudo-var-list-p term-vars))
                  (acl2::eval-alists-agree term-vars
                                           (pairlis$ (append vars (set-difference-equal term-vars vars))
                                                     (append (fcs-ev-list vars a)
                                                             (fcs-ev-list (set-difference-equal term-vars vars) a)))
                                           a))
         :hints(("Goal" :in-theory (enable acl2::eval-alists-agree-by-bad-guy)
                 :do-not-induct t))))


(define wrap-fgl-pathcond-fix ((x pseudo-termp))
  :returns (new-x pseudo-termp)
  (b* ((vars (term-vars x))
       (list-term (construct-list-term vars))
       (tmp (acl2::new-symbol 'tmp vars))
       (bindings (cons (cmr::binding (list tmp) (list `(fgl-pathcond-fix ,list-term)))
                       (bind-vars-to-list-elems vars tmp))))
    (cmr::bindinglist-to-lambda-nest-exec bindings x))
  ///
  
  (defret fcs-ev-of-<fn>
    (equal (fcs-ev new-x a)
           (fcs-ev x a))
    :hints(("Goal" :in-theory (e/d (fcs-ev-bindinglist)
                                   (eval-alists-agree-of-fcs-ev-bindinglist-of-bind-vars-to-list-elems))
            :use ((:instance eval-alists-agree-of-fcs-ev-bindinglist-of-bind-vars-to-list-elems
                   (vars (term-vars x)) (tmp (acl2::new-symbol 'tmp (term-vars x)))))))))
       

;; (define wrap-fgl-pathcond-fix-vars ((vars pseudo-var-list-p)
;;                                     (x pseudo-termp))
;;   :returns (new-x pseudo-termp)
;;   (b* ((vars (pseudo-var-list-fix vars))
;;        (fixes (termlist-apply-fgl-pathcond-fix vars))
;;        (free-vars (term-free-vars x vars)))
;;     `((lambda (,@vars . ,free-vars)
;;         ,(pseudo-term-fix x))
;;       ,@fixes . ,free-vars))
;;   ///
;;   (defret fcs-ev-of-<fn>
;;     (equal (fcs-ev new-x a)
;;            (fcs-ev x a))
;;     :hints (("goal" :use ((:instance eval-alists-agree-for-wrap-fgl-pathcond-fix-vars
;;                            (vars (pseudo-var-list-fix vars))
;;                            (term-vars (term-vars x))))
;;              :in-theory (disable eval-alists-agree-for-wrap-fgl-pathcond-fix-vars)))))


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
          ,(wrap-fgl-pathcond-fix concl)
          ',solve-params
          . ,cases)
       't))
  ///
  (defthm fcs-ev-of-fgl-casesplit-core
    (implies (and (fcs-ev hyp a)
                  (not (fcs-ev concl a)))
             (not (fcs-ev (fgl-casesplit-core hyp concl split-params solve-params cases) a)))))


(define fgl-casesplit-before-core ((hyp pseudo-termp)
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
       (cases (alist-vals cases)))
    `(if ,(pseudo-term-fix hyp)
         (if* ,(fgl-casesplit-solve (list 'quote split-params) "Case split completeness" (disjoin* cases))
              ,(fgl-casesplit-solve-cases (kwote solve-params) case-msgs cases (wrap-fgl-pathcond-fix concl))
              'nil)
       't))
  ///
  (defthm fcs-ev-of-fgl-casesplit-before-core
    (implies (and (fcs-ev hyp a)
                  (not (fcs-ev concl a)))
             (not (fcs-ev (fgl-casesplit-before-core hyp concl split-params solve-params cases) a)))))

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
   (repeat-concl-p)
   (cases casesplit-alist-p)))

(define fgl-casesplit-clause-proc ((clause pseudo-term-listp) config)
  :returns (res pseudo-term-list-listp)
  (b* ((clause (pseudo-term-list-fix clause))
       ((unless (fgl-casesplit-config-p config))
        (cw "fgl-casesplit-clause-proc error: bad config~%")
        (list clause))
       ((fgl-casesplit-config config))
       ((mv hyp concl) (fgl-casesplit-hyp/concl config.split-concl-p clause)))
    (list (list (if config.repeat-concl-p
                    (fgl-casesplit-before-core hyp concl config.split-params config.solve-params config.cases)
                  (fgl-casesplit-core hyp concl config.split-params config.solve-params config.cases)))))
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
    
       
  
(define fgl-casesplit-hint-fn (cases split-params solve-params split-concl-p repeat-concl-p state)
  :mode :program
  (b* (((er cases-trans) (fgl-casesplit-translate-cases cases state))
       (config (make-fgl-casesplit-config :split-params (or split-params
                                                            (fgl-toplevel-sat-check-config))
                                          :solve-params (or solve-params
                                                            (fgl-toplevel-sat-check-config))
                                          :split-concl-p split-concl-p
                                          :repeat-concl-p repeat-concl-p
                                          :cases cases-trans)))
    (value `(:clause-processor (fgl-casesplit-clause-proc clause ',config)))))

(defmacro fgl-casesplit (&key cases split-params solve-params split-concl-p repeat-concl-p)
  `(fgl-casesplit-hint-fn ,cases ,split-params ,solve-params ,split-concl-p ,repeat-concl-p state))




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
                                          (wrap-fgl-pathcond-fix
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
