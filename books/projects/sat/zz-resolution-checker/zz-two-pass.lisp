; ACL2 interface to the ZZ system
; Copyright (C) 2011-2017 Centaur Technology
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

;; In general, this file will be used in conjunction with zz-record.lisp, but
;; it does not actually include zz-record because we want this file to be
;; usable without a TTAG.  Any book that wants to use a two-pass verified SAT
;; scheme can include this book, run some magical forms, and use the ZZV-
;; versions of any ZZ SAT/model-checking functions/macros necessary.
#|
(include-book "zz-record")
|#


(include-book "make-event/acl2x-help" :dir :system)
(include-book "zzv-interface")

(defun zzv-check-proof (aig proof)
  (declare (Xargs :guard t))
  (and (zzchk-run-proof-guard proof)
       (zzchk-check (aig-norm aig) proof)))

(defthm zzv-check-proof-implies-unsat
  (implies (zzv-check-proof aig proof)
           (not (aig-eval aig env))))

;; ZZV-SAT-VALIDATE-RESULT -- check an AIG's SAT result to see whether it's
;; sound.  If SAT, evaluate the assignment, and if UNSAT, run the proof.
(defun zzv-sat-validate-result (aig res)
  (declare (xargs :guard t))
  (b* (((unless (consp res))
        '(failed))
       ((when (eq (car res) 'sat))
        (let ((fal (hons-shrink-alist (cdr res) nil)))
          (if (aig-eval aig fal)
              res
            '(failed))))
       ((when (eq (car res) 'unsat))
        (if (zzv-check-proof aig (cdr res))
            res
          '(failed))))
    res))

(defthm zzv-sat-validate-result-consp
  (consp (zzv-sat-validate-result aig res))
  :rule-classes :type-prescription)

(defthm zzv-sat-validate-result-sat
  (implies (equal (car (zzv-sat-validate-result aig res)) 'sat)
           (aig-eval aig (cdr (zzv-sat-validate-result aig res)))))

(defthm zzv-sat-validate-result-unsat
  (implies (equal (car (zzv-sat-validate-result aig res)) 'unsat)
           (not (aig-eval aig env))))

(in-theory (disable zzv-sat-validate-result))




;; ZZV-SAT-VALIDATE -- pluggable into ZZV-SAT, checks the recorded result for the
;; call as stored in (ZZV-SAT-RESULT-ALIST).  Attach something to
;; ZZV-SAT-RESULT-ALIST so that it can find the results.
(defstub zzv-sat-result-alist () nil)

(defun zzv-sat-validate (aig timeout)
  (declare (xargs :guard t))
  (b* ((key (hons aig timeout))
       (val (hons-get key (zzv-sat-result-alist)))
       ((when (or (not val)
                  (not (consp (cdr val)))))
        '(failed)))
    (zzv-sat-validate-result aig (cdr val))))

(defthm zzv-sat-validate-consp
  (consp (zzv-sat-validate aig timeout))
  :rule-classes :type-prescription)

(defthm zzv-sat-validate-sat
  (implies (equal (car (zzv-sat-validate aig timeout)) 'sat)
           (aig-eval aig (cdr (zzv-sat-validate aig timeout)))))

(defthm zzv-sat-validate-unsat
  (implies (equal (car (zzv-sat-validate aig timeout)) 'unsat)
           (not (aig-eval aig env))))

(in-theory (disable zzv-sat-validate))

(defmacro zzv-sat-validate-mode ()
  '(defattach (zzv-sat-fn zzv-sat-validate)
     :hints (("goal" :in-theory '(zzv-sat-validate-consp
                                  zzv-sat-validate-sat
                                  zzv-sat-validate-unsat)))))

(encapsulate nil
  ;; just make sure it works
  (local (zzv-sat-validate-mode)))





;; ZZV-BATCH-SAT-VALIDATE-RESULTS -- check the AIGs' SAT results to see whether
;; they're sound.
(defun zzv-batch-sat-validate-results (aigs results)
  (declare (xargs :guard (true-listp results)))
  (if (atom aigs)
      nil
    (cons (zzv-sat-validate-result (car aigs) (car results))
          (zzv-batch-sat-validate-results (cdr aigs) (cdr results)))))

(defthm zzv-batch-sat-validate-result-len
  (equal (len (zzv-batch-sat-validate-results aigs results))
         (len aigs)))

(defthm zzv-batch-sat-validate-results-entries-consp
  (implies (member-equal entry (zzv-batch-sat-validate-results aigs results))
           (consp entry)))

(defthm zzv-batch-sat-validate-results-entry-sat
  (implies (equal (car (nth n (zzv-batch-sat-validate-results aigs results))) 'sat)
           (aig-eval (nth n aigs)
                     (cdr (nth n (zzv-batch-sat-validate-results
                                  aigs results))))))

(defthm zzv-batch-sat-validate-results-entry-unsat
  (implies (equal (car (nth n (zzv-batch-sat-validate-results aigs results))) 'unsat)
           (not (aig-eval (nth n aigs) env))))

(in-theory (disable zzv-batch-sat-validate-results))



;; ZZV-BATCH-SAT-VALIDATE -- pluggable into ZZV-BATCH-SAT, checks the recorded
;; result for the call as stored in (ZZV-BATCH-SAT-RESULT-ALIST).  Attach
;; something to ZZV-BATCH-SAT-RESULT-ALIST so that it can find the results.
(defstub zzv-batch-sat-result-alist () nil)

(defun zzv-batch-sat-validate (aigs timeout)
  (declare (xargs :guard t))
  (b* ((key (hons aigs timeout))
       (val (hons-get key (zzv-batch-sat-result-alist))))
    (zzv-batch-sat-validate-results
     aigs (and (consp val)
               (true-listp (cdr val))
               (cdr val)))))

(defthm zzv-batch-sat-validate-len
  (equal (len (zzv-batch-sat-validate aigs timeout))
         (len aigs)))

(defthm zzv-batch-sat-validate-entries-consp
  (implies (member-equal entry (zzv-batch-sat-validate aigs timeout))
           (consp entry)))

(defthm zzv-batch-sat-validate-entry-sat
  (implies (equal (car (nth n (zzv-batch-sat-validate aigs timeout))) 'sat)
           (aig-eval (nth n aigs)
                     (cdr (nth n (zzv-batch-sat-validate
                                  aigs timeout))))))

(defthm zzv-batch-sat-validate-entry-unsat
  (implies (equal (car (nth n (zzv-batch-sat-validate aigs timeout))) 'unsat)
           (not (aig-eval (nth n aigs) env))))

(defmacro zzv-batch-sat-validate-mode ()
  '(defattach (zzv-batch-sat-fn zzv-batch-sat-validate)
     :hints (("goal" :in-theory '(zzv-batch-sat-validate-len
                                  zzv-batch-sat-validate-entries-consp
                                  zzv-batch-sat-validate-entry-sat
                                  zzv-batch-sat-validate-entry-unsat)))))

(encapsulate nil
  (local (zzv-batch-sat-validate-mode)))









;; zzv-modelcheck-validate-result -- check a FSM's modelchecking result to see
;; whether it's sound.  If refuted, evaluate the assignment, and if proved,
;; check the invariant.

(defun zzv-modelcheck-validate-result (stepfns prop initsts result)
  (declare (xargs :guard t))
  (if (atom result)
      '(failed)
    (case (car result)
      (refuted
       (b* (((unless (and (consp (cdr result))
                          (consp (cddr result))))
             '(failed))
            ((cons ctrex-initst inputs) (cdr result))
            (ctrex-initst (hons-shrink-alist ctrex-initst nil))
            (keys (alist-keys initsts))
            (initsts (hons-shrink-alist initsts nil))
            (ok (and (alists-agree keys initsts ctrex-initst)
                     (not (check-property stepfns prop ctrex-initst inputs)))))
         (fast-alist-free ctrex-initst)
         (fast-alist-free initsts)
         (if ok
             result
           '(failed))))
      (proved
       (b* (((unless (and (consp (cdr result))
                          (consp (cddr result))
                          (consp (cdddr result))))
             '(failed))
            ((list* invar
                    inductivity-proof
                    sufficiency-proof
                    initialization-proof) (cdr result))
            ((unless (hons-subset (aig-vars invar)
                                  (alist-keys stepfns)))
             '(failed
               "invariant's variables were not a subset of the state variables"))
            (stepfns (hons-shrink-alist stepfns nil))
            ((unless (zzv-check-proof
                      (aig-and
                       invar
                       (aig-not (aig-restrict invar stepfns)))
                      inductivity-proof))
             (fast-alist-free stepfns)
             '(failed
               "inductivity proof was malformed"))
            (- (fast-alist-free stepfns))
            ((unless (zzv-check-proof
                      (aig-and invar (aig-not prop))
                      sufficiency-proof))
             '(failed
               "sufficiency proof was malformed"))
            (initsts (hons-shrink-alist initsts nil))
            ((unless (zzv-check-proof
                      (aig-not (aig-partial-eval invar initsts))
                      initialization-proof))
             (fast-alist-free initsts)
             '(failed
               "initialization proof was malformed")))
         (fast-alist-free initsts)
         result))
      (t result))))


(defthm consp-zzv-modelcheck-validate-result
  (consp (zzv-modelcheck-validate-result stepfns prop initsts result))
  :rule-classes :type-prescription)


(defthm consp-zzv-modelcheck-validate-result-trace-when-refuted
  (let ((res (zzv-modelcheck-validate-result stepfns prop initsts result)))
    (implies (equal (car res) 'refuted)
             (and (consp (cdr res))
                  (consp (cddr res))))))

(defthm zzv-modelcheck-validate-result-when-refuted
  (let ((res (zzv-modelcheck-validate-result stepfns prop initsts result)))
    (implies (equal (car res) 'refuted)
             (and (equal (check-property stepfns prop (cadr res) (cddr res))
                         nil)
                  (alists-agree (alist-keys initsts) initsts (cadr res))))))

(defthm zzv-modelcheck-validate-result-when-proved
  (implies
   (and (equal (car (zzv-modelcheck-validate-result
                     stepfns prop initsts result ))
               'proved)
        (alists-agree (alist-keys initsts) initsts ctrex-initst))
   (check-property stepfns prop ctrex-initst ctrex-frames))
  :hints(("Goal" :in-theory (disable hons-subset))))

(in-theory (disable zzv-modelcheck-validate-result))



;; ZZV-MODELCHECK-VALIDATE -- pluggable into ZZV-MODELCHECK, checks the recorded
;; result for the call as stored in ZZV-MODELCHECK-RESULT-ALIST.  Attach
;; something to ZZV-MODELCHECK-RESULT-ALIST so that it can find the results.
(defstub zzv-modelcheck-result-alist () nil)

(defun zzv-modelcheck-validate (stepfns prop initsts timeout max-depth engine)
  (declare (xargs :guard t))
  (b* ((key (hons-list* stepfns prop initsts timeout max-depth engine))
       (val (hons-get key (zzv-modelcheck-result-alist))))
    (zzv-modelcheck-validate-result
     stepfns prop initsts (and (consp val) (cdr val)))))

(defthm consp-zzv-modelcheck-validate
  (consp (zzv-modelcheck-validate stepfns prop initsts timeout max-depth engine))
  :rule-classes :type-prescription)


(defthm consp-zzv-modelcheck-validate-trace-when-refuted
  (let ((res (zzv-modelcheck-validate stepfns prop initsts timeout max-depth engine)))
    (implies (equal (car res) 'refuted)
             (and (consp (cdr res))
                  (consp (cddr res))))))

(defthm zzv-modelcheck-validate-when-refuted
  (let ((res (zzv-modelcheck-validate stepfns prop initsts timeout max-depth engine)))
    (implies (equal (car res) 'refuted)
             (and (equal (check-property stepfns prop (cadr res) (cddr res))
                         nil)
                  (alists-agree (alist-keys initsts) initsts (cadr res))))))

(defthm zzv-modelcheck-validate-when-proved
  (implies
   (and (equal (car (zzv-modelcheck-validate
                     stepfns prop initsts timeout max-depth engine))
               'proved)
        (alists-agree (alist-keys initsts) initsts ctrex-initst))
   (check-property stepfns prop ctrex-initst ctrex-frames))
  :hints(("Goal" :in-theory (disable hons-subset))))

(in-theory (disable zzv-modelcheck-validate))

(defmacro zzv-modelcheck-validate-mode ()
  '(defattach (zzv-modelcheck zzv-modelcheck-validate)
     :hints (("goal" :in-theory '(consp-zzv-modelcheck-validate
                                  consp-zzv-modelcheck-validate-trace-when-refuted
                                  zzv-modelcheck-validate-when-refuted
                                  zzv-modelcheck-validate-when-proved)))))

(encapsulate nil
  (local (zzv-modelcheck-validate-mode)))



(defmacro zzv-validate-mode ()
  '(progn (zzv-sat-validate-mode)
          (zzv-batch-sat-validate-mode)
          (zzv-modelcheck-validate-mode)))



(make-event
 `(defconst *zz-record-book*
    ,(concatenate 'string (cbd) "zz-record")))


(defmacro zzv-two-pass-mode ()
  '(acl2x-replace (zzv-record-mode)       ;; recording on first pass
                  (zzv-validate-mode)     ;; checking on second pass
                  :single-pass            ;; trust the sat/model checker
                  (zzv-raw-mode)
                  :outside-certification  ;; trust the sat/model checker
                  (zzv-raw-mode)))

(defmacro zz-two-pass-start ()
  `(progn
     (make-event
      (value '(progn (value-triple '(:acl2x-load-state-global
                                     define-zzv-result-alists))
                     (local (include-book ,*zz-record-book*)))))
     (zzv-two-pass-mode)))



(defmacro zz-two-pass-stop ()
  '(make-event
    (b* (((mv sat-result-alist state)
          (sneaky-load 'zzv-sat-results state))
         ((mv batch-sat-result-alist state)
          (sneaky-load 'zzv-batch-sat-results state))
         ((mv modelcheck-result-alist state)
          (sneaky-load 'zzv-modelcheck-results state))
         (state (if (acl2::f-get-global 'acl2::certify-book-info state)
                    (acl2::f-put-global
                     'define-zzv-result-alists
                     `(local
                       (progn (defconst *zzv-sat-result-alist*
                                (hons-shrink-alist ',sat-result-alist nil))
                              (defun zzv-sat-result-alist-temp ()
                                (declare (xargs :guard t))
                                *zzv-sat-result-alist*)
                              (defattach zzv-sat-result-alist
                                zzv-sat-result-alist-temp)
                              (defconst *zzv-batch-sat-result-alist*
                                (hons-shrink-alist ',batch-sat-result-alist nil))
                              (defun zzv-batch-sat-result-alist-temp ()
                                (declare (xargs :guard t))
                                *zzv-batch-sat-result-alist*)
                              (defattach zzv-batch-sat-result-alist
                                zzv-batch-sat-result-alist-temp)
                              (defconst *zzv-modelcheck-result-alist*
                                (hons-shrink-alist ',modelcheck-result-alist nil))
                              (defun zzv-modelcheck-result-alist-temp ()
                                (declare (xargs :guard t))
                                *zzv-modelcheck-result-alist*)
                              (defattach zzv-modelcheck-result-alist
                                zzv-modelcheck-result-alist-temp)))
                     state)
                  state)))
      (value '(acl2::use-acl2x-replace)))))

;; This is helpful for debugging things that will be done in two-pass mode: run
;; the proof-recording version, then (zz-transfer-proofs), then the proof
;; cehcking version.  :Redef may need to be on in order to run this more than
;; once in a session.
(defmacro zz-transfer-proofs ()
  '(make-event
    (b* (((mv sat-result-alist state)
          (sneaky-load 'zzv-sat-results state))
         ((mv batch-sat-result-alist state)
          (sneaky-load 'zzv-batch-sat-results state))
         ((mv modelcheck-result-alist state)
          (sneaky-load 'zzv-modelcheck-results state)))
      (value
       `(local
         (progn (defconst *zzv-sat-result-alist*
                  (hons-shrink-alist ',sat-result-alist nil))
                (defun zzv-sat-result-alist-temp ()
                  (declare (xargs :guard t))
                  *zzv-sat-result-alist*)
                (defattach zzv-sat-result-alist
                  zzv-sat-result-alist-temp)
                (defconst *zzv-batch-sat-result-alist*
                  (hons-shrink-alist ',batch-sat-result-alist nil))
                (defun zzv-batch-sat-result-alist-temp ()
                  (declare (xargs :guard t))
                  *zzv-batch-sat-result-alist*)
                (defattach zzv-batch-sat-result-alist
                  zzv-batch-sat-result-alist-temp)
                (defconst *zzv-modelcheck-result-alist*
                  (hons-shrink-alist ',modelcheck-result-alist nil))
                (defun zzv-modelcheck-result-alist-temp ()
                  (declare (xargs :guard t))
                  *zzv-modelcheck-result-alist*)
                (defattach zzv-modelcheck-result-alist
                  zzv-modelcheck-result-alist-temp)))))))







(defevaluator zzv-cp-ev zzv-cp-ev-lst
  ((aig-eval aig env)
   (check-property stepfns prop initsts inputs)
   (if a b c)
   (alists-agree keys a b)
   (not a)))


(defun zzv-sat-cp (clause hints)
  (declare (xargs :guard t))
  (b* (((unless (and (consp hints)
                     (consp (cdr hints))))
        (list clause))
       ((list* aig timeout env-term) hints)
       (sat-res (zzv-sat aig timeout))
       ((unless (eq (car sat-res)
                    'unsat))
        (cw "ZZV-SAT-CP error: ZZV-SAT returned ~x0~%" sat-res)
        (list clause)))
    (list (cons `(aig-eval ',aig ,env-term)
                clause))))

(include-book "clause-processors/join-thms" :dir :System)

(def-join-thms zzv-cp-ev)

(defthm zzv-sat-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (zzv-cp-ev (conjoin-clauses
                            (zzv-sat-cp clause hints))
                           a))
           (zzv-cp-ev (disjoin clause) a))
  :rule-classes :clause-processor)

(defun zzv-modelcheck-cp (clause hints)
  (declare (Xargs :guard t))
  (b* (((unless (<= 8 (len hints)))
        (cw "ZZV-MODELCHECK-CP failed: hints should be a list of length 8 but
has length ~x0~%" (len hints))
        (list clause))
       ((list stepfns prop initsts timeout max-depth engine
              ctrex-initst-term ctrex-frames-term)
        hints)
       (mc-res (zzv-modelcheck stepfns prop initsts timeout max-depth engine))
       ((unless (eq (car mc-res) 'proved))
        (cw "ZZV-MODELCHECK-CP failed: bad MC result, ~x0~%" mc-res)
        (list clause)))
    (list (cons `(alists-agree ',(alist-keys initsts) ',initsts
                               ,ctrex-initst-term)
                clause)
          (cons `(not (check-property ',stepfns ',prop ,ctrex-initst-term
                                      ,ctrex-frames-term))
                clause))))


(defthm zzv-modelcheck-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (zzv-cp-ev (conjoin-clauses
                            (zzv-modelcheck-cp clause hints))
                           a))
           (zzv-cp-ev (disjoin clause) a))
  :rule-classes :clause-processor)

