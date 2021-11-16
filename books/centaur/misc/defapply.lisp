; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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

; defapply.lisp -- introduces an executable apply function that recognizes a
; specified set of function symbols.

; cert_param: (non-acl2r)

(in-package "ACL2")

(local
 (progn

   ;; Infrastructure for testing this
   (defun all-syms-in-world (w)
     (remove-duplicates (strip-cars w)))

   (defun list-of-nilsp (x)
     (if (atom x)
         (eq x nil)
       (and (eq (car x) nil)
            (list-of-nilsp (cdr x)))))

   (defun logic-function-syms (syms world)
     (if (atom syms)
         nil
       (if (and (not (eq (getprop (car syms) 'formals :none 'current-acl2-world
                                  world)
                         :none))
                (member (getprop (car syms) 'symbol-class nil 'current-acl2-world world)
                        '(:ideal :common-lisp-compliant))
                (not (member (car syms)
                             (global-val 'untouchable-fns world)))
                (not (member (car syms) '(synp ;; must-be-equal
                                          open-output-channel!
                                          wormhole-eval)))
                (not (assoc (car syms) *ttag-fns*))
                ;; (list-of-nilsp (fgetprop (car syms) 'stobjs-out nil
                ;;                          world))
                ;; (list-of-nilsp (fgetprop (car syms) 'stobjs-in nil
                ;;                          world))
                (not (and (member (car syms) *ec-call-bad-ops*)
                          (not (equal (fgetprop (car syms) 'guard ''t
                                                world)
                                      ''t)))))
           (cons (car syms) (logic-function-syms (cdr syms) world))
         (logic-function-syms (cdr syms) world))))

   (comp t) ; helpful e.g. for Allegro CL

   (make-event
    `(defconst *all-logic-function-syms*
       ',(let ((world (w state)))
           (logic-function-syms (all-syms-in-world world) world))))))


(include-book "std/util/bstar" :dir :system)
(include-book "clause-processors/generalize" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "evaluator-metatheorems")
(include-book "interp-function-lookup")
(include-book "tools/def-functional-instance" :dir :system)
(include-book "misc/without-waterfall-parallelism" :dir :system)

(defmacro ecc (call)
  (declare (xargs :guard (consp call)))
  (cond ((member-eq (car call) acl2::*ec-call-bad-ops*)
         call)
        (t `(ec-call ,call))))

(defun make-list-of-nths (sym start n)
  (declare (xargs :guard (and (natp start)
                              (natp n))))
  (if (zp n)
      nil
    (cons `(nth ,start ,sym)
          (make-list-of-nths sym (1+ start) (1- n)))))

(defun defapply-call (fn world)
  (b* ((formals (fgetprop fn 'formals :none world))
       (stobjs-out (fgetprop fn 'stobjs-out :none world))
       (stobjs-in (fgetprop fn 'stobjs-in nil world)))
    (cond
     ((or (eq formals :none)
          (eq stobjs-out :none))
      (er hard 'defapply-call "~
The function ~x0 is missing its ~x1 property; perhaps it is not defined.~%"
          fn (if (eq formals :none) 'formals 'stobjs-out)))
     ((or (assoc fn *ttag-fns*)
          (member fn '(mv-list return-last
; Matt K. mod 11/2021 for addition of do$ to *stobjs-out-invalid*
                               do$))
          (remove nil stobjs-in)) ;; takes a stobj or needs a ttag
      `(mv t (non-exec (ecc (,fn . ,(make-list-of-nths 'args 0 (length formals)))))))
     ((and (consp stobjs-out) (consp (cdr stobjs-out)))
      `(mv t (mv-list ,(len stobjs-out)
                      (ecc (,fn . ,(make-list-of-nths 'args 0 (length formals)))))))
     (t `(mv t (ecc (,fn . ,(make-list-of-nths 'args 0 (length formals)))))))))

(defun defapply-cases (fns world)
  (if (atom fns)
      `((t (mv nil nil)))
    (cons `(,(car fns) ,(defapply-call (car fns) world))
          (defapply-cases (cdr fns) world))))


(defun make-apply-thm-name (apply-name fn)
  (if (or (equal (symbol-package-name fn)
                 (symbol-package-name apply-name))
          (member-symbol-name fn
                              (pkg-imports
                               (symbol-package-name apply-name))))
      (intern-in-package-of-symbol
       (concatenate
        'string (symbol-name apply-name)
        "-OF-" (symbol-name fn))
       apply-name)
    (intern-in-package-of-symbol
     (concatenate
      'string (symbol-name apply-name)
      "-OF-" (symbol-package-name fn) "::" (symbol-name fn))
     apply-name)))


(defthmd nth-open-for-defapply
  (implies (syntaxp (quotep n))
           (equal (nth n (cons a b))
                  (if (zp n)
                      a
                    (nth (1- n) b)))))

(defun make-apply-thms (fns name world)
  (if (atom fns)
      nil
    (let ((formals (fgetprop (car fns) 'formals nil world)))
      (cons `(defthm ,(make-apply-thm-name name (car fns))
               (equal (,name ',(car fns) (list . ,formals))
                      (list t ,(if (eq (car fns) 'return-last)
                                   (car (last formals))
                                 `(,(car fns) . ,formals)))))
            (make-apply-thms (cdr fns) name world)))))


(defun function-type-prescriptions (fns world)
  (declare (xargs :mode :program))
  (if (atom fns)
      nil
    (let ((rune `(:type-prescription ,(car fns))))
      (if (not (equal (formula rune nil world) ''t))
          (cons rune (function-type-prescriptions
                      (cdr fns) world))
        (function-type-prescriptions
         (cdr fns) world)))))


(defun defapply-fn (name fns world theoremsp)
  (declare (xargs :mode :program))
  (let* ((cases (defapply-cases fns world)))
    `(encapsulate nil
       (local (in-theory (e/d**
                          (nth-open-for-defapply
                            car-cons cdr-cons (zp)
                           (eqlablep)
                           . ,(function-type-prescriptions
                               fns world)))))
       (local (defthm open-hide-for-defapply
                (equal (hide x) x)
                :hints (("goal" :expand (hide x)))))
       (defun ,name (fn args)
         (declare (xargs :guard (true-listp args)
                         :normalize nil)
                  (ignorable fn args))
         (case fn
           . ,cases))
       . ,(and theoremsp (make-apply-thms fns name world)))))


(defmacro defapply (name fns &key (theoremsp 't))
  `(make-event
    (defapply-fn ',name ',fns (w state) ,theoremsp)))


;; Starting a clause processor that will prove the following type of
;; theorem in more or less linear time:
;; (implies (mv-nth 0 (an-apply-function fn args))
;;          (equal (mv-nth 1 (an-apply-function fn args))
;;                 (an-evaluator (cons fn (kwote-lst args)) nil)))
;; for an evaluator which recognizes a superset of the functions
;; recognized by the apply function.


(acl2::def-meta-extract evmeta-ev evmeta-ev-lst)

(defun term-list-of-nths (n start term)
  (if (zp n)
      nil
    (cons `(nth ',start ,term)
          (term-list-of-nths (1- n) (1+ start) term))))

(defun list-of-nthsp (n start term list)
  (if (zp n)
      (eq list nil)
    (let ((entry (car list)))
      (case-match entry
        (('nth ('quote !start) !term)
         (list-of-nthsp (1- n) (1+ start) term (cdr list)))))))

(defthm list-of-nthsp-term-list-of-nths
  (iff (list-of-nthsp n start term list)
       (equal list (term-list-of-nths (nfix n) start term))))

(defun funcall-equals-values-clause (fnname arity values)
  `((equal (cons 't (cons (,fnname
                           . ,(term-list-of-nths arity 0 'args))
                          'nil))
           ,values)))

(defthm funcall-equal-values-clause-correct
  (implies (evmeta-ev-theoremp
            (disjoin (funcall-equals-values-clause
                      fnname arity values)))
           (equal (evmeta-ev values a)
                  (list t (evmeta-ev
                           `(,fnname . ,(term-list-of-nths arity 0 'args))
                           a))))
  :hints (("goal" :use
           ((:instance evmeta-ev-falsify
                       (x (disjoin (funcall-equals-values-clause
                                    fnname arity values)))
                       (a a))))))


(encapsulate nil
  ;; ev-apply-arglist
  (defun ev-apply-arglist (n evfn term alist)
    (if (zp n)
        nil
      (cons `(,evfn (car ,term) ,alist)
            (ev-apply-arglist (1- n) evfn `(cdr ,term) alist))))

  ;; (defun ev-apply-arglist-on-result (n evfn res alist)
  ;;   (if (zp n)
  ;;       nil
  ;;     (cons `(,evfn ',(car res) ',alist)
  ;;           (ev-apply-arglist-on-result
  ;;            (1- n) evfn (cdr res) alist))))
  (local (in-theory (enable ev-of-arglist)))

  (defthm evmeta-ev-lst-ev-apply-arglist
    (implies (not (equal evfn 'quote))
             (equal (evmeta-ev-lst
                     (ev-apply-arglist arity evfn term alist) a)
                    (evmeta-ev-lst
                     (ev-of-arglist
                      arity evfn
                      (evmeta-ev term a)
                      (evmeta-ev alist a))
                     nil)))
    :hints (("goal" :in-theory (enable evmeta-ev-of-fncall-args)
             :induct (ev-apply-arglist arity evfn term alist))))

  (defthm evmeta-ev-ev-apply-arglist
    (implies (and (not (equal evfn 'quote))
                  (not (equal fn 'quote)))
             (equal (evmeta-ev
                     (cons fn
                           (ev-apply-arglist arity evfn term alist))
                     a)
                    (evmeta-ev
                     (cons fn
                           (kwote-lst
                            (evmeta-ev-lst
                             (ev-of-arglist
                              arity evfn
                              (evmeta-ev term a)
                              (evmeta-ev alist a))
                             nil)))
                     nil)))
    :hints(("Goal" :in-theory (enable evmeta-ev-of-fncall-args)))))

(encapsulate nil
  (local (defthm consolidate-consts-+
           (implies (syntaxp (and (quotep a) (quotep b)))
                    (equal (+ a b c)
                           (+ (+ a b) c)))))

  (local (defthm nthcdr-plus-one
           (implies (natp idx)
                    (equal (nthcdr (+ 1 idx) lst)
                           (cdr (nthcdr idx lst))))))

  (local (defthm car-nthcdr
           (equal (car (nthcdr n lst))
                  (nth n lst))))

  (local (defthm cadr-nth-quote-lst
           (equal (cadr (nth n (kwote-lst lst)))
                  (nth n lst))))

  (local (defthm consp-nth-kwote-lst
           (implies (and (natp idx) (< idx (len lst)))
                    (consp (nth idx (kwote-lst lst))))
           :hints(("Goal" :induct (nth idx lst)))))

  (local (defthm quote-nth-kwote-lst
           (implies (and (natp idx) (< idx (len lst)))
                    (equal (car (nth idx (kwote-lst lst)))
                           'quote))
           :hints(("Goal" :induct (nth idx lst)))))

  (local (defthm nth-len-greater
           (implies (and (natp idx)
                         (<= (len lst) idx))
                    (equal (nth idx lst) nil))))

  (local (defthm len-kwote-lst
           (equal (len (kwote-lst lst)) (len lst))))

  (local (in-theory (disable w)))
  (local (in-theory (enable ev-of-arglist)))

  (local
   (defthm evmeta-ev-lst-term-list-of-nths1
     (implies (and (evmeta-ev-meta-extract-global-facts)
                   (check-ev-of-quote evfn quote-thmname (w state))
                   (check-ev-of-variable evfn var-thmname (w state))
                   (not (equal evfn 'quote))
                   (natp idx) (natp n))
              (equal (evmeta-ev-lst
                      (term-list-of-nths n idx args)
                      a)
                     (evmeta-ev-lst
                      (ev-of-arglist
                       n evfn
                       (nthcdr idx (kwote-lst (evmeta-ev args a)))
                       alst)
                      nil)))
     :hints(("Goal" :in-theory (enable evmeta-ev-of-fncall-args))
            (and stable-under-simplificationp
                 (case-match id ((('0 '1) . &) t))
                 '(:cases ((< idx (len (evmeta-ev args a)))))))
     :rule-classes nil))


  (defthm evmeta-ev-lst-term-list-of-nths
    (implies (and (evmeta-ev-meta-extract-global-facts)
                  (check-ev-of-quote evfn quote-thmname (w state))
                  (check-ev-of-variable evfn var-thmname (w state))
                  (not (equal evfn 'quote))
                  (natp idx) (natp n))
              (equal (evmeta-ev-lst
                      (term-list-of-nths n idx args)
                      a)
                     (evmeta-ev-lst
                      (ev-of-arglist
                       n evfn
                       (nthcdr idx (kwote-lst (evmeta-ev args a)))
                       nil)
                      nil)))
     :hints(("Goal" :in-theory (enable evmeta-ev-of-fncall-args))
            (and stable-under-simplificationp
                 (case-match id ((('0 '1) . &) t))
                 '(:cases ((< idx (len (evmeta-ev args a)))))))))


(in-theory (disable funcall-equals-values-clause))


(defun reduce-identities (term fn)
  (case-match term
    ((!fn) term)
    ((!fn ('nth . &) . &) term)
    (('mv-list & sub . &) (reduce-identities sub fn))
    (('return-last & & sub) (reduce-identities sub fn))
    (& term)))

(defthm reduce-identities-identity
  (equal (evmeta-ev (reduce-identities term fn) a)
         (evmeta-ev term a)))

(in-theory (disable reduce-identities))

;; Analyzes a term like the body of an apply function: either a final
;; case (cons 'nil (cons 'nil 'nil)), or a nest of IFs where each test
;; asks (eql fn 'some-fnname), the true-branch is a cons of 'T onto a
;; function application
(defun apply-cases-ok (term rule-alist evfn wrld)
  (declare (xargs :normalize nil
                  :guard (plist-worldp wrld)
                  :verify-guards nil))
  (case-match term
    (('if ('eql 'fn ('quote fnname . &). &) values rest . &)
     (b* ((erp
           (apply-cases-ok rest rule-alist evfn wrld))
          ((when erp) erp)
          ((when (or (keywordp fnname) (eq fnname 'quote)))
           (msg "~x0 is not allowed as a function name."
                    fnname))
          (look (hons-get fnname rule-alist))
          ((when (not look))
           (msg "Function ~x0 not recognized by evaluator."
                fnname))
          ((cons arity rune) (cdr look))
          ((unless (natp arity))
           (msg "Function ~x0 supposedly has an arity of ~x1"
                fnname arity))
          (rule-name (if (and (consp rune)
                              (consp (cdr rune)))
                         (cadr rune)
                       rune))
          ((unless (check-ev-of-call evfn fnname arity rule-name wrld))
           (msg "Function ~x0 has malformed evaluator constraint" fnname)))
       (case-match values
         (('cons ''t ('cons call . &) . &)
          (b* ((fncall (reduce-identities call fnname)))
            (case-match fncall
              ((!fnname . args)
               ;;              (prog2$ (cw "fncall: ~x0, fnname-args case~%"
               ;;                          fncall)
               (if (list-of-nthsp arity 0 'args args)
                   nil
                 (msg "Malformed function call ~x0: bad arity?"
                      fncall)))
              (& (msg "Unrecognized form of return value: ~x0"
                      call)))))
         (& (msg "Unrecognized form of return value: ~x0"
                 values)))))
    ('(cons 'nil (cons 'nil 'nil))
     nil)
    (& (msg "Unrecognized subterm: ~x0" term))))

(defun apply-cases-ind (term)
  (declare (xargs :normalize nil))
  (case-match term
    (('if ('eql 'fn ('quote . &) . &) & rest . &)
     (apply-cases-ind rest))
    (& term)))




(encapsulate nil
  (local
   (in-theory '((:COMPOUND-RECOGNIZER NATP-COMPOUND-RECOGNIZER)
                (:CONGRUENCE IFF-IMPLIES-EQUAL-NOT)
                ; (:DEFINITION APPLY-CASES-OK)
                (:DEFINITION EQ)
                (:DEFINITION EQL)
                ;; Jared: changed hons-get-fn-do-hopy to hons-get for new hons code
                (:DEFINITION HONS-GET)
                (:DEFINITION KWOTE)
                (:DEFINITION KWOTE-LST)
                (:DEFINITION NATP)
                (:DEFINITION NFIX)
                (:DEFINITION NOT)
                (:DEFINITION NTHCDR)
                (:DEFINITION SYNP)
                (:ELIM CAR-CDR-ELIM)
                (:EXECUTABLE-COUNTERPART CAR)
                (:EXECUTABLE-COUNTERPART CDR)
                (:EXECUTABLE-COUNTERPART CONS)
                (:EXECUTABLE-COUNTERPART CONSP)
                (:EXECUTABLE-COUNTERPART EQUAL)
                (:EXECUTABLE-COUNTERPART KEYWORDP)
                (:EXECUTABLE-COUNTERPART KWOTE-LST)
                (:EXECUTABLE-COUNTERPART MV-NTH)
                (:EXECUTABLE-COUNTERPART NOT)
                (:EXECUTABLE-COUNTERPART SYMBOLP)
                (:EXECUTABLE-COUNTERPART TRUE-LISTP)
                (:EXECUTABLE-COUNTERPART ZP)
                (:INDUCTION APPLY-CASES-IND)
                (:META MV-NTH-CONS-META)
                (:REWRITE EVMETA-EV-OF-FNCALL-ARGS)
                evmeta-ev-of-variable
                evmeta-ev-of-quote
                ;; evmeta-ev-of-lambda
                evmeta-ev-lst-of-atom
                evmeta-ev-lst-of-cons
                evmeta-ev-of-cons-call
                evmeta-ev-of-kwote-lst-call
                evmeta-ev-of-if-call
                evmeta-ev-of-eql-call
                ;; (:REWRITE EVMETA-EV-CONSTRAINT-1)
                ;; (:REWRITE EVMETA-EV-constraint-16)
                ;; (:REWRITE EVMETA-EV-constraint-18)
                ;; (:REWRITE EVMETA-EV-constraint-21)
                ;; (:REWRITE EVMETA-EV-CONSTRAINT-2)
                ;; (:REWRITE EVMETA-EV-constraint-24)
                ;; (:REWRITE EVMETA-EV-CONSTRAINT-4)
                ;; (:REWRITE EVMETA-EV-CONSTRAINT-5)
                ;; (:REWRITE EVMETA-EV-constraint-8)
                ;; (:REWRITE EVMETA-EV-constraint-11)
                (:REWRITE EVMETA-EV-EV-APPLY-ARGLIST)
                (:REWRITE EVMETA-EV-LST-TERM-LIST-OF-NTHS)
                (:REWRITE EVMETA-EV-THEOREMP-CONJOIN-CLAUSES-CONS)
                ; consp-term-list-of-nths zp
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;                 (:REWRITE ASSOC-EQ-IS-ASSOC-EQUAL)
                (:REWRITE CAR-CONS)
                (:REWRITE CDR-CONS)
                ;; (:REWRITE EV-FUNCTION-CLAUSE-CORRECT)
                (:REWRITE FUNCALL-EQUAL-VALUES-CLAUSE-CORRECT)
                (:REWRITE LIST-OF-NTHSP-TERM-LIST-OF-NTHS)
                (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL)
                (:TYPE-PRESCRIPTION KEYWORDP)
                check-ev-of-quote-correct
                check-ev-of-call-correct
                check-ev-of-variable-correct
                ev-of-arglist-is-ground
               ;;  (:TYPE-PRESCRIPTION KWOTE-LST)
               ;;  (:TYPE-PRESCRIPTION TERM-LIST-OF-NTHS)
                )))
  (defthm apply-cases-ok-correct
    (let ((erp (apply-cases-ok term rule-alist evfn (w state))))
      (implies (and (evmeta-ev-meta-extract-global-facts)
                    (check-ev-of-quote evfn quote-thmname (w state))
                    (check-ev-of-variable evfn var-thmname (w state))
                    (not (equal evfn 'quote))
                    (mv-nth 0 (evmeta-ev term a))
                    (not erp))
               (equal (mv-nth 1 (evmeta-ev term a))
                      (evmeta-ev
                       `(,evfn (cons fn (kwote-lst args)) 'nil)
                       a))))
    :hints (("goal":induct (apply-cases-ind term)
             :expand ((apply-cases-ok term rule-alist evfn (w state)))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance reduce-identities-identity
                                    (term (cadadr (cdaddr term)))
                                    (fn (cdr (assoc-equal 'fn a))))))))))


;; (def-functional-instance
;;   interp-function-lookup-correct-for-evmeta-ev
;;   interp-function-lookup-correct
;;   ((ifl-ev evmeta-ev)
;;    (ifl-ev-lst evmeta-ev-lst)
;;    (ifl-ev-falsify evmeta-ev-falsify)
;;    (ifl-ev-meta-extract-global-badguy
;;     evmeta-ev-meta-extract-global-badguy))
;;   :hints ((and stable-under-simplificationp
;;                '(:use (evmeta-ev-of-fncall-args
;;                        evmeta-ev-falsify
;;                        evmeta-ev-meta-extract-global-badguy)))))

;; (def-functional-instance
;;   interp-function-lookup-correct-1-for-evmeta-ev
;;   interp-function-lookup-correct-1
;;   ((ifl-ev evmeta-ev)
;;    (ifl-ev-lst evmeta-ev-lst)
;;    (ifl-ev-falsify evmeta-ev-falsify)
;;    (ifl-ev-meta-extract-global-badguy
;;     evmeta-ev-meta-extract-global-badguy)))

(without-waterfall-parallelism
(defun apply-for-ev-cp (clause hints state)
  (declare (ignore hints)
           (xargs :stobjs state
                  :verify-guards nil))
  (case-match clause
    ((('implies
       ('mv-nth ''0 (applyfn 'fn 'args))
       ('equal ('mv-nth ''1 (applyfn 'fn 'args))
               (evalfn . '((cons fn (kwote-lst args)) 'nil)))))
     (b* (((when (eq evalfn 'quote))
           (mv "The eval function is QUOTE which is silly."
               nil state))
          ;; ((unless (consp app))
          ;;  (mv "the clause is malformed in an improbable way"
          ;;      nil state))
          ;; ((cons applyfn formals) app)
          (world (w state))
          (rule-alist (ev-collect-apply-lemmas evalfn nil world))
          ;; ((mv erp body formals defs)
          ;;  (interp-function-lookup applyfn nil nil world))
          ((mv ok formals body)
           (fn-get-def applyfn state))
          ((unless ok) (mv "error looking up apply function" nil state))
          ((unless (equal '(fn args) formals))
           (mv "The formals in the clause don't match the world"
               nil state))
          ;; (clauses-for-apply-def
          ;;  (interp-defs-alist-clauses defs))
          (erp
           (apply-cases-ok body rule-alist evalfn world))
          ((when erp) (mv erp nil state))
          (quote-name (cdr (hons-get :quote rule-alist)))
          (var-name (cdr (hons-get :lookup-var rule-alist)))
          ((unless (check-ev-of-quote evalfn (cadr quote-name) world))
           (mv "The quote constraint is malformed" nil state))
          ((unless (check-ev-of-variable evalfn (cadr var-name) world))
           (mv "The variable constraint is malformed" nil state)))
       (value nil)))
    (& (mv (msg "The clause was not of the correct form: ~x0"
                clause)
           nil state)))))

(in-theory (disable ev-collect-apply-lemmas))

(include-book "tools/with-quoted-forms" :dir :system)

(local (defthm len-of-kwote-lst
         (equal (len (kwote-lst x)) (len x))))

(local (defthm len-of-evmeta-ev-lst
         (equal (len (evmeta-ev-lst x a)) (len x))))

(local (defthm evmeta-ev-lst-of-kwote-lst
         (equal (evmeta-ev-lst (kwote-lst x) a)
                (true-list-fix x))))

(defthm apply-for-ev-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (evmeta-ev-meta-extract-global-facts)
                (evmeta-ev-theoremp
                 (conjoin-clauses
                  (clauses-result
                   (apply-for-ev-cp clause hints state)))))
           (evmeta-ev (disjoin clause) a))
  :hints(("goal" :in-theory
            (e/d (evmeta-ev-disjoin-when-consp
                  evmeta-ev-of-fncall-args)
                 (apply-cases-ok-correct
                  evmeta-ev-meta-extract-fn-check-def
                  apply-cases-ok
                  pseudo-term-listp
                  ;; assoc
                  hons-assoc-equal
                  ;; assoc-equal
                  default-car default-cdr
                  nth alistp interp-defs-alist-clauses w))
            :restrict
            ((evmeta-ev-disjoin-when-consp
              ((x clause)))))
         (and stable-under-simplificationp
              (bind-as-in-definition
               apply-for-ev-cp
               (rule-alist body evalfn quote-name
                           var-name applyfn formals)
               `(:use ((:instance
                        apply-cases-ok-correct
                        (term ,body)
                        (rule-alist ,rule-alist)
                        (evfn ,evalfn)
                        (quote-thmname (cadr ,quote-name))
                        (var-thmname (cadr ,var-name))
                        (a (pairlis$ ,formals
                                     (evmeta-ev-lst ,formals a))))
                       (:instance EVMETA-EV-META-EXTRACT-FN-CHECK-DEF
                        (fn ,applyfn) (st state) (formals ,formals) (body ,body)
                        (args (kwote-lst (evmeta-ev-lst ,formals a)))
                        (a a)))
                 :do-not-induct t))))
  :otf-flg t
  :rule-classes :clause-processor)



(local
 (progn
   (defapply evmeta-ev-apply
     (EQL EQUAL IF NOT
          ;; USE-BY-HINT USE-THESE-HINTS
          CAR CDR NTH
          CONS CONSP
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced assoc by assoc-equal).]
          ASSOC-EQUAL
          KWOTE-LST SYMBOLP
          PAIRLIS$ MV-NTH hide ;; return-last makes this fail (guard issue)
          )
     :theoremsp nil)

   (without-waterfall-parallelism
    (defthm evmeta-ev-apply-agrees-with-evmeta-ev
      (implies (mv-nth 0 (evmeta-ev-apply fn args))
               (equal (mv-nth 1 (evmeta-ev-apply fn args))
                      (evmeta-ev (cons fn (kwote-lst args)) nil)))
      :hints (("goal" :clause-processor
               (apply-for-ev-cp clause nil state))
              (use-by-computed-hint clause)
              (use-these-hints-hint clause))))))



(defun mk-defeval-entries (fns world)
  (if (atom fns)
      nil
    (let ((formals (getprop (car fns) 'formals nil 'current-acl2-world world)))
      (cons (cons (car fns) formals)
            (mk-defeval-entries (cdr fns) world)))))

(logic)


(defevaluator cadr-nth-ev cadr-nth-ev-lst
  ((car x) (cdr x) (nth n x)))


(defun term-count-cdrs (x)
  (declare (xargs :guard (pseudo-termp x)))
  (b* (((when (or (atom x) (not (eq (car x) 'cdr))))
        (mv 0 x))
       ((mv count final) (term-count-cdrs (cadr x))))
    (mv (+ 1 count) final)))

(Defthm natp-term-count-cdrs
  (natp (mv-nth 0 (term-count-cdrs x)))
  :rule-classes :type-prescription)

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm term-count-cdrs-correct
  (mv-let (n y)
    (term-count-cdrs x)
    (equal (nthcdr n (cadr-nth-ev y a))
           (cadr-nth-ev x a)))
  :hints (("goal" :induct (term-count-cdrs x))))

(local (defthm car-of-nthcdr
         (equal (car (nthcdr n x))
                (nth n x))))

(defthm term-count-cdrs-correct-nth
  (mv-let (n y)
    (term-count-cdrs x)
    (equal (nth n (cadr-nth-ev y a))
           (car (cadr-nth-ev x a))))
  :hints (("goal" :use ((:instance car-of-nthcdr
                         (n (mv-nth 0 (term-count-cdrs x)))
                         (x (cadr-nth-ev (mv-nth 1 (term-count-cdrs x))
                                      a))))
           :in-theory (disable car-of-nthcdr))))

(defun car-to-nth-meta (x)
  (declare (xargs :guard (pseudo-termp x)))
  (b* (((unless (and (consp x) (eq (car x) 'car))) x)
       ((mv n inner-term) (term-count-cdrs (cadr x))))
    `(nth ',n ,inner-term)))

(defthmd car-to-nth-meta-correct
  (equal (cadr-nth-ev x a)
         (cadr-nth-ev (car-to-nth-meta x) a))
  :rule-classes ((:meta :trigger-fns (car))))

(defthmd nth-of-cdr
  (equal (nth n (cdr x))
         (nth (+ 1 (nfix n)) x)))

(defconst *apply/ev/concrete-ev-template*
  '(progn
     (encapsulate nil
       (defapply _name_-apply
         _fnsyms_
         :theoremsp nil)

       (def-ruleset before-_name_-ev (current-theory :here))
       (with-output
        :off :all :on (error)
        (make-event
         `(defevaluator-fast _name_-ev _name_-ev-lst
            ,(mk-defeval-entries '_fnsyms_ (w state))
            :namedp t)))
       (def-ruleset _name_-ev-rules
         (set-difference-theories
          (current-theory :here)
          (ruleset 'before-_name_-ev)))

       (local (in-theory (Disable _name_-apply)))

       (defthmd _name_-apply-agrees-with-_name_-ev
         (implies (mv-nth 0 (_name_-apply fn args))
                  (equal (mv-nth 1 (_name_-apply fn args))
                         (_name_-ev (cons fn (kwote-lst args)) nil)))
         :hints (("goal" :clause-processor
                  (apply-for-ev-cp clause nil state)
                  :in-theory (disable*
                              (:rules-of-class :definition :here)
                              (:rules-of-class :type-prescription :here)))
                 (use-by-computed-hint clause)
                 (use-these-hints-hint clause)
                 (cw "fell through: ~x0~%" clause)))
       (defthmd _name_-apply-agrees-with-_name_-ev-rev
         (implies (mv-nth 0 (_name_-apply fn args))
                  (equal (_name_-ev (cons fn (kwote-lst args)) nil)
                         (mv-nth 1 (_name_-apply fn args))))
         :hints(("Goal" :in-theory '(_name_-apply-agrees-with-_name_-ev))))

       (defthmd _name_-apply-of-fns
         (implies (member f '_fnsyms_)
                  (mv-nth 0 (_name_-apply f args)))
         :hints (("goal" :in-theory '(_name_-apply
                                      nth (eql)
                                      member-of-cons
                                      member-when-atom))))
       (local (in-theory (enable _name_-apply-of-fns
                                 car-cdr-elim
                                 car-cons
                                 cdr-cons
                                 acl2-count
                                 (:t acl2-count)
                                 o< o-finp
                                 pseudo-term-listp
                                 pseudo-termp
                                 eqlablep
                                 consp-assoc-equal
                                 assoc-eql-exec-is-assoc-equal
                                 alistp-pairlis$
                                 atom not eq
                                 symbol-listp-forward-to-true-listp)))

       (mutual-recursion
        (defun _name_-ev-concrete (x a appalist)
          (declare (xargs :guard (and (pseudo-termp x)
                                      (alistp appalist)
                                      (alistp a))
                          :hints(("Goal" :in-theory (enable
                                                     car-cdr-elim
                                                     car-cons
                                                     cdr-cons
                                                     acl2-count
                                                     (:t acl2-count)
                                                     o< o-finp)))))
          (b* (((when (atom x)) (and (symbolp x) x (cdr (assoc x a))))
               ((when (eq (car x) 'quote)) (cadr x))
               (args (_name_-ev-concrete-lst
                      (cdr x) a appalist))
               ((when (consp (car x)))
                (_name_-ev-concrete
                 (caddar x)
                 (pairlis$ (cadar x) args)
                 appalist))
               ((unless (mbt (symbolp (car x)))) nil)
               ((mv ok val)
                (_name_-apply (car x) args))
               ((when ok) val))
            (cdr (assoc-equal (cons (car x) args) appalist))))
        (defun _name_-ev-concrete-lst (x a appalist)
          (declare (xargs :guard (and (pseudo-term-listp x)
                                      (alistp appalist)
                                      (alistp a))))
          (if (atom x)
              nil
            (cons (_name_-ev-concrete (car x) a appalist)
                  (_name_-ev-concrete-lst (cdr x) a appalist)))))

       (defthm _name_-ev-concrete-lst-of-kwote-lst
         (equal (_name_-ev-concrete-lst (kwote-lst x) a appalist)
                (list-fix x))
         :hints(("Goal" :in-theory (enable kwote-lst list-fix kwote))))

       (defthm _name_-eval-nth-kwote-lst
         (equal (_name_-ev (nth n (kwote-lst x)) a)
                (nth n x))
         :hints(("Goal" :in-theory (enable kwote-lst kwote nth))))

       (defthm nth-of-_name_-ev-concrete-lst
         (equal (nth n (_name_-ev-concrete-lst x a appalist))
                (_name_-ev-concrete (nth n x) a appalist))
         :hints(("Goal" :in-theory (e/d (nth)
                                        (_name_-ev-concrete))
                 :induct t
                 :expand ((_name_-ev-concrete nil a appalist))))))

     (defthm _name_-ev-concrete-is-instance-of-_name_-ev
       t
       :hints (("goal" :use ((:functional-instance
                              (:theorem (equal (_name_-ev x a) (_name_-ev x a)))
                              (_name_-ev
                               (lambda (x a)
                                 (_name_-ev-concrete x a appalist)))
                              (_name_-ev-lst
                               (lambda (x a)
                                 (_name_-ev-concrete-lst x a appalist)))))
                :expand ((_name_-ev-concrete x a appalist)
                         (:free (x y)
                          (_name_-ev-concrete (cons x y)
                                              nil appalist))
                         (_name_-ev-concrete nil a appalist)
                         (_name_-ev-concrete-lst x a appalist)
                         (_name_-ev-concrete-lst x-lst a appalist)
                         (:free (x) (hide x)))
                :in-theory (e/d** (_name_-apply-of-fns
                                   car-to-nth-meta-correct
                                   ;; _name_-ev-rules
                                   kwote nfix
                                   _name_-ev-of-fncall-args
                                   _name_-ev-of-nonsymbol-atom
                                   _name_-ev-of-bad-fncall
                                   (cons) (equal) (member-equal) (eql)
                                   car-cons cdr-cons _name_-eval-nth-kwote-lst
                                   list-fix-when-true-listp
                                   _name_-apply-agrees-with-_name_-ev-rev
                                   _name_-apply-of-fns
                                   _name_-ev-concrete-lst-of-kwote-lst
                                   nth-of-_name_-ev-concrete-lst
                                   nth-of-cdr
                                   nth-0-cons
                                   (:t _name_-ev-concrete-lst))
                                  ;; (_name_-apply
                                  ;;  member-of-cons
                                  ;;  subsetp-car-member
                                  ;;  member-equal
                                  ;;  _name_-ev-concrete
                                  ;;  set::double-containment
                                  ;;  default-cdr
                                  ;;  (_name_-apply)
                                  ;;  (:rules-of-class :definition :here))
                                  ;; (kwote ;; kwote-lst _name_-ev-concrete-lst
                                  ;;  nfix _name_-ev-of-fncall-args)
                                  )
                ;; :in-theory '(_name_-apply-agrees-with-_name_-ev
                ;;              _name_-apply-of-fns
                ;;              (member-equal) (take))
                )
               (and stable-under-simplificationp
                    '(:expand ((:free (fn args) (_name_-apply fn args))
                               (:free (x) (hide x))))))
       :rule-classes nil)))

(defun defapply/ev/concrete-ev-fn (name fns)
  (declare (xargs :mode :program))
  (template-subst
   *apply/ev/concrete-ev-template*
   :atom-alist `((_name_ . ,name)
                 (_fnsyms_ . ,fns))
   :str-alist `(("_NAME_" . ,(symbol-name name)))
   :pkg-sym name))

(defmacro defapply/ev/concrete-ev (name fns)
  (defapply/ev/concrete-ev-fn name fns))



(set-rewrite-stack-limit 10000)

(comp t) ; helpful e.g. for Allegro CL

(local
 (progn
   ;; (defapply/ev/concrete-ev mything2 (if len mv-list binary-append))

   (without-waterfall-parallelism
    (make-event
     `(defapply/ev/concrete-ev
        everything

        ;; Note: Earlier this was (nthcdr 400 *all-logic-function-syms*), but
        ;; Allegro CL died with a large rewrite stack.

        ,(take 100 *all-logic-function-syms*))))))

;;  100:    2.02      97M
;;  200:    4.02     204M
;;  400:    8.77     592M
;;  600:   16.43    1303M
;;  800:   27.43    2474M
;; 1000:   44.35    4235M
;; 1200:   66.82    6708M
;; 1246:   71.74    7391M

