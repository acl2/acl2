; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

; defapply.lisp -- introduces an executable apply function that recognizes a
; specified set of function symbols.

(in-package "ACL2")

(include-book "tools/bstar" :dir :system)
(include-book "clause-processors/generalize" :dir :system)
(include-book "tools/rulesets" :dir :system)
(include-book "clause-processors/use-by-hint" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "tools/defevaluator-fast" :dir :system)
(include-book "tools/mv-nth" :dir :system)
(include-book "evaluator-metatheorems")
(include-book "interp-function-lookup")
(include-book "tools/def-functional-instance" :dir :system)

(set-waterfall-parallelism nil) ; for apply-for-ev-cp

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
       (stobjs-out (fgetprop fn 'stobjs-out :none world)))
    (cond
     ((or (eq formals :none)
          (eq stobjs-out :none))
      (er hard 'defapply-call "~
The function ~x0 is missing its ~x1 property; perhaps it is not defined.~%"
          fn (if formals 'stobjs-out 'formals)))
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
  (intern-in-package-of-symbol
   (concatenate
    'string (symbol-name apply-name)
    "-OF-" (symbol-package-name fn) "::" (symbol-name fn))
   apply-name))


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
                         :normalize nil))
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

  (local
   (defthm evmeta-ev-lst-term-list-of-nths1
     (implies (and (evmeta-ev-theoremp
                    (disjoin (ev-quote-clause evfn quote-name)))
                   (evmeta-ev-theoremp
                    (disjoin (ev-lookup-var-clause evfn var-name)))
                   (not (equal evfn 'quote))
                   (natp idx) (natp n))
              (equal (evmeta-ev-lst
                      (term-list-of-nths n idx args)
                      a)
                     (evmeta-ev-lst
                      (ev-apply-arglist-on-result
                       n evfn
                       (nthcdr idx (kwote-lst (evmeta-ev args a)))
                       alst)
                      nil)))
     :hints(("Goal" :in-theory (enable evmeta-ev-constraint-0))
            (and stable-under-simplificationp
                 (case-match id ((('0 '1) . &) t))
                 '(:cases ((< idx (len (evmeta-ev args a)))))))
     :rule-classes nil))


  (defthm evmeta-ev-lst-term-list-of-nths
     (implies (and (evmeta-ev-theoremp
                    (disjoin (ev-quote-clause evfn quote-name)))
                   (evmeta-ev-theoremp
                    (disjoin (ev-lookup-var-clause evfn var-name)))
                   (not (equal evfn 'quote))
                   (natp idx) (natp n))
              (equal (evmeta-ev-lst
                      (term-list-of-nths n idx args)
                      a)
                     (evmeta-ev-lst
                      (ev-apply-arglist-on-result
                       n evfn
                       (nthcdr idx (kwote-lst (evmeta-ev args a)))
                       nil)
                      nil)))
     :hints(("Goal" :in-theory (enable evmeta-ev-constraint-0))
            (and stable-under-simplificationp
                 (case-match id ((('0 '1) . &) t))
                 '(:cases ((< idx (len (evmeta-ev args a)))))))))


(in-theory (disable funcall-equals-values-clause))


(defun reduce-identities (term fn)
  (case-match term
    ((!fn . &) term)
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
(defun apply-cases-ok (term rule-alist evfn clauses)
  (declare (xargs :normalize nil))
  (case-match term
    (('if ('eql 'fn ('quote fnname . &). &) values rest . &)
     (b* (((mv erp clauses)
           (apply-cases-ok rest rule-alist evfn clauses))
          ((when erp) (mv erp nil))
          ((when (or (keywordp fnname) (eq fnname 'quote)))
           (mv (msg "~x0 is not allowed as a function name."
                    fnname) nil))
          (look (hons-get fnname rule-alist))
          ((when (not look))
           (mv (msg "Function ~x0 not recognized by evaluator."
                    fnname) nil))
          ((cons arity rune) (cdr look))
          ((unless (natp arity))
           (mv (msg "Function ~x0 supposedly has an arity of ~x1"
                    fnname arity)
               nil))
          (clauses
           (cons (ev-function-clause evfn fnname arity rune)
                 clauses)))
       (case-match values
         (('cons ''t ('cons call . &) . &)
          (b* ((fncall (reduce-identities call fnname)))
            (case-match fncall
              ((!fnname . args)
               ;;              (prog2$ (cw "fncall: ~x0, fnname-args case~%"
               ;;                          fncall)
               (if (list-of-nthsp arity 0 'args args)
                   (mv nil clauses)
                 (mv (msg "Malformed function call ~x0: bad arity?"
                          fncall)
                     nil)))
              (& (mv (msg "Unrecognized form of return value: ~x0"
                          call)
                     nil)))))
         (& (mv (msg "Unrecognized form of return value: ~x0"
                     values)
                nil)))))
    ('(cons 'nil (cons 'nil 'nil))
     (mv nil clauses))
    (& (mv (msg "Unrecognized subterm: ~x0" term) nil))))

(defun apply-cases-ind (term)
  (declare (xargs :normalize nil))
  (case-match term
    (('if ('eql 'fn ('quote . &) . &) & rest . &)
     (apply-cases-ind rest))
    (& term)))



(defthm apply-cases-ok-old-clauses-correct
  (mv-let (erp out-clauses)
    (apply-cases-ok term rule-alist evfn in-clauses)
    (implies (and (not (evmeta-ev-theoremp
                   (conjoin-clauses in-clauses)))
                  (not erp))
             (not (evmeta-ev-theoremp
                   (conjoin-clauses out-clauses)))))
  :hints(("Goal" :in-theory (e/d** ((:induction apply-cases-ind)
                                    ;; Jared: changed from hons-get-fn-do-hopy
                                    ;; to hons-get for new hons code
                                    eq hons-get natp nfix
                                    (:rules-of-class :executable-counterpart
                                                     :here)
                                    evmeta-ev-theoremp-conjoin-clauses-cons
                                    list-of-nthsp-term-list-of-nths))
          :induct (apply-cases-ind term)
          :expand ((apply-cases-ok term rule-alist evfn in-clauses)
                   (apply-cases-ok '(cons 'nil (cons 'nil 'nil))
                                   rule-alist evfn in-clauses)))))




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
                (:REWRITE EVMETA-EV-CONSTRAINT-0)
                (:REWRITE EVMETA-EV-CONSTRAINT-1)
                (:REWRITE EVMETA-EV-CONSTRAINT-14)
                (:REWRITE EVMETA-EV-CONSTRAINT-16)
                (:REWRITE EVMETA-EV-CONSTRAINT-19)
                (:REWRITE EVMETA-EV-CONSTRAINT-2)
                (:REWRITE EVMETA-EV-CONSTRAINT-22)
                (:REWRITE EVMETA-EV-CONSTRAINT-4)
                (:REWRITE EVMETA-EV-CONSTRAINT-5)
                (:REWRITE EVMETA-EV-CONSTRAINT-6)
                (:REWRITE EVMETA-EV-CONSTRAINT-9)
                (:REWRITE EVMETA-EV-EV-APPLY-ARGLIST)
                (:REWRITE EVMETA-EV-LST-TERM-LIST-OF-NTHS)
                (:REWRITE EVMETA-EV-THEOREMP-CONJOIN-CLAUSES-CONS)
                ; consp-term-list-of-nths zp
; [Removed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2.]
;                 (:REWRITE ASSOC-EQ-IS-ASSOC-EQUAL)
                (:REWRITE CAR-CONS)
                (:REWRITE CDR-CONS)
                (:REWRITE EV-FUNCTION-CLAUSE-CORRECT)
                (:REWRITE FUNCALL-EQUAL-VALUES-CLAUSE-CORRECT)
                (:REWRITE LIST-OF-NTHSP-TERM-LIST-OF-NTHS)
                (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL)
                (:TYPE-PRESCRIPTION KEYWORDP)
               ;;  (:TYPE-PRESCRIPTION KWOTE-LST)
               ;;  (:TYPE-PRESCRIPTION TERM-LIST-OF-NTHS)
                )))
  (defthm apply-cases-ok-correct
    (mv-let (erp clauses)
      (apply-cases-ok term rule-alist evfn in-clauses)
      (implies (and (not erp)
                    (evmeta-ev-theoremp
                     (conjoin-clauses clauses))
                    (evmeta-ev-theoremp
                     (disjoin (ev-quote-clause evfn quote-name)))
                    (evmeta-ev-theoremp
                     (disjoin (ev-lookup-var-clause evfn var-name)))
                    (not (equal evfn 'quote))
                    (mv-nth 0 (evmeta-ev term a)))
               (equal (mv-nth 1 (evmeta-ev term a))
                      (evmeta-ev
                       `(,evfn (cons fn (kwote-lst args)) 'nil)
                       a))))
    :hints (("goal":induct (apply-cases-ind term)
             :expand ((apply-cases-ok term rule-alist evfn in-clauses))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance reduce-identities-identity
                                    (term (cadadr (cdaddr term)))
                                    (fn (cdr (assoc-equal 'fn a))))))))))


(def-functional-instance
  interp-function-lookup-correct-for-evmeta-ev
  interp-function-lookup-correct
  ((ifl-ev evmeta-ev)
   (ifl-ev-lst evmeta-ev-lst)
   (ifl-ev-falsify evmeta-ev-falsify)
   (ifl-ev-meta-extract-global-badguy
    evmeta-ev-meta-extract-global-badguy))
  :hints ((and stable-under-simplificationp
               '(:use (evmeta-ev-constraint-0
                       evmeta-ev-falsify
                       evmeta-ev-meta-extract-global-badguy)))))

(def-functional-instance
  interp-function-lookup-correct-1-for-evmeta-ev
  interp-function-lookup-correct-1
  ((ifl-ev evmeta-ev)
   (ifl-ev-lst evmeta-ev-lst)
   (ifl-ev-falsify evmeta-ev-falsify)
   (ifl-ev-meta-extract-global-badguy
    evmeta-ev-meta-extract-global-badguy)))

(defun apply-for-ev-cp (clause hints state)
  (declare (ignore hints)
           (xargs :stobjs state
                  :verify-guards nil))
  (case-match clause
    ((('implies
       ('mv-nth ''0 app)
       ('equal ('mv-nth ''1 app)
               (evalfn . '((cons fn (kwote-lst args)) 'nil)))))
     (b* (((when (eq evalfn 'quote))
           (mv "The eval function is QUOTE which is silly."
               nil state))
          ((unless (consp app))
           (mv "the clause is malformed in an improbable way"
               nil state))
          ((cons applyfn formals) app)
          (world (w state))
          (rule-alist (ev-collect-apply-lemmas evalfn nil world))
          ((mv erp body formals-look defs)
           (interp-function-lookup applyfn nil nil world))
          ((when erp) (mv erp nil state))
          ((unless (equal formals formals-look))
           (mv "The formals in the clause don't match the world"
               nil state))
          (clauses-for-apply-def
           (interp-defs-alist-clauses defs))
          ((mv erp cases-clauses)
           (apply-cases-ok body rule-alist evalfn nil))
          ((when erp) (mv erp nil state))
          (quote-name (cdr (hons-get :quote rule-alist)))
          (var-name (cdr (hons-get :lookup-var rule-alist))))
       (value
        (list* (ev-quote-clause evalfn quote-name)
               (ev-lookup-var-clause evalfn var-name)
               (append clauses-for-apply-def
                       cases-clauses)))))
    (& (mv (msg "The clause was not of the correct form: ~x0"
                clause)
           nil state))))

(in-theory (disable ev-collect-apply-lemmas))

(include-book "tools/with-quoted-forms" :dir :system)

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
            (e/d (evmeta-ev-disjoin-when-consp)
                 (apply-cases-ok-correct
                  apply-cases-ok
                  pseudo-term-listp
                  assoc hons-assoc-equal
                  assoc-equal default-car default-cdr
                  nth alistp interp-defs-alist-clauses w))
            :restrict
            ((evmeta-ev-disjoin-when-consp
              ((x clause)))))
         (and stable-under-simplificationp
              (bind-as-in-definition
               apply-for-ev-cp
               (rule-alist body evalfn quote-name
                           var-name)
               `(:use ((:instance
                        apply-cases-ok-correct
                        (term ,body)
                        (rule-alist ,rule-alist)
                        (evfn ,evalfn)
                        (in-clauses nil)
                        (quote-name ,quote-name)
                        (var-name ,var-name)))
                 :do-not-induct t))))
  :otf-flg t
  :rule-classes :clause-processor)



(local
 (progn
   (defapply evmeta-ev-apply
     (EQL EQUAL IF NOT
          USE-BY-HINT USE-THESE-HINTS CAR CDR NTH
          CONS CONSP
; [Changed by Matt K. to handle changes to member, assoc, etc. after ACL2 4.2
;  (replaced assoc by assoc-equal).]
          ASSOC-EQUAL
          KWOTE-LST SYMBOLP
          PAIRLIS$ MV-NTH hide ;; return-last makes this fail (guard issue)
          )
     :theoremsp nil)

   (defthm evmeta-ev-apply-agrees-with-evmeta-ev
     (implies (mv-nth 0 (evmeta-ev-apply fn args))
              (equal (mv-nth 1 (evmeta-ev-apply fn args))
                     (evmeta-ev (cons fn (kwote-lst args)) nil)))
     :hints (("goal" :clause-processor
              (apply-for-ev-cp clause nil state))
             (use-by-computed-hint clause)
             (use-these-hints-hint clause)))))


#||


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
                                            open-output-channel!)))
             (list-of-nilsp (fgetprop (car syms) 'stobjs-out nil
                                      world))
             (list-of-nilsp (fgetprop (car syms) 'stobjs-in nil
                                      world))
             (not (and (member (car syms) *ec-call-bad-ops*)
                       (not (equal (fgetprop (car syms) 'guard ''t
                                             world)
                                   ''t)))))
        (cons (car syms) (logic-function-syms (cdr syms) world))
      (logic-function-syms (cdr syms) world))))

(defun mk-defeval-entries (fns world)
  (if (atom fns)
      nil
    (let ((formals (getprop (car fns) 'formals nil 'current-acl2-world world)))
      (cons (cons (car fns) formals)
            (mk-defeval-entries (cdr fns) world)))))



(logic)

(make-event
 `(defconst *all-logic-function-syms*
    ',(let ((world (w state)))
        (logic-function-syms (all-syms-in-world world) world))))

(make-event
 `(defconst *defeval-entries-for-all-reasonable-functions*
    ',(let ((world (w state)))
        (mk-defeval-entries *all-logic-function-syms* world))))


(make-event
 `(defapply big-test-apply
    ,*all-logic-function-syms*
    :theoremsp nil))

(make-event
 `(defevaluator-fast big-test-ev big-test-ev-lst
    ,*defeval-entries-for-all-reasonable-functions*))


(time$
 (defthm big-test-apply-agrees-with-big-teste-ev
     (implies (mv-nth 0 (big-test-apply fn args))
              (equal (mv-nth 1 (big-test-apply fn args))
                     (big-test-ev (cons fn (kwote-lst args)) nil)))
     :hints (("goal" :clause-processor
              (apply-for-ev-cp clause nil state)
              :in-theory (disable*
                          (:rules-of-class :definition :here)
                          (:rules-of-class :type-prescription :here)))
             (use-by-computed-hint clause)
             (use-these-hints-hint clause)
             (cw "fell through: ~x0~%" clause))))
;; awesome!

||#

