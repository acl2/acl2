; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")
(include-book "projects/apply/top" :dir :system)
(include-book "macros" )
;(include-book "rp-rewriter")
(include-book "aux-functions")
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "proofs/measure-lemmas")
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)

(define create-eval-fnc (fnc-alist)
  :guard (fnc-alistp fnc-alist)
  :enabled t
  (if (atom fnc-alist)
      nil
    (cons
     (cons (caar fnc-alist)
           (sas 'a 0 (cdar fnc-alist)))
     (create-eval-fnc (cdr fnc-alist)))))

(defmacro create-eval (fnc-alist &optional (eval-name 'big-evl) &key namedp)
  `(make-event
    `(defevaluator
       ,',eval-name ,',(sa (symbol-name eval-name) '-lst)
       ,(create-eval-fnc ,fnc-alist)
       :namedp ,,namedp)))

;; (encapsulate
;;   (((foo) => *))
;;   (local
;;    (defun foo ()
;;      nil)))

(defconst *small-evl-fncs*
  '(;;(foo . 0)
    (equal . 2)
    (falist . 2)
    (not . 1)
    (if . 3)
    (hide . 1)
    (implies . 2)
    (casesplit-from-context-trig . 1)
    (dont-rw-context . 1)
    (cons . 2)
    (synp . 3)
    (return-last . 3)
    (rp . 2)
    (equals . 2)
    (cdr . 1)
    (car . 1)
    (iff . 2)
    (typespec-check . 2)
    (acl2-numberp . 1)
    (unary-- . 1)
    (unary-/ . 1)
    (< . 2)
    (char-code . 1)
    (characterp . 1)
    (code-char . 1)
    (integerp . 1)
    (natp . 1)
    (zp . 1)
    (not . 1)
    (bitp . 1)
    (rationalp . 1)
    (symbolp . 1)
    (complex-rationalp . 1)
    (denominator . 1)
    (stringp . 1)
    (numerator . 1)
    (realpart . 1)
    (imagpart . 1)
    (COERCE . 2)
    (symbol-package-name . 1)
    (intern-in-package-of-symbol . 2)
    (symbol-name . 1)
    (acl2::bad-atom<= . 2)
    (binary-+ . 2)
    (binary-* . 2)
    (consp . 1)
    (force . 1)
    (force$ . 3)

    ;; Below are temporary, will probably be removed when def-formula-checks
    ;; start supporting mutually recursive funcitons
    (rp-equal . 2)
    (rp-equal-subterms . 2)
    (rp-equal-cnt . 3)
    (rp-equal-cnt-subterms . 3)
    
    (apply$ . 2)
    (apply$-userfn . 2)
    (badge-userfn . 1)
    ))

(with-output
  :off :all
  :gag-mode nil
  (create-eval *small-evl-fncs*
               rp-evl
               :namedp t))

#|(progn
  ;; TEMPORARY. NEED TO REMOVE WHEN ABLE TO ADD APPLY$ and OTHERS TO EVALUATOR. 
  (skip-proofs
   (defthm rp-evl-of-apply$-call
     (implies (and (consp x)
                   (equal (car x) 'apply$))
              (equal (rp-evl x a)
                     (apply$ (rp-evl (cadr x) a)
                             (rp-evl (caddr x) a))))))

  (skip-proofs
   (defthm rp-evl-of-badge-userfn-call
     (implies (and (consp x)
                   (equal (car x) 'badge-userfn))
              (equal (rp-evl x a)
                     (badge-userfn (rp-evl (cadr x) a))))))

  (skip-proofs
   (defthm rp-evl-of-apply$-userfn-call
     (implies (and (consp x)
                   (equal (car x) 'apply$-userfn))
              (equal (rp-evl x a)
                     (apply$-userfn (rp-evl (cadr x) a)
                                    (rp-evl (caddr x) a)))))))|#

(acl2::def-meta-extract rp-evl rp-evl-lst)

(defmacro rp-evlt (term a)
  `(rp-evl (rp-trans ,term) ,a))

(defmacro rp-evlt-lst (lst a)
  `(rp-evl-lst (rp-trans-lst ,lst) ,a))

(acl2::add-untranslate-pattern (rp-evl (rp-trans ?x) ?y)  (rp-evlt ?x ?y))
(acl2::add-untranslate-pattern (rp-evl-lst (rp-trans-lst ?x) ?y)  (rp-evlt-lst ?x ?y))

(encapsulate
  nil
  (defun eval-and-all (lst a)
    (declare (xargs :guard (and (rp-term-listp lst) (alistp a))))
    (if (atom lst)
        t
      (and (rp-evlt (car lst) a)
           (eval-and-all (cdr lst) a))))

  (local (in-theory (enable cons-count-car-subterms
                            cons-count-cdr-subterms is-if-cons-count
                            m-measure-lemma6 is-rp-cons-count
                            o-p-cons-count measure-lemmas)))
  (mutual-recursion
   (defun valid-sc (term a)
     (declare
      (xargs :measure (acl2::nat-list-measure (list (cons-count term)))))
     (cond ((atom term) t)
           ((eq (car term) 'quote) t)
           ((is-if term)
            (and (or (valid-sc (cadr term) a)
                     #|(and (not (rp-evlt (caddr term) a))
                     (not (rp-evlt (cadddr term) a)))|#)
                 (if (rp-evlt (cadr term) a)
                     (valid-sc (caddr term) a)
                   (valid-sc (cadddr term) a))))
           ((is-rp term)
            (and (eval-and-all (context-from-rp term nil)
                               a)
                 (valid-sc (ex-from-rp term) a)))
           (t
            (and (implies (is-equals term)
                          (equal (rp-evlt (cadr term) a)
                                 (rp-evlt (caddr term) a)))
                 (valid-sc-subterms (cdr term) a)))))
   (defun valid-sc-subterms (subterms a)
     (declare
      (xargs :measure (acl2::nat-list-measure (list (cons-count subterms)))))
     (cond ((atom subterms) t)
           (t (and (valid-sc (car subterms) a)
                   (valid-sc-subterms (cdr subterms)
                                      a))))))
  ;; (table rp-rw 'valid-sc-fnc 'valid-sc)
  ;; (table rp-rw 'eval-and-all-fnc 'eval-and-all)
  )

(xdoc::defxdoc
  valid-sc
  :parents (rp-utilities)
  :short "A function that checks the side-conditions in a term is correct"
  :long "<p> (valid-sc term a) traverses the term and evaluates the
 side-conditions. Whenever it encounters a term of the form (rp ''prop x), it
 calls (rp-evlt `(prop ,x) a). Whenever it encounters a term of the form (if
 test then else), it recursively calls valid-sc for the test; and 'then' and
 'else' cases under the context of (rp-evlt test a)</p>
<p> For every step that RP-Rewriter takes, we prove that valid-sc on terms are
 maintained. Therefore, users have to prove that meta-rules also retains this invariance.</p>")

(encapsulate
  nil
  (local
   (in-theory (enable measure-lemmas )))
  (make-flag valid-sc :defthm-macro-name defthm-valid-sc))

#|(defmacro valid-rp-meta-rule-gen (index)
`(make-event
(b* ((world (w state))
(sk-fnc-name (SA "EVALS-EQUAL-SK"
(if (= ,index 0) nil ,index)))
(fnc-name (sa "VALID-RP-META-RULEP"
(if (= ,index 0) nil ,index)))
(fnc-name2 (sa "VALID-RP-META-RULE-LISTP"
(if (= ,index 0) nil ,index)))
(eval (cdr
(assoc-eq 'evl
(table-alist 'rp-rw world))))
(valid-sc-fnc (cdr
(assoc-eq 'valid-sc-fnc
(table-alist 'rp-rw world)))))
`(progn
(defun-sk ,sk-fnc-name (term1 term2)
(forall a
(implies (,valid-sc-fnc term1 a)
(and
(,valid-sc-fnc term2 a)
(equal (,eval term1 a)
(,eval term2 a))))))

#|(verify-guards ,sk-fnc-name)||#

         ;(table rp-rw 'meta-defunsk ',sk-fnc-name) ;

(defun-sk ,fnc-name (rule state-)
(declare (xargs :guard (weak-rp-meta-rule-rec-p rule)
:verify-guards nil))
(forall
term
(b* (((mv error res)
(magic-ev-fncall (rp-meta-fnc rule)
(list term)
state-
t nil)))
(implies
(and (not error)
(acl2::logicp (rp-meta-fnc rule) (w state-)))
(and
(if (rp-meta-dont-rw rule)
(and
#|(implies (,valid-sc-fnc term a)
(,valid-sc-fnc (mv-nth 0 res) a))||#
(implies (rp-termp term)
(,sk-fnc-name term (mv-nth 0 res))))
(and #|(implies (,valid-sc-fnc term a)
(,valid-sc-fnc res a))||#
(implies (rp-termp term)
(,sk-fnc-name term res)))))))))

         ;(table rp-rw 'meta-valid-fn ',fnc-name) ;

(defun ,fnc-name2 (rules state)
(declare (xargs :guard (weak-rp-meta-rule-recs-p rules)
:verify-guards nil
:stobjs (state)))
(if (atom rules)
(equal rules nil)
(and (,fnc-name (car rules) state)
(,fnc-name2 (cdr rules) state))))

         ;(table rp-rw 'meta-valids-fn ',fnc-name2) ;
))))||#

#|(valid-rp-meta-rule-gen 0)||#

#|(table rp-rw 'index 0)||#

(progn
  (defun-sk evals-equal-sk (term1 term2)
    (forall a
            (implies (valid-sc term1 a)
                     (and (valid-sc term2 a)
                          (equal (rp-evlt term1 a)
                                 (rp-evlt term2 a))))))
  #|(defun-sk valid-rp-meta-rulep (rule state-)
  (declare (xargs :guard (weak-rp-meta-rule-rec-p rule)
  :verify-guards nil))
  (forall
  term
  (b* (((mv error res)
  (magic-ev-fncall (rp-meta-fnc rule)
  (list term)
  state- t nil)))
  (implies (and (not error)
  (acl2::logicp (rp-meta-fnc rule)
  (w state-)))
  (and (if (rp-meta-dont-rw rule)
  (and (implies (rp-termp term)
  (evals-equal-sk term (mv-nth 0 res))))
  (and (implies (rp-termp term)
  (evals-equal-sk term res)))))))))

  (defun valid-rp-meta-rule-listp (rules state)
  (declare (xargs :guard (weak-rp-meta-rule-recs-p rules)
  :verify-guards nil
  :stobjs (state)))
  (if (atom rules)
  (equal rules nil)
  (and (valid-rp-meta-rulep (car rules) state)
  (valid-rp-meta-rule-listp (cdr rules) state))))||#)

(defun eval-and-all-nt (lst a)
  (declare (xargs :guard (and (rp-term-listp lst) (alistp a))))
  (if (atom lst)
      t
    (and (rp-evl (car lst) a)
         (eval-and-all-nt (cdr lst) a))))

(mutual-recursion
 (defun valid-sc-nt (term a)
   (declare
    (xargs :measure (acl2::nat-list-measure (list (cons-count term)))
           :hints (("Goal"
                    :in-theory (e/d (measure-lemmas) ())))))
   (cond ((atom term) t)
         ((eq (car term) 'quote) t)
         ((is-if term)
          (and (or (valid-sc-nt (cadr term) a)
                   #|(and (not (rp-evl (caddr term) a))
                   (not (rp-evl (cadddr term) a)))|#)
               (if (rp-evl (cadr term) a)
                   (valid-sc-nt (caddr term) a)
                 (valid-sc-nt (cadddr term) a))))
         ((is-rp term)
          (and (eval-and-all-nt (context-from-rp term nil) a)
               (valid-sc-nt (ex-from-rp term) a)))
         (t
          (and (implies (is-equals term)
                        (equal (rp-evl (cadr term) a)
                               (rp-evl (caddr term) a)))
               (valid-sc-nt-subterms (cdr term) a)))))
 (defun valid-sc-nt-subterms (subterms a)
   (declare
    (xargs :measure (acl2::nat-list-measure (list (cons-count subterms)))))
   (cond ((atom subterms) t)
         (t (and (valid-sc-nt (car subterms) a)
                 (valid-sc-nt-subterms (cdr subterms)
                                       a))))))

(make-flag valid-sc-nt :defthm-macro-name defthm-valid-sc-nt
           :hints (("Goal"
                    :in-theory (e/d (measure-lemmas) ()))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; valid rule functions

(defun valid-rulep-sk-body (rule a)
  (implies (eval-and-all-nt (rp-hyp rule) a)
           (and (if (rp-iff-flag rule)
                    (iff (rp-evl (rp-lhs rule) a)
                         (rp-evl (rp-rhs rule) a))
                  (equal (rp-evl (rp-lhs rule) a)
                         (rp-evl (rp-rhs rule) a)))
                (valid-sc-nt (rp-rhs rule) a))))

(defun-sk valid-rulep-sk (rule)
  (forall a
          (valid-rulep-sk-body rule a)))

(defun valid-rulep (rule)
  (and (rule-syntaxp rule)
       (valid-rulep-sk rule)))

(defun valid-rulesp (rules)
  (if (endp rules)
      (equal rules nil)
    (and (valid-rulep (car rules))
         (valid-rulesp (cdr rules)))))

(defun valid-rules-alistp (rules-alistp)
  (if (endp rules-alistp)
      (equal rules-alistp nil)
    (and (consp (car rules-alistp))
         (symbolp (caar rules-alistp))
         (valid-rulesp (cdar rules-alistp))
         (valid-rules-alistp (cdr rules-alistp)))))

(defun valid-rules-list-listp (rules-list)
  (if (atom rules-list)
      (equal rules-list nil)
    (and (valid-rulesp (car rules-list))
         (valid-rules-list-listp (cdr rules-list)))))

(defun valid-rules-alistp-def2 (rules-alist)
  (and (alistp rules-alist)
       (symbol-listp (strip-cars rules-alist))
       (valid-rules-list-listp (strip-cdrs rules-alist))))


(defun-sk valid-rp-statep (rp-state)
  (declare (xargs :stobjs (rp-state)))
  (forall key
          (or (not (symbolp key))
              (and (valid-rulesp
                    (rules-alist-outside-in-get key rp-state))
                   (valid-rulesp
                    (rules-alist-inside-out-get key rp-state))))))

(defthm valid-rulesp-implies-rule-list-syntaxp
  (implies (valid-rulesp rules)
           (rule-list-syntaxp rules)))

(defthm valid-rp-statep-and-rp-statep-implies-valid-rp-state-syntaxp
  (implies (and (rp-statep rp-state)
                (valid-rp-statep rp-state))
           (valid-rp-state-syntaxp rp-state))
  :hints (("goal"
           :expand ((valid-rp-state-syntaxp rp-state)
                    (valid-rp-state-syntaxp-aux rp-state))
           :use ((:instance valid-rp-statep-necc
                            (key (valid-rp-state-syntaxp-aux-witness rp-state))))
           :in-theory (e/d ()
                           (valid-rp-statep
                            valid-rp-state-syntaxp-aux
                            rp-statep)))))
