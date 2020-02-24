; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

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
(include-book "macros" )
;(include-book "rp-rewriter")
(include-book "aux-functions")
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "proofs/measure-lemmas")
(include-book "std/basic/two-nats-measure" :dir :system)

(defrec rp-evaluators
  (valid-rp-meta-rule-listp
   valid-rp-meta-rulep
   eval-and-all
   valid-sc
   valid-sc-subterms
   rp-evl
   rp-evl-lst
   rp-evl-meta-extract-global-badguy
   rp-evl-meta-extract-contextual-badguy
   rp-evl-falsify
   rp-evl-falsify-sufficient
   rp-evl-constraint-0
   rp-evl-meta-extract-global-badguy-sufficient
   valid-rp-meta-rulep-witness
   valid-rp-meta-rulep-necc
   evals-equal-sk
   evals-equal-sk-necc
   evals-equal-sk-witness
   )
  nil)

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

(defconst *small-evl-fncs*
  '((equal . 2)
    (falist . 2)
    (not . 1)
    (if . 3)
    (hide . 1)
    (implies . 2)
    (cons . 2)
    (synp . 3)
    (return-last . 3)
    (rp . 2)
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
    (SYMBOL-PACKAGE-NAME . 1)
    (INTERN-IN-PACKAGE-OF-SYMBOL . 2)
    (SYMBOL-NAME . 1)
    (acl2::BAD-ATOM<= . 2)
    (binary-+ . 2)
    (binary-* . 2)
    (consp . 1)
    (force . 1)

    ;; Below are temporary, will probably be removed when def-formula-checks
    ;; start supporting mutually recursive funcitons
    (rp-equal . 2)
    (rp-equal-subterms . 2)
    (rp-equal-cnt . 3)
    (rp-equal-cnt-subterms . 3)
    ))

(with-output
  :off :all
  :gag-mode nil
  (create-eval *small-evl-fncs*
               rp-evl
               :namedp t))

(acl2::def-meta-extract rp-evl rp-evl-lst)



(defmacro rp-evlt (term a)
  `(rp-evl (rp-trans ,term) ,a))

(defmacro rp-evlt-lst (lst a)
  `(rp-evl-lst (rp-trans-lst ,lst) ,a))


;; ;; register the rp-evl name because it may change later when a new meta rule is
;; ;; added.
;; (table rp-rw 'evl 'rp-evl)

;; ;; register the rp-evl-lst name
;; (table rp-rw 'evl-lst 'rp-evl-lst)

;; ;register the fuction list that  created the evaluator
;; (table rp-rw 'evl-fncs *small-evl-fncs*)

#|(encapsulate
  nil
  (with-output
    :off :all
    :gag-mode nil
    (defmacro generate-valid-sc (index)
      `(make-event
        (B* ((world (w state))
             (fnc-name (SA "VALID-SC"
                           (if (= ,index 0) nil ,index)))
             (fnc-lst-name (SA "VALID-SC-SUBTERMS"
                               (if (= ,index 0) nil ,index)))
             (eval (cdr
                    (assoc-eq 'evl
                              (table-alist 'rp-rw world))))
             (eval-and-all (SA "EVAL-AND-ALL"
                               (if (= ,index 0) nil ,index)) ))

          `(encapsulate
             nil

             (defun ,eval-and-all (lst a)
               ;; necessary for the context argument.
               ;; Anding all the context should be in the hypothesis of the main theorem.
               (declare (xargs :guard (and (rp-term-listp lst)
                                           (alistp a))))
               (if (atom lst)
                   t
                 (and (,eval (car lst) a)
                      ;;(booleanp (car lst))
                      (,eval-and-all (cdr lst) a))))

             (local
              (in-theory (enable CONS-COUNT-CAR-SUBTERMS
                                 CONS-COUNT-CDR-SUBTERMS
                                 IS-IF-CONS-COUNT
                                 M-MEASURE-LEMMA6
                                 IS-RP-CONS-COUNT
                                 O-P-CONS-COUNT
                                 measure-lemmas)))

             (mutual-recursion
              (defun ,fnc-name (term a)
                (declare (xargs :measure (acl2::nat-list-measure
                                          (list #|(count-lambdas term)||#
                                           (cons-count term)))))
                (cond
                 ((atom term)
                  t)
                 ((eq (car term) 'quote)
                  t)
                 ((is-if term)
                  (and (,fnc-name (cadr term) a)
                       (if (,eval (cadr term) a)
                           (,fnc-name (caddr term) a)
                         (,fnc-name (cadddr term) a))))
                 ((is-rp term)
                  (and
                   (,eval-and-all (context-from-rp term nil) a)
                   (,fnc-name (ex-from-rp term) a)))
                 #|((is-lambda-strict term)
                 (,fnc-name (beta-reduce-lambda-expr term) a))||#
                 (t (,fnc-lst-name (cdr term) a))))

              (defun ,fnc-lst-name (subterms a)
                (declare (xargs :measure (acl2::nat-list-measure
                                          (list #|(count-lambdas-lst subterms)||#
                                           (cons-count subterms)))))
                (cond
                 ((atom subterms) t)
                 (t
                  (and (,fnc-name (car subterms) a)
                       (,fnc-lst-name (cdr subterms) a))))))

             (table rp-rw 'valid-sc-fnc ',fnc-name)
             (table rp-rw 'eval-and-all-fnc ',eval-and-all)
             )))))

  (generate-valid-sc 0))||#


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
   (defun
     valid-sc (term a)
     (declare
      (xargs :measure (acl2::nat-list-measure (list (cons-count term)))))
     (cond ((atom term) t)
           ((eq (car term) 'quote) t)
           ((is-if term)
            (and (valid-sc (cadr term) a)
                 (if (rp-evlt (cadr term) a)
                     (valid-sc (caddr term) a)
                     (valid-sc (cadddr term) a))))
           ((is-rp term)
            (and (eval-and-all (context-from-rp term nil)
                               a)
                 (valid-sc (ex-from-rp term) a)))
           (t (valid-sc-subterms (cdr term) a))))
   (defun
     valid-sc-subterms (subterms a)
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

         ;(table rp-rw 'meta-defunsk ',sk-fnc-name)

         

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

         ;(table rp-rw 'meta-valid-fn ',fnc-name)

         (defun ,fnc-name2 (rules state)
           (declare (xargs :guard (weak-rp-meta-rule-recs-p rules)
                           :verify-guards nil
                           :stobjs (state)))
           (if (atom rules)
               (equal rules nil)
             (and (,fnc-name (car rules) state)
                  (,fnc-name2 (cdr rules) state))))

         ;(table rp-rw 'meta-valids-fn ',fnc-name2)
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
 (defun-sk valid-rp-meta-rulep (rule state-)
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
                 (valid-rp-meta-rule-listp (cdr rules) state)))))



(defun eval-and-all-nt (lst a)
  (declare (xargs :guard (and (rp-term-listp lst) (alistp a))))
  (if (atom lst)
      t
    (and (rp-evl (car lst) a)
         (eval-and-all-nt (cdr lst) a))))

(mutual-recursion
 (defun
     valid-sc-nt (term a)
   (declare
    (xargs :measure (acl2::nat-list-measure (list (cons-count term)))
           :hints (("Goal"
                    :in-theory (e/d (measure-lemmas) ())))))
   (cond ((atom term) t)
         ((eq (car term) 'quote) t)
         ((is-if term)
          (and (valid-sc-nt (cadr term) a)
               (if (rp-evl (cadr term) a)
                   (valid-sc-nt (caddr term) a)
                 (valid-sc-nt (cadddr term) a))))
         ((is-rp term)
          (and (eval-and-all-nt (context-from-rp term nil)
                                a)
               (valid-sc-nt (ex-from-rp term) a)))
         (t (valid-sc-nt-subterms (cdr term) a))))
 (defun
     valid-sc-nt-subterms (subterms a)
   (declare
    (xargs :measure (acl2::nat-list-measure (list (cons-count subterms)))))
   (cond ((atom subterms) t)
         (t (and (valid-sc-nt (car subterms) a)
                 (valid-sc-nt-subterms (cdr subterms)
                                       a))))))

(make-flag valid-sc-nt :defthm-macro-name defthm-valid-sc-nt
           :hints (("Goal"
                    :in-theory (e/d (measure-lemmas) ()))))
