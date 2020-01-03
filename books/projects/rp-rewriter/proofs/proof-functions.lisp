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

(include-book "../macros")
(local (include-book "local-lemmas"))
(include-book "../rp-rewriter")
(include-book "../aux-functions")
(local (include-book "aux-function-lemmas"))
(include-book "../eval-functions")

;;;;;;;;;;;;;;;;;;;


(defun eval-sc (lst a)
  ;;!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!OLD FUNCTION
  ;; "and" all the side-conditions;
  ;; side conditions is an assoc list.
  ;; second element in each entry is the side condition that is expected to be
  ;; correct.
  ;; first element in each entry is the condition in which the side condition
  ;; holds.
  ;; i.e, (if first-element side-condition t)
  (declare (xargs :guard (and (alistp lst)
                              (alistp a)
                              (rp-term-list-listp (strip-cars lst))
                              (rp-term-list-listp (strip-cdrs lst)))))
  (if (atom lst)
      t
    (and (implies (eval-and-all (caar lst) a)
                  (eval-and-all (cdar lst) a))
         (eval-sc (cdr lst) a))))

(defun fnc-alist-to-fnc-call (fnc-alist)
  (cons (car fnc-alist)
        (sas 'a 0 (cdr fnc-alist))))

(defun context-fncs-validp (context-fncs)
  ;;; not used anymore.
  (if (atom context-fncs)
      `',(equal context-fncs nil)
    `(if (booleanp ,(fnc-alist-to-fnc-call (car context-fncs)))
         ,(context-fncs-validp (cdr context-fncs))
       'nil)))

;; (create-eval
;;  (append *valid-context-fnc*
;;          *small-evl-fncs*)
;;  big-evl)

;; ;; TEST
;; (defthm valid-context-fnc*-is-valid
;;   (implies
;;    (alistp a)
;;    (big-evl (context-fncs-validp *valid-context-fnc*) a)))


(defun valid-sc-bindings (bindings a)
  (if (atom bindings)
      t
    (and (valid-sc (cdar bindings) a)
         (valid-sc-bindings (cdr bindings) a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  nil

  (local
   (include-book "measure-lemmas"))
  (local
   (in-theory (enable measure-lemmas)))

  (mutual-recursion

   (defun ext-side-conditions (term context)
     ;; extract side conditions
     ;; input context is collected from if statements and it is a list of
     ;; pseudo-termp2's.
     (declare (xargs
               :verify-guards nil
               :measure (cons-count term)
               :guard (and (rp-termp term)
                           (rp-term-listp context))))
     (cond
      ((or (atom term)
           (quotep term))
       nil)
      ((is-if term)
       (b* ((if-context (cadr term));(ex-from-rp (cadr term)))
            (not-if-context (dumb-negate-lit2 if-context)))
         (append
          (ext-side-conditions (cadr term)
                               context)
          (ext-side-conditions (caddr term)
                               (cons if-context context))
          (ext-side-conditions (cadddr term)
                               (cons not-if-context context)))))
      ((is-rp term)
       (b* (((mv rp-context term-without-rp)
             (extract-from-rp-with-context term nil)))
         (cons (cons context rp-context)
               (ext-side-conditions term-without-rp context))))
      (t (ext-side-conditions-subterms (cdr term) context))))

   (defun ext-side-conditions-subterms (subterms context)
     (declare (xargs
               :measure (cons-count subterms)
               :guard (and (rp-term-listp subterms)
                           (rp-term-listp context))))
     (if (atom subterms)
         nil
       (append (ext-side-conditions (car subterms) context)
               (ext-side-conditions-subterms (cdr subterms) context)))))

  (make-flag ext-side-conditions :defthm-macro-name defthm-ext-side-conditions)

  (defun context-free-scp (alst)
    ;; alst is a alist of side conditions.
    ;; if the first element in each entry in the alist is nil, then return nil
    (if (atom alst)
        t;(equal alst nil)
      (and (equal (caar alst) nil)
           (context-free-scp (cdr alst)))))

  (defun ex-and-eval-sc (term context a)
    (eval-sc (ext-side-conditions term context) a))

  (defun ex-and-eval-sc-subterms (subterms context a)
    (eval-sc (ext-side-conditions-subterms subterms context) a)))

(defun-sk valid-sc-any (term)
  (forall a
          (valid-sc term a)))

(defun-sk valid-sc-subterms-any (subterms)
  (forall a
          (valid-sc-subterms subterms a)))

(defun valid-rulep-sk-body (rule a)
  (implies (rp-evl (rp-hyp rule) a)
           (and (if (rp-iff-flag rule)
                    (iff (rp-evl (rp-lhs rule) a)
                         (rp-evl (rp-rhs rule) a))
                  (equal (rp-evl (rp-lhs rule) a)
                         (rp-evl (rp-rhs rule) a)))
                (implies (include-fnc (rp-rhs rule) 'rp)
                         (valid-sc-nt (rp-rhs rule) a)))))

(defun-sk valid-rulep-sk (rule)
  (forall a
          (valid-rulep-sk-body rule a)))

(defun valid-rulep (rule)
  (and (rule-syntaxp rule)
       (valid-rulep-sk rule)))

(defun valid-rulesp (rules)
  (if (endp rules)
      t;(equal rules nil)
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
      t;(equal rules-list nil)
    (and (valid-rulesp (car rules-list))
         (valid-rules-list-listp (cdr rules-list)))))

(defun valid-rules-alistp-def2 (rules-alist)
  (and (alistp rules-alist)
       (symbol-listp (strip-cars rules-alist))
       (valid-rules-list-listp (strip-cdrs rules-alist))))

(defun valid-term-syntaxp1 (term)
  (pseudo-termp term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  nil

  (local
   (include-book "measure-lemmas"))
  (local
   (use-measure-lemmas t))

  (mutual-recursion
   ;; check if two terms are equivalent by discarding rp and synp terms
   ;; used by rp-apply-bindings-lemmas
   (defun rp-equal2 (term1 term2)
     (declare (xargs :mode :logic
                     :measure (cons-count term2)
                     :verify-guards nil
                     :guard (and (rp-termp term1)
                                 (rp-termp term2))))
     ;; term1 should be term, term2 should be rule-lhs
     (let* ((term1 (ex-from-rp term1))
            (term1 (extract-from-synp term1))
            (term2 (ex-from-rp term2))
            (term2 (extract-from-synp term2)))
       (cond
        ((or (atom term1) (atom term2))
         (equal term1 term2))
        ((should-term-be-in-cons term2 term1)
         (let ((nterm (put-term-in-cons term1)))
           (and (rp-equal2 (cadr nterm) (cadr term2))
                (rp-equal2 (caddr nterm) (caddr term2)))))
        ((should-term-be-in-cons term1 term2)
         (let ((nterm (put-term-in-cons term2)))
           (and (rp-equal2 (cadr term1) (cadr nterm))
                (rp-equal2 (caddr term1) (caddr nterm)))))
        ((or (quotep term1) (quotep term2))
         (equal term1 term2))
        (t (and (equal (car term1) (car term2))
                (rp-equal2-subterms (cdr term1) (cdr term2)))))))

   (defun rp-equal2-subterms (subterm1 subterm2)
     (declare (xargs :mode :logic
                     :measure (cons-count subterm2)
                     :verify-guards nil
                     :guard (and (rp-term-listp subterm1)
                                 (rp-term-listp subterm2))))
     (if (or (atom subterm1)
             (atom subterm2))
         (equal subterm1 subterm2)
       (and (rp-equal2 (car subterm1) (car subterm2))
            (rp-equal2-subterms (cdr subterm1) (cdr subterm2))))))

  (make-flag rp-equal2 :defthm-macro-name defthm-rp-equal2))

(defun good-bindingsp (rule term bindings a)
  (declare (ignorable a))
  ;; when var-bindings is applied to the lhs of the rule, it is the same as the term
  (and
   (equal (rp-evlt (rp-apply-bindings (rp-lhs rule) bindings) a)
          (rp-evlt term a))
   ;;(rp-equal2 (rp-apply-bindings (rp-lhs rule) bindings) term)
   ))

(define rp-equal2-bindings (keys bindings1 bindings2)
  :guard (and (bindings-alistp bindings1)
              (bindings-alistp bindings2))
  :verify-guards nil
  (if (atom keys)
      t;(equal bindings1 nil)
    (let ((entry1 (assoc-eq (car keys) bindings1))
          (entry2 (assoc-eq (car keys) bindings2)))
      (and entry1
           entry2
           (rp-equal2 (car entry1) (car entry2))
           (rp-equal2-bindings (cdr keys) bindings1 bindings2)))))

(define rp-equal2-bindings-1to1 (bindings1 bindings2)
  :guard (and (bindings-alistp bindings1)
              (bindings-alistp bindings2))
  :verify-guards nil
  (if (or (atom bindings1)
          (atom bindings2))
      (equal bindings1 bindings2)
    (let ((entry1 (car bindings1))
          (entry2 (car bindings2)))
      (and
       (equal (car entry1) (car entry2))
       (rp-equal2 (cdr entry1) (cdr entry2))
       (rp-equal2-bindings-1to1 (cdr bindings1) (cdr bindings2))))))

#|(define all-vars-bound (vars bindings)
  :enabled t
  :guard (and (symbol-listp vars)
              (bindings-alistp bindings))
  (if (atom vars)
      t;(equal vars nil)
    (and (assoc-eq (car vars) bindings)
         (all-vars-bound (cdr vars) bindings))))||#

(mutual-recursion
 (defun all-vars-bound (term acc-bindings)
   (cond
    ((atom term)
     (consp (assoc-eq term acc-bindings)))
    ((eq (car term) 'quote)
     t)
    (t
     (all-vars-bound-subterms (cdr term)
                              acc-bindings))))
 (defun all-vars-bound-subterms (subterms acc-bindings)
   (if (atom subterms)
       t
     (and (all-vars-bound (car subterms)
                          acc-bindings)
          (all-vars-bound-subterms (cdr subterms)
                                   acc-bindings)))))

(make-flag all-vars-bound :defthm-macro-name defthm-all-vars-bound)

(mutual-recursion
 (defun get-vars2 (term)
   (cond ((atom term)
          (list term))
         ((quotep term)
          nil)
         (t
          (get-vars2-subterms (cdr term)))))
 (defun get-vars2-subterms (subterms)
   (if (atom subterms)
       nil
     (append (get-vars2 (car subterms))
             (get-vars2-subterms (cdr subterms))))))

#|(encapsulate
  nil
  (mutual-recursion
   (defun subtermp (small-term term)
     (if (or (atom term)
             (quotep term))
         (equal small-term term)
       (or (equal small-term term)
           (subtermp-subterms small-term (cdr term)))))
   (defun subtermp-subterms (small-term subterms)
     (if (atom subterms)
         nil
       (or (subtermp small-term (car subterms))
           (subtermp-subterms small-term (cdr subterms))))))

  (defun subtermp-lst (small-subterms subterms)
    (if (atom small-subterms)
        t
      (and (subtermp-subterms (car small-subterms)
                              subterms)
           (subtermp-lst (cdr small-subterms)
                         subterms))))

  (make-flag subtermp :defthm-macro-name defthm-subtermp)

  )||#

(defun merge-lists (lst1 lst2)
  (declare (xargs :mode :program))
  (if (atom lst1)
      lst2
    (merge-lists (cdr lst1)
                 (ADD-TO-SET-EQUAL
                  (car lst1) lst2))))

(defun quotep-sym (x)
  (declare (xargs :guard t))
  (and (consp x)
       (consp (cdr x))
       (eq (car x) 'quote)
       (symbolp (cadr x))
       (cadr x)
       (not (consp (cddr x)))))

(defun valid-termp (term context a)
  (and (rp-termp term)
       (eval-and-all context a)
       (valid-sc term a)))


(defun rp-evl-of-trans-list (lst a)
     (if (atom lst)
         (rp-evl ''nil a)
       (if (atom (cdr lst))
           (rp-evl `(cons ,(car lst) 'nil) a)
         (cons (rp-evl (car lst) a)
               (rp-evl-of-trans-list (cdr lst) a)))))
