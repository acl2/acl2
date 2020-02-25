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

(include-book "std/lists/remove-duplicates" :dir :system)
(include-book "misc/beta-reduce" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "std/util/defines" :dir :system)
;; Functions and lemmas used by both correctness proofs (rp-correct.lisp) and
;; guards (rp-rewriter.lisp)

(defun rp (prop term)
  (declare (ignorable prop))
  term)

(defun falist (fast-list term)
  (declare (ignorable fast-list))
  term)

(defconst *big-number*
  (1- (expt 2 60)))

(defun is-nonnil-fix (term)
  (declare (xargs :guard t))
  (case-match term (('nonnil-fix &) t) (& nil)))

(defun nonnil-p (term)
  (declare (xargs :guard t))
  (or (and (quotep term)
           (consp (cdr term)) ;; so that it is not (list 'quote)
           (not (equal (cadr term) 'nil)))
      (case-match term
        (('cons & &)
         t)
        (& nil))
;(is-nonnil-fix term)
      ))

(defun nonnil-listp (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      (equal lst nil)
    (and (nonnil-p (car lst))
         (nonnil-listp (cdr lst)))))

(defun nonnil-fix (x)
  (if x x t))

(defthm not-nonnil-fix
  (equal (not (nonnil-fix x))
         nil))

(encapsulate
  nil

  (defun beta-reduce-lamdas (term limit)
    (declare (xargs :measure (acl2-count limit)
                    :guard (and (natp limit))))
    ;; gets a term that could be a cascade of lambda expressions and turns it into
    ;; a regular expression.
    (if (zp limit)
        term
      (if (atom term)
          term
        (if (and (acl2::flambda-applicationp term)
                 (pseudo-termp term))
            (beta-reduce-lamdas (acl2::beta-reduce-lambda-expr term)
                                (1- limit))
          term))))

  (mutual-recursion
   ;; searchs all the lambda terms and performs beta reduction on them.

   (defun beta-search-reduce (term limit)
     (declare (xargs :measure  (nfix limit)
                     :guard (and (natp limit))))
     (if (or (atom term)
             (quotep term)
             (zp limit))
         term
       (if (and (acl2::lambda-expr-p term)
                (pseudo-termp term))
           ;; !!!! PSEUDO-TERMP IS FOR THE GUARD. PROBABLY  BAD FOR RUNTIME!!!
           ;; it is ok for the time being because this function is not intended
           ;; for big terms.
           (beta-search-reduce (acl2::beta-reduce-lambda-expr term)
                               (1- limit))
         (cons (car term)
               (beta-search-reduce-subterms (cdr term) (1- limit))))))

   (defun beta-search-reduce-subterms (subterms limit)
     (declare (xargs :measure  (nfix limit)
                     :guard (and (natp limit))))
     (if (or (zp limit)
             (atom subterms))
         subterms
       (cons (beta-search-reduce (car subterms) (1- limit))
             (beta-search-reduce-subterms (cdr subterms) (1- limit)))))))

(define is-rp (term)
  :inline t
  (case-match term (('rp ('quote type) &)
                    (and (symbolp type)
                         (not (booleanp type))
                         (not (equal type 'quote))
                         (not (equal type 'rp))
                         (not (equal type 'list))
                         (not (equal type 'falist))))
    (& nil))
  ///
  (defthmd is-rp-implies
    (implies (is-rp term)
             (case-match term
               (('rp ('quote type) &)
                (and (symbolp type)
                     (not (equal type 'falist))
                     (not (booleanp type))
                     (not (equal type 'quote))))
               (& nil)))))
(define is-if (term)
  :inline t
  (case-match term (('if & & &) t)
    (& nil)))

(define is-return-last (term)
  :enabled t
  :inline t
  (case-match term (('return-last & & &) t)
    (& nil)))

(define is-rp-soft (term)
  :enabled t
  :inline t
  (case-match term (('rp & &) t)
    (& nil)))

(define is-lambda (term)
  (case-match term
    ((('lambda & &) .  &)
     t)
    (& nil)))

(defun is-member (e lst)
  (declare (xargs :guard t))
  (if (atom lst)
      nil
    (or (equal e (car lst))
        (is-member e (cdr lst)))))

(defun union-equal2 (lst1 lst2)
  (declare (xargs :guard t))
  (cond ((atom lst1)
         lst2)
        ((is-member (car lst1) lst2)
         (union-equal2 (cdr lst1) lst2))
        (t
         (cons (car lst1)
               (union-equal2 (cdr lst1) lst2)))))

(defun remove-vars (big small)
  (declare (xargs :guard t))
  (if (atom big)
      nil
    (if (is-member (car big) small)
        (remove-vars (cdr big) small)
      (cons (car big)
            (remove-vars (cdr big) small)))))

(mutual-recursion
 (defun get-lambda-free-vars (term)
   (declare (xargs :guard t
                   :guard-hints (("Goal"
                                  :in-theory (e/d (is-lambda) ())))))
   (cond
    ((atom term) (mv t (list term)))
    ((quotep term) (mv t nil))
    ((is-lambda term)
     (b* (((mv valid sub-vars) (get-lambda-free-vars (caddr (car term))))
          (lambda-vars (cadr (car term)))
          ((mv valid-2 global-vars) (get-lambda-free-vars-lst (cdr term))))
       (mv (and valid
                valid-2
                (equal (remove-vars sub-vars lambda-vars) nil))
           global-vars)))
    (t (get-lambda-free-vars-lst (cdr term)))))

 (defun get-lambda-free-vars-lst (lst)
   (if (atom lst)
       (mv t nil)
     (b* (((mv valid-1 vars-1)
           (get-lambda-free-vars (car lst)))
          ((mv valid-2 vars-2)
           (get-lambda-free-vars-lst (cdr lst))))
       (mv (and valid-1 valid-2)
           (union-equal2 vars-1 vars-2))))))

#|(encapsulate
  nil
  (local
   (make-flag get-lambda-free-vars :defthm-macro-name
              defthm-get-lambda-free-vars))
  (local
   (defthm-get-lambda-free-vars
     (defthm true-listp-get-lambda-free-vars
       (true-listp (get-lambda-free-vars term))
       :flag get-lambda-free-vars)

     (defthm true-listp-get-lambda-free-vars-lst
       (true-listp (get-lambda-free-vars-lst lst))
       :flag get-lambda-free-vars-lst)))

  (verify-guards get-lambda-free-vars-lst))||#

(mutual-recursion
 (defun lambda-exp-free-p (term)
   (declare (xargs :guard t :mode :logic))
   (cond ((atom term) t)
         ((eq (car term) 'quote)
          t)
         (t (and (atom (car term))
                 (lambda-exp-free-listp (cdr term))))))

 (defun lambda-exp-free-listp (subterms)
   (if (atom subterms)
       (eq subterms nil)
     (and (lambda-exp-free-p (car subterms))
          (lambda-exp-free-listp (cdr subterms))))))

(encapsulate
  nil

  (defun falist-consistent-aux (falist term)
    ;; given an unquoted falist (a fast alist from (falist & &)), compares it
    ;; with the term and makes sure that they're consistent.
    (declare (xargs :guard t))
    (if (atom falist)
        (and (equal falist nil)
             (equal term ''nil))
      (b* ((cf (car falist))
           (cf-key (if (consp cf) (car cf) nil))
           (cf-val (if (consp cf) (cdr cf) nil)))
        (and
         (consp cf)
         (case-match term
           (('cons ('cons ('quote key1) val1) rest1)
            (and (equal cf-key key1)
                 (equal cf-val val1)
                 (falist-consistent-aux (cdr falist)
                                        rest1)))
           (('cons ('quote (key1 . val1)) rest1)
            (and #|(if (equal key1 nil)
             (equal cf-key (list 'quote))
             nil)||#
             (equal cf-key key1)
             (equal cf-val (list 'quote val1))
             (falist-consistent-aux (cdr falist)
                                    rest1)))
           (('quote ((key1 . val1) . rest1))
            (and (equal cf-key key1)
                 (equal cf-val (list 'quote val1))
                 (falist-consistent-aux (cdr falist)
                                        `',rest1)))
           (& nil))))))

  (define falist-consistent (falist-term)
    :parents (rp-utilities)
    :enabled t
    :short "Given a falist term \(falist \* \*\), checks consistence of arguments."
    (case-match falist-term
      (('falist ('quote falist) term)
       (falist-consistent-aux falist term))
      (('falist ''nil ''nil)
       t)
      (& nil)))

  (defun is-falist (term)
    ;; checks if it is a falist statement?
    (declare (xargs :guard t))
    (case-match term (('falist & &) t) (& nil)))

  (defun is-falist-strict (term)
    ;; checks if it is a falist statement?
    (declare (xargs :guard t))
    (case-match term (('falist ('quote &) &) t) (& nil)))

  #|(mutual-recursion
  (defun all-falist-consistent (term)
  ;; searches the term for (falist & &) and if found, checkes whether
  ;; they're consistent.
  (declare (xargs :guard t #|(rp-termp term)||#))
  (cond
  ((or (atom term)
  (quotep term))
  t)
  ((is-falist term)
  (and (falist-consistent term)
  (all-falist-consistent (caddr term))))
  (t (all-falist-consistent-lst (cdr term)))))

  (defun all-falist-consistent-lst (lst)
  (declare (xargs :guard t #|(rp-term-listp lst)||#))
  (if (atom lst)
  t
  (and (all-falist-consistent (car lst))
  (all-falist-consistent-lst (cdr lst))))))||#

  #|(defun all-falist-consistent-bindings (bindings)
  ;; input is var-bindings;
  ;; checks if the values are falist-consistent
  (if (atom bindings)
  t
  (and (consp (car bindings))
  (all-falist-consistent (cdar bindings))
  (all-falist-consistent-bindings (cdr bindings)))))||#)

(encapsulate
  nil

  (define is-lambda-strict (x)
    :prepwork ((local (in-theory (enable is-lambda))))
    (and (is-lambda x)
         (symbol-listp (cadr (car x)))
         (equal (len (cadr (car x)))
                (len (cdr x)))
;(lambda-exp-free-listp (cdr x)) ;; variables should not have lambda expressions
         (b* (((mv valid &)
               (get-lambda-free-vars x)))
           valid)))

  (local
   (in-theory (enable is-rp
                      is-lambda
                      is-lambda-strict
                      is-rp-soft)))

  (acl2::defines
   rp-termp
   (define rp-termp (term)
     ;; same as pseudo-termp but does not allow nil as a symbol
     :enabled t
     :parents (rp-utilities)
     :short "Similarly to pseudo-termp, defines the syntax for terms. "
     (cond ((atom term) (and (symbolp term) term))
           ((eq (car term) 'quote)
            (and (consp (cdr term))
                 (null (cdr (cdr term)))))
           ((eq (car term) 'rp)
            (and (is-rp term)
                 (rp-termp (caddr term))))
           ((eq (car term) 'falist)
            (and (falist-consistent term)
                 (rp-termp (caddr term))))
           (t (and (symbolp (car term))
                   (car term)
                   (rp-term-listp (cdr term))))))

   (define rp-term-listp (lst)
     :enabled t
     (cond ((atom lst) (eq lst nil))
           (t (and (rp-termp (car lst))
                   (rp-term-listp (cdr lst)))))))

  (defun rp-term-list-listp (lst)
    (declare (xargs :guard t))
    (if (atom lst)
        (equal lst nil)
      (and (rp-term-listp (car lst))
           (rp-term-list-listp (cdr lst))))))

(defun falist-syntaxp (unquoted-falist)
  ;; on the unquoted fast-alist (which is the first parameter of (falist & &)
  ;; but unquoted), checks the syntacial correctness
  (declare (xargs :guard t))
  (and (alistp unquoted-falist)
       (rp-term-listp
        (strip-cdrs unquoted-falist))))

;; (encapsulate
;;   nil
;;   (local
;;    (in-theory (enable is-rp)))
;;   (mutual-recursion
;;    ;; checks if all the terms with a function symbol
;;    ;; "rp" satisfies the is-rp condition.
;;    (defun rp-syntaxp (term)
;;      (declare (xargs :guard t))
;;      (cond
;;       ((atom term) t)
;;       ((eq (car term) 'quote) t)
;;       ((eq (car term) 'rp)
;;        (and (is-rp term)
;;             (rp-syntaxp (caddr term))))
;;       (t (rp-syntaxp-lst (cdr term)))))
;;    (defun rp-syntaxp-lst (lst)
;;      (cond
;;       ((atom lst) t)
;;       (t (and (rp-syntaxp (car lst))
;;               (rp-syntaxp-lst (cdr lst))))))))

;; (defun rp-syntaxp-bindings (bindings)
;;   (rp-syntaxp-lst (strip-cdrs bindings)))

(defthm rp-termp-implies-cdr-listp
  (implies (and (consp term)
                (rp-termp term)
                (not (equal (car term) 'quote)))
           (rp-term-listp (cdr term)))
  :hints (("Goal"
           :Expand ((RP-TERMP TERM)
                    (RP-TERM-LISTP (CDR TERM))
                    (RP-TERM-LISTP (CdDR TERM)))
           :in-theory (e/d (is-rp) ()))))

(encapsulate
  nil
  (define fnc-alistp (fnc-alist)
    :enabled t
    (if (atom fnc-alist)
        (equal fnc-alist nil)
      (and (consp (car fnc-alist))
           (symbolp (caar fnc-alist))
           (natp (cdar fnc-alist))
           (fnc-alistp (cdr fnc-alist)))))

  (defmacro bindings-alistp (bindings)
    `(and (alistp ,bindings)
;(symbol-listp (strip-cars ,bindings))
          (rp-term-listp (strip-cdrs ,bindings)))))

(defun cons-count (x)
  (cond ((atom x)
         1)
        (t
         (+ (cons-count (car x))
            (cons-count (cdr x))))))

(mutual-recursion
 (defun count-lambdas (x)
   (declare (xargs :guard t
                   :guard-hints (("Goal"
                                  :in-theory (e/d (is-lambda is-lambda-strict) ())))))
   (cond ((atom x) 0)
         ((eq (car x) 'quote) 0)
         ((is-lambda-strict x)
          (+ 1
             (count-lambdas (caddr (car x)))))
         (t (count-lambdas-lst (cdr x)))))

 (defun count-lambdas-lst (lst)
   (if (atom lst)
       0
     (+ (count-lambdas (car lst))
        (count-lambdas-lst (cdr lst))))))

(defun cons-consp (lst)
  (declare (xargs :guard t))
  ;;  all the elements should be conses and not quoteps
  (if (atom lst)
      (equal lst nil)
    (and (consp (car lst))
         (not (quotep (car lst)))
         (cons-consp (cdr lst)))))

(acl2::defines
 include-fnc
 (define include-fnc (term fnc)
   :enabled t
   :guard (symbolp fnc)
   :parents (rp-utilities)
   :short "Searches a term for an instance of fnc. Returns t or nil."
   (if (or (atom term)
           (quotep term))
       nil
     (if (eq (car term) fnc)
         t
       (include-fnc-subterms (cdr term) fnc))))

 (define include-fnc-subterms (subterms fnc)
   :guard (symbolp fnc)
   :enabled t
   :parents (rp-utilities)
   :short "Searches a list of terms for an instance of fnc. Returns t or nil."
   (if (atom subterms)
       nil
     (or (include-fnc (car subterms) fnc)
         (include-fnc-subterms (cdr subterms) fnc)))))

(defun is-honsed-assoc-eq-values (term)
  (declare (xargs :guard t))
  (case-match term
    (('assoc-eq-vals ('quote &) ('falist ('quote &) &))
     t)
    (& nil)))

(encapsulate
  nil

  (local
   (in-theory (enable is-rp)))

  (defun-inline is-synp (term)
    (declare (xargs :guard t #|(and (rp-termp term))||#))
    (case-match term (('synp & & &) t) (& nil)))

  (defund-inline is-rp-loose (term)
    (declare (xargs :guard t #|(and (rp-termp term))||#))
    (case-match term (('rp & &) t) (& nil)))

  (define ex-from-falist (term)
    (case-match term
      (('falist & x)
       x)
      (& term)))

  (define ex-from-rp (term)
    :enabled t
    :parents (rp-utilities)
    :short "Extracts a term if it is wrapped in an rp instance."
    (if (is-rp term)
        (ex-from-rp (caddr term))
      term))

  (local
   (in-theory (enable IS-RP-LOOSE)))

  (define ex-from-rp-loose (term)
    :parents (rp-utilities)
    :short "Same as @(see rp::ex-from-rp) when term is @(see rp::rp-termp) but
    a little faster."
    (mbe :logic (if (is-rp-loose term)
                    (ex-from-rp-loose (caddr term))
                  term)
         :exec (case-match term (('rp & x)
                                 (ex-from-rp-loose x))
                 (& term))))

  (local
   (in-theory (enable ex-from-rp-loose)))

  (defun extract-from-rp-with-context (term context)
    (declare (xargs :guard t #|(rp-termp term)||#))
    (if (is-rp term)
        (b* ((type (cadr (cadr term)))
             ((mv rcontext rterm)
              (extract-from-rp-with-context (caddr term) context)))
          (mv (cons `(,type ,(ex-from-rp (caddr term))) rcontext) rterm))
      (mv context term)))

  (defun extract-from-synp (term)
    (declare (xargs :guard t #|(rp-termp term)||#))
    (case-match term
      (('synp & & &) ''t)
      (& term)))

  (defun ex-from-synp (term)
    (if (is-synp term)
        ''t
      term))

  (defun-inline is-cons (term)
    (declare (xargs :guard (and t)))
    (case-match term (('cons & &) t) (& nil)))

  (defun-inline is-quoted-pair (term)
    (declare (xargs :guard (and t)))
    (and #|(quotep term)||#
     (consp term)
     (eq (car term) 'quote)
     (consp (cdr term))
     (consp (unquote term))))

  (defun-inline should-term-be-in-cons (rule-lhs term)
    (declare (xargs :guard t #|(and (rp-termp term)
                    (rp-termp rule-lhs))||#))
    (and (is-quoted-pair term) ;(quotep term)
         ;;(consp (unquote term))
         (is-cons rule-lhs);;(case-match rule-lhs (('cons & &) t) (& nil))
         ))

  (defun-inline put-term-in-cons (term)
    (declare (xargs :guard (and #|(rp-termp term)||#
                            (should-term-be-in-cons '(cons x y) term))))
    `(cons ',(car (unquote term))
           ',(cdr (unquote term))))

  (define context-from-rp (term context)
    :short "Expands the context with the side-conditions from the term"
    :parents (rp-utilities)
    (if (is-rp term)
        (let ((type (car (cdr (car (cdr term)))))
              (x (car (cdr (cdr term)))))
          (b* ((rcontext (context-from-rp x context)))
            (cons (cons type (cons (ex-from-rp x) 'nil))
                  rcontext)))
      context)))

(define dumb-negate-lit2 (term)
  :enabled t
  :inline t
  (cond ((atom term)
         (acl2::fcons-term* 'not term))
        ((acl2::fquotep term)
         (cond ((equal term ''nil)
                ''t)
               (t ''nil)))
        ((case-match term (('not &) t) (& nil))
         (acl2::fargn term 1))
        ((and (case-match term (('equal & &) t) (& nil))
              (or (equal (acl2::fargn term 2)
                         ''nil)
                  (equal (acl2::fargn term 1)
                         ''nil)))
         (if (equal (acl2::fargn term 2)
                    ''nil)
             (acl2::fargn term 1)
           (acl2::fargn term 2)))
        (t (acl2::fcons-term* 'not term))))

(encapsulate
  nil

  (mutual-recursion
   (defun get-vars1 (q acc)
     (declare (xargs :guard (and (true-listp acc)
                                 #|(rp-termp q)||#)
                     :verify-guards nil))
     (if (quotep q)
         acc
       (if (atom q)
           (if (member-equal q acc) acc (cons q acc))
         (get-vars-subterms (cdr q) acc))))

   (defun get-vars-subterms (subterms acc)
     (declare (xargs :guard (and (true-listp acc)
                                 #|(rp-term-listp subterms)||#)
                     :verify-guards nil))
     (if (atom subterms)
         acc
       (get-vars-subterms (cdr subterms)
                          (get-vars1 (car subterms) acc)))))

  (make-flag get-vars1 :defthm-macro-name defthm-get-vars1)

  (defthm-get-vars1
    (defthm true-listp-get-vars1
      (implies (true-listp acc)
               (true-listp (get-vars1 q acc)))
      :flag get-vars1)
    (defthm true-listp-get-vars-subterms
      (implies (true-listp acc)
               (true-listp (get-vars-subterms subterms acc)))
      :flag get-vars-subterms))

  (verify-guards get-vars1)

  (defun get-vars (term)
    (declare (xargs :guard t #|(rp-termp term)||#))
    (get-vars1 term nil)))

(encapsulate
  nil
  (defrec custom-rewrite-rule
    (lhs (flg . hyp) rule-fnc . (rhs . rune))
    t) ; t when we are confident that the code is OK

  (defun weak-custom-rewrite-rule-listp (rules)
    (declare (xargs :guard t))
    (if (atom rules)
        (eq rules nil)
      (and (weak-custom-rewrite-rule-p (car rules))
           (weak-custom-rewrite-rule-listp (cdr rules)))))

  (defun-inline rp-hyp (rule)
    ;; return hyps from a given rule
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :hyp))

  (defun-inline rp-lhs (rule)
    ;; return hyps from a given rule
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :lhs))

  (defun-inline rp-rhs (rule)
    ;; return hyps from a given rule
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :rhs))

  (defun-inline rp-rune (rule)
    ;; return hyps from a given rule
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :rune))

  (defun-inline rp-iff-flag (rule)
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :flg))

  (defun-inline rp-rule-fnc (rule)
    (declare (xargs :guard (weak-custom-rewrite-rule-p rule)))
    (access custom-rewrite-rule rule :rule-fnc)))

(encapsulate
  nil

  (defmacro rp-hypm (rule)
    ;; return hyps from a given rule

    `(access custom-rewrite-rule ,rule :hyp))

  (defmacro rp-lhsm (rule)
    ;; return hyps from a given rule
    `(access custom-rewrite-rule ,rule :lhs))

  (defmacro rp-rhsm (rule)
    ;; return hyps from a given rule
    `(access custom-rewrite-rule ,rule :rhs))

  (defmacro rp-runem (rule)
    ;; return hyps from a given rule
    `(access custom-rewrite-rule ,rule :rune))

  (defmacro rp-iff-flagm (rule)
    `(access custom-rewrite-rule ,rule :flg)))

(defun remove-from-alist (alist key)
  (declare (xargs :guard t))
  (if (atom alist)
      alist
    (if (not (consp (car alist)))
        alist
      (if (equal (caar alist) key)
          (remove-from-alist (cdr alist) key)
        (cons-with-hint (car alist)
                        (remove-from-alist (cdr alist) key)
                        alist)))))

(encapsulate
  nil

  (define dont-rw-if-fix (dont-rw)
    (case-match
      dont-rw
      ((& & & &)
       dont-rw)
      (& '(nil nil nil nil)))
    ///
    (local
     (defthmd dont-rw-if-fix-type
       (let ((res (dont-rw-if-fix dont-rw)))
         (and (consp res)
              (consp (cdr res))
              (consp (cddr res))
              (consp (cdddr res))
              (equal (cddddr res) nil))))))

  (define strict-quotep (term)
    :enabled t
    (and (consp term)
         (eq (car term) 'quote)
         (consp (cdr term))
         (not (cddr term))))

  (defun dont-rw-syntaxp-aux (dont-rw)
    (declare (xargs :guard t))
    (if (atom dont-rw)
        t
      (and (or (atom (car dont-rw))
               (dont-rw-syntaxp-aux (car dont-rw)))
           (dont-rw-syntaxp-aux (cdr dont-rw)))))

  (defund dont-rw-syntaxp (dont-rw)
    (declare (xargs :guard t))
    (or (atom dont-rw)
        (dont-rw-syntaxp-aux dont-rw)))

  (define should-not-rw (dont-rw)
    :inline t
    (and (atom dont-rw)
         dont-rw))

  (defund dont-rw-syntax-fix (dont-rw)
    (declare (xargs :guard t))
    (if (dont-rw-syntaxp dont-rw)
        dont-rw
      (progn$ (hard-error 'dont-rw-syntax-fix
                          "this dont'rw is being fixed. This should have
    not happened... ~p0 ~%"
                          (list (cons #\0 dont-rw)))
              t))))

(defun context-syntaxp (context)
  (declare (xargs :guard t))
  (rp-term-listp context))

(mutual-recursion

 (defun remove-return-last (term)
   (declare (xargs :guard t))
   (cond
    ((or (atom term)
         (quotep term)
         (is-falist term))
     term)
    ((is-return-last term)
     (remove-return-last (cadddr term)))
    (t (cons (car term)
             (remove-return-last-subterms (cdr term))))))

 (defun remove-return-last-subterms (subterms)
   (declare (xargs :guard t #|(rp-term-listp subterms)||#))
   (if (atom subterms)
       subterms
     (cons (remove-return-last (car subterms))
           (remove-return-last-subterms (cdr subterms))))))

(defund is-hide (term)
  (declare (xargs :guard t))
  (case-match term
    (('hide &) t)
    (& nil)))

(in-theory (disable extract-from-rp-with-context))

(mutual-recursion
 (defun search-term (term seq)
   ;; case insensitive search on the term
   (cond ((atom term)
          (search seq (symbol-name term)  :test 'char-equal))
         ((quotep term)
          nil)
         ((consp (car term))
          (or (search-subterms (car term) seq)
              (search-subterms (cdr term) seq)))
         (t
          (or (search seq (symbol-name (car term)) :test 'char-equal)
              (search-subterms (cdr term) seq)))))
 (defun search-subterms (subterms seq)
   (if (atom subterms)
       nil
     (or (search-term (car subterms) seq)
         (search-subterms (cdr subterms) seq)))))

(encapsulate
  nil

  (local
   (defthm consp-extract-from-rp
     (implies (consp (ex-from-rp term))
              (consp term))))

  (local
   (defthm consp-ex-from-rp-loose
     (implies (consp (ex-from-rp-loose term))
              (consp term))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp-loose
                               is-rp-loose)
                              ())))))

  (local
   (defthm extract-from-rp-acl2-count
     (implies (consp term)
              (< (acl2-count (cdr (ex-from-rp term)))
                 (acl2-count term)))))

  (local
   (defthm ex-from-rp-loose-acl2-count
     (implies (consp term)
              (< (acl2-count (cdr (ex-from-rp-loose term)))
                 (acl2-count term)))
     :hints (("Goal"
              :in-theory (e/d (ex-from-rp-loose
                               is-rp-loose) ())))))

  (acl2::defines
   rp-equal
   :parents (rp-utilities)
   :short "Check if two terms are equivalent by discarding rp terms"
   (define rp-equal (term1 term2)
     :enabled t
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard t))
     "Check syntactic equivalance of two terms by ignoring all the rp terms"
     (let* ((term1 (ex-from-rp term1))
            (term2 (ex-from-rp term2)))
       (cond
        ((or (atom term1)
             (atom term2)
             (acl2::fquotep term1)
             (acl2::fquotep term2))
         (equal term1 term2))
        (t (and (equal (car term1) (car term2))
                (rp-equal-subterms (cdr term1) (cdr term2)))))))

   (define rp-equal-subterms (subterm1 subterm2)
     :enabled t
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard t #|(and (rp-term-listp subterm1)
                     (rp-term-listp subterm2))||#))
     (if (or (atom subterm1)
             (atom subterm2))
         (equal subterm1 subterm2)
       (and (rp-equal (car subterm1) (car subterm2))
            (rp-equal-subterms (cdr subterm1) (cdr subterm2))))))

  (acl2::defines
   rp-equal-cw
   :parents (rp-utilities)
   :short "Same as @(see rp::rp-equal) but prints a mismatch."
   (define rp-equal-cw (term1 term2)
     :enabled t
     (declare (xargs :mode :logic
                     :guard t #|(and (rp-termp term1)
                     (rp-termp term2))||#))
     "Check syntactic equivalance of two terms by ignoring all the rp terms"
     (let* ((term1 (ex-from-rp term1))
            (term2 (ex-from-rp term2)))
       (cond
        ((or (atom term1)
             (atom term2)
             (acl2::fquotep term1)
             (acl2::fquotep term2))
         (or (equal term1 term2)
             (cw "Mismatch: term1=~p0, term2=~p1 ~%" term1 term2)))
        (t (and (or (equal (car term1) (car term2))
                    (cw "Mismatch: term1=~p0, term2=~p1 ~%" term1 term2))
                (rp-equal-cw-subterms (cdr term1) (cdr term2)))))))

   (define rp-equal-cw-subterms (subterm1 subterm2)
     :enabled t
     (declare (xargs :mode :logic
                     :guard t #|(and (rp-term-listp subterm1)
                     (rp-term-listp subterm2))||#))
     (if (or (atom subterm1)
             (atom subterm2))
         (or (equal subterm1 subterm2)
             (cw "Mismatch: subterm1=~p0, sunterm2=~p1 ~%" subterm1 subterm2))
       (and (rp-equal-cw (car subterm1) (car subterm2))
            (rp-equal-cw-subterms (cdr subterm1) (cdr subterm2))))))

  (mutual-recursion
   ;; check if two terms are equivalent by discarding rp terms
   (defun rp-equal-loose (term1 term2)
     (declare (xargs :mode :logic
                     :verify-guards nil
;           :measure (+ (cons-count term1)
;                      (cons-count term2))
                     :guard t #|(and (rp-termp term1)
                     (rp-termp term2))||#))
     "Check syntactic equivalance of two terms by ignoring all the rp terms"
     (let* ((term1 (ex-from-rp-loose term1))
            (term2 (ex-from-rp-loose term2)))
       (cond
        ((or (atom term1) (atom term2)
             (acl2::fquotep term1) (acl2::fquotep term2))
         (equal term1 term2))
        (t (and (equal (car term1) (car term2))
                (rp-equal-loose-subterms (cdr term1) (cdr term2)))))))

   (defun rp-equal-loose-subterms (subterm1 subterm2)
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard t #|(and (rp-term-listp subterm1)
                     (rp-term-listp subterm2))||#))
     (if (or (atom subterm1)
             (atom subterm2))
         (equal subterm1 subterm2)
       (and (rp-equal-loose (car subterm1) (car subterm2))
            (rp-equal-loose-subterms (cdr subterm1) (cdr subterm2))))))

  (acl2::defines
   rp-equal-cnt
   :parents (rp-utilities)
   :short "Same as @(see rp::rp-equal) but when counts down from cnt and starts ~
   using 'equal' when it hits 0."
   ;; check if two terms are equivalent by discarding rp terms
   (define rp-equal-cnt (term1 term2 cnt)
     :enabled t
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard (and (integerp cnt)
                                 #|(rp-termp term1)||#
                                 #|(rp-termp term2)||#)))
     "Same as rp-equal but also runs equal after counter goes below 0."
     (or (if (and (< cnt 0))
             (equal term1 term2)
           nil)
         (let* ((term1 (ex-from-rp term1))
                (term2 (ex-from-rp term2)))
           (cond
            ((or (atom term1) (atom term2)
                 (acl2::fquotep term1)
                 (acl2::fquotep term2))
             (equal term1 term2))
            (t ;(or (if (< cnt 0) (equal term1 term2) nil)
             (and (equal (car term1) (car term2))
                  (rp-equal-cnt-subterms (cdr term1) (cdr term2) (1- cnt))))))))

   (define rp-equal-cnt-subterms (subterm1 subterm2 cnt)
     :enabled t
     (declare (xargs :mode :logic
                     :verify-guards nil
                     :guard (and (integerp cnt)
                                 #|(rp-term-listp subterm1)||#
                                 #|(rp-term-listp subterm2)||#)))
     (if (or (atom subterm1)
             (atom subterm2))
         (equal subterm1 subterm2)
       (and (rp-equal-cnt (car subterm1) (car subterm2) cnt)
            (rp-equal-cnt-subterms (cdr subterm1) (cdr subterm2) cnt)))))

  (mutual-recursion
   ;; check if two terms are equivalent by discarding rp terms
   (defun p-rp-equal-cnt (term1 term2 cnt)
     (declare (xargs :mode :program))
     "Same as rp-equal but also runs equal after counter goes below 0."
     (or (if (and (< cnt 0))
             (equal term1 term2)
           nil)
         (let* ((term1 (ex-from-rp-loose term1))
                (term2 (ex-from-rp-loose term2)))
           (cond
            ((or (atom term1) (atom term2)
                 (acl2::fquotep term1)
                 (acl2::fquotep term2))
             (equal term1 term2))
            (t ;(or (if (< cnt 0) (equal term1 term2) nil)
             (and (equal (car term1) (car term2))
                  (p-rp-equal-cnt-subterms (cdr term1) (cdr term2) (1- cnt))))))))

   (defun p-rp-equal-cnt-subterms (subterm1 subterm2 cnt)
     (if (or (atom subterm1)
             (atom subterm2))
         (equal subterm1 subterm2)
       (and (p-rp-equal-cnt (car subterm1) (car subterm2) cnt)
            (p-rp-equal-cnt-subterms (cdr subterm1) (cdr subterm2) cnt))))))

(encapsulate
  nil

  (local
   (in-theory (disable rp-hyp rp-lhs rp-rhs)))

  (define no-free-variablep (rule)
    (declare (xargs :guard (and (weak-custom-rewrite-rule-p rule)
                                #|(rp-termp (rp-hyp rule))||#
                                #|(rp-termp (rp-lhs rule))||#
                                #|(rp-termp (rp-rhs rule))||#)))
    (let ((vars (get-vars (rp-lhs rule))))
      (and (subsetp (get-vars (rp-hyp rule))
                    vars
                    :test 'equal)
           (subsetp (get-vars (rp-rhs rule))
                    vars
                    :test 'equal)))
    ///
    (in-theory (disable (:type-prescription no-free-variablep))))

  (define rule-syntaxp (rule &key warning)
    :parents (rp-utilities)
    :short "Syntax check for a 'rule' defined with rp::custom-rewrite-rule. If
    warning key is set to non-nil, a warning is issued for failures. "
    (and
     (or (weak-custom-rewrite-rule-p rule)
         (and warning
              (hard-error
               'rule-syntaxp
               "ATTENTION! weak-custom-rewrite-rule-p failed! ~p0 ~%"
               (list (cons #\0 rule)))))
     (or (not (include-fnc (rp-lhs rule) 'rp))
         (and warning
              (cw "ATTENTION! (not (include-fnc (rp-lhs rule) 'rp))
    failed! LHS cannot contain an instance of rp. ~%")))
     (or (not (include-fnc (rp-hyp rule) 'rp))
         (and warning
              (cw "ATTENTION! (not (include-fnc (rp-hyp rule) 'rp))
    failed! HYP cannot contain an instance of rp. ~%")))
     (or (not (include-fnc (rp-rhs rule) 'falist))
         (and warning
              (cw "ATTENTION! (not (include-fnc (rp-rhs rule) 'falist))
    failed! RHS cannot contain an instance of falist ~%")))
     (or (not (include-fnc (rp-hyp rule) 'falist))
         (and warning
              (cw "ATTENTION! (not (include-fnc (rp-hyp rule) 'falist))
    failed! HYP cannot contain an instance of falist ~%")))
     (or (and
          (or (rp-termp (rp-hyp rule))
              (and warning
                   (cw "ATTENTION! (rp-termp (rp-hyp rule)) failed! Hyp of the ~
    rule does not satisfy rp::rp-termp. ~%")))
          (or (rp-termp (rp-lhs rule))
              (and warning
                   (cw "ATTENTION! (rp-termp (rp-lhs rule)) failed! LSH of the ~
    rule does not satisfy rp::rp-termp. ~%")))
          (or (rp-termp (rp-rhs rule))
              (and warning
                   (cw "ATTENTION! (rp-termp (rp-rhs rule)) failed! RHS of the ~
    rule does not satisfy rp::rp-termp. ~%")))

          (or (not (include-fnc (rp-lhs rule) 'if))
              (and warning
                   (cw "ATTENTION! (not (include-fnc (rp-lhs rule) 'if))
    failed! LHS cannot contain an instance of 'if'. ~%")))
          (or (consp (rp-lhs rule))
              (and warning
                   (cw "ATTENTION! (consp (rp-lhs rule)) failed! LHS cannot
    be a variable. ~%")))
          (or (not (acl2::fquotep (rp-lhs rule)))
              (and warning
                   (cw "ATTENTION! (not (acl2::fquotep (rp-lhs rule))) failed!
    LHS cannot be a quoted value ~%")))
          (or (not (include-fnc (rp-lhs rule) 'synp))
              (and warning
                   (cw "ATTENTION! (not (include-fnc (rp-lhs rule) 'synp))
    failed! LHS cannot contain an instance of synp ~%")))
          (or (no-free-variablep rule)
              (and warning
                   (cw "ATTENTION! (no-free-variablep rule) failed! We do not
    support rules with free variables ~%")))
          (not (include-fnc (rp-lhs rule) 'list))
          (not (include-fnc (rp-hyp rule) 'list))
          (not (include-fnc (rp-rhs rule) 'list)))
         (and (equal warning ':err)
              (hard-error
               'rule-syntaxp
               "Error  is issued for: ~%
 rp-rune: ~p0 ~% rp-hyp: ~p1 ~% rp-lhs: ~p2 ~% rp-rhs ~p3 ~%"
               (list (cons #\0 (rp-rune rule))
                     (cons #\1 (rp-hyp rule))
                     (cons #\2 (rp-lhs rule))
                     (cons #\3 (rp-rhs rule)))))
         (and warning
              (cw "Warning in rp::rule-syntaxp is issued for: ~%
 rp-rune: ~p0 ~% rp-hyp: ~p1 ~% rp-lhs: ~p2 ~% rp-rhs ~p3 ~%"
                  (rp-rune rule)
                  (rp-hyp rule)
                  (rp-lhs rule)
                  (rp-rhs rule))))))

  (defun rule-list-syntaxp (rules)
    (declare (xargs :guard t))
    (if (atom rules)
        t;(equal rules nil)
      (and (rule-syntaxp (car rules))
           (rule-list-syntaxp (cdr rules)))))

  (defun rule-list-list-syntaxp (rules)
    (declare (xargs :guard t))
    (if (atom rules)
        t;(equal rules nil)
      (and (rule-list-syntaxp (car rules))
           (rule-list-list-syntaxp (cdr rules)))))

  (defun rules-alistp (rules)
    (declare (xargs :guard t))
    (and (alistp rules)
         (symbol-listp (strip-cars rules))
         (rule-list-list-syntaxp (strip-cdrs rules)))))

(defun conjecture-syntaxp (term)
  (declare (xargs :guard t))
  (and (not (include-fnc term 'rp))
       (not (include-fnc term 'falist))
       (rp-termp term)))

(acl2::defines
 ex-from-rp-all
 :parents (rp-utilities)
 :short "Removes all instances of 'rp' from a term"
 (define ex-from-rp-all (term)
   (b* ((term (ex-from-rp term)))
     (cond ((atom term)
            term)
           ((quotep term)
            term)
           (t
            (cons (car term)
                  (ex-from-rp-all-lst (cdr term)))))))

 (define ex-from-rp-all-lst (lst)
   (if (atom lst)
       lst
     (cons (ex-from-rp-all (car lst))
           (ex-from-rp-all-lst (cdr lst))))))

(encapsulate
  nil

  (defrec rp-meta-rule-rec
    (trig-fnc ;; trigger function name
     fnc ;; function name that meta rule executes
     dont-rw ;; if meta rule also returns a structure for dont-rw
     . valid-syntax ;; if meta rule returns valid-syntax (rp-valid-termp)
     )
    t)

  (defun rp-meta-fnc (rule)
    (declare (xargs :guard (weak-rp-meta-rule-rec-p rule)))
    (access rp-meta-rule-rec rule :fnc))

  (defun rp-meta-trig-fnc (rule)
    (declare (xargs :guard (weak-rp-meta-rule-rec-p rule)))
    (access rp-meta-rule-rec rule :trig-fnc))

  (defun rp-meta-dont-rw (rule)
    (declare (xargs :guard (weak-rp-meta-rule-rec-p rule)))
    (access rp-meta-rule-rec rule :dont-rw))

  (defun rp-meta-syntax-verified (rule)
    (declare (xargs :guard (weak-rp-meta-rule-rec-p rule)))
    (access rp-meta-rule-rec rule :valid-syntax))

  #|(defun rp-meta-rule-syntaxp (term)
  "Returned term from meta rule functin should meet this syntax."
  (rp-valid-termp term))||#

  (defun rp-meta-rule-rec-p (rule state)
    (declare (xargs :guard t
                    :stobjs (state)))
    (and (weak-rp-meta-rule-rec-p rule)
         (symbolp (rp-meta-fnc rule))
         (acl2::logicp (rp-meta-fnc rule) (w state))
         (symbolp (rp-meta-trig-fnc rule))
         (booleanp (rp-meta-dont-rw rule))
         (booleanp (rp-meta-syntax-verified rule))))

  (defun weak-rp-meta-rule-recs-p (xs)
    (declare (xargs :guard t))
    (if (atom xs)
        (eq xs nil)
      (and (weak-rp-meta-rule-rec-p (car xs))
           (weak-rp-meta-rule-recs-p (cdr xs)))))

  (defun rp-meta-rule-recs-p (rules state)
    (declare (xargs :guard t
                    :stobjs (state)))
    (if (atom rules)
        (eq rules nil)
      (and (rp-meta-rule-rec-p (car rules) state)
           (rp-meta-rule-recs-p (cdr rules) state))))

  (in-theory (disable weak-rp-meta-rule-rec-p
                      rp-meta-syntax-verified
                      rp-meta-dont-rw
                      rp-meta-trig-fnc
                      rp-meta-fnc))

  (defund rp-meta-valid-syntaxp (meta-rule term state)
    (declare (xargs :guard (rp-meta-rule-rec-p meta-rule state)
                    :stobjs (state)))
    (b* (((mv error res)
          (magic-ev-fncall (rp-meta-fnc meta-rule)
                           (list term)
                           state
                           t nil)))
      (implies
       (and (not error)
            (acl2::logicp (rp-meta-fnc meta-rule) (w state)))
       (and (if (rp-meta-dont-rw meta-rule)
                (and
                 (dont-rw-syntaxp (mv-nth 1 res))
                 (if (rp-meta-syntax-verified meta-rule)
                     (implies (rp-termp term)
                              (rp-termp (mv-nth 0 res)))
                   t))
              (and (if (rp-meta-syntax-verified meta-rule)
                       (implies (rp-termp term)
                                (rp-termp res))
                     t)))))))

  (defun-sk rp-meta-valid-syntaxp-sk (meta-rule state-)
    (declare (xargs :guard (and (STATE-P1 STATE-))
                    :verify-guards nil))
    (forall term
            (rp-meta-valid-syntaxp meta-rule term state-)))

  (defund rp-meta-valid-syntax-listp (meta-rules state)
    (declare (xargs :guard (rp-meta-rule-recs-p meta-rules state)
                    :verify-guards nil
                    :stobjs (state)))
    (if (atom meta-rules)
        (eq meta-rules nil)
      (and (rp-meta-valid-syntaxp-sk (car meta-rules) state)
           (rp-meta-valid-syntax-listp (cdr meta-rules) state))))

  #|(defmacro rp-meta-rulesp (meta-rules &optional (state 'state))
  (declare (xargs :guard t)
  (ignorable state))
  `(and (weak-rp-meta-rule-recs-p ,meta-rules)
  ;;(rp-meta-valid-syntax-listp ,meta-rules ,state)
  ))||#)

(mutual-recursion
 (defun subtermp (term subterm)
   (declare (xargs :guard t))
   (cond ((atom term)
          (equal term subterm))
         ((quotep term)
          (equal term subterm))
         (t
          (or (equal term subterm)
              (equal (car term) subterm)
              (subtermp-lst (cdr term) subterm)))))
 (defun subtermp-lst (lst subterm)
   (if (atom lst)
       nil
     (or (subtermp (car lst) subterm)
         (subtermp-lst (cdr lst) subterm)))))

(encapsulate
  nil

  (defun rp-beta-reduce-get-val (key keys vals)
    (declare (xargs :guard t))
    (cond ((atom keys)
           (progn$ (cw "warning binding problem! ~p0 ~%" key)
                   key))
          ((equal key (car keys))
           (if (consp vals) (car vals) key))
          (t (rp-beta-reduce-get-val key (cdr keys)
                                     (if (consp vals) (cdr vals) nil)))))

  (mutual-recursion
   (defun rp-beta-reduce (term keys vals)
     (declare (xargs :guard t))
     (cond ((atom term)
            (rp-beta-reduce-get-val term keys vals))
           ((acl2::fquotep term) term)
           (t (cons-with-hint (car term)
                              (rp-beta-reduce-subterms (cdr term) keys vals)
                              term))))

   (defun rp-beta-reduce-subterms (subterms keys vals)
     (cond ((atom subterms) subterms)
           (t (cons-with-hint (rp-beta-reduce (car subterms) keys vals)
                              (rp-beta-reduce-subterms (cdr subterms) keys vals)
                              subterms)))))

  (defund rp-beta-reduce-main (term)
    (declare (xargs :guard t
                    :guard-hints (("Goal"
                                   :in-theory (e/d (is-lambda) ())))))
    (if (is-lambda term)
        (rp-beta-reduce (caddr (car term)) (cadar term) (cdr term))
      term)))

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies (and (consp x)
                   (consp (cdr x)))
              (< (len (evens x))
                 (len x)))))

  (local
   (defthm lemma2
     (implies (and (consp x)
                   )
              (< (len (evens x))
                 (1+ (len x))))))

  (local
   (defthm lemma3
     (IMPLIES (AND (CONSP (CDR L)) (CONSP L))
              (< (LEN (EVENS L)) (+ 1 (LEN (CDR L)))))))

  (defun merge-comperator (l1 l2 acc comperator)
    (declare (xargs :guard (and (true-listp l1)
                                (true-listp l2)
                                (true-listp acc)
                                (symbolp comperator ))
                    :measure (+ (len l1) (len l2))))
    (cond
     ((endp l1)
      (revappend acc l2))
     ((endp l2)
      (revappend acc l1))
     ((apply$ comperator (list (car l1) (car l2)))
      (merge-comperator  (cdr l1)
                         l2
                         (cons (car l1) acc)
                         comperator))
     (t (merge-comperator  l1 (cdr l2)
                           (cons (car l2) acc) comperator))))

  (defun merge-comperator-sort (l comperator)
    (declare (xargs :guard (and (true-listp l)
                                (symbolp comperator))
                    :measure (len l)
                    :verify-guards nil))
    (cond ((endp (cdr l)) l)
          (t (merge-comperator
              (merge-comperator-sort (evens l) comperator)
              (merge-comperator-sort (odds l) comperator)
              nil
              comperator))))

  (local
   (defthm true-listp-of-merge-comprerator
     (implies (and (true-listp l1)
                   (true-listp l2)
                   (true-listp acc))
              (true-listp (merge-comperator l1 l2 acc comperator)))))

  (local
   (defthm true-listp-of-merge-sort
     (implies (true-listp l)
              (true-listp (merge-comperator-sort l comperator)))))

  (verify-guards merge-comperator-sort))

(define remove-disabled-meta-rules ((meta-rules weak-rp-meta-rule-recs-p)
                                    (disabled-meta-rules ))
  :guard-hints (("Goal"
                 :in-theory (e/d (weak-rp-meta-rule-rec-p) ())))
  (cond ((atom disabled-meta-rules)
         meta-rules)
        ((atom meta-rules)
         meta-rules)
        (t (b* ((entry (hons-assoc-equal (rp-meta-fnc (car meta-rules))
                                         disabled-meta-rules)))
             (if (and (consp entry)
                      (cdr entry))
                 (remove-disabled-meta-rules (cdr meta-rules)
                                             disabled-meta-rules)
               (cons (car meta-rules)
                     (remove-disabled-meta-rules (cdr meta-rules)
                                                 disabled-meta-rules)))))))


(progn

  (defund get-rune-name (fn state)
    (declare (xargs :guard (and (symbolp fn))
                    :stobjs (state)
                    :verify-guards t))
    (b* ((mappings
          (getpropc fn 'acl2::runic-mapping-pairs
                    nil (w state)))
         ((when (atom mappings))
          (progn$ (hard-error 'get-rune-name
                              " ~p0 does not seem to exist. ~%"
                              (list (cons #\0 fn)))
                  fn))
         (mapping (car mappings)))
      (if (consp mapping)
          (cdr mapping)
        fn)))

  (defmacro add-rp-rule (rule-name &optional (disabled 'nil))
    `(make-event
      (b* ((rune (get-rune-name ',rule-name state))
           (- (get-rules `(,rune) state :warning :err)))
        `(progn
           (table rp-rules-inorder ',rune nil)
           (table rp-rules ',rune ,,(not disabled))))))

  (defmacro def-rp-rule (rule-name rule &rest hints)
    `(progn
       (defthm
         ,rule-name ,rule ,@hints)
       (add-rp-rule ,rule-name)))

  (defmacro def-rp-rule$ (defthmd disabled rule-name rule  &rest hints)
    `(progn
       (,(if defthmd 'defthmd 'defthm)
        ,rule-name ,rule ,@hints)
       (add-rp-rule ,rule-name ,disabled))))



 


(defun trans-list (lst)
  (declare (xargs :guard t))
  (if (atom lst)
      ''nil
    (if (atom (cdr lst))
        `(cons ,(car lst) 'nil)
      `(cons ,(car lst) ,(trans-list (cdr lst))))))

(progn
  (mutual-recursion
   (defun rp-trans (term)
     (cond ((atom term)
            term)
           ((quotep term)
            term)
           ((and (equal (car term) 'list))
            (trans-list (rp-trans-lst (cdr term))))
           ((and (is-falist term))
            (rp-trans (caddr term)))
           (t (cons-with-hint (car term)
                              (rp-trans-lst (cdr term))
                              term))))
   (defun rp-trans-lst (lst)
     (if (atom lst)
         nil
       (cons-with-hint (rp-trans (car lst))
                       (rp-trans-lst (cdr lst))
                       lst))))

  (make-flag rp-trans :defthm-macro-name defthm-rp-trans)

  (local
   (defthm rp-trans-lst-consp
     (equal (consp (rp-trans-lst lst))
            (consp lst))
     :hints (("Goal"
              :induct (len lst)
              :in-theory (e/d () ())))))

  (verify-guards rp-trans)

  (memoize 'rp-trans))

(mutual-recursion
 (defun rp-untrans (term)
   (declare (xargs :guard t))
   (cond ((atom term)
          term)
         ((quotep term)
          term)
         ((is-cons term)
          (b* ((a (rp-untrans (cadr term)))
               (b (rp-untrans (caddr term))))
            (case-match b
              (('list . rest)
               `(list ,a . ,rest))
              (&
               `(list ,a ,b)))))
         (t (cons (car term)
                  (rp-untrans-lst (cdr term))))))
 (defun rp-untrans-lst (lst)
   (if (atom lst)
       nil
     (cons (rp-untrans (car lst))
           (rp-untrans-lst (cdr lst))))))
