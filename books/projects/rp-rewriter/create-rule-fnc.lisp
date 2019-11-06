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

(include-book "aux-functions")

(include-book "rp-rewriter")

(include-book "macros")



(defund get-rune-name (fn  state)
  (declare (xargs :guard (and (symbolp fn))
                  :stobjs (state)
                  :verify-guards t))
  (b* ((mappings
        (getpropc fn 'acl2::runic-mapping-pairs
                  nil (w state)))
       ((when (atom mappings))
        fn)
       (mapping (car mappings)))
    (if (consp mapping)
        (cdr mapping)
      fn)))

(mutual-recursion
 (defun get-synp-call (term)
   (cond
    ((atom term) nil)
    ((acl2::fquotep term) nil)
    ((and (case-match term (('synp & & ('quote &)) t) (& nil)))
     (b* ((hyp (unquote (cadddr term))))
       hyp))
    (t (get-synp-call-lst (cdr term)))))
 (defun get-synp-call-lst (lst)
   (if (atom lst)
       nil
     (or (get-synp-call (car lst))
         (get-synp-call-lst (cdr lst))))))

(defun rule->lhs-and-syntaxp (term)
  (case-match term
    (('implies p ('equal a &))
     (mv a (get-synp-call p)))
    (('implies p ('iff a &))
     (mv a (get-synp-call p)))
    (('implies p ('not a))
     (mv a (get-synp-call p)))
    (('implies p a)
     (mv a (get-synp-call p)))
    (('equal a &)
     (mv a nil))
    (('iff a &)
     (mv a nil))
    (('not a)
     (mv a nil))
    (&
     (mv nil nil))))

(progn
  (mutual-recursion
   (defun create-bindings-for-lhs (lhs cnt bindings)
     (cond
      ((atom lhs)
       (b* ((entry (assoc-equal lhs bindings)))
         (if entry
             (mv (acons lhs (cons cnt (cdr entry)) bindings) (1+ cnt))
           (mv (acons lhs (list cnt) bindings) (1+ cnt)))))
      ((acl2::fquotep lhs)
       (mv bindings cnt))
      (t
       (create-bindings-for-lhs-lst (cdr lhs) cnt bindings))))

   (defun create-bindings-for-lhs-lst (lst cnt bindings)
     (if (atom lst)
         (mv bindings cnt)
       (b* (((mv bindings cnt) (create-bindings-for-lhs (car lst)
                                                        cnt
                                                        bindings)))
         (create-bindings-for-lhs-lst (cdr lst) cnt bindings)))))

  (defun clear-lhs-bindings (synp-vars bindings)
    (if (atom bindings)
        nil
      (b* ((key (caar bindings))
           (val (cdar bindings)))
        (if (or (> (len val) 1)
                (member-equal key synp-vars))
            (acons key val (clear-lhs-bindings synp-vars (cdr bindings)))
          (clear-lhs-bindings synp-vars (cdr bindings))))))

  (defun get-lhs-bindings (lhs synp)
    (b* (((mv bindings &)
          (create-bindings-for-lhs lhs 0 nil))
         (bindings (fast-alist-free bindings))
         (synp-vars (get-vars synp)))
      (clear-lhs-bindings synp-vars bindings))))

(mutual-recursion
 (defun create-case-from-lhs (lhs bindings)
   (cond
    ((atom lhs)
     (b* ((entry (assoc-equal lhs bindings)))
       (if (and entry)
           (if (not (consp (cdr entry)))
               (mv (hard-error 'create-case-from-lhs
                               "Bindings have an unexpected shape ~%"
                               nil)
                   bindings)
             (mv (sa 'x (cadr entry))
                 (acons lhs (cddr entry) bindings)))
         (mv '& bindings))))
    ((acl2::fquotep lhs)
     (mv (list 'quote lhs) bindings))
    (t (b* (((mv rest bindings)
             (create-case-from-lhs-lst (cdr lhs) bindings)))
         (mv `(',(car lhs) . ,rest)
             bindings)))))

 (defun create-case-from-lhs-lst (lst bindings)
   (if (atom lst)
       (mv nil bindings)
     (b* (((mv rest bindings)
           (create-case-from-lhs (car lst) bindings))
          ((mv rest2 bindings)
           (create-case-from-lhs-lst (cdr lst) bindings)))
       (mv (cons rest rest2)
           bindings)))))

(progn
  (defun get-rp-equals-for-repeated-aux (vals)
    (if (or (atom vals)
            (atom (cdr vals)))
        nil
      (cons `(p-rp-equal-cnt ,(sa 'x (car vals))
                             ,(sa 'x (cadr vals))
                             0)
            (get-rp-equals-for-repeated-aux (cdr vals)))))

  (defun get-rp-equals-for-repeated (bindings)
    (if (atom bindings)
        nil
      (b* ((val (cdar bindings)))
        (if (< (len val) 2)
            (get-rp-equals-for-repeated (cdr bindings))
          (append (get-rp-equals-for-repeated-aux val)
                  (get-rp-equals-for-repeated (cdr bindings)))))))

  (defun get-bindings-for-synp (bindings)
    (if (atom bindings)
        nil
      (acons (caar bindings)
             (sa 'x (cadar bindings))
             (get-bindings-for-synp (cdr bindings)))))

  (defun create-full-case (lhs synp bindings)
    (b* (((mv case-statement &)
          (create-case-from-lhs lhs bindings))
         (rp-equals (get-rp-equals-for-repeated bindings))
         (bindings-for-synp (get-bindings-for-synp bindings)))
      (if (or rp-equals
              synp)
          `(,case-statement
            (and ,@rp-equals
                 ,(if synp
                      (rp-apply-bindings synp bindings-for-synp)
                    t)))
        nil))))

(defun create-rule-fnc (rule-name rule-term)
  (if (include-fnc rule-term 'cons)
      nil
    (b* (((mv lhs synp)
          (rule->lhs-and-syntaxp rule-term))
         ((unless lhs)
          nil)
         (lhs-bindings (get-lhs-bindings lhs synp))
         (lhs-bindings (fast-alist-clean lhs-bindings))
         (full-case1 (create-full-case lhs synp lhs-bindings))
         ((unless full-case1)
          nil))
      `(defun ,(intern-in-package-of-symbol
                (symbol-name (sa rule-name '$fnc))
                rule-name)
           (rule-term)
         (declare (xargs :mode :program))
         (case-match rule-term
           ,full-case1)))))



#|(b* ((term '(implies (IF
                      (SYNP 'NIL
                            '(SYNTAXP (OR (ATOM b) (ATOM (CAR b))))
                            '(IF (IF (ATOM b) (ATOM b) (ATOM (CAR b)))
                                 'T
                                 'NIL))
                      (BITP B)
                      'NIL)
                     (equal (BINARY-AND A (BINARY-AND A c B))
                            (BINARY-AND A B)))))
  (create-rule-fnc 'acl2::test-rule term))


(defun test_rule_fnc (term state)
  (declare (xargs :stobjs (state)))
  (b* (((mv & res)
        (magic-ev-fncall 'TEST-RULE_$FNC (list term)
                         state t nil)))
    res))||#


(defun generate-rule-fncs (runes existing-rw-fncs state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (if (atom runes)
      nil
    (b* ((rune (car runes))
         (rule-name (case-match rune
                      ((& name)
                       name)
                      (& rune)))
         (rune (get-rune-name rule-name state))
         ((when (or (atom rune)
                    (and (Not (equal (car rune) ':rewrite))
                         (Not (equal (car rune) ':type-prescription)))))
          (generate-rule-fncs (cdr runes) existing-rw-fncs state))
         ((when (hons-get rule-name existing-rw-fncs))
          (generate-rule-fncs (cdr runes) existing-rw-fncs state))
         (formula (meta-extract-formula rule-name state))
         ((when (equal formula ''t))
          (generate-rule-fncs (cdr runes) existing-rw-fncs state))
         (fnc-def (create-rule-fnc rule-name formula))
         ((unless fnc-def)
          (generate-rule-fncs (cdr runes) existing-rw-fncs state)))
      (cons
       `(progn
          ,fnc-def
          (table rw-fncs
                 ',rule-name
                 ',(intern-in-package-of-symbol
                   (symbol-name (sa rule-name '$fnc))
                   rule-name)))
       (generate-rule-fncs (cdr runes) existing-rw-fncs state)))))

(defun generate-rule-fncs-main (runes state)
  (declare (xargs :mode :program
                  :stobjs (state)))
  (b* ((world (w state))
       (existing-rw-fncs (make-fast-alist (table-alist 'rw-fncs world)))
       (new-fnc-defs (generate-rule-fncs runes existing-rw-fncs state))
       (- (fast-alist-free existing-rw-fncs)))
    new-fnc-defs))


(defmacro create-rule-fncs
    (&key (runes '(let ((world (w state))) (current-theory :here))))
  `(with-output
     :off :all
     :gag-mode nil
     (make-event
      (b* ((runes ,runes)
           (fnc-defs (generate-rule-fncs-main runes state)))
        (if fnc-defs
            `(progn
               ,@fnc-defs)
          `(value-triple :redundant))))))
