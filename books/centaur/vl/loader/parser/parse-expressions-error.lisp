; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "parse-expressions-def")
(local (include-book "../../util/arithmetic"))
(local (non-parallel-book))

(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           ;consp-when-vl-atomguts-p
                           ;tag-when-vl-ifstmt-p
                           ;tag-when-vl-seqblockstmt-p
                           )))

(defun vl-val-when-error-claim-fn (name extra-args)
  (let ((full-args (append extra-args '(tokens warnings))))
    `'(,name (implies (mv-nth 0 (,name . ,full-args))
                      (equal (mv-nth 1 (,name . ,full-args))
                             nil)))))

(defmacro vl-val-when-error-claim (name &key extra-args)
  (vl-val-when-error-claim-fn name extra-args))

(with-output
 :off prove :gag-mode :goals
 (encapsulate
  ()
  (local (in-theory (disable (force))))
  (make-event
   `(defthm-parse-expressions-flag vl-parse-expression-val-when-error
      ,(vl-val-when-error-claim vl-parse-attr-spec)
      ,(vl-val-when-error-claim vl-parse-attribute-instance-aux)
      ,(vl-val-when-error-claim vl-parse-attribute-instance)
      ,(vl-val-when-error-claim vl-parse-0+-attribute-instances)
      ,(vl-val-when-error-claim vl-parse-1+-expressions-separated-by-commas)
      ,(vl-val-when-error-claim vl-parse-system-function-call)
      ,(vl-val-when-error-claim vl-parse-mintypmax-expression)
      ,(vl-val-when-error-claim vl-parse-range-expression)
      ,(vl-val-when-error-claim vl-parse-concatenation)
      ,(vl-val-when-error-claim vl-parse-concatenation-or-multiple-concatenation)
      ,(vl-val-when-error-claim vl-parse-hierarchial-identifier :extra-args (recursivep))
      ,(vl-val-when-error-claim vl-parse-function-call)
      ,(vl-val-when-error-claim vl-parse-0+-bracketed-expressions)
      ,(vl-val-when-error-claim vl-parse-indexed-id)
      ,(vl-val-when-error-claim vl-parse-primary)
      ,(vl-val-when-error-claim vl-parse-unary-expression)
      ,(vl-val-when-error-claim vl-parse-power-expression-aux)
      ,(vl-val-when-error-claim vl-parse-power-expression)
      ,(vl-val-when-error-claim vl-parse-mult-expression-aux)
      ,(vl-val-when-error-claim vl-parse-mult-expression)
      ,(vl-val-when-error-claim vl-parse-add-expression-aux)
      ,(vl-val-when-error-claim vl-parse-add-expression)
      ,(vl-val-when-error-claim vl-parse-shift-expression-aux)
      ,(vl-val-when-error-claim vl-parse-shift-expression)
      ,(vl-val-when-error-claim vl-parse-compare-expression-aux)
      ,(vl-val-when-error-claim vl-parse-compare-expression)
      ,(vl-val-when-error-claim vl-parse-equality-expression-aux)
      ,(vl-val-when-error-claim vl-parse-equality-expression)
      ,(vl-val-when-error-claim vl-parse-bitand-expression-aux)
      ,(vl-val-when-error-claim vl-parse-bitand-expression)
      ,(vl-val-when-error-claim vl-parse-bitxor-expression-aux)
      ,(vl-val-when-error-claim vl-parse-bitxor-expression)
      ,(vl-val-when-error-claim vl-parse-bitor-expression-aux)
      ,(vl-val-when-error-claim vl-parse-bitor-expression)
      ,(vl-val-when-error-claim vl-parse-logand-expression-aux)
      ,(vl-val-when-error-claim vl-parse-logand-expression)
      ,(vl-val-when-error-claim vl-parse-logor-expression-aux)
      ,(vl-val-when-error-claim vl-parse-logor-expression)
      ,(vl-val-when-error-claim vl-parse-expression)
      :hints((and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))

