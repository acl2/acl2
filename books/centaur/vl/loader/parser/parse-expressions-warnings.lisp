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

(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           ;consp-when-vl-atomguts-p
                           ;tag-when-vl-ifstmt-p
                           ;tag-when-vl-seqblockstmt-p
                           )))


(defun vl-warninglist-claim-fn (name extra-args)
  (let ((full-args (append extra-args '(tokens warnings))))
    `'(,name (implies (force (vl-warninglist-p warnings))
                      (vl-warninglist-p (mv-nth 3 (,name . ,full-args)))))))

(defmacro vl-warninglist-claim (name &key extra-args)
  (vl-warninglist-claim-fn name extra-args))

(with-output
 :off prove :gag-mode :goals
 (make-event
  `(defthm-parse-expressions-flag vl-parse-expression-warninglist
     ,(vl-warninglist-claim vl-parse-attr-spec)
     ,(vl-warninglist-claim vl-parse-attribute-instance-aux)
     ,(vl-warninglist-claim vl-parse-attribute-instance)
     ,(vl-warninglist-claim vl-parse-0+-attribute-instances)
     ,(vl-warninglist-claim vl-parse-1+-expressions-separated-by-commas)
     ,(vl-warninglist-claim vl-parse-system-function-call)
     ,(vl-warninglist-claim vl-parse-mintypmax-expression)
     ,(vl-warninglist-claim vl-parse-range-expression)
     ,(vl-warninglist-claim vl-parse-concatenation)
     ,(vl-warninglist-claim vl-parse-concatenation-or-multiple-concatenation)
     ,(vl-warninglist-claim vl-parse-hierarchial-identifier :extra-args (recursivep))
     ,(vl-warninglist-claim vl-parse-function-call)
     ,(vl-warninglist-claim vl-parse-0+-bracketed-expressions)
     ,(vl-warninglist-claim vl-parse-indexed-id)
     ,(vl-warninglist-claim vl-parse-primary)
     ,(vl-warninglist-claim vl-parse-unary-expression)
     ,(vl-warninglist-claim vl-parse-power-expression-aux)
     ,(vl-warninglist-claim vl-parse-power-expression)
     ,(vl-warninglist-claim vl-parse-mult-expression-aux)
     ,(vl-warninglist-claim vl-parse-mult-expression)
     ,(vl-warninglist-claim vl-parse-add-expression-aux)
     ,(vl-warninglist-claim vl-parse-add-expression)
     ,(vl-warninglist-claim vl-parse-shift-expression-aux)
     ,(vl-warninglist-claim vl-parse-shift-expression)
     ,(vl-warninglist-claim vl-parse-compare-expression-aux)
     ,(vl-warninglist-claim vl-parse-compare-expression)
     ,(vl-warninglist-claim vl-parse-equality-expression-aux)
     ,(vl-warninglist-claim vl-parse-equality-expression)
     ,(vl-warninglist-claim vl-parse-bitand-expression-aux)
     ,(vl-warninglist-claim vl-parse-bitand-expression)
     ,(vl-warninglist-claim vl-parse-bitxor-expression-aux)
     ,(vl-warninglist-claim vl-parse-bitxor-expression)
     ,(vl-warninglist-claim vl-parse-bitor-expression-aux)
     ,(vl-warninglist-claim vl-parse-bitor-expression)
     ,(vl-warninglist-claim vl-parse-logand-expression-aux)
     ,(vl-warninglist-claim vl-parse-logand-expression)
     ,(vl-warninglist-claim vl-parse-logor-expression-aux)
     ,(vl-warninglist-claim vl-parse-logor-expression)
     ,(vl-warninglist-claim vl-parse-expression)
     :hints(("Goal" :in-theory (disable (force)))
            (and acl2::stable-under-simplificationp
                 (flag::expand-calls-computed-hint
                  acl2::clause
                  ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))))))
