; VL Verilog Toolkit
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "parse-expressions-def")
(local (include-book "../util/arithmetic"))

(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           ;consp-when-vl-atomguts-p
                           ;tag-when-vl-ifstmt-p
                           ;tag-when-vl-seqblockstmt-p
                           )))



(defun vl-tokenlist-claim-fn (name extra-args)
  (let ((full-args (append extra-args '(tokens warnings))))
    `'(,name (implies (force (vl-tokenlist-p tokens))
                      (vl-tokenlist-p (mv-nth 2 (,name . ,full-args)))))))

(defmacro vl-tokenlist-claim (name &key extra-args)
  (vl-tokenlist-claim-fn name extra-args))

(with-output
 :off prove :gag-mode :goals
 (make-event
  `(defthm-vl-flag-parse-expression vl-parse-expression-tokenlist
     ,(vl-tokenlist-claim vl-parse-attr-spec-fn)
     ,(vl-tokenlist-claim vl-parse-attribute-instance-aux-fn)
     ,(vl-tokenlist-claim vl-parse-attribute-instance-fn)
     ,(vl-tokenlist-claim vl-parse-0+-attribute-instances-fn)
     ,(vl-tokenlist-claim vl-parse-1+-expressions-separated-by-commas-fn)
     ,(vl-tokenlist-claim vl-parse-system-function-call-fn)
     ,(vl-tokenlist-claim vl-parse-mintypmax-expression-fn)
     ,(vl-tokenlist-claim vl-parse-range-expression-fn)
     ,(vl-tokenlist-claim vl-parse-concatenation-fn)
     ,(vl-tokenlist-claim vl-parse-concatenation-or-multiple-concatenation-fn)
     ,(vl-tokenlist-claim vl-parse-hierarchial-identifier-fn :extra-args (recursivep))
     ,(vl-tokenlist-claim vl-parse-function-call-fn)
     ,(vl-tokenlist-claim vl-parse-0+-bracketed-expressions-fn)
     ,(vl-tokenlist-claim vl-parse-indexed-id-fn)
     ,(vl-tokenlist-claim vl-parse-primary-fn)
     ,(vl-tokenlist-claim vl-parse-unary-expression-fn)
     ,(vl-tokenlist-claim vl-parse-power-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-power-expression-fn)
     ,(vl-tokenlist-claim vl-parse-mult-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-mult-expression-fn)
     ,(vl-tokenlist-claim vl-parse-add-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-add-expression-fn)
     ,(vl-tokenlist-claim vl-parse-shift-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-shift-expression-fn)
     ,(vl-tokenlist-claim vl-parse-compare-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-compare-expression-fn)
     ,(vl-tokenlist-claim vl-parse-equality-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-equality-expression-fn)
     ,(vl-tokenlist-claim vl-parse-bitand-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-bitand-expression-fn)
     ,(vl-tokenlist-claim vl-parse-bitxor-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-bitxor-expression-fn)
     ,(vl-tokenlist-claim vl-parse-bitor-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-bitor-expression-fn)
     ,(vl-tokenlist-claim vl-parse-logand-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-logand-expression-fn)
     ,(vl-tokenlist-claim vl-parse-logor-expression-aux-fn)
     ,(vl-tokenlist-claim vl-parse-logor-expression-fn)
     ,(vl-tokenlist-claim vl-parse-expression-fn)
     :hints(("Goal" :induct (vl-flag-parse-expression flag recursivep tokens warnings))
            (and acl2::stable-under-simplificationp
                 (flag::expand-calls-computed-hint
                  acl2::clause
                  ',(flag::get-clique-members 'vl-parse-expression-fn (w state))))))))
