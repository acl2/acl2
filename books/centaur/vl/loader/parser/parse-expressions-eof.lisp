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



(defun vl-eof-claim-fn (name extra-args type)
  (let ((full-args (append extra-args '(tokens warnings))))
    `'(,name (implies (not (consp tokens))
                      ,(cond ((eq type :error)
                              `(mv-nth 0 (,name . ,full-args)))
                             ((eq type nil)
                              `(equal (mv-nth 1 (,name . ,full-args))
                                      nil))
                             (t
                              (er hard? 'vl-eof-claim-fn
                                  "Bad type: ~x0." type)))))))

(defmacro vl-eof-claim (name type &key extra-args)
  (vl-eof-claim-fn name extra-args type))

(with-output
 :off prove :gag-mode :goals
 (encapsulate
  ()
  (local (in-theory (disable (force))))
  (make-event
   `(defthm-parse-expressions-flag vl-parse-expression-eof
      ,(vl-eof-claim vl-parse-attr-spec :error)
      ,(vl-eof-claim vl-parse-attribute-instance-aux :error)
      ,(vl-eof-claim vl-parse-attribute-instance :error)
      ,(vl-eof-claim vl-parse-0+-attribute-instances nil)
      ,(vl-eof-claim vl-parse-1+-expressions-separated-by-commas :error)
      ,(vl-eof-claim vl-parse-system-function-call :error)
      ,(vl-eof-claim vl-parse-mintypmax-expression :error)
      ,(vl-eof-claim vl-parse-range-expression :error)
      ,(vl-eof-claim vl-parse-concatenation :error)
      ,(vl-eof-claim vl-parse-concatenation-or-multiple-concatenation :error)
      ,(vl-eof-claim vl-parse-hierarchial-identifier :error :extra-args (recursivep))
      ,(vl-eof-claim vl-parse-function-call :error)
      ,(vl-eof-claim vl-parse-0+-bracketed-expressions nil)
      ,(vl-eof-claim vl-parse-indexed-id :error)
      ,(vl-eof-claim vl-parse-primary :error)
      ,(vl-eof-claim vl-parse-unary-expression :error)
      ,(vl-eof-claim vl-parse-power-expression-aux :error)
      ,(vl-eof-claim vl-parse-power-expression :error)
      ,(vl-eof-claim vl-parse-mult-expression-aux :error)
      ,(vl-eof-claim vl-parse-mult-expression :error)
      ,(vl-eof-claim vl-parse-add-expression-aux :error)
      ,(vl-eof-claim vl-parse-add-expression :error)
      ,(vl-eof-claim vl-parse-shift-expression-aux :error)
      ,(vl-eof-claim vl-parse-shift-expression :error)
      ,(vl-eof-claim vl-parse-compare-expression-aux :error)
      ,(vl-eof-claim vl-parse-compare-expression :error)
      ,(vl-eof-claim vl-parse-equality-expression-aux :error)
      ,(vl-eof-claim vl-parse-equality-expression :error)
      ,(vl-eof-claim vl-parse-bitand-expression-aux :error)
      ,(vl-eof-claim vl-parse-bitand-expression :error)
      ,(vl-eof-claim vl-parse-bitxor-expression-aux :error)
      ,(vl-eof-claim vl-parse-bitxor-expression :error)
      ,(vl-eof-claim vl-parse-bitor-expression-aux :error)
      ,(vl-eof-claim vl-parse-bitor-expression :error)
      ,(vl-eof-claim vl-parse-logand-expression-aux :error)
      ,(vl-eof-claim vl-parse-logand-expression :error)
      ,(vl-eof-claim vl-parse-logor-expression-aux :error)
      ,(vl-eof-claim vl-parse-logor-expression :error)
      ,(vl-eof-claim vl-parse-expression :error)
      :hints((and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))
