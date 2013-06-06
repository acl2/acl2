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
   `(defthm-vl-flag-parse-expression vl-parse-expression-eof
      ,(vl-eof-claim vl-parse-attr-spec-fn :error)
      ,(vl-eof-claim vl-parse-attribute-instance-aux-fn :error)
      ,(vl-eof-claim vl-parse-attribute-instance-fn :error)
      ,(vl-eof-claim vl-parse-0+-attribute-instances-fn nil)
      ,(vl-eof-claim vl-parse-1+-expressions-separated-by-commas-fn :error)
      ,(vl-eof-claim vl-parse-system-function-call-fn :error)
      ,(vl-eof-claim vl-parse-mintypmax-expression-fn :error)
      ,(vl-eof-claim vl-parse-range-expression-fn :error)
      ,(vl-eof-claim vl-parse-concatenation-fn :error)
      ,(vl-eof-claim vl-parse-concatenation-or-multiple-concatenation-fn :error)
      ,(vl-eof-claim vl-parse-hierarchial-identifier-fn :error :extra-args (recursivep))
      ,(vl-eof-claim vl-parse-function-call-fn :error)
      ,(vl-eof-claim vl-parse-0+-bracketed-expressions-fn nil)
      ,(vl-eof-claim vl-parse-indexed-id-fn :error)
      ,(vl-eof-claim vl-parse-primary-fn :error)
      ,(vl-eof-claim vl-parse-unary-expression-fn :error)
      ,(vl-eof-claim vl-parse-power-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-power-expression-fn :error)
      ,(vl-eof-claim vl-parse-mult-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-mult-expression-fn :error)
      ,(vl-eof-claim vl-parse-add-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-add-expression-fn :error)
      ,(vl-eof-claim vl-parse-shift-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-shift-expression-fn :error)
      ,(vl-eof-claim vl-parse-compare-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-compare-expression-fn :error)
      ,(vl-eof-claim vl-parse-equality-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-equality-expression-fn :error)
      ,(vl-eof-claim vl-parse-bitand-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-bitand-expression-fn :error)
      ,(vl-eof-claim vl-parse-bitxor-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-bitxor-expression-fn :error)
      ,(vl-eof-claim vl-parse-bitor-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-bitor-expression-fn :error)
      ,(vl-eof-claim vl-parse-logand-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-logand-expression-fn :error)
      ,(vl-eof-claim vl-parse-logor-expression-aux-fn :error)
      ,(vl-eof-claim vl-parse-logor-expression-fn :error)
      ,(vl-eof-claim vl-parse-expression-fn :error)
      :hints(("Goal"
              :induct (vl-flag-parse-expression flag recursivep tokens warnings))
             (and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))
