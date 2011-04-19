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
(include-book "parse-expressions-tokenlist") ;; sucky
(include-book "parse-expressions-error")     ;; sucky
(local (include-book "../util/arithmetic"))

(local (in-theory (disable consp-under-iff-when-true-listp
                           member-equal-when-member-equal-of-cdr-under-iff
                           default-car
                           default-cdr
                           ;consp-when-vl-atomguts-p
                           ;tag-when-vl-ifstmt-p
                           ;tag-when-vl-seqblockstmt-p
                           )))

(defun vl-expression-claim-fn (name extra-args type)
  (let ((full-args (append extra-args '(tokens warnings))))
    `'(,name (implies (and (force (vl-tokenlist-p tokens))
                           (force (not (mv-nth 0 (,name . ,full-args)))))
                      ,(cond ((eq type :expr)
                              `(vl-expr-p (mv-nth 1 (,name . ,full-args))))
                             ((eq type :exprlist)
                              `(vl-exprlist-p (mv-nth 1 (,name . ,full-args))))
                             ((eq type :atts)
                              `(vl-atts-p (mv-nth 1 (,name . ,full-args))))
                             ((eq type :erange)
                              `(vl-erange-p (mv-nth 1 (,name . ,full-args))))
                             ((eq type :mixed)
                              `(vl-mixed-binop-list-p (mv-nth 1 (,name . ,full-args))))
                             (t
                              (er hard? 'vl-expression-claim-fn
                                  "Bad type: ~x0." type)))))))

(defmacro vl-expression-claim (name type &key extra-args)
  (vl-expression-claim-fn name extra-args type))

(with-output
 :off prove :gag-mode :goals
 (encapsulate
  ()
  (local (in-theory (enable vl-maybe-expr-p)))
  ;(local (in-theory (disable stringp-when-vl-maybe-string-p)))
  (make-event
   `(defthm-vl-flag-parse-expression vl-parse-expression-value
      (vl-parse-attr-spec-fn
       (implies (and (force (vl-tokenlist-p tokens))
                     (force (not (mv-nth 0 (vl-parse-attr-spec)))))
                (and (consp (mv-nth 1 (vl-parse-attr-spec)))
                     (stringp (car (mv-nth 1 (vl-parse-attr-spec))))
                     (vl-maybe-expr-p (cdr (mv-nth 1 (vl-parse-attr-spec)))))))
      ,(vl-expression-claim vl-parse-attribute-instance-aux-fn :atts)
      ,(vl-expression-claim vl-parse-attribute-instance-fn :atts)
      ,(vl-expression-claim vl-parse-0+-attribute-instances-fn :atts)
      ,(vl-expression-claim vl-parse-1+-expressions-separated-by-commas-fn :exprlist)
      ,(vl-expression-claim vl-parse-system-function-call-fn :expr)
      ,(vl-expression-claim vl-parse-mintypmax-expression-fn :expr)
      ,(vl-expression-claim vl-parse-range-expression-fn :erange)
      ,(vl-expression-claim vl-parse-concatenation-fn :expr)
      ,(vl-expression-claim vl-parse-concatenation-or-multiple-concatenation-fn :expr)
      ,(vl-expression-claim vl-parse-hierarchial-identifier-fn :expr :extra-args (recursivep))
      ,(vl-expression-claim vl-parse-function-call-fn :expr)
      ,(vl-expression-claim vl-parse-0+-bracketed-expressions-fn :exprlist)
      ,(vl-expression-claim vl-parse-indexed-id-fn :expr)
      ,(vl-expression-claim vl-parse-primary-fn :expr)
      ,(vl-expression-claim vl-parse-unary-expression-fn :expr)
      ,(vl-expression-claim vl-parse-power-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-power-expression-fn :expr)
      ,(vl-expression-claim vl-parse-mult-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-mult-expression-fn :expr)
      ,(vl-expression-claim vl-parse-add-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-add-expression-fn :expr)
      ,(vl-expression-claim vl-parse-shift-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-shift-expression-fn :expr)
      ,(vl-expression-claim vl-parse-compare-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-compare-expression-fn :expr)
      ,(vl-expression-claim vl-parse-equality-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-equality-expression-fn :expr)
      ,(vl-expression-claim vl-parse-bitand-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-bitand-expression-fn :expr)
      ,(vl-expression-claim vl-parse-bitxor-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-bitxor-expression-fn :expr)
      ,(vl-expression-claim vl-parse-bitor-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-bitor-expression-fn :expr)
      ,(vl-expression-claim vl-parse-logand-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-logand-expression-fn :expr)
      ,(vl-expression-claim vl-parse-logor-expression-aux-fn :mixed)
      ,(vl-expression-claim vl-parse-logor-expression-fn :expr)
      ,(vl-expression-claim vl-parse-expression-fn :expr)
      :hints(("Goal"
              :induct (vl-flag-parse-expression flag recursivep tokens warnings)
              :do-not '(generalize fertilize))
             (and acl2::stable-under-simplificationp
                  (flag::expand-calls-computed-hint
                   acl2::clause
                   ',(flag::get-clique-members 'vl-parse-expression-fn (w state)))))))))


