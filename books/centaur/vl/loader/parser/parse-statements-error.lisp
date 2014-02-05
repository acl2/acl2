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
(include-book "parse-statements-def")
(local (include-book "../../util/arithmetic"))

(local (in-theory (disable (:t vl-is-token?)
                           (:type-prescription acl2-count-positive-when-consp)
                           (:linear acl2-count-positive-when-consp)
                           ;vl-is-token?-when-not-consp-of-tokens
                           acl2::consp-under-iff-when-true-listp
                           (:rewrite acl2::consp-by-len)
                           consp-when-member-equal-of-cons-listp
                           double-containment
                           member-equal-when-member-equal-of-cdr-under-iff
                           vl-is-some-token?-when-not-consp-of-tokens
                           vl-parse-expression-eof-vl-parse-expression
                           acl2::acl2-count-when-member
                           vl-tokenlist-p-of-vl-match-token-fn
                           default-car
                           vl-parse-assignment-result
                           acl2::subsetp-member
                           default-<-1
                           default-<-2
                           default-cdr
                           (:type-prescription acl2-count)
                           (:t vl-is-some-token?)
                           (:meta acl2::cancel_times-equal-correct)
                           (:meta acl2::cancel_plus-equal-correct)
                           (:meta acl2::cancel_plus-lessp-correct)
                           vl-is-some-token?-when-not-consp-of-types
                           magically-reduce-possible-types-from-vl-is-some-token?
                           magically-resolve-vl-is-some-token?
                           car-when-all-equalp
                           member-equal-when-all-equalp
                           not
                           (:type-prescription vl-make-case-statement)
                           first-under-iff-when-vl-exprlist-p
                           vl-exprlist-p-of-cons
                           )))

(with-output
 :off prove :gag-mode :goals
 (make-event
  `(defthm-parse-statements-flag vl-parse-statement-val-when-error
     ,(vl-val-when-error-claim vl-parse-case-item)
     ,(vl-val-when-error-claim vl-parse-1+-case-items)
     ,(vl-val-when-error-claim vl-parse-case-statement
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-conditional-statement
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-loop-statement
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-par-block
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-seq-block
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-procedural-timing-control-statement
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-wait-statement
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-statement-aux
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-statement)
     ,(vl-val-when-error-claim vl-parse-statement-or-null)
     ,(vl-val-when-error-claim vl-parse-statements-until-end)
     ,(vl-val-when-error-claim vl-parse-statements-until-join)
     :hints('(:do-not '(simplify))
            (flag::expand-calls-computed-hint
             acl2::clause
             ',(flag::get-clique-members 'vl-parse-statement-fn
                                         (w state)))
            (and stable-under-simplificationp
                 '(:do-not nil))))))
