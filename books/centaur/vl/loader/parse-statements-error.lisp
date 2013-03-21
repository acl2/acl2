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
(include-book "parse-statements-def")
(local (include-book "../util/arithmetic"))

(local (in-theory (disable (:type-prescription vl-is-token?-fn)
                           (:type-prescription acl2-count-positive-when-consp)
                           (:linear acl2-count-positive-when-consp)
                           vl-is-token?-fn-when-not-consp-of-tokens
                           consp-under-iff-when-true-listp
                           (:rewrite acl2::consp-by-len)
                           consp-when-member-equal-of-cons-listp
                           double-containment
                           member-equal-when-member-equal-of-cdr-under-iff
                           vl-is-some-token?-fn-when-not-consp-of-tokens
                           vl-parse-expression-eof-vl-parse-expression-fn
                           acl2::acl2-count-when-member
                           vl-tokenlist-p-of-vl-match-token-fn
                           default-car
                           vl-parse-assignment-result
                           acl2::subsetp-member
                           default-<-1
                           default-<-2
                           default-cdr
                           (:type-prescription acl2-count)
                           (:type-prescription vl-is-some-token?-fn)
                           (:meta acl2::cancel_times-equal-correct)
                           (:meta acl2::cancel_plus-equal-correct)
                           (:meta acl2::cancel_plus-lessp-correct)
                           (:rewrite vl-is-some-token?-fn-when-not-consp-of-types)
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
  `(defthm-vl-flag-parse-statement vl-parse-statement-val-when-error
     ,(vl-val-when-error-claim vl-parse-case-item-fn)
     ,(vl-val-when-error-claim vl-parse-1+-case-items-fn)
     ,(vl-val-when-error-claim vl-parse-case-statement-fn
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-conditional-statement-fn
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-loop-statement-fn
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-par-block-fn
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-seq-block-fn
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-procedural-timing-control-statement-fn
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-wait-statement-fn
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-statement-aux-fn
                               :extra-args (atts))
     ,(vl-val-when-error-claim vl-parse-statement-fn)
     ,(vl-val-when-error-claim vl-parse-statement-or-null-fn)
     ,(vl-val-when-error-claim vl-parse-statements-until-end-fn)
     :hints(("Goal" :induct (vl-flag-parse-statement flag atts tokens warnings))
            '(:do-not '(simplify))
            (flag::expand-calls-computed-hint
             acl2::clause
             ',(flag::get-clique-members 'vl-parse-statement-fn
                                         (w state)))
            (and stable-under-simplificationp
                 '(:do-not nil))))))
