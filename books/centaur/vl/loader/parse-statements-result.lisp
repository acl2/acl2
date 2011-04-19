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
(include-book "parse-statements-tokenlist")
(local (include-book "../util/arithmetic"))


(defun vl-stmt-claim-fn (name extra-args extra-hyps type true-listp)
  (let* ((full-args (append extra-args '(tokens warnings)))
         (claim     (ACL2::substitute `(mv-nth 1 (,name . ,full-args)) 'val type)))
    `'(,name (implies (and (force (vl-tokenlist-p tokens))
                           (force (not (mv-nth 0 (,name . ,full-args))))
                           ,@extra-hyps)
                      ,(if true-listp
                           `(and ,claim
                                 (true-listp (mv-nth 1 (,name . ,full-args))))
                         claim)))))

(defmacro vl-stmt-claim (name type &key extra-args extra-hyps true-listp)
  (vl-stmt-claim-fn name extra-args extra-hyps type true-listp))

(with-output
 :off prove :gag-mode :goals
 (make-event
  `(defthm-vl-flag-parse-statement vl-parse-statement-type

     ,(vl-stmt-claim vl-parse-case-item-fn
                     (vl-parsed-caseitemlist-p val)
                     :true-listp t)
     ,(vl-stmt-claim vl-parse-1+-case-items-fn
                     (vl-parsed-caseitemlist-p val)
                     :true-listp t)
     ,(vl-stmt-claim vl-parse-case-statement-fn
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-conditional-statement-fn
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-loop-statement-fn
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-par-block-fn
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-seq-block-fn
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-procedural-timing-control-statement-fn
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-wait-statement-fn
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-statement-aux-fn
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-statement-fn
                     (vl-stmt-p val))
     ,(vl-stmt-claim vl-parse-statement-or-null-fn
                     (vl-stmt-p val))
     ,(vl-stmt-claim vl-parse-statements-until-end-fn
                     (vl-stmtlist-p val)
                     :true-listp t)
     :hints(("Goal" :induct (vl-flag-parse-statement flag atts tokens warnings))
            (and acl2::stable-under-simplificationp
                 (flag::expand-calls-computed-hint
                  acl2::clause
                  ',(flag::get-clique-members 'vl-parse-statement-fn (w state))))))))
