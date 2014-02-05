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
(include-book "parse-statements-tokenlist")
(local (include-book "../../util/arithmetic"))


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


;; Sol -- accumulated-persistence hacking
(local (in-theory (disable vl-atomicstmt-p-by-tag-when-vl-stmt-p
                           vl-eventtriggerstmt-p-by-tag-when-vl-atomicstmt-p
                           vl-atomicstmt-p-when-vl-deassignstmt-p
                           vl-disablestmt-p-by-tag-when-vl-atomicstmt-p
                           vl-deassignstmt-p-by-tag-when-vl-atomicstmt-p
                           vl-assignstmt-p-by-tag-when-vl-atomicstmt-p
                           vl-nullstmt-p-by-tag-when-vl-atomicstmt-p
                           vl-enablestmt-p-by-tag-when-vl-atomicstmt-p
                           acl2-count-positive-when-consp
                           vl-is-token?-fn-when-not-consp-of-tokens
                           vl-stmt-p-when-neither-atomic-nor-compound
                           acl2::consp-under-iff-when-true-listp
                           double-containment
                           member-equal-when-member-equal-of-cdr-under-iff
                           acl2::consp-by-len
                           acl2::acl2-count-when-member
                           consp-when-member-equal-of-cons-listp
                           consp-when-member-equal-of-cons-listp
                           (:t vl-is-token?)
                           (:t acl2-count)
                           (:t vl-tokenlist-p)
                           vl-stmt-p-when-member-equal-of-vl-stmtlist-p
                           rationalp-implies-acl2-numberp
                           rationalp-when-integerp
                           integerp-when-natp
                           default-<-2
                           default-<-1
                           natp-when-posp
                           not
                           acl2::true-listp-when-character-listp-rewrite
                           acl2::true-listp-when-symbol-listp-rewrite
                           acl2::true-listp-when-string-listp-rewrite
                           sets::sets-are-true-lists
                           )))

(with-output
 :off prove :gag-mode :goals
 (make-event
  `(defthm-parse-statements-flag vl-parse-statement-type

     ,(vl-stmt-claim vl-parse-case-item
                     (vl-parsed-caseitemlist-p val)
                     :true-listp t)
     ,(vl-stmt-claim vl-parse-1+-case-items
                     (vl-parsed-caseitemlist-p val)
                     :true-listp t)
     ,(vl-stmt-claim vl-parse-case-statement
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-conditional-statement
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-loop-statement
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-par-block
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-seq-block
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-procedural-timing-control-statement
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-wait-statement
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-statement-aux
                     (vl-stmt-p val)
                     :extra-args (atts)
                     :extra-hyps ((force (vl-atts-p atts))))
     ,(vl-stmt-claim vl-parse-statement
                     (vl-stmt-p val))
     ,(vl-stmt-claim vl-parse-statement-or-null
                     (vl-stmt-p val))
     ,(vl-stmt-claim vl-parse-statements-until-end
                     (vl-stmtlist-p val)
                     :true-listp t)
     ,(vl-stmt-claim vl-parse-statements-until-join
                     (vl-stmtlist-p val)
                     :true-listp t)
     :hints((and acl2::stable-under-simplificationp
                 (flag::expand-calls-computed-hint
                  acl2::clause
                  ',(flag::get-clique-members 'vl-parse-statement-fn (w state))))))))
