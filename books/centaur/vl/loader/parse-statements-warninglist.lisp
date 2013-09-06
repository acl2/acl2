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

(with-output
 :off prove :gag-mode :goals
 (make-event
  `(defthm-vl-flag-parse-statement vl-parse-statement-warninglist
     ,(vl-warninglist-claim vl-parse-case-item-fn)
     ,(vl-warninglist-claim vl-parse-1+-case-items-fn)
     ,(vl-warninglist-claim vl-parse-case-statement-fn
                         :extra-args (atts))
     ,(vl-warninglist-claim vl-parse-conditional-statement-fn
                         :extra-args (atts))
     ,(vl-warninglist-claim vl-parse-loop-statement-fn
                         :extra-args (atts))
     ,(vl-warninglist-claim vl-parse-par-block-fn
                         :extra-args (atts))
     ,(vl-warninglist-claim vl-parse-seq-block-fn
                         :extra-args (atts))
     ,(vl-warninglist-claim vl-parse-procedural-timing-control-statement-fn
                         :extra-args (atts))
     ,(vl-warninglist-claim vl-parse-wait-statement-fn
                         :extra-args (atts))
     ,(vl-warninglist-claim vl-parse-statement-aux-fn
                         :extra-args (atts))
     ,(vl-warninglist-claim vl-parse-statement-fn)
     ,(vl-warninglist-claim vl-parse-statement-or-null-fn)
     ,(vl-warninglist-claim vl-parse-statements-until-end-fn)
     ,(vl-warninglist-claim vl-parse-statements-until-join-fn)
     :hints(("Goal" :induct (vl-flag-parse-statement flag atts tokens warnings))
            (and acl2::stable-under-simplificationp
                 (flag::expand-calls-computed-hint
                  acl2::clause
                  ',(flag::get-clique-members 'vl-parse-statement-fn (w state))))))))
