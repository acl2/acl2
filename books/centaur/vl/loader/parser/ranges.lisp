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
(include-book "expressions")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))



; Dimensions and ranges are introduced with the following rules.
;
; dimension ::= '[' dimension_constant_expression ':' dimension_constant_expression ']'
;
; range ::= '[' msb_constant_expression ':' lsb_constant_expression ']'
;
; But these are all just aliases to constant_expression, which we treat as
; regular expressions.  Note also that the names above in "range" are
; misleading, since no particular order is required.  Moreover, we do not make
; any distinction between dimensions and ranges.  That is, in either case, we
; call vl-parse-range and produce vl-range-p objects.

(defparser vl-parse-range ()
  :result (vl-range-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-lbrack))
        (msb := (vl-parse-expression))
        (:= (vl-match-token :vl-colon))
        (lsb := (vl-parse-expression))
        (:= (vl-match-token :vl-rbrack))
        (return (make-vl-range :msb msb
                               :lsb lsb))))

(defparser vl-parse-0+-ranges ()
  ;; Note: assumes brackets denote subsequent ranges to be matched, and as a
  ;; result it may indeed cause an error.
  :result (vl-rangelist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails gracefully
  :count strong-on-value
  (seqw tokens warnings
        (unless (vl-is-token? :vl-lbrack)
          (return nil))
        (first := (vl-parse-range))
        (rest := (vl-parse-0+-ranges))
        (return (cons first rest))))

