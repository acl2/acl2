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
(include-book "parse-expressions")
(local (include-book "../util/arithmetic"))



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

(defparser vl-parse-range (tokens warnings)
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

(defparser vl-parse-0+-ranges (tokens warnings)
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




(defun vl-pretty-range (x)
  (declare (xargs :guard (vl-range-p x)))
  (list 'range
        (vl-pretty-expr (vl-range->msb x))
        (vl-pretty-expr (vl-range->lsb x))))

(defun vl-pretty-maybe-range (x)
  (declare (xargs :guard (vl-maybe-range-p x)
                  :guard-hints (("Goal" :in-theory (enable vl-maybe-range-p)))))
  (if (not x)
      '(no-range)
    (vl-pretty-range x)))

(defun vl-pretty-range-list (x)
  (declare (xargs :guard (vl-rangelist-p x)))
  (if (consp x)
      (cons (vl-pretty-range (car x))
            (vl-pretty-range-list (cdr x)))
    nil))

(defun vl-pretty-maybe-range-list (x)
  (declare (xargs :guard (vl-maybe-range-list-p x)))
  (if (consp x)
      (cons (vl-pretty-maybe-range (car x))
            (vl-pretty-maybe-range-list (cdr x)))
    nil))




(local
 (encapsulate
  ()
  (local (include-book "lexer"))

  (defmacro test-range (&key input range (successp 't))
    `(assert! (let ((tokens (vl-make-test-tstream ,input)))
                (mv-let (erp val tokens warnings)
                        (vl-parse-range tokens nil)
                        (declare (ignore tokens))
                        (if erp
                            (prog2$ (cw "ERP is ~x0.~%" erp)
                                    (not ,successp))
                          (prog2$ (cw "VAL is ~x0.~%" val)
                                  (and ,successp
                                       (vl-range-p val)
                                       (not warnings)
                                       (equal ',range (vl-pretty-range val)))))))))

  (test-range :input "[7:0]"
              :range (range 7 0))

  (test-range :input "[3:6]"
              :range (range 3 6))

  (test-range :input "[7 : 0]"
              :range (range 7 0))

  (test-range :input "[foo : bar]"
              :range (range (id "foo") (id "bar")))

  (test-range :input "[foo : ]"
              :successp nil)

  (test-range :input "[foo]"
              :successp nil)))
