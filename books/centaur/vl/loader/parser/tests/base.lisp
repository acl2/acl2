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
(include-book "../../lexer/lexer") ;; for make-test-tokens, etc.
(include-book "../../../parsetree")

; We now introduce a function to convert expressions into a "pretty" format
; which makes it a bit easier to see if an expression is what you expect for
; writing unit tests.

(defun vl-pretty-atom (x)
  (declare (xargs :guard (vl-atom-p x)))
  (let ((guts (vl-atom->guts x)))
    (cond ((vl-constint-p guts)    (vl-constint->value guts))
          ((vl-weirdint-p guts)    (list 'weird (vl-bitlist->string (vl-weirdint->bits guts))))
          ((vl-string-p guts)      (list 'str  (vl-string->value guts)))
          ((vl-real-p guts)        (list 'real (vl-real->value guts)))
          ((vl-id-p guts)          (list 'id   (vl-id->name guts)))
          ((vl-hidpiece-p guts)    (list 'hid  (vl-hidpiece->name guts)))
          ((vl-funname-p guts)     (list 'fun  (vl-funname->name guts)))
          ((vl-sysfunname-p guts)  (list 'sys  (vl-sysfunname->name guts))))))

(mutual-recursion

 (defun vl-pretty-expr (x)
   (declare (xargs :guard (vl-expr-p x)
                   :measure (two-nats-measure (acl2-count x) 1)))
   (if (vl-fast-atom-p x)
       (vl-pretty-atom x)
     (list* (vl-nonatom->op x)
            (vl-pretty-atts (vl-nonatom->atts x))
            (vl-pretty-exprlist (vl-nonatom->args x)))))

 (defun vl-pretty-atts (x)
   (declare (xargs :guard (vl-atts-p x)
                   :measure (two-nats-measure (acl2-count x) 0)))
   (if (atom x)
       nil
     (cons
      (if (cdar x)
          (list (caar x) '<- (vl-pretty-expr (cdar x)))
        (caar x))
      (vl-pretty-atts (cdr x)))))

 (defun vl-pretty-exprlist (x)
   (declare (xargs :guard (vl-exprlist-p x)
                   :measure (two-nats-measure (acl2-count x) 0)))
   (if (atom x)
       nil
     (cons (vl-pretty-expr (car x))
           (vl-pretty-exprlist (cdr x))))))


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



(defund vl-pretty-plainarg (x)
  (declare (xargs :guard (vl-plainarg-p x)))
  (let ((expr (vl-plainarg->expr x)))
    (if (not expr)
        :blank
      (vl-pretty-expr expr))))

(defprojection vl-pretty-plainarg-list (x)
  (vl-pretty-plainarg x)
  :guard (vl-plainarglist-p x))

(defund vl-pretty-namedarg (x)
  (declare (xargs :guard (vl-namedarg-p x)))
  (let ((name (vl-namedarg->name x))
        (expr (vl-namedarg->expr x)))
    (list name '<-- (if expr (vl-pretty-expr expr) :blank))))

(defprojection vl-pretty-namedarg-list (x)
  (vl-pretty-namedarg x)
  :guard (vl-namedarglist-p x))

(defund vl-pretty-arguments (x)
  (declare (xargs :guard (vl-arguments-p x)))
  (if (vl-arguments->namedp x)
      (list :namedargs
            (vl-pretty-namedarg-list (vl-arguments->args x)))
    (list :plainargs
          (vl-pretty-plainarg-list (vl-arguments->args x)))))
