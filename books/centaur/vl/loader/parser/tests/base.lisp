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
(include-book "../../../mlib/expr-tools")

; We now introduce a function to convert expressions into a "pretty" format
; which makes it a bit easier to see if an expression is what you expect for
; writing unit tests.

(define vl-pretty-atom ((x vl-expr-p))
  :guard (vl-atom-p x)
  (let ((guts (vl-atom->guts x)))
    (cond ((vl-constint-p guts)    (vl-constint->value guts))
          ((vl-weirdint-p guts)
           (list 'weird
                 (vl-bitlist->string (vl-weirdint->bits guts))))
          ((vl-string-p guts)      (list 'str  (vl-string->value guts)))
          ((vl-real-p guts)        (list 'real (vl-real->value guts)))
          ((vl-id-p guts)          (list 'id   (vl-id->name guts)))
          ((vl-hidpiece-p guts)    (list 'hid  (vl-hidpiece->name guts)))
          ((vl-funname-p guts)     (list 'fun  (vl-funname->name guts)))
          ((vl-sysfunname-p guts)  (list 'sys  (vl-sysfunname->name guts)))
          ((vl-keyguts-p guts)     (list 'key  (vl-keyguts->type guts)))
          ((vl-basictype-p guts)   (list 'basic  (vl-basictype->kind guts)))
          ((vl-tagname-p guts)     (list 'tag  (vl-tagname->name guts)))

          ((vl-time-p guts)
           (list 'time
                 (concatenate 'string
                              (vl-time->quantity guts)
                              (vl-timeunit->string
                               (vl-time->units guts)))))
          ((vl-extint-p guts)
           (list 'ext (vl-extint->value guts)))
          (t
           (raise "Unsupported kind of atom: ~x0." x)))))

(defines vl-pretty-exprs
  :flag nil

  (define vl-pretty-expr ((x vl-expr-p))
    :measure (vl-expr-count x)
    (if (vl-fast-atom-p x)
        (vl-pretty-atom x)
      (list* (vl-nonatom->op x)
             (vl-pretty-atts (vl-nonatom->atts x))
             (vl-pretty-exprlist (vl-nonatom->args x)))))

  (define vl-pretty-atts ((x vl-atts-p))
    :measure (vl-atts-count x)
    (b* ((x (vl-atts-fix x)))
      (if (atom x)
          nil
        (cons
         (if (cdar x)
             (list (caar x) '<- (vl-pretty-expr (cdar x)))
           (caar x))
         (vl-pretty-atts (cdr x))))))

  (define vl-pretty-exprlist ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-expr (car x))
            (vl-pretty-exprlist (cdr x))))))

(define vl-pretty-range ((x vl-range-p))
  (list 'range
        (vl-pretty-expr (vl-range->msb x))
        (vl-pretty-expr (vl-range->lsb x))))

(define vl-pretty-maybe-range ((x vl-maybe-range-p))
  (if (not x)
      '(no-range)
    (vl-pretty-range x)))

(define vl-pretty-range-list ((x vl-rangelist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-range (car x))
          (vl-pretty-range-list (cdr x)))))

(define vl-pretty-maybe-range-list ((x vl-maybe-range-list-p))
  (if (atom x)
      nil
    (cons (vl-pretty-maybe-range (car x))
          (vl-pretty-maybe-range-list (cdr x)))))

(define vl-pretty-plainarg ((x vl-plainarg-p))
  (let ((expr (vl-plainarg->expr x)))
    (if (not expr)
        :blank
      (vl-pretty-expr expr))))

(define vl-pretty-plainarg-list ((x vl-plainarglist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-plainarg (car x))
          (vl-pretty-plainarg-list (cdr x)))))

(define vl-pretty-namedarg ((x vl-namedarg-p))
  (let ((name (vl-namedarg->name x))
        (expr (vl-namedarg->expr x)))
    (list name '<-- (if expr (vl-pretty-expr expr) :blank))))

(define vl-pretty-namedarg-list ((x vl-namedarglist-p))
  (if (atom x)
      nil
    (cons (vl-pretty-namedarg (car x))
          (vl-pretty-namedarg-list (cdr x)))))

(define vl-pretty-arguments ((x vl-arguments-p))
  (vl-arguments-case x
    :named (list :namedargs (vl-pretty-namedarg-list x.args))
    :plain (list :plainargs (vl-pretty-plainarg-list x.args))))



(define vl-pretty-fwdtypedef ((x vl-fwdtypedef-p))
  (b* (((vl-fwdtypedef x) x))
    (list 'fwdtypedef
          x.kind
          x.name)))

(define vl-pretty-packeddimension ((x vl-packeddimension-p))
  :prepwork ((local (in-theory (enable vl-packeddimension-p))))
  (if (eq x :vl-unsized-dimension)
      x
    (vl-pretty-range x)))

(defprojection vl-pretty-packeddimensionlist ((x vl-packeddimensionlist-p))
  (vl-pretty-packeddimension x))

(define vl-pretty-enumbasetype ((x vl-enumbasetype-p))
  (b* (((vl-enumbasetype x) x))
    (list* x.kind
           (if x.signedp 'signed 'unsigned)
           (and x.dim
                (list (vl-pretty-packeddimension x.dim))))))

(define vl-pretty-enumitem ((x vl-enumitem-p))
  (b* (((vl-enumitem x) x))
    (append (list x.name)
            (and x.range (list (vl-pretty-range x.range)))
            (and x.value
                 (list '= (vl-pretty-expr x.value))))))

(defprojection vl-pretty-enumitemlist ((x vl-enumitemlist-p))
  (vl-pretty-enumitem x))

(defines vl-pretty-datatype

  (define vl-pretty-datatype ((x vl-datatype-p))
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      (:vl-coretype
       (list* x.name
              (if x.signedp 'signed 'unsigned)
              (vl-pretty-packeddimensionlist x.dims)))

      (:vl-struct
       (append '(:vl-struct)
               (if x.packedp '(packed) nil)
               (if x.signedp '(signed) nil)
               (vl-pretty-structmemberlist x.members)
               (and x.dims
                    (cons :dims (vl-pretty-packeddimensionlist x.dims)))))

      (:vl-union
       (append '(:vl-union)
               (if x.taggedp '(tagged) nil)
               (if x.packedp '(packed) nil)
               (if x.signedp '(signed) nil)
               (vl-pretty-structmemberlist x.members)
               (and x.dims
                    (cons :dims (vl-pretty-packeddimensionlist x.dims)))))

      (:vl-enum
       (append '(:vl-enum)
               (vl-pretty-enumbasetype x.basetype)
               (vl-pretty-enumitemlist x.items)
               (and x.dims
                    (cons :dims (vl-pretty-packeddimensionlist x.dims)))))

      (:vl-usertype
       (append '(:vl-usertype)
               (list (vl-pretty-expr x.kind))
               (and x.dims
                    (cons :dims (vl-pretty-packeddimensionlist x.dims)))))))

  (define vl-pretty-structmemberlist ((x vl-structmemberlist-p))
    :measure (vl-structmemberlist-count x)
    (if (atom x)
        nil
      (cons (vl-pretty-structmember (car x))
            (vl-pretty-structmemberlist (cdr x)))))

  (define vl-pretty-structmember ((x vl-structmember-p))
    :measure (vl-structmember-count x)
    (b* (((vl-structmember x) x))
      (append (list x.name)
              (and x.rand (list x.rand))
              (vl-pretty-datatype x.type)
              (and x.dims
                   (cons :dims (vl-pretty-packeddimensionlist x.dims)))
              (and x.rhs
                   (list '= (vl-pretty-expr x.rhs)))))))

(define vl-pretty-typedef ((x vl-typedef-p))
  (b* (((vl-typedef x) x))
    (list :vl-typedef x.name
          (vl-pretty-datatype x.type))))

(define vl-pretty-type-declaration ((x (or (vl-typedef-p x)
                                           (vl-fwdtypedef-p x))))
  (if (eq (tag x) :vl-fwdtypedef)
      (vl-pretty-fwdtypedef x)
    (vl-pretty-typedef x)))
