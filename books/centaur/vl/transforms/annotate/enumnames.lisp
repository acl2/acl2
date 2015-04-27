; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author:  Sol Swords <sswords@centtech.com>

(in-package "VL")

(include-book "../../parsetree")
(include-book "../../mlib/expr-tools")
(include-book "centaur/fty/visitor" :dir :system)
(local (std::add-default-post-define-hook :fix))

(defxdoc enum-names
  :short "Making sense of the names defined by enum types."
  :long "<p>Enum types are unique among datatypes in that using one has a side
effect of declaring some names with assigned values.  We deal with these early
on by declaring these names as parameters.  For example:</p>

@({
 typedef enum logic [3:0] { red=1, blue, green, yellow[nyellows-1:0]=2, orange[3:5] };
 })

<p>results in the following parameter declarations:</p>

@({
 parameter logic [3:0] red = 1;
 parameter logic [3:0] blue = red + 1;
 parameter logic [3:0] green = blue + 1;
 })

<p>So far these are straightforward, but the declaration for yellow presents a
problem.  The correct formulation results in the following assignments:

@({
 yellow[nyellows-1] = 2;
 yellow[nyellows-2] = 3;
 ...
 yellow[0] = 2+nyellows;
 })

<p>But we don't have a closed-form expression to write this, so we'll make one
up: the fictional system function @('$enumrange(firstidx, lastidx, startval)').
To continue with the declarations:</p>

@({
 parameter logic [3:0] yellow [nyellows-1:0] = $enumrange(nyellows-1, 0, green+1);
 parameter logic [3:0] orange [3:5] = $enumrange(3, 5, yellow[0]);
 })

<p>The above example illustrates how we create parameters for the names
declared in an enum type.  This transformation then applies this to every enum
found in the datatype of a variable, parameter, or typedef declaration.</p>")


(define vl-enumname-declaration ((x vl-enumitem-p)
                                 (lastval vl-expr-p)
                                 (basetype vl-datatype-p)
                                 (loc vl-location-p))
  :returns (param vl-paramdecl-p)
  (b* (((vl-enumitem x))
       (val (or x.value
                (make-vl-binary :op :vl-binary-plus
                                :left lastval
                                :right (vl-make-index 1)))))
    (make-vl-paramdecl
     :name x.name
     :localp t
     :type
     (make-vl-explicitvalueparam
      :type (if x.range
                (vl-datatype-update-udims
                 ;; Basetype isn't allowed to have unpacked dims
                 (list (vl-range->packeddimension x.range))
                 basetype)
              basetype)
      :default (if x.range
                   (make-vl-call :name (vl-idscope "$enumrange")
                                 :systemp t
                                 :args (list (vl-range->msb x.range)
                                             (vl-range->lsb x.range)
                                             val))
                 val))
     :loc loc)))

(define vl-enumname-declarations ((x vl-enumitemlist-p)
                                  (lastval vl-expr-p)
                                  (basetype vl-datatype-p)
                                  (loc vl-location-p))
  :returns (paramdecls vl-paramdecllist-p)
  (b* (((when (atom x)) nil)
       ((vl-enumitem x1) (car x))
       (nextval (make-vl-index
                 :scope (vl-idscope x1.name)
                 :indices (if x1.range (list (vl-range->lsb x1.range)) nil)))
       (decl (vl-enumname-declaration x1 lastval basetype loc)))
    (cons decl (vl-enumname-declarations (cdr x) nextval basetype loc))))

(defines vl-datatype-enumname-declarations
  (define vl-datatype-enumname-declarations ((x vl-datatype-p)
                                             (loc vl-location-p))
    :returns (paramdecls vl-paramdecllist-p)
    :measure (vl-datatype-count x)
    (vl-datatype-case x
      :vl-enum (vl-enumname-declarations
                x.items (vl-make-index 0) x.basetype loc)
      :vl-struct (vl-structmemberlist-enumname-declarations x.members loc)
      :vl-union (vl-structmemberlist-enumname-declarations x.members loc)
      :otherwise nil))
  (define vl-structmemberlist-enumname-declarations ((x vl-structmemberlist-p)
                                                     (loc vl-location-p))
    :returns (paramdecls vl-paramdecllist-p)
    :measure (vl-structmemberlist-count x)
    (if (atom x)
        nil
      (append (vl-datatype-enumname-declarations (vl-structmember->type (car x))
                                                 loc)
              (vl-structmemberlist-enumname-declarations (cdr x) loc))))
  ///
  (deffixequiv-mutual vl-datatype-enumname-declarations))

(define vl-paramdecl-enumname-declarations ((x vl-paramdecl-p))
  :returns (paramdecls vl-paramdecllist-p)
  (b* (((vl-paramdecl x)))
    (vl-paramtype-case x.type
      ;; Note: Not sure how this should work for type parameters.  Presumably
      ;; it shouldn't hurt to make the declarations, even if it's going to get
      ;; overridden?
      :vl-typeparam (and x.type.default
                         (vl-datatype-enumname-declarations x.type.default x.loc))
      :vl-explicitvalueparam (vl-datatype-enumname-declarations x.type.type x.loc)
      :otherwise nil)))

(define vl-vardecl-enumname-declarations ((x vl-vardecl-p))
  :returns (paramdecls vl-paramdecllist-p)
  (b* (((vl-vardecl x)))
    (vl-datatype-enumname-declarations x.type x.loc)))

(define vl-typedef-enumname-declarations ((x vl-typedef-p))
  :returns (paramdecls vl-paramdecllist-p)
  (b* (((vl-typedef x)))
    (vl-datatype-enumname-declarations x.type x.minloc)))

(define vl-paramdecllist-enumname-declarations ((x vl-paramdecllist-p))
  :returns (paramdecls vl-paramdecllist-p)
  (if (atom x)
      nil
    (append (vl-paramdecl-enumname-declarations (car x))
            (vl-paramdecllist-enumname-declarations (cdr x)))))

(define vl-vardecllist-enumname-declarations ((x vl-vardecllist-p))
  :returns (paramdecls vl-paramdecllist-p)
  (if (atom x)
      nil
    (append (vl-vardecl-enumname-declarations (car x))
            (vl-vardecllist-enumname-declarations (cdr x)))))

(define vl-typedeflist-enumname-declarations ((x vl-typedeflist-p))
  :returns (paramdecls vl-paramdecllist-p)
  (if (atom x)
      nil
    (append (vl-typedef-enumname-declarations (car x))
            (vl-typedeflist-enumname-declarations (cdr x)))))

(define vl-module-add-enumname-declarations ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x))
       (decls (append (vl-paramdecllist-enumname-declarations x.paramdecls)
                      (vl-vardecllist-enumname-declarations x.vardecls)
                      (vl-typedeflist-enumname-declarations x.typedefs))))
    (change-vl-module x :paramdecls (append-without-guard
                                     x.paramdecls decls))))

(defprojection vl-modulelist-add-enumname-declarations ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-add-enumname-declarations x))

(define vl-interface-add-enumname-declarations ((x vl-interface-p))
  :returns (new-x vl-interface-p)
  (b* (((vl-interface x))
       (decls (append (vl-paramdecllist-enumname-declarations x.paramdecls)
                      (vl-vardecllist-enumname-declarations x.vardecls))))
    (change-vl-interface x :paramdecls (append-without-guard
                                        x.paramdecls decls))))

(defprojection vl-interfacelist-add-enumname-declarations ((x vl-interfacelist-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-add-enumname-declarations x))

(define vl-design-add-enumname-declarations ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       (decls (append (vl-paramdecllist-enumname-declarations x.paramdecls)
                      (vl-vardecllist-enumname-declarations x.vardecls)
                      (vl-typedeflist-enumname-declarations x.typedefs))))
    (change-vl-design x :paramdecls (append-without-guard
                                     x.paramdecls decls)
                      :mods (vl-modulelist-add-enumname-declarations x.mods)
                      :interfaces (vl-interfacelist-add-enumname-declarations x.interfaces))))


    
