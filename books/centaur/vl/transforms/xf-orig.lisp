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
(include-book "../parsetree")
(include-book "../mlib/expr-tools")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc origexprs
  :parents (transforms)
  :short "Add @('VL_ORIG_EXPR') annotations to some expressions."

  :long "<p>In this transformation, we annotate many expressions with their
@('VL_ORIG_EXPR') attribute (see @(see vl-atts-p)).  The idea is to associate
each expression with its \"original version,\" as it was read from the source
file, before any simplification has taken place.</p>

<p>Why do we want to do this?  Transformations like @(see oprewrite) can, for
instance, simplify expressions such as @('a == b') into @('&(a ~^ b)'), and
these reduced expressions may not correspond to anything the logic designer
actually wrote in the source file.  So, if we want to print an error message or
warning about this expression, we would prefer to write it as @('a == b')
instead.  By saving the original version of the expression as an attribute, we
can easily remember where the expression came from.</p>

<p>The core function, @(see vl-expr-origexprs), is rather cute.  As we
encounter each expression, say @('x'), we just cons together a new expression
with the same fields, except that we add an @('VL_ORIG_EXPR') attribute whose
value is @('x') itself.  This is really quite fast, and we do not need to do
any pretty-printing ahead of time.</p>

<p>In error messages, we typically use this attribute implicitly, by calling
@(see vl-pps-origexpr).</p>")

(local (xdoc::set-default-parents origexprs))

(defines vl-expr-origexprs
  :short "Recursively annotate an expression with @('VL_ORIG_EXPR')
attributes."
  :long "<p>Even though we recursively annotate an expression, this function is
really very fast.  We need not do any pretty-printing, because we are only
consing the original version of X into its attributes.</p>"

  (define vl-expr-origexprs ((x vl-expr-p))
    :returns (new-x vl-expr-p)
    :measure (vl-expr-count x)
    :verify-guards nil
    ;; We don't annotate atoms, since they have no attributes.
    (if (vl-fast-atom-p x)
        (vl-expr-fix x)
      (change-vl-nonatom x
                         :args (vl-exprlist-origexprs (vl-nonatom->args x))
                         :atts (acons "VL_ORIG_EXPR" (vl-expr-fix x)
                                      (vl-nonatom->atts x)))))

  (define vl-exprlist-origexprs ((x vl-exprlist-p))
    :returns (new-x (and (vl-exprlist-p new-x)
                         (equal (len new-x) (len x))))
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (cons (vl-expr-origexprs (car x))
            (vl-exprlist-origexprs (cdr x)))))

  ///
  (verify-guards vl-expr-origexprs)
  (defprojection vl-exprlist-origexprs (x)
    (vl-expr-origexprs x)
    :nil-preservingp nil
    :already-definedp t)
  (deffixequiv-mutual vl-expr-origexprs))

(defmacro def-vl-origexprs (name &key body)
  (let* ((mksym-package-symbol (pkg-witness "VL"))
         (fn   (mksym name '-origexprs))
         (type (mksym name '-p))
         (fix  (mksym name '-fix)))
    `(define ,fn ((x ,type))
       :returns (new-x ,type)
       :short ,(cat "Add @('VL_ORIG_EXPR') annotations throughout a @(see "
                    (symbol-name type) ")")
       (let ((x (,fix x)))
         ,body))))

(defmacro def-vl-origexprs-list (name &key element)
  (let* ((mksym-package-symbol (pkg-witness "VL"))
         (fn      (mksym name '-origexprs))
         (elem-fn (mksym element '-origexprs))
         (type    (mksym name '-p)))
    `(defprojection ,fn ((x ,type))
       :returns (new-x ,type)
       :short ,(cat "Add @('VL_ORIG_EXPR') annotations throughout a @(see "
                    (symbol-name type) ")")
       (,elem-fn x))))

(def-vl-origexprs vl-assign
  :body
  (b* (((vl-assign x) x))
    (change-vl-assign x
                      :lvalue (vl-expr-origexprs x.lvalue)
                      :expr   (vl-expr-origexprs x.expr))))

(def-vl-origexprs-list vl-assignlist :element vl-assign)

(def-vl-origexprs vl-plainarg
  :body
  (b* (((vl-plainarg x) x)
       ((unless x.expr)
        ;; No expressions in a blank.
        x))
    (change-vl-plainarg x :expr (vl-expr-origexprs x.expr))))

(def-vl-origexprs vl-namedarg
  :body
  (b* (((vl-namedarg x) x)
       ((unless x.expr)
        ;; No expressions in a blank.
        x))
    (change-vl-namedarg x :expr (vl-expr-origexprs x.expr))))

(def-vl-origexprs-list vl-plainarglist :element vl-plainarg)
(def-vl-origexprs-list vl-namedarglist :element vl-namedarg)

(def-vl-origexprs vl-arguments
  :body
  (vl-arguments-case x
    :named (make-vl-arguments-named :args (vl-namedarglist-origexprs x.args))
    :plain (make-vl-arguments-plain :args (vl-plainarglist-origexprs x.args))))

(def-vl-origexprs vl-gateinst
  :body
  (b* (((vl-gateinst x) x))
    (change-vl-gateinst x :args (vl-plainarglist-origexprs x.args))))

(def-vl-origexprs-list vl-gateinstlist :element vl-gateinst)

(def-vl-origexprs vl-modinst
  :body
  (b* (((vl-modinst x) x))
    (change-vl-modinst x
                       :portargs (vl-arguments-origexprs x.portargs))))

(def-vl-origexprs-list vl-modinstlist :element vl-modinst)


;; <p><b>BOZO</b> consider extending origexprs to other parts of the parse tree,
;; such as always statements.

(def-vl-origexprs vl-module
  :body
  (b* (((when (vl-module->hands-offp x))
        x)
       ((vl-module x) x)
       (assigns   (vl-assignlist-origexprs x.assigns))
       (gateinsts (vl-gateinstlist-origexprs x.gateinsts))
       (modinsts  (vl-modinstlist-origexprs x.modinsts)))
    (change-vl-module x
                      :assigns assigns
                      :gateinsts gateinsts
                      :modinsts modinsts)))

(def-vl-origexprs-list vl-modulelist :element vl-module)

(define vl-design-origexprs
  :short "Top-level @(see origexprs) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-origexprs x.mods))))
