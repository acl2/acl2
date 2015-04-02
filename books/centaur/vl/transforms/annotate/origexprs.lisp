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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/stmt-tools")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc origexprs
  :parents (annotate)
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
    (vl-expr-update-atts
     (vl-expr-update-subexprs
      x (vl-exprlist-origexprs (vl-expr->subexprs x)))
     (acons "VL_ORIG_EXPR" (vl-expr-fix x)
            (vl-expr->atts x))))

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

(fty::defvisitor-template vl-origexprs-template
  ((x :object))
  :returns (new-x :update)
  :type-fns ((vl-expr     vl-expr-origexprs)
             (vl-exprlist vl-exprlist-origexprs)
             (vl-atts     :skip))
  :fnname-template <type>-origexprs)

(encapsulate
  ()
  (set-bogus-mutual-recursion-ok t) ;; implicitly local
  (fty::defvisitors vl-design-origexprs
    :template vl-origexprs-template
    :types (vl-design)))

