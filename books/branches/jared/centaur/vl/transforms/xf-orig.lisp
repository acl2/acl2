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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))


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
@(see vl-pps-origexpr).</p>

<p><b>BOZO</b> consider extending origexprs to other parts of the parse tree,
such as always statements.</p>")


(defsection vl-expr-origexprs
  :parents (origexprs)
  :short "Recursively annotate an expression with @('VL_ORIG_EXPR')
attributes."
  :long "<p><b>Signature:</b> @(call vl-expr-origexprs) returns
@('x-prime').</p>

<p>Even though we recursively annotate an expression, this function is really
very fast.  We need not do any pretty-printing, because we are only consing the
original version of X into its attributes.</p>"

  (mutual-recursion

   (defund vl-expr-origexprs (x)
     "Returns X-PRIME"
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     ;; We don't annotate atoms, since they have no attributes.
     (if (vl-fast-atom-p x)
         x
       (change-vl-nonatom x
                          :args (vl-exprlist-origexprs (vl-nonatom->args x))
                          :atts (acons "VL_ORIG_EXPR" x (vl-nonatom->atts x)))))

   (defund vl-exprlist-origexprs (x)
     "Returns X-PRIME"
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         nil
       (cons (vl-expr-origexprs (car x))
             (vl-exprlist-origexprs (cdr x))))))

  (defthm vl-exprlist-origexprs-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-origexprs x)
                    nil))
    :hints(("Goal" :in-theory (enable vl-exprlist-origexprs))))

  (defthm vl-exprlist-origexprs-of-cons
    (equal (vl-exprlist-origexprs (cons a x))
           (cons (vl-expr-origexprs a)
                 (vl-exprlist-origexprs x)))
    :hints(("Goal" :in-theory (enable vl-exprlist-origexprs))))

  (defprojection vl-exprlist-origexprs (x)
    (vl-expr-origexprs x)
    :nil-preservingp nil
    :already-definedp t)

  (flag::make-flag vl-flag-expr-origexprs
                   vl-expr-origexprs
                   :flag-mapping ((vl-expr-origexprs . expr)
                                  (vl-exprlist-origexprs . list)))

  (defthm-vl-flag-expr-origexprs lemma
    (expr (implies (force (vl-expr-p x))
                   (vl-expr-p (vl-expr-origexprs x)))
          :name vl-expr-p-of-vl-expr-origexprs)
    (list (implies (force (vl-exprlist-p x))
                   (vl-exprlist-p (vl-exprlist-origexprs x)))
          :name vl-exprlist-p-of-vl-exprlist-origexprs)
    :hints(("Goal"
            :induct (vl-flag-expr-origexprs flag x)
            :expand ((vl-expr-origexprs x)
                     (vl-exprlist-origexprs x))
            :do-not '(generalize fertilize)))))




(defmacro def-vl-origexprs (name &key type body)
  (let* ((name-s       (symbol-name name))
         (type-s       (symbol-name type))
         (thm-type-s   (cat type-s "-OF-" name-s))
         (thm-type     (intern-in-package-of-symbol thm-type-s name))
         (short (cat "Add @('VL_ORIG_EXPR') annotations throughout "
                            "a @(see " type-s ")"))
         (long         (cat "<p><b>Signature:</b> @(call " name-s ") returns @('x-prime').</p>")))
    `(defsection ,name
       :parents (origexprs)
       :short ,short
       :long ,long

      (defund ,name (x)
        "Returns X-PRIME"
        (declare (xargs :guard (,type x)))
        ,body)

      (local (in-theory (enable ,name)))

      (defthm ,thm-type
        (implies (force (,type x))
                 (,type (,name x)))))))


(defmacro def-vl-origexprs-list (name &key type element)
  (let* ((name-s (symbol-name name))
         (type-s (symbol-name type))
         (thm-type-s (cat (symbol-name type) "-OF-" (symbol-name name) "-1"))
         (thm-type   (intern-in-package-of-symbol thm-type-s name))
         (short      (cat "Add @('VL_ORIG_EXPR') annotations throughout "
                          "a @(see " type-s ")"))
         (long       (cat "<p><b>Signature:</b> @(call " name-s ") returns
@('x-prime').</p>")))

    `(defsection ,name
       :parents (origexprs)
       :short ,short
       :long ,long

      (defprojection ,name (x)
        (,element x)
        :guard (,type x))

      (defthm ,thm-type
        (implies (force (,type x))
                 (,type (,name x)))
        :hints(("Goal" :induct (len x)))))))


(def-vl-origexprs vl-assign-origexprs
  :type vl-assign-p
  :body (b* ((lvalue       (vl-assign->lvalue x))
             (expr         (vl-assign->expr x))
             (lvalue-prime (vl-expr-origexprs lvalue))
             (expr-prime   (vl-expr-origexprs expr))
             (x-prime      (change-vl-assign x
                                             :lvalue lvalue-prime
                                             :expr expr-prime)))
            x-prime))

(def-vl-origexprs-list vl-assignlist-origexprs
  :type vl-assignlist-p
  :element vl-assign-origexprs)



(def-vl-origexprs vl-plainarg-origexprs
  :type vl-plainarg-p
  :body (b* ((expr (vl-plainarg->expr x))
             ((when (not expr))
              ;; No expressions in a blank.
              x)
             (expr-prime (vl-expr-origexprs expr))
             (x-prime    (change-vl-plainarg x
                                             :expr expr-prime)))
            x-prime))

(def-vl-origexprs vl-namedarg-origexprs
  :type vl-namedarg-p
  :body (b* ((expr (vl-namedarg->expr x))
             ((when (not expr))
              ;; No expressions in a blank.
              x)
             (expr-prime (vl-expr-origexprs expr))
             (x-prime    (change-vl-namedarg x
                                             :expr expr-prime)))
            x-prime))

(def-vl-origexprs-list vl-plainarglist-origexprs
  :type vl-plainarglist-p
  :element vl-plainarg-origexprs)

(def-vl-origexprs-list vl-namedarglist-origexprs
  :type vl-namedarglist-p
  :element vl-namedarg-origexprs)

(def-vl-origexprs vl-arguments-origexprs
  :type vl-arguments-p
  :body (b* ((namedp     (vl-arguments->namedp x))
             (args       (vl-arguments->args x))
             (args-prime (if namedp
                             (vl-namedarglist-origexprs args)
                           (vl-plainarglist-origexprs args)))
             (x-prime    (vl-arguments namedp args-prime)))
            x-prime))

(def-vl-origexprs vl-gateinst-origexprs
  :type vl-gateinst-p
  :body (b* ((args       (vl-gateinst->args x))
             (args-prime (vl-plainarglist-origexprs args))
             (x-prime    (change-vl-gateinst x
                                             :args args-prime)))
            x-prime))

(def-vl-origexprs-list vl-gateinstlist-origexprs
  :type vl-gateinstlist-p
  :element vl-gateinst-origexprs)

(def-vl-origexprs vl-modinst-origexprs
  :type vl-modinst-p
  :body (b* ((args       (vl-modinst->portargs x))
             (args-prime (vl-arguments-origexprs args))
             (x-prime    (change-vl-modinst x
                                            :portargs args-prime)))
            x-prime))

(def-vl-origexprs-list vl-modinstlist-origexprs
  :type vl-modinstlist-p
  :element vl-modinst-origexprs)

(def-vl-origexprs vl-module-origexprs
  :type vl-module-p
  :body (b* (((when (vl-module->hands-offp x))
              x)
             (assigns-prime   (vl-assignlist-origexprs (vl-module->assigns x)))
             (gateinsts-prime (vl-gateinstlist-origexprs (vl-module->gateinsts x)))
             (modinsts-prime  (vl-modinstlist-origexprs (vl-module->modinsts x)))
             (x-prime         (change-vl-module x
                                                :assigns assigns-prime
                                                :gateinsts gateinsts-prime
                                                :modinsts modinsts-prime)))
            x-prime))

(defthm vl-module->name-of-vl-module-origexprs
  (equal (vl-module->name (vl-module-origexprs x))
         (vl-module->name x))
  :hints(("Goal" :in-theory (enable vl-module-origexprs))))


(def-vl-origexprs-list vl-modulelist-origexprs
  :type vl-modulelist-p
  :element vl-module-origexprs)

(defthm vl-modulelist->names-of-vl-modulelist-origexprs
  (equal (vl-modulelist->names (vl-modulelist-origexprs x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))

