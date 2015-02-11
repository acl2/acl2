; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/stmt-tools")
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
  (let* ((mksym-package-symbol (pkg-witness "VL2014"))
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
  (let* ((mksym-package-symbol (pkg-witness "VL2014"))
         (fn      (mksym name '-origexprs))
         (elem-fn (mksym element '-origexprs))
         (type    (mksym name '-p)))
    `(defprojection ,fn ((x ,type))
       :returns (new-x ,type)
       :short ,(cat "Add @('VL_ORIG_EXPR') annotations throughout a @(see "
                    (symbol-name type) ")")
       (,elem-fn x))))

(def-vl-origexprs vl-maybe-expr
  :body
  (if x
      (vl-expr-origexprs x)
    nil))

(def-vl-origexprs vl-range
  :body
  (b* (((vl-range x)))
    (change-vl-range x
                     :msb (vl-expr-origexprs x.msb)
                     :lsb (vl-expr-origexprs x.lsb))))

(def-vl-origexprs vl-maybe-range
  :body
  (if x
      (vl-range-origexprs x)
    nil))

(def-vl-origexprs-list vl-rangelist :element vl-range)

(def-vl-origexprs vl-gatedelay
  :body
  (b* (((vl-gatedelay x)))
    (change-vl-gatedelay x
                         :rise (vl-expr-origexprs x.rise)
                         :fall (vl-expr-origexprs x.fall)
                         :high (vl-maybe-expr-origexprs x.high))))

(def-vl-origexprs vl-maybe-gatedelay
  :body
  (if x
      (vl-gatedelay-origexprs x)
    nil))














(def-vl-origexprs vl-assign
  :body
  (b* (((vl-assign x)))
    (change-vl-assign x
                      :lvalue (vl-expr-origexprs x.lvalue)
                      :expr   (vl-expr-origexprs x.expr)
                      :delay  (vl-maybe-gatedelay-origexprs x.delay))))

(def-vl-origexprs-list vl-assignlist :element vl-assign)



(def-vl-origexprs vl-plainarg
  :body
  (b* (((vl-plainarg x))
       ((unless x.expr)
        ;; No expressions in a blank.
        x))
    (change-vl-plainarg x :expr (vl-expr-origexprs x.expr))))

(def-vl-origexprs vl-namedarg
  :body
  (b* (((vl-namedarg x))
       ((unless x.expr)
        ;; No expressions in a blank.
        x))
    (change-vl-namedarg x :expr (vl-expr-origexprs x.expr))))

(def-vl-origexprs-list vl-plainarglist :element vl-plainarg)
(def-vl-origexprs-list vl-namedarglist :element vl-namedarg)

(def-vl-origexprs vl-arguments
  :body
  (vl-arguments-case x
    :vl-arguments-named
    (change-vl-arguments-named x :args (vl-namedarglist-origexprs x.args))
    :vl-arguments-plain
    (change-vl-arguments-plain x :args (vl-plainarglist-origexprs x.args))))

(def-vl-origexprs vl-gateinst
  :body
  (b* (((vl-gateinst x)))
    (change-vl-gateinst x
                        :args (vl-plainarglist-origexprs x.args)
                        :range (vl-maybe-range-origexprs x.range)
                        :delay (vl-maybe-gatedelay-origexprs x.delay))))

(def-vl-origexprs-list vl-gateinstlist :element vl-gateinst)



(def-vl-origexprs vl-paramvalue
  :body
  (vl-paramvalue-case x
    :expr (vl-expr-origexprs x)
    :datatype x))  ;; bozo add datatypes

(def-vl-origexprs vl-maybe-paramvalue
  :body
  (if x
      (vl-paramvalue-origexprs x)
    nil))

(def-vl-origexprs-list vl-paramvaluelist :element vl-paramvalue)

(def-vl-origexprs vl-namedparamvalue
  :body
  (b* (((vl-namedparamvalue x)))
    (change-vl-namedparamvalue x :value (vl-maybe-paramvalue-origexprs x.value))))

(def-vl-origexprs-list vl-namedparamvaluelist :element vl-namedparamvalue)

(def-vl-origexprs vl-paramargs
  :body
  (vl-paramargs-case x
    :vl-paramargs-named
    (change-vl-paramargs-named x :args (vl-namedparamvaluelist-origexprs x.args))
    :vl-paramargs-plain
    (change-vl-paramargs-plain x :args (vl-paramvaluelist-origexprs x.args))))

(def-vl-origexprs vl-modinst
  :body
  (b* (((vl-modinst x)))
    (change-vl-modinst x
                       :portargs  (vl-arguments-origexprs x.portargs)
                       :paramargs (vl-paramargs-origexprs x.paramargs)
                       :range     (vl-maybe-range-origexprs x.range)
                       :delay     (vl-maybe-gatedelay-origexprs x.delay))))

(def-vl-origexprs-list vl-modinstlist :element vl-modinst)






(def-vl-origexprs vl-evatom
  :body
  (b* (((vl-evatom x)))
    (change-vl-evatom x :expr (vl-expr-origexprs x.expr))))

(def-vl-origexprs-list vl-evatomlist :element vl-evatom)

(def-vl-origexprs vl-eventcontrol
  :body
  (b* (((vl-eventcontrol x)))
    (change-vl-eventcontrol x :atoms (vl-evatomlist-origexprs x.atoms))))


(def-vl-origexprs vl-delaycontrol
  :body
  (b* (((vl-delaycontrol x)))
    (change-vl-delaycontrol x :value (vl-expr-origexprs x.value))))

(def-vl-origexprs vl-repeateventcontrol
  :body
  (b* (((vl-repeateventcontrol x)))
    (change-vl-repeateventcontrol x
                                  :ctrl (vl-eventcontrol-origexprs x.ctrl)
                                  :expr (vl-expr-origexprs x.expr))))

(def-vl-origexprs vl-delayoreventcontrol
  :body
  (case (tag x)
    (:vl-delaycontrol (vl-delaycontrol-origexprs x))
    (:vl-eventcontrol (vl-eventcontrol-origexprs x))
    (otherwise        (vl-repeateventcontrol-origexprs x))))

(def-vl-origexprs vl-maybe-delayoreventcontrol
  :body
  (if x
      (vl-delayoreventcontrol-origexprs x)
    nil))

(defthm vl-maybe-delayoreventcontrol-origexprs-under-iff
  (iff (vl-maybe-delayoreventcontrol-origexprs x)
       x)
  :hints(("Goal" :in-theory (enable vl-maybe-delayoreventcontrol-origexprs))))

(defines vl-stmt-origexprs

  (define vl-stmt-origexprs ((x vl-stmt-p))
    :returns (new-x vl-stmt-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* ((x (vl-stmt-fix x))

         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-nullstmt x)
            (:vl-assignstmt
             (b* (((vl-assignstmt x)))
               (change-vl-assignstmt x
                                     :lvalue (vl-expr-origexprs x.lvalue)
                                     :expr   (vl-expr-origexprs x.expr)
                                     :ctrl   (vl-maybe-delayoreventcontrol-origexprs x.ctrl))))
            (:vl-deassignstmt
             (b* (((vl-deassignstmt x)))
               (change-vl-deassignstmt x
                                       :lvalue (vl-expr-origexprs x.lvalue))))

            (:vl-enablestmt
             (b* (((vl-enablestmt x)))
               (change-vl-enablestmt x
                                     :id   (vl-expr-origexprs x.id)
                                     :args (vl-exprlist-origexprs x.args))))
            (:vl-disablestmt
             (b* (((vl-disablestmt x)))
               (change-vl-disablestmt x
                                      :id (vl-expr-origexprs x.id))))
            (:vl-returnstmt
             (b* (((vl-returnstmt x) x))
               (change-vl-returnstmt x
                                     :val (and x.val
                                               (vl-expr-origexprs x.val)))))
            (:vl-eventtriggerstmt
             (b* (((vl-eventtriggerstmt x)))
               (change-vl-eventtriggerstmt x
                                           :id (vl-expr-origexprs x.id))))
            (otherwise
             (progn$ (impossible)
                     x))))

         (exprs (vl-exprlist-origexprs (vl-compoundstmt->exprs x)))
         (stmts (vl-stmtlist-origexprs (vl-compoundstmt->stmts x)))
         (ctrl  (vl-maybe-delayoreventcontrol-origexprs (vl-compoundstmt->ctrl x))))
      (change-vl-compoundstmt x
                              :exprs exprs
                              :stmts stmts
                              :ctrl ctrl)))

  (define vl-stmtlist-origexprs ((x vl-stmtlist-p))
    :returns (new-x (and (vl-stmtlist-p new-x)
                         (equal (len new-x) (len x))))
    :measure (vl-stmtlist-count x)
    (if (atom x)
        nil
      (cons (vl-stmt-origexprs (car x))
            (vl-stmtlist-origexprs (cdr x)))))
  ///

  (verify-guards vl-stmt-origexprs
    :guard-debug t))



(def-vl-origexprs vl-always
  :body
  (b* (((vl-always x)))
    (change-vl-always x
                      :stmt (vl-stmt-origexprs x.stmt))))

(def-vl-origexprs-list vl-alwayslist :element vl-always)



(def-vl-origexprs vl-initial
  :body
  (b* (((vl-initial x)))
    (change-vl-initial x
                      :stmt (vl-stmt-origexprs x.stmt))))

(def-vl-origexprs-list vl-initiallist :element vl-initial)





;; <p><b>BOZO</b> consider extending origexprs to other parts of the parse tree,
;; such as always statements.

(def-vl-origexprs vl-module
  :body
  (b* (((when (vl-module->hands-offp x))
        x)
       ((vl-module x) x)
       (assigns   (vl-assignlist-origexprs x.assigns))
       (gateinsts (vl-gateinstlist-origexprs x.gateinsts))
       (modinsts  (vl-modinstlist-origexprs x.modinsts))
       (alwayses  (vl-alwayslist-origexprs x.alwayses))
       (initials  (vl-initiallist-origexprs x.initials)))

    (change-vl-module x
                      :assigns   assigns
                      :gateinsts gateinsts
                      :modinsts  modinsts
                      :alwayses  alwayses
                      :initials  initials)))

(def-vl-origexprs-list vl-modulelist :element vl-module)

(define vl-design-origexprs
  :short "Top-level @(see origexprs) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-origexprs x.mods))))
