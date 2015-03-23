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
(include-book "allexprs")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc ctxexprs
  :parents (vl-context)
  :short "Functions for gathering expressions and the context in which they
occur."

  :long "<p>Like the @(see allexprs) family of functions, these functions
gather up what we regard as the \"top level\" expressions used throughout some
module.  But whereas the @('allexprs') functions just return flat lists of
expressions, we return a @(see vl-exprctxalist-p) that associates each
expression with a @(see vl-context-p) describing its origin.</p>")

(fty::defalist vl-exprctxalist
  :key-type vl-expr-p
  :val-type vl-context1-p
  :parents (ctxexprs)
  :short "An alist binding @(see vl-expr-p)s to @(see vl-context-p)s."
  :long "<p>These alists are produced by our @(see ctxexprs) functions, and
essentially say where some expressions are from.</p>")

(defthm vl-exprlist-p-of-strip-cars-when-vl-exprctxalist-p
  (implies (vl-exprctxalist-p x)
           (vl-exprlist-p (strip-cars x)))
  :hints(("Goal" :induct (len x))))

(define vl-make-exprctxalist-nrev
  :parents (vl-make-exprctxalist)
  ((exprs vl-exprlist-p)
   (ctx   vl-context1-p)
   nrev)
  (if (atom exprs)
      (nrev-fix nrev)
    (let ((nrev (nrev-push (cons (vl-expr-fix (car exprs))
                                 (vl-context1-fix ctx))
                           nrev)))
      (vl-make-exprctxalist-nrev (cdr exprs) ctx nrev))))

(define vl-make-exprctxalist
  :parents (ctxexprs)
  :short "Bind some expressions to their context."
  ((exprs vl-exprlist-p "List of expressions to bind.")
   (ctx   vl-context1-p  "Context to bind to all of these expressions."))
  :returns (alist vl-exprctxalist-p)
  :verify-guards nil
  (mbe :logic
       (if (atom exprs)
           nil
         (cons (cons (vl-expr-fix (car exprs))
                     (vl-context1-fix ctx))
               (vl-make-exprctxalist (cdr exprs) ctx)))
       :exec
       (with-local-nrev (vl-make-exprctxalist-nrev exprs ctx nrev)))
  ///
  (local (in-theory (enable vl-make-exprctxalist-nrev)))
  (defthm vl-make-exprctxalist-nrev-removal
    (equal (vl-make-exprctxalist-nrev exprs ctx nrev)
           (append nrev (vl-make-exprctxalist exprs ctx))))
  (verify-guards vl-make-exprctxalist))

(defmacro def-vl-ctxexprs (&key type)
  (let* ((mksym-package-symbol 'vl2014::foo)
         (type-p       (mksym type '-p))
         (fix          (mksym type '-fix))
         (collect      (mksym type '-ctxexprs))
         (collect-nrev (mksym type '-ctxexprs-nrev))
         (allexprs     (mksym type '-allexprs)))
    `(progn
       (define ,collect-nrev ((mod stringp) (x ,type-p) nrev)
         :parents (,collect)
         :inline t
         (let ((x (,fix x)))
           (vl-make-exprctxalist-nrev (,allexprs x)
                                      (make-vl-context1 :mod mod :elem x)
                                      nrev)))

       (define ,collect
         :parents (ctxexprs)
         ((mod stringp)
          (x   ,type-p))
         :returns (alist vl-exprctxalist-p)
         (let ((x (,fix x)))
           (vl-make-exprctxalist (,allexprs x)
                                 (make-vl-context1 :mod mod :elem x))))

       (defthm ,(mksym collect-nrev '-removal)
         (equal (,collect-nrev mod x nrev)
                (append nrev (,collect mod x)))
         :hints(("Goal" :in-theory (enable ,collect-nrev
                                           ,collect)))))))

(encapsulate nil
  (local (in-theory (enable vl-port-p)))
  (def-vl-ctxexprs :type vl-port))

(def-vl-ctxexprs :type vl-portdecl)
(def-vl-ctxexprs :type vl-assign)
(def-vl-ctxexprs :type vl-vardecl)
(def-vl-ctxexprs :type vl-paramdecl)
(def-vl-ctxexprs :type vl-fundecl)
(def-vl-ctxexprs :type vl-taskdecl)
(def-vl-ctxexprs :type vl-modinst)
(def-vl-ctxexprs :type vl-gateinst)
(def-vl-ctxexprs :type vl-always)
(def-vl-ctxexprs :type vl-initial)

(defmacro def-vl-ctxexprs-list (&key element list)
  (let* ((mksym-package-symbol 'vl2014::foo)
         (list-type-p       (mksym list '-p))
         (collect-list      (mksym list '-ctxexprs))
         (collect-list-nrev (mksym list '-ctxexprs-nrev))
         (collect-elem      (mksym element '-ctxexprs))
         (collect-elem-nrev (mksym element '-ctxexprs-nrev)))
    `(progn
       (define ,collect-list-nrev
         :parents (,collect-list)
         ((mod stringp)
          (x ,list-type-p)
          nrev)
         (b* (((when (atom x))
               (nrev-fix nrev))
              (nrev (,collect-elem-nrev mod (car x) nrev)))
           (,collect-list-nrev mod (cdr x) nrev)))

       (define ,collect-list
         :parents (ctxexprs)
         :short ,(cat "Collect up a @(see vl-exprctxalist-p) from a list of @(see "
                      (symbol-name list-type-p) ")s.")
         ((mod stringp)
          (x   ,list-type-p))
         :returns (alist vl-exprctxalist-p)
         :verify-guards nil
         (mbe :logic
              (if (atom x)
                  nil
                (append (,collect-elem mod (car x))
                        (,collect-list mod (cdr x))))
              :exec
              (with-local-nrev (,collect-list-nrev mod x nrev)))
         ///
         (defthm ,(mksym collect-list-nrev '-removal)
           (equal (,collect-list-nrev mod x nrev)
                  (append nrev (,collect-list mod x)))
           :hints(("Goal" :in-theory (enable ,collect-list-nrev))))
         (verify-guards ,collect-list)))))

(def-vl-ctxexprs-list :element vl-port      :list vl-portlist)
(def-vl-ctxexprs-list :element vl-portdecl  :list vl-portdecllist)
(def-vl-ctxexprs-list :element vl-assign    :list vl-assignlist)
(def-vl-ctxexprs-list :element vl-vardecl   :list vl-vardecllist)
(def-vl-ctxexprs-list :element vl-paramdecl :list vl-paramdecllist)
(def-vl-ctxexprs-list :element vl-fundecl   :list vl-fundecllist)
(def-vl-ctxexprs-list :element vl-taskdecl  :list vl-taskdecllist)
(def-vl-ctxexprs-list :element vl-modinst   :list vl-modinstlist)
(def-vl-ctxexprs-list :element vl-gateinst  :list vl-gateinstlist)
(def-vl-ctxexprs-list :element vl-always    :list vl-alwayslist)
(def-vl-ctxexprs-list :element vl-initial   :list vl-initiallist)

(define vl-module-ctxexprs ((x vl-module-p))
  :returns (alist vl-exprctxalist-p)
  (b* (((vl-module x) x))
    (mbe :logic
         (append (vl-portlist-ctxexprs      x.name x.ports)
                 (vl-portdecllist-ctxexprs  x.name x.portdecls)
                 (vl-assignlist-ctxexprs    x.name x.assigns)
                 (vl-vardecllist-ctxexprs   x.name x.vardecls)
                 (vl-paramdecllist-ctxexprs x.name x.paramdecls)
                 (vl-fundecllist-ctxexprs   x.name x.fundecls)
                 (vl-taskdecllist-ctxexprs  x.name x.taskdecls)
                 (vl-modinstlist-ctxexprs   x.name x.modinsts)
                 (vl-gateinstlist-ctxexprs  x.name x.gateinsts)
                 (vl-alwayslist-ctxexprs    x.name x.alwayses)
                 (vl-initiallist-ctxexprs   x.name x.initials))
         :exec
         (with-local-nrev
           (b* ((nrev (vl-portlist-ctxexprs-nrev      x.name x.ports      nrev))
                (nrev (vl-portdecllist-ctxexprs-nrev  x.name x.portdecls  nrev))
                (nrev (vl-assignlist-ctxexprs-nrev    x.name x.assigns    nrev))
                (nrev (vl-vardecllist-ctxexprs-nrev   x.name x.vardecls   nrev))
                (nrev (vl-paramdecllist-ctxexprs-nrev x.name x.paramdecls nrev))
                (nrev (vl-fundecllist-ctxexprs-nrev   x.name x.fundecls   nrev))
                (nrev (vl-taskdecllist-ctxexprs-nrev  x.name x.taskdecls  nrev))
                (nrev (vl-modinstlist-ctxexprs-nrev   x.name x.modinsts   nrev))
                (nrev (vl-gateinstlist-ctxexprs-nrev  x.name x.gateinsts  nrev))
                (nrev (vl-alwayslist-ctxexprs-nrev    x.name x.alwayses   nrev))
                (nrev (vl-initiallist-ctxexprs-nrev   x.name x.initials   nrev)))
             nrev)))))

