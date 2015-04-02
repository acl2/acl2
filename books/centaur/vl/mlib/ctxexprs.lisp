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
(include-book "allexprs")
(include-book "scopestack")
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

(defprod vl-ctxexpr
  :layout :tree
  ((ctx  vl-context1-p   "Context where an expression occurs.")
   (expr vl-expr-p       "The expression that occurs there.")
   (ss   vl-scopestack-p "The scopestack where it occurs.")))

(fty::deflist vl-ctxexprlist
  :elt-type vl-ctxexpr)

(define vl-exprlist-ctxexprs-nrev
  :parents (vl-make-ctxexprlist)
  ((exprs vl-exprlist-p)
   (ctx   vl-context1-p)
   (ss    vl-scopestack-p)
   nrev)
  (if (atom exprs)
      (nrev-fix nrev)
    (let ((nrev (nrev-push (make-vl-ctxexpr :expr (car exprs)
                                            :ctx ctx
                                            :ss  ss)
                           nrev)))
      (vl-exprlist-ctxexprs-nrev (cdr exprs) ctx ss nrev))))

(define vl-exprlist-ctxexprs
  :parents (ctxexprs)
  :short "Bind some expressions to their context."
  ((exprs vl-exprlist-p   "List of expressions to bind.")
   (ctx   vl-context1-p   "Context to bind to all of these expressions.")
   (ss    vl-scopestack-p "Scopestack to bind them all to."))
  :returns (ctxexprs vl-ctxexprlist-p)
  :verify-guards nil
  (mbe :logic
       (if (atom exprs)
           nil
         (cons (make-vl-ctxexpr :expr (car exprs)
                                :ctx ctx
                                :ss ss)
               (vl-exprlist-ctxexprs (cdr exprs) ctx ss)))
       :exec
       (with-local-nrev (vl-exprlist-ctxexprs-nrev exprs ctx ss nrev)))
  ///
  (local (in-theory (enable vl-exprlist-ctxexprs-nrev)))
  (defthm vl-exprlist-ctxexprs-nrev-removal
    (equal (vl-exprlist-ctxexprs-nrev exprs ctx ss nrev)
           (append nrev (vl-exprlist-ctxexprs exprs ctx ss))))
  (verify-guards vl-exprlist-ctxexprs))


;; visitor for this now...
(include-book "stmt-tools")

(defines vl-stmt-ctxexprs

  (define vl-stmt-ctxexprs ((x   vl-stmt-p)
                            (ctx vl-context1-p)
                            (ss  vl-scopestack-p))
    :returns (ctxexprs vl-ctxexprlist-p)
    :measure (vl-stmt-count x)
    (if (vl-atomicstmt-p x)
        (vl-exprlist-ctxexprs (vl-stmt-allexprs x) ctx ss)
      (vl-stmt-case x
        (:vl-forstmt
         (b* ((ss (vl-scopestack-push (vl-forstmt->blockscope x) ss)))
           (append (vl-exprlist-ctxexprs (vl-compoundstmt->exprs x) ctx ss)
                   (vl-stmtlist-ctxexprs (vl-compoundstmt->stmts x) ctx ss))))
        (:vl-blockstmt
         (b* ((ss (vl-scopestack-push (vl-blockstmt->blockscope x) ss)))
           (append (vl-exprlist-ctxexprs (vl-compoundstmt->exprs x) ctx ss)
                   (vl-stmtlist-ctxexprs (vl-compoundstmt->stmts x) ctx ss))))
        (:otherwise
         (append (vl-exprlist-ctxexprs (vl-compoundstmt->exprs x) ctx ss)
                 (vl-stmtlist-ctxexprs (vl-compoundstmt->stmts x) ctx ss))))))

  (define vl-stmtlist-ctxexprs ((x   vl-stmtlist-p)
                                (ctx vl-context1-p)
                                (ss  vl-scopestack-p))
    :returns (ctxexprs vl-ctxexprlist-p)
    :measure (vl-stmtlist-count x)
    (if (atom x)
        nil
      (append (vl-stmt-ctxexprs (car x) ctx ss)
              (vl-stmtlist-ctxexprs (cdr x) ctx ss))))

  ///
  (deffixequiv-mutual vl-stmt-ctxexprs))


(define vl-fundecl-ctxexprs ((x   vl-fundecl-p)
                             (mod stringp)
                             (ss  vl-scopestack-p))
  :returns (ctxexprs vl-ctxexprlist-p)
  (b* (((vl-fundecl x) (vl-fundecl-fix x))
       (ctx (make-vl-context1 :mod mod :elem x))
       (part1 (vl-exprlist-ctxexprs
               (append (vl-portdecllist-allexprs x.portdecls)
                       (vl-datatype-allexprs x.rettype))
               ctx ss))
       (ss (vl-scopestack-push (vl-fundecl->blockscope x) ss))
       (part2 (vl-exprlist-ctxexprs
               (append (vl-vardecllist-allexprs x.vardecls)
                       (vl-paramdecllist-allexprs x.paramdecls))
               ctx ss))
       (part3 (vl-stmt-ctxexprs x.body ctx ss)))
    (append part1 part2 part3)))

(define vl-taskdecl-ctxexprs ((x   vl-taskdecl-p)
                              (mod stringp)
                              (ss  vl-scopestack-p))
  :returns (ctxexprs vl-ctxexprlist-p)
  (b* (((vl-taskdecl x) (vl-taskdecl-fix x))
       (ctx (make-vl-context1 :mod mod :elem x))
       (part1 (vl-exprlist-ctxexprs (vl-portdecllist-allexprs x.portdecls)
                                    ctx ss))
       (ss (vl-scopestack-push (vl-taskdecl->blockscope x) ss))
       (part2 (vl-exprlist-ctxexprs
               (append (vl-vardecllist-allexprs x.vardecls)
                       (vl-paramdecllist-allexprs x.paramdecls))
               ctx ss))
       (part3 (vl-stmt-ctxexprs x.body ctx ss)))
    (append part1 part2 part3)))

(define vl-always-ctxexprs ((x   vl-always-p)
                            (mod stringp)
                            (ss  vl-scopestack-p))
  :returns (ctxexprs vl-ctxexprlist-p)
  (b* (((vl-always x) (vl-always-fix x))
       (ctx (make-vl-context1 :mod mod :elem x)))
    (vl-stmt-ctxexprs x.stmt ctx ss)))

(define vl-initial-ctxexprs ((x   vl-initial-p)
                             (mod stringp)
                             (ss  vl-scopestack-p))
  :returns (ctxexprs vl-ctxexprlist-p)
  (b* (((vl-initial x) (vl-initial-fix x))
       (ctx (make-vl-context1 :mod mod :elem x)))
    (vl-stmt-ctxexprs x.stmt ctx ss)))






(defmacro def-vl-ctxexprs (&key type push-p)
  (let* ((mksym-package-symbol 'vl::foo)
         (type-p       (mksym type '-p))
         (fix          (mksym type '-fix))
         (collect      (mksym type '-ctxexprs))
         (allexprs     (mksym type '-allexprs)))
    `(define ,collect
       :parents (ctxexprs)
       ((mod stringp)
        (x   ,type-p)
        (ss  vl-scopestack-p))
       :returns (ctxexprs vl-ctxexprlist-p)
       (let ((x (,fix x)))
         (vl-exprlist-ctxexprs (,allexprs x)
                               (make-vl-context1 :mod mod :elem x)
                               ss)))

(local (defthm vl-ctxelement-p-when-port
         (implies (vl-port-p x)
                  (vl-ctxelement-p x))
         :hints(("Goal" :in-theory (enable vl-port-p)))))

(def-vl-ctxexprs :type vl-port)
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
  (let* ((mksym-package-symbol 'vl::foo)
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
         :short ,(cat "Collect up a @(see vl-ctxexprlist-p) from a list of @(see "
                      (symbol-name list-type-p) ")s.")
         ((mod stringp)
          (x   ,list-type-p))
         :returns (alist vl-ctxexprlist-p)
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
  :returns (alist vl-ctxexprlist-p)
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

