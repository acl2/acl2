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
expressions, we return a @(see vl-ctxexprlist) that associates each
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


(defmacro def-vl-ctxexprs (&key type)
  (let* ((mksym-package-symbol 'vl::foo)
         (type-p       (mksym type '-p))
         (fix          (mksym type '-fix))
         (collect      (mksym type '-ctxexprs))
         (allexprs     (mksym type '-allexprs)))
    `(define ,collect
       :parents (ctxexprs)
       ((x   ,type-p)
        (mod stringp)
        (ss  vl-scopestack-p))
       :returns (ctxexprs vl-ctxexprlist-p)
       (let ((x (,fix x)))
         (vl-exprlist-ctxexprs (,allexprs x)
                               (make-vl-context1 :mod mod :elem x)
                               ss)))))

(local (defthm vl-ctxelement-p-when-port
         (implies (vl-port-p x)
                  (vl-ctxelement-p x))
         :hints(("Goal" :in-theory (enable vl-port-p)))))

(def-vl-ctxexprs :type vl-port)
(def-vl-ctxexprs :type vl-portdecl)
(def-vl-ctxexprs :type vl-assign)
(def-vl-ctxexprs :type vl-alias)
(def-vl-ctxexprs :type vl-vardecl)
(def-vl-ctxexprs :type vl-paramdecl)
(def-vl-ctxexprs :type vl-modinst)
(def-vl-ctxexprs :type vl-gateinst)
(def-vl-ctxexprs :type vl-typedef)

(defmacro def-vl-ctxexprs-list (&key element list)
  (let* ((mksym-package-symbol 'vl::foo)
         (list-type-p       (mksym list '-p))
         (collect-list      (mksym list '-ctxexprs))
         (collect-list-nrev (mksym list '-ctxexprs-nrev))
         (collect-elem      (mksym element '-ctxexprs))
         ;; (collect-elem-nrev (mksym element '-ctxexprs-nrev))
         )
    `(progn
       (define ,collect-list-nrev
         :parents (,collect-list)
         ((x ,list-type-p)
          (mod stringp)
          (ss vl-scopestack-p)
          nrev)
         (b* (((when (atom x))
               (nrev-fix nrev))
              (nrev (nrev-append (,collect-elem (car x) mod ss) nrev)))
           (,collect-list-nrev (cdr x) mod ss nrev)))

       (define ,collect-list
         :parents (ctxexprs)
         :short ,(cat "Collect up a @(see vl-ctxexprlist-p) from a list of @(see "
                      (symbol-name list-type-p) ")s.")
         ((x   ,list-type-p)
          (mod stringp)
          (ss vl-scopestack-p))
         :returns (alist vl-ctxexprlist-p)
         :verify-guards nil
         (mbe :logic
              (if (atom x)
                  nil
                (append (,collect-elem (car x) mod ss)
                        (,collect-list (cdr x) mod ss)))
              :exec
              (with-local-nrev (,collect-list-nrev x mod ss nrev)))
         ///
         (defthm ,(mksym collect-list-nrev '-removal)
           (equal (,collect-list-nrev x mod ss nrev)
                  (append nrev (,collect-list x mod ss)))
           :hints(("Goal" :in-theory (enable ,collect-list-nrev))))
         (verify-guards ,collect-list)))))

(def-vl-ctxexprs-list :element vl-port      :list vl-portlist)
(def-vl-ctxexprs-list :element vl-portdecl  :list vl-portdecllist)
(def-vl-ctxexprs-list :element vl-assign    :list vl-assignlist)
(def-vl-ctxexprs-list :element vl-alias     :list vl-aliaslist)
(def-vl-ctxexprs-list :element vl-vardecl   :list vl-vardecllist)
(def-vl-ctxexprs-list :element vl-paramdecl :list vl-paramdecllist)
(def-vl-ctxexprs-list :element vl-fundecl   :list vl-fundecllist)
(def-vl-ctxexprs-list :element vl-taskdecl  :list vl-taskdecllist)
(def-vl-ctxexprs-list :element vl-modinst   :list vl-modinstlist)
(def-vl-ctxexprs-list :element vl-gateinst  :list vl-gateinstlist)
(def-vl-ctxexprs-list :element vl-typedef   :list vl-typedeflist)
(def-vl-ctxexprs-list :element vl-always    :list vl-alwayslist)
(def-vl-ctxexprs-list :element vl-initial   :list vl-initiallist)


(def-genblob-transform vl-genblob-ctxexprs-nrev ((mod stringp)
                                                 (ss vl-scopestack-p)
                                                 nrev)
  :returns (nrev)
  :no-new-x t
  :apply-to-generates vl-generates-ctxexprs-nrev
  :defines-args (:flag-local nil)
  (b* ((ss (vl-scopestack-push (vl-genblob-fix x) ss))
       ((vl-genblob x))
       (nrev (vl-portlist-ctxexprs-nrev      x.ports      mod ss nrev))
       (nrev (vl-portdecllist-ctxexprs-nrev  x.portdecls  mod ss nrev))
       (nrev (vl-assignlist-ctxexprs-nrev    x.assigns    mod ss nrev))
       (nrev (vl-aliaslist-ctxexprs-nrev     x.aliases    mod ss nrev))
       (nrev (vl-vardecllist-ctxexprs-nrev   x.vardecls   mod ss nrev))
       (nrev (vl-paramdecllist-ctxexprs-nrev x.paramdecls mod ss nrev))
       (nrev (vl-fundecllist-ctxexprs-nrev   x.fundecls   mod ss nrev))
       (nrev (vl-taskdecllist-ctxexprs-nrev  x.taskdecls  mod ss nrev))
       (nrev (vl-modinstlist-ctxexprs-nrev   x.modinsts   mod ss nrev))
       (nrev (vl-gateinstlist-ctxexprs-nrev  x.gateinsts  mod ss nrev))
       (nrev (vl-typedeflist-ctxexprs-nrev   x.typedefs   mod ss nrev))
       (nrev (vl-alwayslist-ctxexprs-nrev    x.alwayses   mod ss nrev))
       (nrev (vl-initiallist-ctxexprs-nrev   x.initials   mod ss nrev)))
    (vl-generates-ctxexprs-nrev     x.generates  mod ss nrev)))

(local (in-theory (disable (:t append)
                           (:t true-listp)
                           acl2::append-under-iff
                           acl2::subsetp-append1)))

(def-genblob-transform vl-genblob-ctxexprs ((mod stringp)
                                            (ss vl-scopestack-p))
  :returns ((ctxexprs vl-ctxexprlist-p))
  :no-new-x t
  :apply-to-generates vl-generates-ctxexprs
  :combine-bindings ((ctxexprs (append ctxexprs1 ctxexprs2)))
  :empty-list-bindings ((ctxexprs nil))
  :verify-guards nil
  (mbe :logic
       (b* ((ss (vl-scopestack-push (vl-genblob-fix x) ss))
            ((vl-genblob x)))
         (append (vl-portlist-ctxexprs      x.ports      mod ss)
                 (vl-portdecllist-ctxexprs  x.portdecls  mod ss)
                 (vl-assignlist-ctxexprs    x.assigns    mod ss)
                 (vl-aliaslist-ctxexprs     x.aliases    mod ss)
                 (vl-vardecllist-ctxexprs   x.vardecls   mod ss)
                 (vl-paramdecllist-ctxexprs x.paramdecls mod ss)
                 (vl-fundecllist-ctxexprs   x.fundecls   mod ss)
                 (vl-taskdecllist-ctxexprs  x.taskdecls  mod ss)
                 (vl-modinstlist-ctxexprs   x.modinsts   mod ss)
                 (vl-gateinstlist-ctxexprs  x.gateinsts  mod ss)
                 (vl-typedeflist-ctxexprs   x.typedefs   mod ss)
                 (vl-alwayslist-ctxexprs    x.alwayses   mod ss)
                 (vl-initiallist-ctxexprs   x.initials   mod ss)
                 (vl-generates-ctxexprs     x.generates  mod ss)))
       :exec (with-local-nrev (vl-genblob-ctxexprs-nrev x mod ss nrev)))
  ///
  (local (in-theory (disable acl2::true-listp-append)))
  (defthm-vl-genblob-ctxexprs-nrev-flag
    (defthm vl-genblob-ctxexprs-nrev-elim
      (implies (true-listp nrev)
               (equal (vl-genblob-ctxexprs-nrev x mod ss nrev)
                      (append nrev (vl-genblob-ctxexprs x mod ss))))
      :flag vl-genblob-ctxexprs-nrev)
    (defthm vl-generates-ctxexprs-nrev-elim
      (implies (true-listp nrev)
               (equal (vl-generates-ctxexprs-nrev x mod ss nrev)
                      (append nrev (vl-generates-ctxexprs x mod ss))))
      :flag vl-generates-ctxexprs-nrev)
    (defthm vl-genblob-ctxexprs-nrev-elim-generate
      (implies (true-listp nrev)
               (equal (vl-genblob-ctxexprs-nrev-generate x mod ss nrev)
                      (append nrev (vl-genblob-ctxexprs-generate x mod ss))))
      :flag vl-genblob-ctxexprs-nrev-generate)
    (defthm vl-genblob-ctxexprs-nrev-elim-gencaselist
      (implies (true-listp nrev)
               (equal (vl-genblob-ctxexprs-nrev-gencaselist x mod ss nrev)
                      (append nrev (vl-genblob-ctxexprs-gencaselist x mod ss))))
      :flag vl-genblob-ctxexprs-nrev-gencaselist)
    (defthm vl-genblob-ctxexprs-nrev-elim-genarrayblocklist
      (implies (true-listp nrev)
               (equal (vl-genblob-ctxexprs-nrev-genarrayblocklist x arrayname mod ss nrev)
                      (append nrev (vl-genblob-ctxexprs-genarrayblocklist x arrayname mod ss))))
      :flag vl-genblob-ctxexprs-nrev-genarrayblocklist)
    (defthm vl-genblob-ctxexprs-nrev-elim-genarrayblock
      (implies (true-listp nrev)
               (equal (vl-genblob-ctxexprs-nrev-genarrayblock x arrayname mod ss nrev)
                      (append nrev (vl-genblob-ctxexprs-genarrayblock x arrayname mod ss))))
      :flag vl-genblob-ctxexprs-nrev-genarrayblock)
    :hints ((acl2::just-expand-mrec-default-hint 'vl-genblob-ctxexprs-nrev id t world)
            (and stable-under-simplificationp
                 (EQL 0 (ACCESS ACL2::CLAUSE-ID ID :FORCING-ROUND))
                 (EQUAL '(1) (ACCESS ACL2::CLAUSE-ID ID :POOL-LST))
                 '(:expand ((vl-genblob-ctxexprs x mod ss)
                            (vl-generates-ctxexprs x mod ss)
                            (vl-genblob-ctxexprs-generate x mod ss)
                            (vl-genblob-ctxexprs-gencaselist x mod ss)
                            (vl-genblob-ctxexprs-genarrayblocklist x arrayname mod ss)
                            (vl-genblob-ctxexprs-genarrayblock x arrayname mod ss))))))
  (verify-guards vl-genblob-ctxexprs
    :hints ((and stable-under-simplificationp
                 '(:expand ((vl-genblob-ctxexprs x mod ss)))))))




(define vl-module-ctxexprs ((x vl-module-p) (ss vl-scopestack-p))
  :returns (alist vl-ctxexprlist-p)
  (vl-genblob-ctxexprs (vl-module->genblob x) (vl-module->name x) ss))

(define vl-interface-ctxexprs ((x vl-interface-p) (ss vl-scopestack-p))
  :returns (alist vl-ctxexprlist-p)
  (vl-genblob-ctxexprs (vl-interface->genblob x) (vl-interface->name x) ss))

(define vl-package-ctxexprs ((x vl-package-p) (ss vl-scopestack-p))
  :returns (alist vl-ctxexprlist-p)
  (vl-genblob-ctxexprs (vl-package->genblob x) (vl-package->name x) ss))


(define vl-design-toplevel-ctxexprs ((x vl-design-p))
  :returns (alist vl-ctxexprlist-p)
  (b* (((vl-design x)))
    (vl-genblob-ctxexprs
     (make-vl-genblob :vardecls x.vardecls
                      :taskdecls x.taskdecls
                      :fundecls x.fundecls
                      :paramdecls x.paramdecls
                      :typedefs x.typedefs)
     "__top__level__design__" ;; ??
     (vl-scopestack-init (vl-design-fix x)))))


(program)

(defun def-expr-check-fn (name formals ctx-included-in-warnings)
  (acl2::template-subst-top
   `(progn
      (define vl-ctxexprlist-<check> ((x vl-ctxexprlist-p))
        :returns (warnings vl-warninglist-p)
        (if (atom x)
            nil
          (append (b* (((vl-ctxexpr x) (car x)))
                    ,(if ctx-included-in-warnings
                         `(vl-expr-<check> . ,formals)
                       `(vl-warninglist-add-ctx
                         (vl-expr-<check> . ,formals)
                         x.ctx)))
                  (vl-ctxexprlist-<check> (cdr x)))))
      (define vl-module-<check> ((x vl-module-p)
                                 (ss vl-scopestack-p))
        :returns (new-x vl-module-p)
        (b* ((warnings (append (vl-ctxexprlist-<check>
                                (vl-module-ctxexprs x ss))
                               (vl-module->warnings x))))
          (change-vl-module x :warnings warnings)))

      (defprojection vl-modulelist-<check> ((x vl-modulelist-p)
                                            (ss vl-scopestack-p))
        :returns (new-x vl-modulelist-p)
        (vl-module-<check> x ss))

      (define vl-interface-<check> ((x vl-interface-p)
                                    (ss vl-scopestack-p))
        :returns (new-x vl-interface-p)
        (b* ((warnings (append (vl-ctxexprlist-<check>
                                (vl-interface-ctxexprs x ss))
                               (vl-interface->warnings x))))
          (change-vl-interface x :warnings warnings)))

      (defprojection vl-interfacelist-<check> ((x vl-interfacelist-p)
                                               (ss vl-scopestack-p))
        :returns (new-x vl-interfacelist-p)
        (vl-interface-<check> x ss))

      (define vl-package-<check> ((x vl-package-p)
                                  (ss vl-scopestack-p))
        :returns (new-x vl-package-p)
        (b* ((warnings (append (vl-ctxexprlist-<check>
                                (vl-package-ctxexprs x ss))
                               (vl-package->warnings x))))
          (change-vl-package x :warnings warnings)))

      (defprojection vl-packagelist-<check> ((x vl-packagelist-p)
                                             (ss vl-scopestack-p))
        :returns (new-x vl-packagelist-p)
        (vl-package-<check> x ss))

      (define vl-design-<check> ((x vl-design-p))
        :returns (new-x vl-design-p)
        (b* (((vl-design x))
             (ss (vl-scopestack-init (vl-design-fix x)))
             (mods (vl-modulelist-<check> x.mods ss))
             (ifs  (vl-interfacelist-<check> x.interfaces ss))
             (pkgs  (vl-packagelist-<check> x.packages ss))
             (warnings (append (vl-ctxexprlist-<check>
                                (vl-design-toplevel-ctxexprs x))
                               x.warnings)))
          (change-vl-design x
                            :mods mods
                            :interfaces ifs
                            :packages pkgs
                            :warnings warnings))))
   (acl2::make-tmplsubst
    :strs `(("<CHECK>" ,(symbol-name name) . ,name)))))

(defmacro def-expr-check (name
                          &key
                          (formals '(x.expr x.ss))
                          ctx-included-in-warnings)
  (def-expr-check-fn name formals ctx-included-in-warnings))

