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
(include-book "scopestack")
(include-book "hid-tools")
(include-book "reportcard")
(include-book "centaur/fty/visitor" :dir :system)
(include-book "centaur/depgraph/mergesort-alist-values" :dir :system)
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))


(defxdoc immdeps
  :parents (hierarchy)
  :short "Functions for collecting the immediate dependencies for various kinds
of descriptions, i.e., for collecting the edges of the @(see hierarchy) graph."

  :long "<p>The top-level function here is @(see vl-design-immdeps), which
produces a @(see vl-immdepgraph-p) which has information about the immediate
dependencies between the design elements and any missing dependencies.</p>")

(define vl-scopestack-toplevel-p
  ;; BOZO move me to mlib/scopestack
  :parents (scopestack)
  :short "Does this scopestack refer to the top level of the design?"
  ((ss vl-scopestack-p))
  (vl-scopestack-case ss
    :global t
    :local nil
    ;; It's not clear what to do here in the NULL case.  A null scopestack can
    ;; be used to fake a scopestack.  It seems reasonable to treat it as either
    ;; being top-level or not.  For now I'll regard these as top-level.
    :null t))

(defprod vl-immdeps
  :parents (immdeps)
  :short "Results of collecting up immediate dependencies."
  :tag :vl-immdeps
  :layout :tree

  ((all-okp  booleanp
             :rule-classes :type-prescription
             :default t
             "Were we able to successfully resolve every identifier we
              encountered?  Even when this is @('nil'), we may be able to
              provide at least mostly accurate dependency information.")

   (deps     string-listp
             "List of dependencies that have been collected.  Note that for
              compatibility with @(see depgraph::toposort), we <b>exclude</b> any
              dependencies that are not found as top-level design elements.
              For instance, if we find a module instance of module @('foo'),
              but @('foo') is not defined, we do <i>not</i> include a
              dependency on @('foo').")

   (warnings vl-warninglist-p
             "Any warnings accumulated during the process of collecting these
              dependencies."))

  :long "<p>It might be better to turn @('deps') into a fast association list
binding names we've seen to T, since there will likely be many duplicates.
But, for now, we'll just use a simple list-based version.  It would be easy to
change this: just modify @(see vl-immdeps-add-raw-dependency) and @(see
vl-immdepgraph-merge).</p>")

(define vl-immdeps-add-raw-dependency
  :parents (vl-immdeps)
  :short "Add a single top-level dependency to the answer we're building."
  ((name stringp "Should exist in the design!")
   (ans  vl-immdeps-p))
  :returns (new-ans vl-immdeps-p)
  :long "<p>This is low level and doesn't check that the @('name') exists.</p>"
  (change-vl-immdeps ans :deps (cons (hons-copy name)
                                     (vl-immdeps->deps ans))))

(define vl-immdeps-add-error
  :parents (vl-immdeps)
  :short "Note that there is an error with the dependencies we're collecting."
  ((ans vl-immdeps-p)
   &key
   (type symbolp)
   (msg  stringp)
   (args true-listp)
   (fatalp booleanp)
   ((fn symbolp) '__function__))
  :returns (new-ans vl-immdeps-p)
  (b* ((w (make-vl-warning :type type
                           :msg msg
                           :args args
                           :fn fn
                           :fatalp fatalp)))
    (change-vl-immdeps ans
                       :all-okp  nil
                       :warnings (cons w (vl-immdeps->warnings ans)))))

(define vl-immdeps-add-pkgdep
  :parents (vl-immdeps)
  :short "Safely add a dependency onto a package.  If the package doesn't
          exist, add a warning instead of a dependency."
  ((pkgname stringp)
   (ans     vl-immdeps-p)
   &key
   ((ss  vl-scopestack-p) 'ss)
   ((ctx acl2::any-p) 'ctx))
  :returns (new-ans vl-immdeps-p)
  (b* ((pkgname (string-fix pkgname))
       (pkg (vl-scopestack-find-package pkgname ss))
       ((unless pkg)
        (vl-immdeps-add-error ans
                              :type :vl-missing-package
                              :msg "~a0: reference to unknown package ~a1."
                              :args (list ctx pkgname)
                              :fatalp t))
       (ans (vl-immdeps-add-raw-dependency pkgname ans)))
    ans))

(define vl-immdeps-add-definition
  :parents (vl-immdeps)
  :short "Safely add a dependency onto a definition (i.e., an interface,
          module, user-defined primitive, etc.  If there is no such definition,
          add a warning instead of a dependency."
  ((name stringp)
   (ans  vl-immdeps-p)
   &key
   ((ss  vl-scopestack-p) 'ss)
   ((ctx acl2::any-p) 'ctx))
  :returns (new-ans vl-immdeps-p)
  (b* ((name (string-fix name))
       (item (vl-scopestack-find-definition name ss))
       ((unless item)
        (vl-immdeps-add-error ans
                              :type :vl-missing-definition
                              :msg "~a0: reference to unknown definition ~a1."
                              :args (list ctx name)
                              :fatalp t))
       (ans (vl-immdeps-add-raw-dependency name ans)))
    ans))

(define vl-immdeps-add-item
  :parents (vl-immdeps)
  :short "Safely add a dependency onto an item (i.e., a parameter, variable,
          function name, type name, etc.)"
  ((name stringp          "Name being referenced.")
   (ans  vl-immdeps-p     "Answer we are building.")
   &key
   ((ss  vl-scopestack-p  "Our current scope.") 'ss)
   ((ctx acl2::any-p      "Context for warnings.") 'ctx))
  :returns (new-ans vl-immdeps-p)
  :long "<p>Some cases:</p>
<ul>
<li>If @('name') refers to a top-level item, we add a dependency onto it.</li>
<li>If it refers to an item from some other package, we instead add a dependency onto
that package.</li>
<li>If it refers to a local item, we don't add any dependency onto it.</li>
<li>If it isn't declared, we add a warning instead of a dependency.</li>
</ul>"
  (b* ((name (string-fix name))
       (ans  (vl-immdeps-fix ans))

       ((mv item item-ss pkg)
        (vl-scopestack-find-item/context name ss))
       ((unless item)
        (vl-immdeps-add-error ans
                              :type :vl-undeclared-identifier
                              :msg "~a0: missing declaration for ~a1."
                              :args (list ctx name)
                              :fatalp t))

       ((when pkg)
        ;; This item was imported from the package named PKG.  We don't care
        ;; what kind of item it is or the particular scope it is from -- that
        ;; scope just says where the import statement lives.  What we care
        ;; about is what package it is defined in, so we can add a dependency
        ;; on that package.
        (vl-immdeps-add-pkgdep pkg ans))

       ;; Otherwise, the item is not imported from a package.  ITEM-SS is the
       ;; scope where the item was found.  There are a few possibilities.
       ((when (vl-scopestack-toplevel-p item-ss))
        ;; The item is found in the very top-level scope, not within any kind
        ;; of containing module/etc.  For instance this might be a reference
        ;; to a top-level function, parameter, etc.  We want to go ahead and
        ;; add a dependency onto this top-level thing.
        (vl-immdeps-add-raw-dependency name ans)))

    ;; Otherwise, the item is (1) not from any other package and (2) not from
    ;; the top-level scope.  The only way for it to be visible in our current
    ;; scope is for it to be a local declaration, or a declaration in some
    ;; superior block such as:
    ;;
    ;;    module m {
    ;;      function foo {
    ;;         item
    ;;         block b {
    ;;          ... reference to item ...
    ;;         }
    ;;      }
    ;;    }
    ;;
    ;; In any of these cases, it is not a top-level declaration.  Moreover,
    ;; since it's not a hierarchical name, it can't be from any other module or
    ;; interface or anything like that.
    ans))


(defsection immdeps-main
  :parents (immdeps)
  :short "Main functions for gathering immediate dependencies from parse tree
elements.")

(local (xdoc::set-default-parents immdeps-main))

(local (defthm hidname-equals-$root
         (implies (vl-hidname-p x)
                  (equal (equal x :vl-$root)
                         (not (stringp x))))
         :hints(("Goal" :in-theory (enable vl-hidname-p)))))



(fty::defvisitor-template immdeps ((x :object)
                                   (ans vl-immdeps-p)
                                   &key
                                   ((ss vl-scopestack-p) 'ss)
                                   ((ctx acl2::any-p) 'ctx))
  :returns (ans1 (:acc ans :fix (vl-immdeps-fix ans)) vl-immdeps-p)
  :field-fns ((atts :skip))
  :fnname-template <type>-immdeps)

; Added by Matt K. 2/20/2016, pending possible mod by Sol to defvisitor.
(set-bogus-measure-ok t)

;; Not dealing with anything that might add a scope yet.
(fty::defvisitor vl-expr-immdeps
  :template immdeps
  :type expressions-and-datatypes
  :type-fns ((vl-scopeexpr vl-scopeexpr-immdeps-fn)
             (vl-expr vl-expr-immdeps-fn))
  :omit-types (vl-scopeexpr)
  :renames ((vl-expr vl-expr-immdeps-aux))
  :measure (two-nats-measure :count 0)

  (define vl-expr-immdeps ((x vl-expr-p)
                                (ans vl-immdeps-p)
                                &key
                                ((ss vl-scopestack-p) 'ss)
                                ((ctx acl2::any-p) 'ctx))
    :returns (ans1 vl-immdeps-p)
    :measure (two-nats-measure (vl-expr-count x) 1)
    (vl-expr-case x
      :vl-call (if x.systemp
                   ;; Skip the function name.
                   (b* ((ans (vl-maybe-datatype-immdeps x.typearg ans))
                        (ans (vl-maybe-exprlist-immdeps x.plainargs ans)))
                     (vl-call-namedargs-immdeps x.namedargs ans))
                 (vl-expr-immdeps-aux x ans))
      :otherwise
      (vl-expr-immdeps-aux x ans)))

  (define vl-scopeexpr-immdeps ((x vl-scopeexpr-p)
                                (ans vl-immdeps-p)
                                &key
                                ((ss vl-scopestack-p) 'ss)
                                ((ctx acl2::any-p) 'ctx))
    :returns (ans1 vl-immdeps-p)
    :measure (two-nats-measure (vl-scopeexpr-count x) 1)
    (vl-scopeexpr-case x
      :end (b* ((ans (vl-hidexpr-immdeps x.hid ans))) ;; Analyzes the indices within the hid
             (vl-hidexpr-case x.hid
               ;; Bare name, no dots, no package -- depend on it
               :end (vl-immdeps-add-item x.hid.name ans)
               ;; Dotted name, no package -- depend on the outermost scope.
               :dot (b* ((name (vl-hidindex->name x.hid.first)))
                      (if (eq name :vl-$root)
                          (vl-immdeps-fix ans)
                        (vl-immdeps-add-item name ans)))))
    :colon
    ;; Pkg::hid - depend on the package, and scan the indices of the hid.
    ;; Don't allow nested colon operators.
    (b* ((ans (if (stringp x.first)
                  (vl-immdeps-add-pkgdep x.first ans)
                ;; BOZO think about other scopes.
                ;; local:: is just something to do with randomize, I don't think we care yet.
                ;; $unit:: is sort of very ambiguous, we might want to treat it as top-level
                ;; or we might want to just not support it.
                (vl-immdeps-fix ans))))
      (vl-scopeexpr-case x.rest
        :end (vl-hidexpr-immdeps x.rest.hid ans) ;; analyze the indices inside the hid
        :colon (vl-immdeps-add-error
                ans :type :vl-bad-scopeexpr
                :msg "Nested colon operators in scopeexprs are not supported: ~a0"
                :args (list (vl-scopeexpr-fix x))
                :fatalp t))))))

(fty::defvisitors vl-misc-immdeps
  :template immdeps
  :types (vl-maybe-gatedelay
          vl-arguments
          vl-paramtype
          vl-maybe-delayoreventcontrol
          vl-exprdist
          vl-propexpr
          vl-propspec
          vl-maybe-rhs))

(fty::defvisitor vl-stmt-immdeps
  :type statements
  :template immdeps
  :type-fns ((vl-stmt vl-stmt-immdeps-fn))
  :renames ((vl-stmt vl-stmt-immdeps-aux))
  :measure (two-nats-measure :count 0)
  (define vl-stmt-immdeps ((x vl-stmt-p)
                           (ans vl-immdeps-p)
                           &key
                           ((ss vl-scopestack-p) 'ss)
                           ((ctx acl2::any-p) 'ctx))
    :returns (ans1 vl-immdeps-p)
    :measure (two-nats-measure (vl-stmt-count x) 1)
    (b* ((ss (vl-stmt-case x
               :vl-blockstmt (vl-scopestack-push (vl-blockstmt->blockscope x) ss)
               :otherwise ss)))
      (vl-stmt-immdeps-aux x ans))))


;; (fty::defvisitor-template immdeps-no-ctx ((x :object)
;;                                           (ans vl-immdeps-p)
;;                                           &key
;;                                           ((ss vl-scopestack-p) 'ss))
;;   :wrapper (b* ((?ctx x)) :body)





(defmacro def-vl-immdeps (type &key body verbosep guard-debug prepwork name-override (ctxp 't))
  (let* ((mksym-package-symbol 'vl::foo)
         (rec            (mksym type '-p))
         (fix            (mksym type '-fix))
         (collect        (or name-override (mksym type '-immdeps))))
    `(define ,collect ((x   ,rec)
                       (ans vl-immdeps-p)
                       &key
                       ((ss       vl-scopestack-p)  'ss)
                       ,@(and ctxp '(((ctx acl2::any-p) 'ctx))))
       :returns (new-ans vl-immdeps-p)
       :verbosep ,verbosep
       :guard-debug ,guard-debug
       :prepwork ,prepwork
       (b* ((x   (,fix x))
            (ans (vl-immdeps-fix ans))
            (ss  (vl-scopestack-fix ss)))
         ,body))))

(defmacro def-vl-immdeps-list (type element &key name-override element-name-override guard-debug verbosep (ctxp 't))
  (let* ((mksym-package-symbol 'vl::foo)
         (list-rec             (mksym type '-p))
         (list-collect         (or name-override (mksym type '-immdeps)))
         (element-collect      (or element-name-override (mksym element '-immdeps))))
    `(define ,list-collect ((x   ,list-rec)
                            (ans vl-immdeps-p)
                            &key
                            ((ss       vl-scopestack-p)  'ss)
                            ,@(and ctxp '(((ctx acl2::any-p) 'ctx))))
       :returns (new-ans vl-immdeps-p)
       :guard-debug ,guard-debug
       :verbosep ,verbosep
       (b* (((when (atom x))
             (vl-immdeps-fix ans))
            (ans (,element-collect (car x) ans)))
         (,list-collect (cdr x) ans)))))


(def-vl-immdeps vl-interfaceport
  :ctxp nil
  :body
  (b* (((vl-interfaceport x))
       (ctx x)
       (ans (vl-dimensionlist-immdeps x.udims ans))
       (ans (vl-immdeps-add-definition x.ifname ans)))
    ans))

(def-vl-immdeps-list vl-interfaceportlist vl-interfaceport :ctxp nil)



(def-vl-immdeps vl-regularport
  :ctxp nil
  :body
  (b* (((vl-regularport x))
       (ctx x))
    (vl-maybe-expr-immdeps x.expr ans)))

(def-vl-immdeps-list vl-regularportlist vl-regularport :ctxp nil)



(def-vl-immdeps vl-port
  :ctxp nil
  :body
  (if (eq (tag x) :vl-interfaceport)
      (vl-interfaceport-immdeps x ans)
    (vl-regularport-immdeps x ans)))

(def-vl-immdeps-list vl-portlist vl-port :ctxp nil)



(def-vl-immdeps vl-portdecl
  :ctxp nil
  :body
  (b* (((vl-portdecl x))
       (ctx x))
    (vl-datatype-immdeps x.type ans)))

(def-vl-immdeps-list vl-portdecllist vl-portdecl :ctxp nil)


;; (def-vl-immdeps vl-gatedelay
;;   :body
;;   (b* (((vl-gatedelay x))
;;        (ans (vl-expr-immdeps x.rise ans))
;;        (ans (vl-expr-immdeps x.fall ans))
;;        (ans (vl-maybe-expr-immdeps x.high ans)))
;;     ans))

;; (def-vl-immdeps vl-maybe-gatedelay
;;   :body
;;   (if x
;;       (vl-gatedelay-immdeps x ans)
;;     ans))

(def-vl-immdeps vl-assign
  :ctxp nil
  :body
  (b* (((vl-assign x))
       (ctx x)
       (ans (vl-expr-immdeps x.lvalue ans))
       (ans (vl-expr-immdeps x.expr ans))
       (ans (vl-maybe-gatedelay-immdeps x.delay ans)))
    ans))

(def-vl-immdeps-list vl-assignlist vl-assign :ctxp nil)

(def-vl-immdeps vl-alias
  :ctxp nil
  :body
  (b* (((vl-alias x))
       (ctx x)
       (ans (vl-expr-immdeps x.lhs ans))
       (ans (vl-expr-immdeps x.rhs ans)))
    ans))

(def-vl-immdeps-list vl-aliaslist vl-alias :ctxp nil)

(def-vl-immdeps vl-vardecl
  :ctxp nil
  :body
  (b* (((vl-vardecl x))
       (ctx x)
       (ans (vl-datatype-immdeps x.type ans))
       (ans (vl-maybe-rhs-immdeps x.initval ans))
       (ans (vl-maybe-gatedelay-immdeps x.delay ans)))
    ans))

(def-vl-immdeps-list vl-vardecllist vl-vardecl :ctxp nil)



(def-vl-immdeps vl-import
  ;; We just add a dependency onto the package being imported from.
  :ctxp nil
  :body
  (b* (((vl-import x))
       (ctx x))
    (vl-immdeps-add-pkgdep x.pkg ans)))

(def-vl-immdeps-list vl-importlist vl-import :ctxp nil)


;; (def-vl-immdeps vl-plainarg
;;   :body
;;   (b* (((vl-plainarg x)))
;;     (vl-maybe-expr-immdeps x.expr ans)))

;; (def-vl-immdeps-list vl-plainarglist vl-plainarg)

;; (def-vl-immdeps vl-namedarg
;;   :body
;;   (b* (((vl-namedarg x)))
;;     (vl-maybe-expr-immdeps x.expr ans)))

;; (def-vl-immdeps-list vl-namedarglist vl-namedarg)

;; (def-vl-immdeps vl-arguments
;;   :body
;;   (vl-arguments-case x
;;     (:vl-arguments-plain (vl-plainarglist-immdeps x.args ans))
;;     (:vl-arguments-named (vl-namedarglist-immdeps x.args ans))))

;; sswords NOTE: this use of vl-argumentlist is no longer correct -- changed meaning 3/21/2017
;; (def-vl-immdeps-list vl-argumentlist vl-arguments)

;; (def-vl-immdeps vl-paramvalue
;;   :body
;;   (vl-paramvalue-case x
;;     :expr (vl-expr-immdeps x.expr ans)
;;     :type (vl-datatype-immdeps x.type ans)))

;; (def-vl-immdeps-list vl-paramvaluelist vl-paramvalue)

;; (def-vl-immdeps vl-maybe-paramvalue
;;   :body
;;   (if x
;;       (vl-paramvalue-immdeps x ans)
;;     ans))


;; (def-vl-immdeps vl-namedparamvalue
;;   :body
;;   (b* (((vl-namedparamvalue x)))
;;     (vl-maybe-paramvalue-immdeps x.value ans)))

;; (def-vl-immdeps-list vl-namedparamvaluelist vl-namedparamvalue)

;; (def-vl-immdeps vl-paramargs
;;   :body
;;   (vl-paramargs-case x
;;     (:vl-paramargs-plain (vl-paramvaluelist-immdeps x.args ans))
;;     (:vl-paramargs-named (vl-namedparamvaluelist-immdeps x.args ans))))

(def-vl-immdeps vl-modinst
  :ctxp nil
  :body
  (b* (((vl-modinst x))
       (ctx x)
       (ans (vl-immdeps-add-definition x.modname ans))
       (ans (vl-maybe-range-immdeps x.range ans))
       (ans (vl-paramargs-immdeps x.paramargs ans))
       (ans (vl-arguments-immdeps x.portargs ans))
       (ans (vl-maybe-gatedelay-immdeps x.delay ans)))
    ans))

(def-vl-immdeps-list vl-modinstlist vl-modinst :ctxp nil)

(def-vl-immdeps vl-gateinst
  :ctxp nil
  :body
  (b* (((vl-gateinst x))
       (ctx x)
       (ans (vl-maybe-range-immdeps x.range ans))
       (ans (vl-plainarglist-immdeps x.args ans))
       (ans (vl-maybe-gatedelay-immdeps x.delay ans)))
    ans))

(def-vl-immdeps-list vl-gateinstlist vl-gateinst :ctxp nil)

(def-vl-immdeps vl-paramdecl
  :ctxp nil
  :body
  (b* (((vl-paramdecl x))
       (ctx x))
    (vl-paramtype-immdeps x.type ans)))

(def-vl-immdeps-list vl-paramdecllist vl-paramdecl :ctxp nil)

;; (def-vl-immdeps vl-evatom
;;   :body
;;   (b* (((vl-evatom x)))
;;     (vl-expr-immdeps x.expr ans)))

;; (def-vl-immdeps-list vl-evatomlist vl-evatom)

;; (def-vl-immdeps vl-eventcontrol
;;   :body
;;   (b* (((vl-eventcontrol x)))
;;     (vl-evatomlist-immdeps x.atoms ans)))

;; (def-vl-immdeps vl-delaycontrol
;;   :body
;;   (b* (((vl-delaycontrol x)))
;;     (vl-expr-immdeps x.value ans)))

;; (def-vl-immdeps vl-repeateventcontrol
;;   :body
;;   (b* (((vl-repeateventcontrol x))
;;        (ans (vl-expr-immdeps x.expr ans))
;;        (ans (vl-eventcontrol-immdeps x.ctrl ans)))
;;     ans))

;; (def-vl-immdeps vl-delayoreventcontrol
;;   :body
;;   (case (tag x)
;;     (:vl-delaycontrol (vl-delaycontrol-immdeps x ans))
;;     (:vl-eventcontrol (vl-eventcontrol-immdeps x ans))
;;     (otherwise        (vl-repeateventcontrol-immdeps x ans))))

;; (def-vl-immdeps vl-maybe-delayoreventcontrol
;;   :body
;;   (if x
;;       (vl-delayoreventcontrol-immdeps x ans)
;;     ans))


;; (defines vl-stmt-immdeps
;;   :flag-local nil
;;   :verify-guards nil
;;   :returns-hints ((and stable-under-simplificationp
;;                        '(:expand ((vl-stmt-immdeps x ans)
;;                                   (vl-stmtlist-immdeps x ans)
;;                                   (vl-caselist-immdeps x ans)))))


;;   (define vl-stmt-immdeps ((x   vl-stmt-p)
;;                            (ans vl-immdeps-p)
;;                            &key
;;                            ((ss vl-scopestack-p) 'ss))
;;     :returns (new-ans vl-immdeps-p)
;;     :measure (vl-stmt-count x)
;;     :flag :stmt
;;     (b* ((x   (vl-stmt-fix x))
;;          (ans (vl-immdeps-fix ans))
;;          (ctx x))
;;       (vl-stmt-case x
;;         (:vl-nullstmt
;;          ans)
;;         (:vl-assignstmt
;;          (b* ((ans (vl-expr-immdeps x.lvalue ans))
;;               (ans (vl-expr-immdeps x.expr ans))
;;               (ans (vl-maybe-delayoreventcontrol-immdeps x.ctrl ans)))
;;            ans))
;;         (:vl-deassignstmt
;;          (vl-expr-immdeps x.lvalue ans))
;;         (:vl-enablestmt
;;          (b* ((ans (vl-expr-immdeps x.id ans))
;;               (ans (vl-exprlist-immdeps x.args ans)))
;;            ans))
;;         (:vl-disablestmt
;;          (vl-expr-immdeps x.id ans))
;;         (:vl-returnstmt
;;          (if x.val (vl-expr-immdeps x.val ans) ans))
;;         (:vl-eventtriggerstmt
;;          (vl-expr-immdeps x.id ans))
;;         (:vl-casestmt
;;          (b* ((ans (vl-expr-immdeps x.test ans))
;;               (ans (vl-caselist-immdeps x.caselist ans))
;;               (ans (vl-stmt-immdeps x.default ans)))
;;            ans))
;;         (:vl-ifstmt
;;          (b* ((ans (vl-expr-immdeps x.condition ans))
;;               (ans (vl-stmt-immdeps x.truebranch ans))
;;               (ans (vl-stmt-immdeps x.falsebranch ans)))
;;            ans))
;;         (:vl-foreverstmt
;;          (vl-stmt-immdeps x.body ans))
;;         (:vl-waitstmt
;;          (b* ((ans (vl-expr-immdeps x.condition ans))
;;               (ans (vl-stmt-immdeps x.body ans)))
;;            ans))
;;         (:vl-repeatstmt
;;          (b* ((ans (vl-expr-immdeps x.condition ans))
;;               (ans (vl-stmt-immdeps x.body ans)))
;;            ans))
;;         (:vl-whilestmt
;;          (b* ((ans (vl-expr-immdeps x.condition ans))
;;               (ans (vl-stmt-immdeps x.body ans)))
;;            ans))
;;         (:vl-forstmt
;;          (b* ((ans (vl-vardecllist-immdeps x.initdecls ans))
;;               (ans (vl-stmtlist-immdeps x.initassigns ans))
;;               (ans (vl-expr-immdeps x.test ans))
;;               (ans (vl-stmtlist-immdeps x.stepforms ans))
;;               (ans (vl-stmt-immdeps x.body ans)))
;;            ans))
;;         (:vl-blockstmt
;;          (b* ((ss (vl-scopestack-push (vl-blockstmt->blockscope x) ss))
;;               (ans (vl-importlist-immdeps x.imports ans))
;;               (ans (vl-paramdecllist-immdeps x.paramdecls ans))
;;               (ans (vl-vardecllist-immdeps x.vardecls ans))
;;               (ans (vl-stmtlist-immdeps x.stmts ans)))
;;            ans))
;;         (:vl-timingstmt
;;          (b* ((ans (vl-delayoreventcontrol-immdeps x.ctrl ans))
;;               (ans (vl-stmt-immdeps x.body ans)))
;;            ans)))))

;;   (define vl-stmtlist-immdeps ((x   vl-stmtlist-p)
;;                                (ans vl-immdeps-p)
;;                                &key
;;                                ((ss vl-scopestack-p) 'ss))
;;     :returns (new-ans vl-immdeps-p)
;;     :measure (vl-stmtlist-count x)
;;     :flag :stmtlist
;;     (b* ((x   (vl-stmtlist-fix x))
;;          (ans (vl-immdeps-fix ans))
;;          ((when (atom x))
;;           ans)
;;          (ans (vl-stmt-immdeps (car x) ans)))
;;       (vl-stmtlist-immdeps (cdr x) ans)))

;;   (define vl-caselist-immdeps ((x   vl-caselist-p)
;;                                (ans vl-immdeps-p)
;;                                &key
;;                                ((ss       vl-scopestack-p)  'ss)
;;                                ((ctx      acl2::any-p)      'ctx))
;;     :returns (new-ans vl-immdeps-p)
;;     :flag :caselist
;;     :measure (vl-caselist-count x)
;;     (b* ((x   (vl-caselist-fix x))
;;          (ans (vl-immdeps-fix ans))
;;          ((when (atom x))
;;           ans)
;;          ((cons exprs1 body1) (car x))
;;          (ans (vl-exprlist-immdeps exprs1 ans))
;;          (ans (vl-stmt-immdeps body1 ans)))
;;       (vl-caselist-immdeps (cdr x) ans)))

;;   ///
;;   (local (set-default-hints
;;           '((and stable-under-simplificationp
;;                  '(:expand ((:free (ss ans) (vl-stmt-immdeps x ans))
;;                             (:free (ss ans) (vl-stmt-immdeps (vl-stmt-fix x) ans))
;;                             (:free (ss ans) (vl-stmtlist-immdeps x ans))
;;                             (:free (ss ans) (vl-stmtlist-immdeps (vl-stmtlist-fix x) ans))
;;                             (:free (ss ans ctx) (vl-caselist-immdeps x ans))
;;                             (:free (ss ans ctx) (vl-caselist-immdeps (vl-caselist-fix x) ans))))))))

;;   (deffixequiv-mutual vl-stmt-immdeps)
;;   (verify-guards vl-stmt-immdeps-fn))


(def-vl-immdeps vl-always
  :ctxp nil
  :body
  (b* (((vl-always x)))
    (vl-stmt-immdeps x.stmt ans :ctx x)))

(def-vl-immdeps-list vl-alwayslist vl-always :ctxp nil)

(def-vl-immdeps vl-initial
  :ctxp nil
  :body
  (b* (((vl-initial x)))
    (vl-stmt-immdeps x.stmt ans :ctx x)))

(def-vl-immdeps-list vl-initiallist vl-initial :ctxp nil)

(def-vl-immdeps vl-final
  :ctxp nil
  :body
  (b* (((vl-final x)))
    (vl-stmt-immdeps x.stmt ans :ctx x)))

(def-vl-immdeps-list vl-finallist vl-final :ctxp nil)



(def-vl-immdeps vl-fundecl
  :ctxp nil
  :body
  (b* (((vl-fundecl x))
       (ctx x)
       (ans (vl-datatype-immdeps x.rettype ans))
       (ans (vl-portdecllist-immdeps x.portdecls ans))
       (ss  (vl-scopestack-push (vl-fundecl->blockscope x) ss))
       (ans (vl-importlist-immdeps x.imports ans))
       (ans (vl-paramdecllist-immdeps x.paramdecls ans))
       (ans (vl-vardecllist-immdeps x.vardecls ans)))
    (vl-stmt-immdeps x.body ans :ctx x)))

(def-vl-immdeps-list vl-fundecllist vl-fundecl :ctxp nil)


(def-vl-immdeps vl-taskdecl
  :ctxp nil
  :body
  (b* (((vl-taskdecl x))
       (ss  (vl-scopestack-push (vl-taskdecl->blockscope x) ss))
       (ans (vl-portdecllist-immdeps x.portdecls ans))
       (ans (vl-importlist-immdeps x.imports ans))
       (ans (vl-paramdecllist-immdeps x.paramdecls ans))
       (ans (vl-vardecllist-immdeps x.vardecls ans)))
    (vl-stmt-immdeps x.body ans :ctx x)))

(def-vl-immdeps-list vl-taskdecllist vl-taskdecl :ctxp nil)


(def-vl-immdeps vl-modport-port
  :ctxp nil
  :body
  (b* (((vl-modport-port x))
       (ctx x))
    (vl-maybe-expr-immdeps x.expr ans)))

(def-vl-immdeps-list vl-modport-portlist vl-modport-port :ctxp nil)

(def-vl-immdeps vl-modport
  :ctxp nil
  :body
  (b* (((vl-modport x)))
    (vl-modport-portlist-immdeps x.ports ans)))

(def-vl-immdeps-list vl-modportlist vl-modport :ctxp nil)

(def-vl-immdeps vl-typedef
  :ctxp nil
  :body
  (b* (((vl-typedef x))
       (ctx x))
    (vl-datatype-immdeps x.type ans)))

(def-vl-immdeps-list vl-typedeflist vl-typedef :ctxp nil)


(def-vl-immdeps vl-assertion
  :name-override vl-assertion-top-immdeps
  :ctxp nil
  :body (vl-assertion-immdeps x ans :ctx ans))

(def-vl-immdeps-list vl-assertionlist vl-assertion
  :element-name-override vl-assertion-top-immdeps
  :ctxp nil)

(def-vl-immdeps vl-cassertion
  :name-override vl-cassertion-top-immdeps
  :ctxp nil
  :body (vl-cassertion-immdeps x ans :ctx ans))

(def-vl-immdeps-list vl-cassertionlist vl-cassertion
  :element-name-override vl-cassertion-top-immdeps
  :ctxp nil)

(def-vl-immdeps vl-propport
  :ctxp t
  :body
  (b* (((vl-propport x))
       (ans (vl-datatype-immdeps x.type ans))
       (ans (vl-propactual-immdeps x.arg ans)))
    ans))

(def-vl-immdeps-list vl-propportlist vl-propport :ctxp t)

(def-vl-immdeps vl-property
  :ctxp nil
  :body
  (b* (((vl-property x))
       (ctx x)
       (ans (vl-propportlist-immdeps x.ports ans))
       (ans (vl-vardecllist-immdeps x.decls ans))
       (ans (vl-propspec-immdeps x.spec ans)))
    ans))

(def-vl-immdeps-list vl-propertylist vl-property :ctxp nil)

(def-vl-immdeps vl-sequence
  :ctxp nil
  :body
  (b* (((vl-sequence x))
       (ctx x)
       (ans (vl-propportlist-immdeps x.ports ans))
       (ans (vl-vardecllist-immdeps x.decls ans))
       (ans (vl-propexpr-immdeps x.expr ans)))
    ans))

(def-vl-immdeps-list vl-sequencelist vl-sequence :ctxp nil)


(def-vl-immdeps vl-modelement
  :prepwork ((local (in-theory (enable vl-modelement-p
                                       tag-reasoning))))
  :ctxp nil
  :body
  (case (tag x)
    (:vl-interfaceport (vl-interfaceport-immdeps x ans))
    (:vl-regularport   (vl-regularport-immdeps x ans))
    (:vl-portdecl      (vl-portdecl-immdeps x ans))
    (:vl-assign        (vl-assign-immdeps x ans))
    (:vl-alias         (vl-alias-immdeps x ans))
    (:vl-vardecl       (vl-vardecl-immdeps x ans))
    (:vl-paramdecl     (vl-paramdecl-immdeps x ans))
    (:vl-fundecl       (vl-fundecl-immdeps x ans))
    (:vl-taskdecl      (vl-taskdecl-immdeps x ans))
    (:vl-modinst       (vl-modinst-immdeps x ans))
    (:vl-gateinst      (vl-gateinst-immdeps x ans))
    (:vl-always        (vl-always-immdeps x ans))
    (:vl-initial       (vl-initial-immdeps x ans))
    (:vl-final         (vl-final-immdeps x ans))
    (:vl-typedef       (vl-typedef-immdeps x ans))
    (:vl-import        (vl-import-immdeps x ans))
    (:vl-fwdtypedef    ans) ;; no dependencies on a forward typedef
    (:vl-genvar        ans) ;; no dependencies
    (:vl-property      (vl-property-immdeps x ans))
    (:vl-sequence      (vl-sequence-immdeps x ans))
    (:vl-clkdecl       ans) ;; BOZO figure out what to do here -- also update module-immdeps!!
    (:vl-gclkdecl      ans) ;; BOZO figure out what to do here -- also update module-immdeps!!
    (:vl-defaultdisable ans) ;; BOZO figure out what to do here -- also update module-immdeps!!
    (:vl-dpiimport     ans) ;; I don't think we care?
    (:vl-dpiexport     ans) ;; I don't think we care?
    (:vl-bind          ans) ;; BOZO figure out what to do here -- also update module/interface-immdeps!!
    (:vl-class         ans) ;; BOZO figure out what to do here -- also update module/package/interface-immdeps!!
    (:vl-covergroup    ans) ;; BOZO figure out what to do here -- also update module/package/interface-immdeps!!
    (:vl-elabtask      ans) ;; BOZO figure out what to do here -- also update module/package/interface-immdeps!!
    (:vl-assertion     (vl-assertion-top-immdeps x ans))
    (:vl-cassertion    (vl-cassertion-top-immdeps x ans))
    (otherwise         (vl-modport-immdeps x ans))))


(defines vl-genelement-immdeps
  :flag-local nil
  :verify-guards nil

  :returns-hints(("Goal"
                  :expand ((vl-genelement-immdeps x ans)
                           (vl-genelementlist-immdeps x ans)
                           (vl-gencaselist-immdeps x ans)
                           (vl-genblocklist-immdeps x ans)
                           (vl-genblock-immdeps x ans))))

  (define vl-genblock-immdeps ((x   vl-genblock-p)
                               (ans vl-immdeps-p)
                               &key
                               ((ss vl-scopestack-p) 'ss))
    :returns (new-ans vl-immdeps-p)
    :measure (vl-genblock-count x)
    :flag :genblock
    (b* (((vl-genblock x) x)
         (scope (vl-sort-genelements x.elems
                                     :scopetype :vl-genblock
                                     :id x.name))
         (ss    (vl-scopestack-push scope ss))
         (ans   (vl-genelementlist-immdeps x.elems ans)))
      ans))

  (define vl-genelement-immdeps ((x   vl-genelement-p)
                                 (ans vl-immdeps-p)
                                 &key
                                 ((ss vl-scopestack-p) 'ss))
    :returns (new-ans vl-immdeps-p)
    :measure (vl-genelement-count x)
    :flag :genelement
    ;; BOZO:
    ;;  1. not sure about which of these have scopes.
    ;;  2. need to add the genvar separately?
    (b* ((x   (vl-genelement-fix x))
         (ctx x)
         (ans (vl-immdeps-fix ans)))
      (vl-genelement-case x
        (:vl-genbase  (vl-modelement-immdeps x.item ans))
        (:vl-genbegin (vl-genblock-immdeps x.block ans))
        (:vl-genif    (b* ((ans (vl-expr-immdeps x.test ans))
                           (ans (vl-genblock-immdeps x.then ans))
                           (ans (vl-genblock-immdeps x.else ans)))
                        ans))
        (:vl-gencase  (b* ((ans (vl-expr-immdeps x.test ans))
                           (ans (vl-gencaselist-immdeps x.cases ans))
                           (ans (vl-genblock-immdeps x.default ans)))
                        ans))
        (:vl-genloop
         ;; BOZO this seems like an awkward place to do this scope stuff.
         (b* (;; Make a fake param for the loop counter, the type and such are irrelevant
              (fake-param (make-vl-paramdecl :name x.var
                                             :type (make-vl-implicitvalueparam)
                                             :loc *vl-fakeloc*))
              (fake-scope (vl-sort-genelements (list (make-vl-genbase :item fake-param))))
              (ans        (vl-expr-immdeps x.initval ans))
              (ss         (vl-scopestack-push fake-scope ss))
              (ans        (vl-expr-immdeps x.continue ans))
              (ans        (vl-expr-immdeps x.nextval ans))
              (ans        (vl-genblock-immdeps x.body ans)))
           ans))
        (:vl-genarray
         (b* ((ans (vl-genblocklist-immdeps x.blocks ans)))
           ans)))))

  (define vl-genelementlist-immdeps ((x   vl-genelementlist-p)
                                     (ans vl-immdeps-p)
                                     &key
                                     ((ss vl-scopestack-p) 'ss))
    :returns (new-ans vl-immdeps-p)
    :measure (vl-genelementlist-count x)
    :flag :genelementlist
    (b* ((x   (vl-genelementlist-fix x))
         (ans (vl-immdeps-fix ans))
         ((when (atom x))
          ans)
         (ans (vl-genelement-immdeps (car x) ans)))
      (vl-genelementlist-immdeps (cdr x) ans)))

  (define vl-gencaselist-immdeps ((x   vl-gencaselist-p)
                                  (ans vl-immdeps-p)
                                  &key
                                  ((ss vl-scopestack-p) 'ss)
                                  ((ctx acl2::any-p) 'ctx))
    :returns (new-ans vl-immdeps-p)
    :measure (vl-gencaselist-count x)
    :flag :gencaselist
    (b* ((x   (vl-gencaselist-fix x))
         (ans (vl-immdeps-fix ans))
         ((when (atom x))
          ans)
         ((cons exprs block) (car x))
         (ans (vl-exprlist-immdeps exprs ans))
         (ans (vl-genblock-immdeps block ans)))
      (vl-gencaselist-immdeps (cdr x) ans)))

  (define vl-genblocklist-immdeps ((x   vl-genblocklist-p)
                                        (ans vl-immdeps-p)
                                        &key
                                        ((ss vl-scopestack-p) 'ss))
    :returns (new-ans vl-immdeps-p)
    :measure (vl-genblocklist-count x)
    :flag :genblocklist
    (b* ((x   (vl-genblocklist-fix x))
         (ans (vl-immdeps-fix ans))
         ((when (atom x))
          ans)
         (ans (vl-genblock-immdeps (car x) ans)))
      (vl-genblocklist-immdeps (cdr x) ans)))

  ///
  (verify-guards vl-genelement-immdeps-fn)
  (deffixequiv-mutual vl-genelement-immdeps))



(defsection immdeps-top
  :parents (immdeps)
  :short "Functions for gathering immediate dependencies from top-level design
elements.")

(local (xdoc::set-default-parents immdeps-top))

(fty::defalist vl-depgraph
  :parents (immdeps)
  :short "A basic dependency graph.  Binds each node to the list of nodes it
depends on.  The format is compatible with @(see depgraph::toposort)."
  :key-type stringp
  :val-type string-listp
  :keyp-of-nil nil
  :valp-of-nil t)

(defthm vl-depgraph-p-of-mergesort-alist-values
  (implies (vl-depgraph-p x)
           (vl-depgraph-p (depgraph::mergesort-alist-values x)))
  :hints(("Goal" :induct (len x))))

(defprod vl-immdepgraph
  :parents (immdeps)
  :tag :vl-immdepgraph
  :layout :tree
  :short "Immediate dependency graph."
  ((all-okp    booleanp
               :rule-classes :type-prescription
               :default t
               "Were we able to successfully resolve every identifier we
                encountered?  Even if this is @('nil'), the resulting @('deps')
                may be very nearly accurate.")

   (deps       vl-depgraph
               "The dependency graph we've collected.  Only includes immediate
                dependencies.  Includes a node for every top-level element.")

   (reportcard vl-reportcard-p
               "Any warnings accumulated during the process of collecting these
                dependencies.")))

(define vl-immdepgraph-merge
  :short "Merge a @(see vl-immdeps) into a @(see vl-immdepgraph)."
  ((name  stringp          "Name of the new node we're adding.")
   (deps  vl-immdeps-p     "Dependencies that you've collected for the new node.")
   (graph vl-immdepgraph-p "Graph we're extending."))
  :returns
  (new-graph vl-immdepgraph-p "Extended with the new dependencies.")
  :long "<p>Note that we don't check for any duplicate names here; we can do a
         better check for uniqueness, later.</p>"
  (b* ((name (string-fix name))
       ((vl-immdeps deps))
       ((vl-immdepgraph graph))
       (new-okp        (and deps.all-okp graph.all-okp))
       (new-reportcard (vl-extend-reportcard-list name deps.warnings graph.reportcard))
       ;; We take care to fix up the dependencies here to remove any
       ;; self-dependencies.
       ;;
       ;; We think it's generally fine to have a self-dependency.  For
       ;; instance, it is certainly okay for a module to recursively
       ;; instantiate itself, via generate statements, at different sizes.
       ;; NCVerilog and VCS also permit, e.g.,
       ;;
       ;;  package p ;
       ;;     parameter size = 4;
       ;;     wire [p::size-1:0] w;
       ;;  endpackage
       ;;
       ;; So for the purposes of dependency-sorting, we're happy to ignore self
       ;; edges.
       (new-deps     (cons (cons name (remove-equal name deps.deps)) graph.deps)))
    (make-vl-immdepgraph :all-okp    new-okp
                         :deps       new-deps
                         :reportcard new-reportcard)))

(defmacro def-vl-immdeps*-list (type element)
  (let* ((mksym-package-symbol 'vl::foo)
         (list-rec             (mksym type '-p))
         (list-collect         (mksym type '-immdeps*))
         (element-collect      (mksym element '-immdeps*)))
    `(define ,list-collect ((x     ,list-rec)
                            (graph vl-immdepgraph-p)
                            &key
                            ((ss       vl-scopestack-p)  'ss))
       :returns (new-graph vl-immdepgraph-p)
       (b* (((when (atom x))
             (vl-immdepgraph-fix graph))
            (graph (,element-collect (car x) graph)))
         (,list-collect (cdr x) graph)))))

(define vl-module-immdeps* ((x     vl-module-p)
                            (graph vl-immdepgraph-p)
                            &key
                            ((ss vl-scopestack-p) 'ss))
  :returns (new-graph vl-immdepgraph-p)
  (b* (((vl-module x) (vl-module-fix x))
       (ss  (vl-scopestack-push x ss))
       (ans (make-vl-immdeps))
       (ans (vl-importlist-immdeps     x.imports    ans))
       (ans (vl-portlist-immdeps       x.ports      ans))
       (ans (vl-portdecllist-immdeps   x.portdecls  ans))
       (ans (vl-vardecllist-immdeps    x.vardecls   ans))
       (ans (vl-paramdecllist-immdeps  x.paramdecls ans))
       (ans (vl-fundecllist-immdeps    x.fundecls   ans))
       (ans (vl-taskdecllist-immdeps   x.taskdecls  ans))
       (ans (vl-assignlist-immdeps     x.assigns    ans))
       (ans (vl-aliaslist-immdeps      x.aliases    ans))
       (ans (vl-modinstlist-immdeps    x.modinsts   ans))
       (ans (vl-gateinstlist-immdeps   x.gateinsts  ans))
       (ans (vl-alwayslist-immdeps     x.alwayses   ans))
       (ans (vl-initiallist-immdeps    x.initials   ans))
       (ans (vl-finallist-immdeps      x.finals     ans))
       (ans (vl-typedeflist-immdeps    x.typedefs   ans))
       (ans (vl-propertylist-immdeps   x.properties ans))
       (ans (vl-sequencelist-immdeps   x.sequences  ans))
       ;; BOZO clkdecls, gclkdecls, defaultdisables
       (ans (vl-assertionlist-immdeps  x.assertions ans))
       (ans (vl-cassertionlist-immdeps x.cassertions ans))
       (ans (vl-genelementlist-immdeps x.generates  ans)))
    (vl-immdepgraph-merge (hons-copy x.name) ans graph)))

(def-vl-immdeps*-list vl-modulelist vl-module)

(define vl-udp-immdeps* ((x     vl-udp-p)
                         (graph vl-immdepgraph-p)
                         &key
                         ((ss vl-scopestack-p) 'ss))
  :returns (new-graph vl-immdepgraph-p)
  (declare (ignorable ss))
  (b* (((vl-udp x) (vl-udp-fix x))
       (ans (make-vl-immdeps))
       ;; I'm not bothering to extend ANS because UDPs should never have
       ;; any dependencies.
       )
    (vl-immdepgraph-merge (hons-copy x.name) ans graph)))

(def-vl-immdeps*-list vl-udplist vl-udp)



(define vl-config-immdeps* ((x     vl-config-p)
                            (graph vl-immdepgraph-p)
                            &key
                            ((ss vl-scopestack-p) 'ss))
  :returns (new-graph vl-immdepgraph-p)
  (declare (ignorable ss))
  (b* (((vl-config x) (vl-config-fix x))
       (ans (make-vl-immdeps))
       ;; BOZO do stuff here if we ever implement configs
       )
    (vl-immdepgraph-merge (hons-copy x.name) ans graph)))

(def-vl-immdeps*-list vl-configlist vl-config)

#||
(trace$ #!vl (vl-package-immdeps*-fn
              :entry (list 'vl-package-immdeps
                           (with-local-ps (vl-pp-package x))
                           graph
                           (vl-scopestack->hashkey ss)))) 

||#
(define vl-package-immdeps* ((x     vl-package-p)
                             (graph vl-immdepgraph-p)
                             &key
                             ((ss vl-scopestack-p) 'ss))
  :returns (new-graph vl-immdepgraph-p)
  (b* (((vl-package x) (vl-package-fix x))
       (ss  (vl-scopestack-push x ss))
       (ans (make-vl-immdeps))
       (ans (vl-fundecllist-immdeps   x.fundecls   ans))
       (ans (vl-taskdecllist-immdeps  x.taskdecls  ans))
       (ans (vl-typedeflist-immdeps   x.typedefs   ans))
       (ans (vl-paramdecllist-immdeps x.paramdecls ans))
       (ans (vl-vardecllist-immdeps   x.vardecls   ans)))
    (vl-immdepgraph-merge (hons-copy x.name) ans graph)))

(def-vl-immdeps*-list vl-packagelist vl-package)


(define vl-interface-immdeps* ((x vl-interface-p)
                               (graph vl-immdepgraph-p)
                               &key
                               ((ss vl-scopestack-p) 'ss))
  :returns (new-graph vl-immdepgraph-p)
  (b* (((vl-interface x) (vl-interface-fix x))
       (ss  (vl-scopestack-push x ss))
       (ans (make-vl-immdeps))
       (ans (vl-importlist-immdeps     x.imports    ans))
       (ans (vl-portlist-immdeps       x.ports      ans))
       (ans (vl-portdecllist-immdeps   x.portdecls  ans))
       (ans (vl-modportlist-immdeps    x.modports   ans))
       (ans (vl-vardecllist-immdeps    x.vardecls   ans))
       (ans (vl-paramdecllist-immdeps  x.paramdecls ans))
       (ans (vl-fundecllist-immdeps    x.fundecls   ans))
       (ans (vl-taskdecllist-immdeps   x.taskdecls  ans))
       (ans (vl-typedeflist-immdeps    x.typedefs   ans))
       (ans (vl-propertylist-immdeps   x.properties ans))
       (ans (vl-sequencelist-immdeps   x.sequences  ans))
       ;; BOZO clkdecls, gclkdecls, defaultdisables
       (ans (vl-modinstlist-immdeps    x.modinsts   ans))
       (ans (vl-assignlist-immdeps     x.assigns    ans))
       (ans (vl-aliaslist-immdeps      x.aliases    ans))
       (ans (vl-assertionlist-immdeps  x.assertions ans))
       (ans (vl-cassertionlist-immdeps x.cassertions ans))
       (ans (vl-alwayslist-immdeps     x.alwayses   ans))
       (ans (vl-initiallist-immdeps    x.initials   ans))
       (ans (vl-finallist-immdeps      x.finals     ans))
       (ans (vl-genelementlist-immdeps x.generates  ans)))
    (vl-immdepgraph-merge (hons-copy x.name) ans graph)))

(def-vl-immdeps*-list vl-interfacelist vl-interface)



(define vl-program-immdeps* ((x     vl-program-p)
                             (graph vl-immdepgraph-p)
                            &key
                            ((ss vl-scopestack-p) 'ss))
  :returns (new-graph vl-immdepgraph-p)
  (declare (ignorable ss))
  (b* (((vl-program x) (vl-program-fix x))
       (ans (make-vl-immdeps))
       ;; BOZO do stuff here if we ever implement programs
       )
    (vl-immdepgraph-merge (hons-copy x.name) ans graph)))

(def-vl-immdeps*-list vl-programlist vl-program)

(define vl-class-immdeps* ((x     vl-class-p)
                           (graph vl-immdepgraph-p)
                           &key
                           ((ss vl-scopestack-p) 'ss))
  :returns (new-graph vl-immdepgraph-p)
  (declare (ignorable ss))
  (b* (((vl-class x) (vl-class-fix x))
       (ans (make-vl-immdeps))
       ;; BOZO do stuff here if we ever implement classes
       )
    (vl-immdepgraph-merge (hons-copy x.name) ans graph)))

(def-vl-immdeps*-list vl-classlist vl-class)


;; Wrappers for top-level elements that we'd normally expect to see within some
;; kind of module or similar.

(defmacro def-vl-immdeps*-wrap (type)
  (let* ((mksym-package-symbol 'vl::foo)
         (foo->name            (mksym type '->name))
         (foop                 (mksym type '-p))
         (foo-immdeps          (mksym type '-immdeps))
         (foo-immdeps*         (mksym type '-immdeps*)))
    `(define ,foo-immdeps* ((x     ,foop)
                            (graph vl-immdepgraph-p)
                            &key
                            ((ss       vl-scopestack-p)  'ss))
       :inline t
       :returns (new-graph vl-immdepgraph-p)
       (b* ((ans (make-vl-immdeps))
            (ans (,foo-immdeps x ans)))
         (vl-immdepgraph-merge (hons-copy (,foo->name x)) ans graph)))))

(def-vl-immdeps*-wrap vl-vardecl)
(def-vl-immdeps*-list vl-vardecllist vl-vardecl)

(def-vl-immdeps*-wrap vl-taskdecl)
(def-vl-immdeps*-list vl-taskdecllist vl-taskdecl)

(def-vl-immdeps*-wrap vl-fundecl)
(def-vl-immdeps*-list vl-fundecllist vl-fundecl)

(def-vl-immdeps*-wrap vl-paramdecl)
(def-vl-immdeps*-list vl-paramdecllist vl-paramdecl)

(def-vl-immdeps*-wrap vl-typedef)
(def-vl-immdeps*-list vl-typedeflist vl-typedef)

(define vl-design-immdeps ((x vl-design-p))
  :short "Construct the immediate dependency graph for a design."
  :long "<p>Note that this is a very expensive operation that has to crawl
through the entire design and do many name lookups.</p>"
  :returns (graph vl-immdepgraph-p)
  (b* (((vl-design x))
       (ss    (vl-scopestack-init x))
       (graph
        (time$ (b* ((graph (make-vl-immdepgraph))
                    (graph (vl-modulelist-immdeps*    x.mods       graph))
                    (graph (vl-udplist-immdeps*       x.udps       graph))
                    (graph (vl-interfacelist-immdeps* x.interfaces graph))
                    (graph (vl-programlist-immdeps*   x.programs   graph))
                    (graph (vl-classlist-immdeps*     x.classes    graph))
                    (graph (vl-packagelist-immdeps*   x.packages   graph))
                    (graph (vl-configlist-immdeps*    x.configs    graph))
                    (graph (vl-vardecllist-immdeps*   x.vardecls   graph))
                    (graph (vl-taskdecllist-immdeps*  x.taskdecls  graph))
                    (graph (vl-fundecllist-immdeps*   x.fundecls   graph))
                    (graph (vl-paramdecllist-immdeps* x.paramdecls graph))
                    ;; We don't do anything with x.imports because scopestack sort of
                    ;; automatically resolves these dependencies for us.
                    ;; We don't do anything with forward typedefs because they don't
                    ;; have any dependency information in them and we expect to see
                    ;; the real typedefs instead.
                    (graph (vl-typedeflist-immdeps* x.typedefs graph)))
                 graph)
               :msg "; vl-design-immdeps crawl: ~st sec, ~sa bytes.~%"
               :mintime 1/2))
       (- (vl-scopestacks-free))
       ((vl-immdepgraph graph))
       (- (or (uniquep (alist-keys graph.deps))
              (raise "Design elements are not unique?  Name clash for ~&0."
                     (duplicated-members (alist-keys graph.deps)))))
       (final-deps
        (time$ (depgraph::mergesort-alist-values graph.deps)
               :msg "; vl-design-immdeps sort: ~st sec, ~sa bytes.~%"
               :mintime 1/2)))
    (change-vl-immdepgraph graph :deps final-deps))
  ///
  (memoize 'vl-design-immdeps)

  (defthm alist-values-are-sets-p-of-vl-design-immdeps
    (b* (((vl-immdepgraph graph) (vl-design-immdeps x)))
      (depgraph::alist-values-are-sets-p graph.deps))))
