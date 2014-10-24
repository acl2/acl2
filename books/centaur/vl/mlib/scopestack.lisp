; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "../parsetree")
;; (include-book "modnamespace")
;; (include-book "find-item")
;; (local (include-book "../util/arithmetic"))
(local (include-book "tools/templates" :dir :system))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (in-theory (disable acl2-count)))
(local (std::add-default-post-define-hook :fix))


;; NOTE: The following constants control what scopes we recognize and what
;; kinds of items may be looked up in various kinds of scopes.  Keyword
;; arguments on items account for various kinds of departures from convention:
;; -- :name foo denotes that the accessor for the name of the item is
;;         vl-itemtype->foo, rather than the default vl-itemtype->name.
;; -- :acc foo denotes that the accessor for the items within the scope is
;;         vl-scopetype->foo, rather than the default vl-scopetype->items.
;; -- :names-defined t denotes that the projection vl-itemlist->names is
;;         already defined (and the one we produce by default might not be
;;         redundant).
;; -- :maybe-stringp t denotes that the name accessor might return nil, rather
;;         than a string.
;; -- :sum-type t denotes that the item actually encompasses two or more item types
;; -- the import item is treated specially, and instead of finding the import itself
;;    you instead get the item imported from the specified package.


(local (defconst *vl-scopes->pkgs*
         ;; this one is special
          ;; scope type      has item types or (type acc-name)
         '((interface        )
           (module           )
           (design           ()   package)
           ;; bozo add function/task ports?
           (package          ))))

(local (defconst *vl-scopes->items*
          ;; scope type      has item types or (type acc-name)
         '((interface    (:import)          paramdecl vardecl modport)
           (module       (:import)          paramdecl vardecl fundecl taskdecl 
                                            (modinst :name instname :maybe-stringp t
                                                     :names-defined t)
                                            (gateinst :maybe-stringp t :names-defined t)
                                            (genelement :name blockname :maybe-stringp t
                                                        :names-defined t
                                                        :sum-type t
                                                        :acc generates))
           (genblob
                         (:import)          portdecl vardecl paramdecl fundecl taskdecl
                                            typedef
                                            (modinst :name instname :maybe-stringp t
                                                     :names-defined t)
                                            (gateinst :maybe-stringp t :names-defined t)
                                            (genelement :name blockname :maybe-stringp t
                                                        :names-defined t
                                                        :sum-type t
                                                        :multi-tags (:vl-genbase :vl-genif :vl-gencase :vl-genloop :vl-genblock :vl-genarray)
                                                        :acc generates))
           ;; fwdtypedefs could be included here but we hope to have resolved them all
           ;; to proper typedefs by the end of loading.
           (fundecl      ()             (blockitem :acc decls :sum-type t :transsum t))
           (design       (:import)      paramdecl vardecl fundecl taskdecl typedef)
           (package      (:import)      paramdecl vardecl fundecl taskdecl typedef))))

(local (defconst *vl-scopes->defs*
          ;; scope type      has item types or (type acc-name)
         '((interface        )
           (module           )
           (design       ()             (module :acc mods) udp interface program)
           (package          ))))

(local (defconst *vl-scopes->portdecls*
          ;; scope type      has item types or (type acc-name)
         '((interface    ()               portdecl)
           (module       ()               portdecl)
           (design           )
           ;; bozo add function/task ports?
           (package          ))))



;; Notes on name spaces -- from SV spec 3.13
;; SV spec lists 8 namespaces:

;; a) Definitions name space:
;;      module
;;      primitive
;;      program
;;      interface
;; declarations outside all other declarations
;; (meaning: not in a package? as well as not nested.
;; Global across compilation units.

;; b) Package name space: all package IDs.  Global across compilation units.

;; c) Compilation-unit scope name space:
;;     functions
;;     tasks
;;     checkers
;;     parameters
;;     named events
;;     netdecls
;;     vardecls
;;     typedefs
;;  defined outside any other containing scope.  Local to compilation-unit
;;  scope (as the name suggests).

;; d) Text macro namespace: local to compilation unit, global within it.
;;    This works completely differently from the others; we'll ignore it here
;;    since we take care of them in the preprocessor.

;; e) Module name space:
;;     modules
;;     interfaces
;;     programs
;;     checkers
;;     functions
;;     tasks
;;     named blocks
;;     instance names
;;     parameters
;;     named events
;;     netdecls
;;     vardecls
;;     typedefs
;;  defined within the scope of a particular
;;     module
;;     interface
;;     package
;;     program
;;     checker
;;     primitive.

;; f) Block namespace:
;;     named blocks
;;     functions
;;     tasks
;;     parameters
;;     named events
;;     vardecl (? "variable type of declaration")
;;     typedefs
;;  within
;;     blocks (named or unnamed)
;;     specifys
;;     functions
;;     tasks.

;; g) Port namespace:  ports within
;;     modules
;;     interfaces
;;     primitives
;;     programs

;; h) Attribute namespace, also separate.

;; Notes on scope rules, from SV spec 23.9.

;; Elements that define new scopes:
;;     — Modules
;;     — Interfaces
;;     — Programs
;;     — Checkers
;;     — Packages
;;     — Classes
;;     — Tasks
;;     — Functions
;;     — begin-end blocks (named or unnamed)
;;     — fork-join blocks (named or unnamed)
;;     — Generate blocks

;; An identifier shall be used to declare only one item within a scope.
;; However, perhaps this doesn't apply to global/compilation-unit scope, since
;; ncverilog and vcs both allow, e.g., a module and a wire of the same name
;; declared at the top level of a file.  We can't check this inside a module
;; since neither allows nested modules, and modules aren't allowed inside
;; packages.

;; This is supposed to be true of generate blocks even if they're not
;; instantiated; as an exception, different (mutually-exclusive) blocks of a
;; conditional generate can use the same name.

;; Search for identifiers referenced (without hierarchical path) within a task,
;; function, named block, generate block -- work outward to the
;; module/interface/program/checker boundary.  Search for a variable stops at
;; this boundary; search for a task, function, named block, or generate block
;; continues to higher levels of the module(/task/function/etc) hierarchy
;; (not the lexical hierarchy!).

;; Hierarchical names

(defsection scopestack
  :parents (mlib)
  :short "A scopestack is a stack of scopes, for looking up identifiers
correctly.")

(local (xdoc::set-default-parents scopestack))

(define vl-blockitem->name ((x vl-blockitem-p))
  :returns (name stringp :rule-classes :type-prescription)
  :prepwork ((local (defthm tag-when-vl-blockitem-p
                      (implies (vl-blockitem-p x)
                               (or (equal (tag x) :vl-vardecl)
                                   (equal (tag x) :vl-paramdecl)))
                      :rule-classes :forward-chaining))
             (local (defthm vl-blockitem-p-of-vl-blockitem-fix-forward
                      (vl-blockitem-p (vl-blockitem-fix x))
                      :rule-classes ((:forward-chaining :trigger-terms ((vl-blockitem-fix x)))))))
  (b* ((x (vl-blockitem-fix x)))
    (case (tag x)
      (:vl-vardecl (vl-vardecl->name x))
      (:vl-paramdecl (vl-paramdecl->name x)))))



(define vl-modinstlist->instnames-nrev ((x vl-modinstlist-p) nrev)
  :parents (vl-modinstlist->instnames)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (name (vl-modinst->instname (car x)))
       (nrev (if name
                 (nrev-push name nrev)
               nrev)))
    (vl-modinstlist->instnames-nrev (cdr x) nrev)))


(define vl-modinstlist->instnames ((x vl-modinstlist-p))
  :parents (vl-modinstlist-p modnamespace)
  :short "Collect all instance names (not module names!) from a @(see
vl-modinstlist-p)."
  :long "<p>The Verilog-2005 Standard requires that module instances be named,
but we relaxed that restriction in our definition of @(see vl-modinst-p)
because of user-defined primitives, which may be unnamed.  So, as with @(see
vl-gateinstlist->names), here we simply skip past any unnamed module
instances.</p>"
  :verify-guards nil
  (mbe :logic (if (consp x)
                  (if (vl-modinst->instname (car x))
                      (cons (vl-modinst->instname (car x))
                            (vl-modinstlist->instnames (cdr x)))
                    (vl-modinstlist->instnames (cdr x)))
                nil)
       :exec (with-local-nrev (vl-modinstlist->instnames-nrev x nrev)))
  ///
  (defthm vl-modinstlist->instnames-exec-removal
    (equal (vl-modinstlist->instnames-nrev x nrev)
           (append nrev (vl-modinstlist->instnames x)))
    :hints(("Goal" :in-theory (enable vl-modinstlist->instnames-nrev))))

  (verify-guards vl-modinstlist->instnames)

  (defthm vl-modinstlist->instnames-when-not-consp
    (implies (not (consp x))
             (equal (vl-modinstlist->instnames x)
                    nil)))

  (defthm vl-modinstlist->instnames-of-cons
    (equal (vl-modinstlist->instnames (cons a x))
           (if (vl-modinst->instname a)
               (cons (vl-modinst->instname a)
                     (vl-modinstlist->instnames x))
             (vl-modinstlist->instnames x))))

  (defthm vl-modinstlist->instnames-of-list-fix
    (equal (vl-modinstlist->instnames (list-fix x))
           (vl-modinstlist->instnames x)))

  (defcong list-equiv equal (vl-modinstlist->instnames x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (vl-modinstlist->instnames-of-list-fix))
            :use ((:instance vl-modinstlist->instnames-of-list-fix
                   (x x))
                  (:instance vl-modinstlist->instnames-of-list-fix
                   (x acl2::x-equiv))))))

  (defthm vl-modinstlist->instnames-of-append
    (equal (vl-modinstlist->instnames (append x y))
           (append (vl-modinstlist->instnames x)
                   (vl-modinstlist->instnames y))))

  (defthm vl-modinstlist->instnames-of-rev
    (equal (vl-modinstlist->instnames (rev x))
           (rev (vl-modinstlist->instnames x))))

  (defthm string-listp-of-vl-modinstlist->instnames
    (string-listp (vl-modinstlist->instnames x))))


(define vl-gateinstlist->names-nrev ((x vl-gateinstlist-p) nrev)
  :parents (vl-gateinstlist->names)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (name (vl-gateinst->name (car x)))
       (nrev (if name
                 (nrev-push name nrev)
               nrev)))
    (vl-gateinstlist->names-nrev (cdr x) nrev)))

(define vl-gateinstlist->names ((x vl-gateinstlist-p))
  :parents (vl-gateinstlist-p modnamespace)
  :short "Collect all instance names declared in a @(see vl-gateinstlist-p)."
  :long "<p>Note that gate instances may be unnamed, in which case we do not
add anything.  In other words, the list of names returned may be shorter than
the number of gate instances in the list.</p>"
  :verify-guards nil
  (mbe :logic (if (consp x)
                  (if (vl-gateinst->name (car x))
                      (cons (vl-gateinst->name (car x))
                            (vl-gateinstlist->names (cdr x)))
                    (vl-gateinstlist->names (cdr x)))
                nil)
       :exec (with-local-nrev (vl-gateinstlist->names-nrev x nrev)))
  ///
  (defthm vl-gateinstlist->names-nrev-removal
    (equal (vl-gateinstlist->names-nrev x nrev)
           (append nrev (vl-gateinstlist->names x)))
    :hints(("Goal" :in-theory (enable vl-gateinstlist->names-nrev))))

  (verify-guards vl-gateinstlist->names)

  (defthm vl-gateinstlist->names-when-not-consp
    (implies (not (consp x))
             (equal (vl-gateinstlist->names x)
                    nil)))

  (defthm vl-gateinstlist->names-of-cons
    (equal (vl-gateinstlist->names (cons a x))
           (if (vl-gateinst->name a)
               (cons (vl-gateinst->name a)
                     (vl-gateinstlist->names x))
             (vl-gateinstlist->names x))))

  (defthm vl-gateinstlist->names-of-list-fix
    (equal (vl-gateinstlist->names (list-fix x))
           (vl-gateinstlist->names x)))

  (defcong list-equiv equal (vl-gateinstlist->names x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (vl-gateinstlist->names-of-list-fix))
            :use ((:instance vl-gateinstlist->names-of-list-fix (x x))
                  (:instance vl-gateinstlist->names-of-list-fix (x acl2::x-equiv))))))

  (defthm vl-gateinstlist->names-of-append
    (equal (vl-gateinstlist->names (append x y))
           (append (vl-gateinstlist->names x)
                   (vl-gateinstlist->names y))))

  (defthm vl-gateinstlist->names-of-rev
    (equal (vl-gateinstlist->names (rev x))
           (rev (vl-gateinstlist->names x))))

  (defthm string-listp-of-vl-gateinstlist->names
    (string-listp (vl-gateinstlist->names x))))


(define vl-genelement->blockname ((x vl-genelement-p))
  :returns (blockname maybe-stringp)
  (vl-genelement-case x
    :vl-genblock x.name
    :vl-genarray x.name
    :otherwise nil))

(define vl-genelementlist->blocknames-nrev ((x vl-genelementlist-p) nrev)
  :parents (vl-genelementlist->blocknames)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (name (vl-genelement->blockname (car x)))
       (nrev (if name
                 (nrev-push name nrev)
               nrev)))
    (vl-genelementlist->blocknames-nrev (cdr x) nrev)))


(define vl-genelementlist->blocknames ((x vl-genelementlist-p))
  :parents (vl-genelementlist-p modnamespace)
  :short "Collect all resolved block names in a @(see vl-genelementlist-p)."
  :long "<p>Note the elements may be unresolved or may not be blocks at all, in
which case we do not add anything.  In other words, the list of names returned
may be shorter than the number of elements in the list.</p>"
  :verify-guards nil
  (mbe :logic (if (consp x)
                  (if (vl-genelement->blockname (car x))
                      (cons (vl-genelement->blockname (car x))
                            (vl-genelementlist->blocknames (cdr x)))
                    (vl-genelementlist->blocknames (cdr x)))
                nil)
       :exec (with-local-nrev (vl-genelementlist->blocknames-nrev x nrev)))
  ///
  (defthm vl-genelementlist->blocknames-nrev-removal
    (equal (vl-genelementlist->blocknames-nrev x nrev)
           (append nrev (vl-genelementlist->blocknames x)))
    :hints(("Goal" :in-theory (enable vl-genelementlist->blocknames-nrev))))

  (verify-guards vl-genelementlist->blocknames)

  (defthm vl-genelementlist->blocknames-when-not-consp
    (implies (not (consp x))
             (equal (vl-genelementlist->blocknames x)
                    nil)))

  (defthm vl-genelementlist->blocknames-of-cons
    (equal (vl-genelementlist->blocknames (cons a x))
           (if (vl-genelement->blockname a)
               (cons (vl-genelement->blockname a)
                     (vl-genelementlist->blocknames x))
             (vl-genelementlist->blocknames x))))

  (defthm vl-genelementlist->blocknames-of-list-fix
    (equal (vl-genelementlist->blocknames (list-fix x))
           (vl-genelementlist->blocknames x)))

  (defcong list-equiv equal (vl-genelementlist->blocknames x) 1
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (vl-genelementlist->blocknames-of-list-fix))
            :use ((:instance vl-genelementlist->blocknames-of-list-fix (x x))
                  (:instance vl-genelementlist->blocknames-of-list-fix (x acl2::x-equiv))))))

  (defthm vl-genelementlist->blocknames-of-append
    (equal (vl-genelementlist->blocknames (append x y))
           (append (vl-genelementlist->blocknames x)
                   (vl-genelementlist->blocknames y))))

  (defthm vl-genelementlist->blocknames-of-rev
    (equal (vl-genelementlist->blocknames (rev x))
           (rev (vl-genelementlist->blocknames x))))

  (defthm string-listp-of-vl-genelementlist->blocknames
    (string-listp (vl-genelementlist->blocknames x))))



(local
 (defsection-progn template-substitution-helpers

   (std::def-primitive-aggregate tmplsubst
     (features atomsubst strsubst))

   (defun scopes->typeinfos (scopes)
     (declare (xargs :mode :program))
     (if (atom scopes)
         nil
       (union-equal (cddar scopes)
                    (scopes->typeinfos (cdr scopes)))))

   (defun typeinfos->tmplsubsts (typeinfos)
     ;; returns a list of conses (features . strsubst-alist)
     (declare (xargs :mode :program))
     (if (atom typeinfos)
         nil
       (cons (b* ((kwds (and (consp (car typeinfos)) (cdar typeinfos)))
                  (type (if (consp (car typeinfos)) (caar typeinfos) (car typeinfos)))
                  (acc (let ((look (cadr (assoc-keyword :acc kwds))))
                         (if look
                             (symbol-name look)
                           (cat (symbol-name type) "S"))))
                  (name (let ((look (cadr (assoc-keyword :name kwds))))
                          (if look (symbol-name look) "NAME")))
                  (maybe-stringp (cadr (assoc-keyword :maybe-stringp kwds)))
                  (names-defined (cadr (assoc-keyword :names-defined kwds)))
                  (sum-type      (cadr (assoc-keyword :sum-type      kwds)))
                  (transsum      (cadr (assoc-keyword :transsum      kwds))))
               (make-tmplsubst :features (append (and maybe-stringp '(:maybe-stringp))
                                                 (and names-defined '(:names-defined))
                                                 (and sum-type      '(:sum-type))
                                                 (and transsum      '(:transsum)))
                               :strsubst
                               `(("__TYPE__" ,(symbol-name type) . vl-package)
                                 ("__ACC__" ,acc . vl-package)
                                 ("__NAME__" ,name . vl-package))))
             (typeinfos->tmplsubsts (cdr typeinfos)))))

   (defun scopes->tmplsubsts (scopes)
     (if (atom scopes)
         nil
       (cons (make-tmplsubst :strsubst `(("__TYPE__" ,(symbol-name (caar scopes)) . vl-package))
                             :atomsubst `((__items__ . ,(cddar scopes)))
                             :features (append (cadar scopes)
                                               (and (cddar scopes) '(:has-items))))
             (scopes->tmplsubsts (cdr scopes)))))

   (defun template-proj (template substs)
     (declare (xargs :mode :program))
     (if (atom substs)
         nil
       (cons (b* (((tmplsubst subst) (car substs))
                  (val
                   (acl2::template-subst-fn template subst.features
                                            nil nil
                                            subst.atomsubst
                                            subst.strsubst
                                            'vl-package)))
               val)
             (template-proj template (cdr substs)))))

   (defun template-append (template substs)
     (declare (xargs :mode :program))
     (if (atom substs)
         nil
       (append (b* (((tmplsubst subst) (car substs))
                    (val
                     (acl2::template-subst-fn template subst.features
                                              nil nil
                                              subst.atomsubst
                                              subst.strsubst
                                              'vl-package)))
                 val)
               (template-append template (cdr substs)))))))


(local (defthmd tag-when-vl-genelement-p
         (implies (vl-genelement-p x)
                  (or (equal (tag x) :vl-genbase)
                      (equal (tag x) :vl-genif)
                      (equal (tag x) :vl-gencase)
                      (equal (tag x) :vl-genloop)
                      (equal (tag x) :vl-genblock)
                      (equal (tag x) :vl-genarray)))
         :hints(("Goal" :in-theory (enable vl-genelement-p tag)))
         :rule-classes :forward-chaining))

(make-event ;; Definition of vl-scopeitem type
 (let ((substs (typeinfos->tmplsubsts (scopes->typeinfos *vl-scopes->items*))))
   `(progn
      (local (in-theory (enable tag-when-vl-genelement-p)))
      (deftranssum vl-scopeitem
        :short "Recognizer for an syntactic element that can occur within a scope."
        ,(template-append '((:@ (not :transsum) vl-__type__)) substs))
      (local (in-theory (disable tag-when-vl-genelement-p
                                 vl-genelement-p-by-tag-when-vl-scopeitem-p)))


      ,@(template-append
         '((:@ :transsum
            (defthm vl-scopeitem-p-when-vl-__type__-p
              (implies (vl-__type__-p x)
                       (vl-scopeitem-p x))
              :hints(("Goal" :in-theory (enable vl-__type__-p))))))
         substs)

      (fty::deflist vl-scopeitemlist
        :elt-type vl-scopeitem-p
        :elementp-of-nil nil
        ///
        . ,(template-proj
            '(defthm vl-scopeitemlist-p-when-vl-__type__list-p
               (implies (vl-__type__list-p x)
                        (vl-scopeitemlist-p x))
               :hints (("goal" :induct (vl-scopeitemlist-p x)
                        :expand ((vl-__type__list-p x)
                                 (vl-scopeitemlist-p x))
                        :in-theory (enable (:i vl-scopeitemlist-p)))))
            substs)))))

(make-event ;; Definition of vl-scopedef type
 (let ((substs (typeinfos->tmplsubsts (scopes->typeinfos *vl-scopes->defs*))))
   `(progn
      (deftranssum vl-scopedef
        :short "Recognizer for an syntactic element that can occur within a scope."
        ,(template-proj 'vl-__type__ substs))

      (fty::deflist vl-scopedeflist
        :elt-type vl-scopedef-p
        :elementp-of-nil nil
        ///
        . ,(template-proj
            '(defthm vl-scopedeflist-p-when-vl-__type__list-p
               (implies (vl-__type__list-p x)
                        (vl-scopedeflist-p x))
               :hints (("goal" :induct (vl-scopedeflist-p x)
                        :expand ((vl-__type__list-p x)
                                 (vl-scopedeflist-p x))
                        :in-theory (enable (:i vl-scopedeflist-p)))))
            substs)))))

(make-event ;; Definition of vl-scope type
 (let ((subst (scopes->tmplsubsts *vl-scopes->items*)))
   `(progn
      (deftranssum vl-scope
        :short "Recognizer for a syntactic element that can have named elements within it."
        ,(template-proj 'vl-__type__ subst))

      (defthm vl-scope-p-tag-forward
        ;; BOZO is this better than the rewrite rule we currently add?
        (implies (vl-scope-p x)
                 (or . ,(template-proj '(equal (tag x) :vl-__type__) subst)))
        :rule-classes :forward-chaining))))






(local ;; For each searchable type foo, we get:
 ;;                  - vl-find-foo: linear search by name in a list of foos
 ;;                  - vl-fast-foolist-alist: fast alist binding names to foos.
 (defconst *scopeitem-alist/finder-template*
   '(progn
      (:@ (not :names-defined)
       (defprojection vl-__type__list->__name__s ((x vl-__type__list-p))
         :returns (names string-listp
                         :hints (("goal" :in-theory (disable (:d vl-__type__list->__name__s))
                                  :induct (vl-__type__list->__name__s x)
                                  :expand ((vl-__type__list->__name__s x)))))
         :parents (vl-__type__list-p)
         (vl-__type__->__name__ x)))

      (fty::defalist vl-__type__-alist :key-type stringp :val-type vl-__type__-p
        :keyp-of-nil nil :valp-of-nil nil)

      (def-vl-find-moditem __type__
        :element->name vl-__type__->__name__
        :list->names vl-__type__list->__name__s
        (:@ :maybe-stringp :names-may-be-nil t)
        (:@ :sum-type :sum-type t))

      (define vl-__type__list-alist ((x vl-__type__list-p)
                                          acc)
        (if (consp x)
            (:@ :maybe-stringp
             (let ((name (hons-copy (vl-__type__->__name__ (car x)))))
               (if name
                   (cons (cons name (vl-__type__-fix (car x)))
                         (vl-__type__list-alist (cdr x) acc))
                 (vl-__type__list-alist (cdr x) acc))))
          (:@ (not :maybe-stringp)
           (cons (cons (vl-__type__->__name__ (car x))
                       (vl-__type__-fix (car x)))
                 (vl-__type__list-alist (cdr x) acc)))
          acc)
        ///
        (defthm lookup-in-vl-__type__list-alist-acc-elim
          (implies (syntaxp (not (equal acc ''nil)))
                   (equal (hons-assoc-equal name (vl-__type__list-alist x acc))
                          (or (hons-assoc-equal name (vl-__type__list-alist x nil))
                              (hons-assoc-equal name acc)))))
        (defthm lookup-in-vl-__type__list-alist-fast
          (implies (stringp name)
                   (equal (hons-assoc-equal name (vl-__type__list-alist x nil))
                          (let ((val (vl-find-__type__ name x)))
                            (and val
                                 (cons name val)))))
          :hints(("Goal" :in-theory (disable (:d vl-__type__list-alist))
                  :induct (vl-__type__list-alist x nil)
                  :expand ((vl-__type__list-alist x nil)
                           (vl-find-__type__ name x)))))))))

;; (local (defthm member-nil
;;          (not (member x nil))))

;; prevent defalist from making a few expensive rules
(local (acl2::ruletable-delete-tags! acl2::alistp-rules (:cons-member)))
(local (table acl2::listp-rules
              nil 
              (let ((alist (table-alist 'acl2::listp-rules acl2::world)))
                (set-difference-equal
                 alist
                 (list (assoc 'ACL2::ELEMENT-LIST-P-WHEN-SUBSETP-EQUAL-NON-TRUE-LIST alist)
                       (assoc 'ACL2::ELEMENT-LIST-P-WHEN-SUBSETP-EQUAL-TRUE-LIST alist))))
              :clear))


(local (in-theory (disable alistp acl2::alistp-when-keyval-alist-p-rewrite
                           ;;acl2::consp-under-iff-when-true-listp
                           acl2::subsetp-when-atom-right
                           ;;stringp-when-true-listp
                           double-containment
                           default-cdr
                           ;;acl2::true-listp-when-atom
                           ;;acl2::consp-when-member-equal-of-atom-listp
                           acl2::subsetp-member
                           acl2::str-fix-default
                           acl2::stringp-when-maybe-stringp
                           ;;acl2::car-when-all-equalp
                           consp-when-member-equal-of-cons-listp
                           (:t member-equal)
                           member-equal
                           default-car
                           consp-when-member-equal-of-vl-gencaselist-p
                           consp-when-member-equal-of-vl-caselist-p
                           consp-when-member-equal-of-vl-commentmap-p
                           consp-when-member-equal-of-vl-atts-p
                           acl2::consp-when-member-equal-of-keyval-alist-p
                           acl2::consp-of-car-when-alistp
                           (tau-system)
                           not)))



;; copied from find-item
(defmacro def-vl-find-moditem (type
                               &key
                               element->name
                               list->names
                               names-may-be-nil
                               sum-type)

  (let* ((mksym-package-symbol 'vl::foo)
         (fn            (mksym 'vl-find- type))
         (element-p     (mksym 'vl- type '-p))
         (fix           (mksym 'vl- type '-fix))
         (type?         (mksym type '?))
         (tag           (intern (cat "VL-" (symbol-name type)) "KEYWORD"))
         (list-p        (mksym 'vl- type 'list-p))
         (element->name (or element->name
                            (mksym 'vl- type '->name)))
         (list->names   (or list->names
                            (mksym 'vl- type 'list->names))))

    `(define ,fn
       :short ,(cat "Look up a " (symbol-name type) " in a list, by its name.")
       ((name stringp)
        (x    ,list-p))
       :hooks ((:fix :args ((x ,list-p))))
       :returns (,type? (iff (,element-p ,type?)
                             ,type?)
                        :hints(("Goal" :in-theory (disable (:d ,fn))
                                :induct (,fn name x)
                                :expand ((:free (name) (,fn name x))))))
       :guard-hints (("goal" :in-theory (disable ,fn)))
       (cond ((atom x)
              nil)
             ((equal name (,element->name (car x)))
              (,fix (car x)))
             (t
              (,fn name (cdr x))))
       ///
       (local (in-theory (disable (force) (:d ,fn))))
       (local (set-default-hints
               '((and (equal (car id) '(0))
                      '(:induct (,fn name x) :expand ((:free (name) (,fn name x))))))))
       (defthm ,(mksym fn '-under-iff)
         ,(if names-may-be-nil
              `(implies (force (stringp name))
                        (iff (,fn name x)
                             (member-equal name (,list->names x))))
            `(iff (,fn name x)
                  (member-equal name (,list->names x)))))

       (defthm ,(mksym element->name '-of- fn)
         (implies (,fn name x)
                  (equal (,element->name (,fn name x))
                         name)))

       ,@(and (not sum-type)
              `((local (defthm ,(mksym 'tag-when- element-p '-strong)
                (implies (,element-p x)
                         (equal (tag x)
                                ,tag))
                  :hints(("Goal" :in-theory (enable ,(mksym 'tag-when- element-p))))))

                (defthm ,(mksym 'tag-of- fn)
                  (equal (tag (,fn name x))
                         (if (,fn name x)
                             ,tag
                           nil)))))

       (defthm ,(mksym 'member-equal-of- fn)
         (implies (force (,list-p x))
                  (iff (member-equal (,fn name x) x)
                       (,fn name x)))
         :hints (("goal" :induct (,fn name x)
                  :expand ((:free (name) (,fn name x))
                           (:free (name) (,fn name nil))))))

       (defthm ,(mksym 'consp-of- fn '-when-member-equal)
         (implies (and (member-equal name (,list->names x))
                       (force (stringp name)))
                  (consp (,fn name x))))

       (local (set-default-hints nil)))))

(local (defthm vl-genelement-fix-type
         (consp (vl-genelement-fix x))
         :hints(("Goal" :expand ((:with vl-genelement-fix (vl-genelement-fix x)))))
         :rule-classes :type-prescription))

(local (defthm vl-blockitem-fix-type
         (consp (vl-blockitem-fix x))
         :hints(("Goal" :expand ((:with vl-blockitem-fix (vl-blockitem-fix x)))))
         :rule-classes :type-prescription))


(make-event ;; Definition of scopeitem alists/finders
 (b* ((substs (typeinfos->tmplsubsts (scopes->typeinfos (append *vl-scopes->items*
                                                                *vl-scopes->defs*
                                                                *vl-scopes->pkgs*
                                                                *vl-scopes->portdecls*))))
      (events (template-proj *scopeitem-alist/finder-template* substs)))
   `(progn . ,events)))






;; ;; Now we define:
;; ;; - how to look up a package name in the global design
;; ;; - how to look up a scopeitem in a package, not considering its imports
;; ;; - how to look up a name in a list of import statements.
;; ;; These don't involve the scopestack yet: in each case we know in which scope
;; ;; to find the item.  This works and doesn't need some gross recursive
;; ;; implementation because the following isn't allowed:
;; ;; package bar;
;; ;;   parameter barparam = 13032;
;; ;; endpackage
;; ;; package foo;
;; ;;   import bar::barparam;
;; ;; endpackage
;; ;; module baz ();
;; ;;   import foo::barparam; // fail -- barparam isn't exported by foo.
;; ;; endmodule

;; ;; We then use the above functions to define other scopestack functions resolve
;; ;; imports.


;; (define vl-design->package-alist ((x vl-design-p))
;;   :enabled t
;;   (vl-packagelist-alist (vl-design->packages x) nil)
;;   ///
;;   (memoize 'vl-design->package-alist))

;; (define vl-design-find-package ((name stringp) (x vl-design-p))
;;   :returns (res (iff (vl-package-p res) res))
;;   (mbe :logic (vl-find-package (string-fix name) (vl-design->packages x))
;;        :exec (cdr (hons-get (string-fix name) (vl-design->package-alist x)))))








(defoption vl-maybe-design-p vl-design-p)





(local
 (defun def-scopetype-find (scope importp itemtypes resultname resulttype)
   (declare (xargs :mode :program))
   (b* ((substs (typeinfos->tmplsubsts itemtypes))
        ((unless itemtypes) '(value-triple nil))
        (template
          `(progn
             (define vl-__scope__-scope-find-__result__
               :ignore-ok t
               :parents (vl-scope-find)
               ((name  stringp)
                (scope vl-__scope__-p))
               :returns (item    (iff (__resulttype__ item) item))
               (b* (((vl-__scope__ scope))
                    (?name (string-fix name)))
                 (or . ,(template-proj
                                  '(vl-find-__type__ name scope.__acc__)
                                  substs))))

             (define vl-__scope__-scope-__result__-alist
               :parents (vl-scope-find)
               :ignore-ok t
               ((scope vl-__scope__-p)
                acc)
               :returns (alist)
               (b* (((vl-__scope__ scope))
                    . ,(reverse
                        (template-proj
                         '(acc (vl-__type__list-alist scope.__acc__ acc))
                         substs)))
                 acc)
               ///
               (local (in-theory (enable vl-__scope__-scope-find-__result__)))
               (defthm vl-__scope__-scope-__result__-alist-lookup-acc-elim
                 (implies (syntaxp (not (equal acc ''nil)))
                          (equal (hons-assoc-equal name (vl-__scope__-scope-__result__-alist scope acc))
                                 (or (hons-assoc-equal name (vl-__scope__-scope-__result__-alist scope nil))
                                     (hons-assoc-equal name acc)))))
               (defthm vl-__scope__-scope-__result__-alist-correct
                 (implies (stringp name)
                          (equal (hons-assoc-equal name (vl-__scope__-scope-__result__-alist scope nil))
                                 (b* ((item (vl-__scope__-scope-find-__result__ name scope)))
                                   (and item
                                        (cons name item))))))
               ;; (defthmd vl-__scope__-scope-__result__-alist-correct2
               ;;   (implies (stringp name)
               ;;            (equal (vl-__scope__-scope-find-__result__ name scope)
               ;;                   (let ((look (hons-assoc-equal name (vl-__scope__-scope-__result__-alist scope nil))))
               ;;                     (mv (consp look) (cdr look))))))
               ))))
     (acl2::template-subst-fn template (and importp '(:import)) nil nil nil
                              `(("__SCOPE__" ,(symbol-name scope) . vl-package)
                                ("__RESULT__" ,(symbol-name resultname) . vl-package)
                                ("__RESULTTYPE__" ,(symbol-name resulttype) . vl-package))
                              'vl-package))))


(make-event ;; Definition of vl-design-scope-find-package vl-design-scope-package-alist
 (b* ((substs (scopes->tmplsubsts *vl-scopes->pkgs*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find
                   '__type__
                   (:@ :import t) (:@ (not :import) nil)
                   '__items__ 'package 'vl-package-p))
               substs))))


(make-event ;; Definitions of e.g. vl-module-scope-find-item and vl-module-scope-item-alist
 (b* ((substs (scopes->tmplsubsts *vl-scopes->items*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__
                   (:@ :import t) (:@ (not :import) nil)
                   '__items__ 'item 'vl-scopeitem-p))
               substs))))

(make-event ;; Definitions of e.g. vl-design-scope-find-definition and vl-design-scope-definition-alist
 (b* ((substs (scopes->tmplsubsts *vl-scopes->defs*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__ 
                   (:@ :import t) (:@ (not :import) nil)
                   '__items__ 'definition 'vl-scopedef-p))
               substs))))


(make-event ;; Definition of scopetype-find and -fast-alist functions
 (b* ((substs (scopes->tmplsubsts *vl-scopes->portdecls*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__
                   (:@ :import t) (:@ (not :import) nil)
                   '__items__ 'portdecl 'vl-portdecl-p))
               substs))))




(define vl-package-scope-item-alist-top ((x vl-package-p))
  :enabled t
  (make-fast-alist (vl-package-scope-item-alist x nil))
  ///
  (memoize 'vl-package-scope-item-alist-top))

(define vl-design-scope-package-alist-top ((x vl-design-p))
  :enabled t
  (make-fast-alist (vl-design-scope-package-alist x nil))
  ///
  (memoize 'vl-design-scope-package-alist-top))


;; (make-event ;; Definition of vl-package-scope-find-nonimported-item
;;  (b* ((substs (scopes->tmplsubsts (list (assoc 'package *vl-scopes->items*)))))
;;    `(progn . ,(template-proj
;;                '(make-event
;;                  (def-scopetype-find '__type__ nil
;;                    '__items__ 'nonimported-item 'vl-scopeitem-p))
;;                substs))))




;; Now, we want a function for looking up imported names.  This must first look
;; for the name explicitly imported, then implicitly.

;; What do we do when we find an import of a name from a package that doesn't
;; contain that name?  This should be an error, but practially speaking I think
;; we want to check for these in one place and not disrupt other code with
;; error handling.  So in this case we just don't find the item.
(define vl-importlist-find-explicit-item ((name stringp) (x vl-importlist-p) (design vl-maybe-design-p))
  :returns (mv (package (iff (stringp package) package))
               (item (iff (vl-scopeitem-p item) item)))
  (b* (((when (atom x)) (mv nil nil))
       ((vl-import x1) (car x))
       ((when (and (stringp x1.part)
                   (equal x1.part (string-fix name))))
        ;; if we don't have a design, I think we still want to say we found the
        ;; item, just not what it is.
        (b* ((package (and design (vl-design-scope-find-package x1.pkg design))))
          ;; regardless of whether the package exists or has the item, return found
          (mv x1.pkg (and package (vl-package-scope-find-item name package))))))
    (vl-importlist-find-explicit-item name (cdr x) design))
  ///
  (more-returns
   (package :name maybe-string-type-of-vl-importlist-find-explicit-item-package
            (or (stringp package) (not package))
            :rule-classes :type-prescription)))

;; (local
;;  (defthm equal-of-vl-importlist-find-explicit-item
;;    (equal (equal (vl-importlist-find-explicit-item name scope design) x)
;;           (and (consp x)
;;                (consp (cdr x))
;;                (not (cddr x))
;;                (equal (mv-nth 0 (vl-importlist-find-explicit-item name scope design))
;;                       (mv-nth 0 x))
;;                (equal (mv-nth 1 (vl-importlist-find-explicit-item name scope design))
;;                       (mv-nth 1 x))))
;;    :hints(("Goal" :in-theory (enable mv-nth-expand-to-conses
;;                                      equal-of-cons
;;                                      vl-importlist-find-explicit-item)))))


(define vl-importlist->explicit-item-alist ((x vl-importlist-p) (design vl-maybe-design-p)
                                            acc)
  (b* (((when (atom x)) acc)
       ((vl-import x1) (car x))
       ((unless (stringp x1.part))
        (vl-importlist->explicit-item-alist (cdr x) design acc))
        ;; if we don't have a design, it seems like returning the package but
        ;; not the item is the best way to go here, since we might have
        ;; imported the name from the package but can't find out.
       (package (and design (cdr (hons-get x1.pkg (vl-design-scope-package-alist-top design)))))
       (item (and package (cdr (hons-get x1.part (vl-package-scope-item-alist-top package))))))
    (hons-acons x1.part (cons x1.pkg item)
                (vl-importlist->explicit-item-alist (cdr x) design acc)))
  ///
  (defthm vl-importlist->explicit-item-alist-lookup-acc-elim
    (implies (syntaxp (not (equal acc ''nil)))
             (equal (hons-assoc-equal name (vl-importlist->explicit-item-alist x design acc))
                    (or (hons-assoc-equal name (vl-importlist->explicit-item-alist x design nil))
                        (hons-assoc-equal name acc)))))
  (defthm vl-importlist->explicit-item-alist-correct
    (implies (stringp name)
             (equal (hons-assoc-equal name (vl-importlist->explicit-item-alist x design nil))
                    (b* (((mv pkg item) (vl-importlist-find-explicit-item name x design)))
                      (and (or pkg item)
                           (cons name (cons pkg item))))))
    :hints(("Goal" :in-theory (enable vl-importlist-find-explicit-item)))))

(define vl-importlist-find-implicit-item ((name stringp) (x vl-importlist-p) (design vl-maybe-design-p))
  :returns (mv (package (iff (stringp package) package))
               (item (iff (vl-scopeitem-p item) item)))
  (b* (((when (atom x)) (mv nil nil))
       ((vl-import x1) (car x))
       ((unless (eq x1.part :vl-import*))
        (vl-importlist-find-implicit-item name (cdr x) design))
       (package (and design (vl-design-scope-find-package x1.pkg design)))
       ((unless package) (mv x1.pkg nil))
       (item (vl-package-scope-find-item (string-fix name) package)))
    (if item
        (mv x1.pkg item)
      (vl-importlist-find-implicit-item name (cdr x) design)))
  ///
  (more-returns
   (package :name maybe-string-type-of-vl-importlist-find-implicit-item-package
          (or (stringp package) (not package))
          :rule-classes :type-prescription)))


(define vl-importlist->star-packages ((x vl-importlist-p))
  :returns (packages string-listp)
  (b* (((when (atom x)) nil)
       ((vl-import x1) (car x)))
    (if (eq x1.part :vl-import*)
        (cons x1.pkg (vl-importlist->star-packages (cdr x)))
      (vl-importlist->star-packages (cdr x)))))


(define vl-import-stars-find-item ((name stringp) (packages string-listp) (design vl-maybe-design-p))
  :returns (mv (package (iff (stringp package) package))
               (item (iff (vl-scopeitem-p item) item)))
  (b* (((when (atom packages)) (mv nil nil))
       (pkg (string-fix (car packages)))
       (package (and design (cdr (hons-get pkg (vl-design-scope-package-alist-top design)))))
       ((unless package) (mv pkg nil))
       (item (cdr (hons-get (string-fix name)
                            (vl-package-scope-item-alist-top package))))
       ((when item) (mv pkg item)))
    (vl-import-stars-find-item name (cdr packages) design))
  ///
  (defthm vl-import-stars-find-item-correct
    (equal (vl-import-stars-find-item name (vl-importlist->star-packages x) design)
           (vl-importlist-find-implicit-item name x design))
    :hints(("Goal" :in-theory (enable vl-importlist-find-implicit-item
                                      vl-importlist->star-packages)))))

(defprod vl-scopeinfo
  ((locals "Locally defined names bound to their declarations")
   (imports "Explicitly imported names bound to (package-name . declaration)")
   (star-packages string-listp "Names of packages imported with *"))
  :layout :tree)

(define vl-scopeinfo-lookup ((name stringp) (x vl-scopeinfo-p) (design vl-maybe-design-p))
  :returns (mv package item)
  (b* (((vl-scopeinfo x))
       (name (string-fix name))
       (local-item (cdr (hons-get name x.locals)))
       ((when local-item) (mv nil local-item))
       (import-item (cdr (hons-get name x.imports)))
       ((when (consp import-item)) (mv (car import-item) (cdr import-item))))
    (vl-import-stars-find-item name x.star-packages design)))
       













;; (fty::deflist vl-scopelist :elt-type vl-scope :elementp-of-nil nil)

(local (defthm type-of-vl-scope-fix
         (consp (vl-scope-fix x))
         :hints (("goal" :use ((:instance consp-when-vl-scope-p
                                (x (vl-scope-fix x))))
                  :in-theory (disable consp-when-vl-scope-p)))
         :rule-classes :type-prescription))


(fty::defflexsum vl-scopestack
  (:null :cond (atom x)
   :shape (eq x nil)
   :ctor-body nil)
  (:global :cond (eq (car x) :global)
   :fields ((design :type vl-design-p :acc-body (Cdr x)))
   :ctor-body (cons :global design))
  (:local :cond t
   :fields ((top :type vl-scope-p :acc-body (car x))
            (super :type vl-scopestack-p :acc-body (cdr x)))
   :ctor-body (cons top super)))

(define vl-scopestack->design ((x vl-scopestack-p))
  :returns (design (iff (vl-design-p design) design))
  :measure (vl-scopestack-count x)
  (vl-scopestack-case x
    :null nil
    :global x.design
    :local (vl-scopestack->design x.super)))

(define vl-scopestack-push ((scope vl-scope-p) (x vl-scopestack-p))
  :returns (x1 vl-scopestack-p)
  (make-vl-scopestack-local :top scope :super x))

(define vl-scopestack-pop ((x vl-scopestack-p))
  :returns (super vl-scopestack-p)
  (vl-scopestack-case x
    :local x.super
    :otherwise (vl-scopestack-fix x)))

(define vl-scopestack-init
  :short "Create an initial scope stack for an entire design."
  ((design vl-design-p))
  :returns (ss vl-scopestack-p)
  (make-vl-scopestack-global :design design))


(local (defthm vl-maybe-design-p-when-iff
         (implies (iff (vl-design-p x) x)
                  (vl-maybe-design-p x))))


(local
 (defun def-vl-scope-find (table result resulttype stackp importsp)
   (declare (xargs :mode :program))
   (b* ((substs (scopes->tmplsubsts table))
        (template
          `(progn
             (define vl-scope-find-__result__
               :short "Look up a plain identifier to find an __result__ in a scope."
               ((name  stringp)
                (scope vl-scope-p)
                (:@ :import (design vl-maybe-design-p)))
               :returns (mv (pkg-name    (iff (stringp pkg-name) pkg-name))
                            (__result__ (iff (__resulttype__ __result__) __result__)))
               (b* ((scope (vl-scope-fix scope)))
                 (case (tag scope)
                   ,@(template-append
                      '((:@ :has-items
                         (:vl-__type__
                          (:@ (not :import)
                           (mv nil (vl-__type__-scope-find-__result__ name scope)))
                          (:@ :import
                           (b* (((vl-__type__ scope :quietp t))
                                (item (vl-__type__-scope-find-__result__ name scope))
                                ((when item) (mv nil item))
                                ((mv pkg item) (vl-importlist-find-explicit-item
                                                name scope.imports design))
                                ((when (or pkg item)) (mv pkg item)))
                             (vl-importlist-find-implicit-item name scope.imports design))))))
                      substs)
                   (otherwise (mv nil nil))))
               ///
               (more-returns
                (pkg-name :name maybe-string-type-of-vl-scope-find-__result__-pkg-name
                         (or (stringp pkg-name) (not pkg-name))
                         :rule-classes :type-prescription)))


             (define vl-scope-__result__-scopeinfo
               :short "Make a fast lookup table for __result__s in a scope.  Memoized."
               ((scope vl-scope-p)
                (:@ :import (design vl-maybe-design-p)))
               :returns (scopeinfo vl-scopeinfo-p)
               (b* ((scope (vl-scope-fix scope)))
                 (case (tag scope)
                   ,@(template-append
                      '((:@ :has-items
                         (:vl-__type__
                          (b* (((vl-__type__ scope :quietp t)))
                            (make-vl-scopeinfo
                             :locals (make-fast-alist
                                      (vl-__type__-scope-__result__-alist scope nil))
                             (:@ :import
                              :imports (make-fast-alist
                                        (vl-importlist->explicit-item-alist scope.imports design nil))
                              :star-packages (vl-importlist->star-packages scope.imports)))))))
                      substs)
                   (otherwise (make-vl-scopeinfo))))
               ///
               (local (in-theory (enable vl-scope-find-__result__
                                         vl-scopeinfo-lookup)))
               (defthm vl-scope-__result__-scopeinfo-correct
                 (implies (stringp name)
                          (equal (vl-scopeinfo-lookup name (vl-scope-__result__-scopeinfo scope (:@ :import design)) design)
                                 (vl-scope-find-__result__ name scope (:@ :import design))))
                 :hints (("goal" :expand ((vl-import-stars-find-item name nil design)))))
               (memoize 'vl-scope-__result__-scopeinfo))

             (define vl-scope-find-__result__-fast
               :short "Like @(see vl-scope-find-__result__), but uses a fast lookup table"
               ((name stringp)
                (scope vl-scope-p)
                (:@ :import (design vl-maybe-design-p)))
               :enabled t
               (mbe :logic (vl-scope-find-__result__ name scope (:@ :import design))
                    :exec (vl-scopeinfo-lookup name (vl-scope-__result__-scopeinfo scope (:@ :import design)) (:@ :import design) (:@ (not :import) nil))))

             ,@(and stackp
                    `((define vl-scopestack-find-__result__/context
                        ((name stringp)
                         (ss   vl-scopestack-p))
                        :hints (("goal" :expand ((vl-scopestack-fix ss))))
                        :guard-hints (("goal" :expand ((vl-scopestack-p ss))))
                        :returns (mv (__result__ (iff (__resulttype__ __result__) __result__))
                                     (__result__-ss vl-scopestack-p)
                                     (pkg-name (iff (stringp pkg-name) pkg-name)))
                        :measure (vl-scopestack-count ss)
                        (b* ((ss (vl-scopestack-fix ss)))
                          (vl-scopestack-case ss
                            :null (mv nil nil nil)
                            :global (b* (((mv pkg-name __result__)
                                          (vl-scope-find-__result__-fast name ss.design
                                                                         (:@ :import ss.design))))
                                      (mv __result__ (vl-scopestack-fix ss) pkg-name))
                            :local (b* ((:@ :import
                                         (design (vl-scopestack->design ss)))
                                        ((mv pkg-name __result__)
                                         (vl-scope-find-__result__-fast name ss.top (:@ :import design)))
                                        ((when (or pkg-name __result__))
                                         (mv __result__ ss pkg-name)))
                                     (vl-scopestack-find-__result__/context name ss.super)))))

                      (define vl-scopestack-find-__result__
                        :short "Look up a plain identifier in the current scope stack."
                        ((name stringp)
                         (ss   vl-scopestack-p))
                        :returns (__result__ (iff (__resulttype__ __result__) __result__))
                        (b* (((mv __result__ & &) (vl-scopestack-find-__result__/context name ss)))
                          __result__))

                      (define vl-scopestack-find-__result__/ss
                        :short "Look up a plain identifier in the current scope stack."
                        ((name stringp)
                         (ss   vl-scopestack-p))
                        :returns (mv (__result__ (iff (__resulttype__ __result__) __result__))
                                     (__result__-ss vl-scopestack-p))
                        (b* (((mv __result__ context-ss pkg-name)
                              (vl-scopestack-find-__result__/context name ss))
                             ((unless pkg-name) (mv __result__ context-ss))
                             (design (vl-scopestack->design context-ss))
                             (pkg (and design (cdr (hons-get pkg-name (vl-design-scope-package-alist-top design)))))
                             ((unless pkg) ;; this should mean __result__ is already nil
                              (mv __result__ nil))
                             (pkg-ss (vl-scopestack-push pkg (vl-scopestack-init design))))
                          (mv __result__ pkg-ss))))))))
     (acl2::template-subst-fn template (and importsp '(:import)) nil nil nil
                              `(("__RESULT__" ,(symbol-name result) . vl-package)
                                ("__RESULTTYPE__" ,(symbol-name resulttype) . vl-package))
                              'vl-package))))

(make-event
#||
  (define vl-scope-find-item ...)
  (define vl-scope-item-alist ...)
  (define vl-scope-find-item-fast ...)
  (define vl-scopestack-find-item ...)
||#

 (def-vl-scope-find *vl-scopes->items* 'item 'vl-scopeitem-p t t))

(make-event
#||
  (define vl-scope-find-definition ...)
  (define vl-scope-definition-alist ...)
  (define vl-scope-find-definition-fast ...)
  (define vl-scopestack-find-definition ...)
||#
 (def-vl-scope-find *vl-scopes->defs* 'definition 'vl-scopedef-p t nil))

(make-event
#||
  (define vl-scope-find-package ...)
  (define vl-scope-package-alist ...)
  (define vl-scope-find-package-fast ...)
  (define vl-scopestack-find-package ...)
||#
 (def-vl-scope-find *vl-scopes->pkgs* 'package 'vl-package-p t nil))

(make-event
#||
  (define vl-scope-find-portdecl ...)
  (define vl-scope-portdecl-alist ...)
  (define vl-scope-find-portdecl-fast ...)
||#
 (def-vl-scope-find *vl-scopes->portdecls* 'portdecl 'vl-portdecl-p nil nil))




(define vl-scopestacks-free ()
  (progn$ (clear-memoize-table 'vl-scope-item-scopeinfo)
          (clear-memoize-table 'vl-scope-definition-scopeinfo)
          (clear-memoize-table 'vl-scope-package-scopeinfo)
          (clear-memoize-table 'vl-scope-portdecl-scopeinfo)
          (clear-memoize-table 'vl-design-scope-package-alist-top)
          (clear-memoize-table 'vl-package-scope-item-alist-top)))


