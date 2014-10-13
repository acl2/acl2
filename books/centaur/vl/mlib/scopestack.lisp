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


;; NOTE: This constant controls most of the rest of the file by defining what
;; scope types exist and what types of named items are contained in each of
;; them.  Keyword arguments on items account for various kinds of departures
;; from convention:
;; -- :name foo denotes that the accessor for the name of the item is
;;         vl-itemtype->foo, rather than the default vl-itemtype->name.
;; -- :acc foo denotes that the accessor for the items within the scope is
;;         vl-scopetype->foo, rather than the default vl-scopetype->items.
;; -- :names-defined t denotes that the projection vl-itemlist->names is
;;         already defined (and the one we produce by default might not be
;;         redundant).
;; -- :maybe-stringp t denotes that the name accessor might return nil, rather
;;         than a string.
(local (defconst *vl-scopes->items*
          ;; scope type      has item types or (type acc-name)
         '((interface        paramdecl vardecl modport)
           (module           paramdecl vardecl fundecl taskdecl 
                             (modinst :name instname :maybe-stringp t
                                      :names-defined t))
           ;; fwdtypedefs could be included here but we hope to have resolved them all
           ;; to proper typedefs by the end of loading.
           (fundecl          (blockitem :acc decls :sum-type t))
           (design           paramdecl vardecl fundecl taskdecl typedef)
           (package          ))))

(local (defconst *vl-scopes->defs*
          ;; scope type      has item types or (type acc-name)
         '((interface        )
           (module           )
           (design           (module :acc mods) udp interface program)
           (package          ))))

(local (defconst *vl-scopes->pkgs*
          ;; scope type      has item types or (type acc-name)
         '((interface        )
           (module           )
           (design           package)
           (package          ))))

(local (defconst *vl-scopes->portdecls*
          ;; scope type      has item types or (type acc-name)
         '((interface        portdecl)
           (module           portdecl)
           (design           )
           (package          ))))


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




(local
 (defsection-progn template-substitution-helpers

   (std::def-primitive-aggregate tmplsubst
     (features atomsubst strsubst))

   (defun scopes->typeinfos (scopes)
     (declare (xargs :mode :program))
     (if (atom scopes)
         nil
       (union-equal (cdar scopes)
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
                  (sum-type      (cadr (assoc-keyword :sum-type      kwds))))
               (make-tmplsubst :features (append (and maybe-stringp '(:maybe-stringp))
                                                 (and names-defined '(:names-defined))
                                                 (and sum-type      '(:sum-type)))
                               :strsubst
                               `(("__TYPE__" ,(symbol-name type) . vl-package)
                                 ("__ACC__" ,acc . vl-package)
                                 ("__NAME__" ,name . vl-package))))
             (typeinfos->tmplsubsts (cdr typeinfos)))))

   (defun scopes->tmplsubsts (scopes)
     (if (atom scopes)
         nil
       (cons (make-tmplsubst :strsubst `(("__TYPE__" ,(symbol-name (caar scopes)) . vl-package))
                             :atomsubst `((__items__ . ,(cdar scopes)))
                             :features (and (cdar scopes) '(:has-items)))
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


(make-event ;; Definition of vl-scopeitem type
 (let ((substs (typeinfos->tmplsubsts (remove-equal '(blockitem :acc decls)
                                                    (scopes->typeinfos *vl-scopes->items*)))))
   `(progn
      (deftranssum vl-scopeitem
        :short "Recognizer for an syntactic element that can occur within a scope."
        ,(template-append '((:@ (not :sum-type) vl-__type__)) substs))

      ,@(template-append
         '((:@ :sum-type
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
              `((defthm ,(mksym 'tag-of- fn)
                  (equal (tag (,fn name x))
                         (if (,fn name x)
                             ,tag
                           nil)))))

       (defthm ,(mksym 'member-equal-of- fn)
         (implies (force (,list-p x))
                  (iff (member-equal (,fn name x) x)
                       (,fn name x))))

       (defthm ,(mksym 'consp-of- fn '-when-member-equal)
         (implies (and (member-equal name (,list->names x))
                       (force (stringp name)))
                  (consp (,fn name x))))

       (local (set-default-hints nil)))))

(local
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

      (define vl-fast-__type__list-alist ((x vl-__type__list-p)
                                          acc)
        (if (consp x)
            (:@ :maybe-stringp
             (let ((name (vl-__type__->__name__ (car x))))
               (if name
                   (hons-acons name
                               (vl-__type__-fix (car x))
                               (vl-fast-__type__list-alist (cdr x) acc))
                 (vl-fast-__type__list-alist (cdr x) acc))))
             (:@ (not :maybe-stringp)
              (hons-acons (vl-__type__->__name__ (car x))
                          (vl-__type__-fix (car x))
                          (vl-fast-__type__list-alist (cdr x) acc)))
          acc)
        ///
        (defthm lookup-in-vl-__type__list-alist-fast
          (implies (stringp name)
                   (equal (hons-assoc-equal name (vl-fast-__type__list-alist x acc))
                          (let ((val (vl-find-__type__ name x)))
                            (if val
                                (cons name val)
                              (hons-assoc-equal name acc)))))
          :hints(("Goal" :in-theory (disable (:d vl-fast-__type__list-alist))
                  :induct (vl-fast-__type__list-alist x acc)
                  :expand ((vl-fast-__type__list-alist x acc)
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
                           not)))

(make-event ;; Definition of scopeitem alists/finders
 (b* ((substs (typeinfos->tmplsubsts (scopes->typeinfos (append *vl-scopes->items*
                                                                *vl-scopes->defs*
                                                                *vl-scopes->pkgs*
                                                                *vl-scopes->portdecls*))))
      (events (template-proj *scopeitem-alist/finder-template* substs)))
   `(progn . ,events)))

(local
 (defun def-scopetype-find (scope itemtypes resultname resulttype)
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
               :returns (item (iff (__resulttype__ item) item))
               (b* (((vl-__scope__ scope))
                    (?name (string-fix name)))
                 (or . ,(template-proj
                         '(vl-find-__type__ name scope.__acc__)
                         substs))))

             (define vl-__scope__-scope-__result__-alist
               :parents (vl-scope-find)
               :ignore-ok t
               ((scope vl-__scope__-p))
               :returns (alist)
               (b* (((vl-__scope__ scope))
                    (acc nil)
                    . ,(reverse
                        (template-proj
                         '(acc (vl-fast-__type__list-alist scope.__acc__ acc))
                         substs)))
                 acc)
               ///
               (local (in-theory (enable vl-__scope__-scope-find-__result__)))
               (defthm vl-__scope__-scope-__result__-alist-correct
                 (implies (stringp name)
                          (equal (hons-assoc-equal name (vl-__scope__-scope-__result__-alist scope))
                                 (if (vl-__scope__-scope-find-__result__ name scope)
                                     (cons name (vl-__scope__-scope-find-__result__ name scope))
                                   nil))))))))
     (acl2::template-subst-fn template nil nil nil nil
                              `(("__SCOPE__" ,(symbol-name scope) . vl-package)
                                ("__RESULT__" ,(symbol-name resultname) . vl-package)
                                ("__RESULTTYPE__" ,(symbol-name resulttype) . vl-package))
                              'vl-package))))

(make-event ;; Definition of scopetype-find and -fast-alist functions
 (b* ((substs (scopes->tmplsubsts *vl-scopes->items*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__ '__items__ 'item 'vl-scopeitem-p))
               substs))))

(make-event ;; Definition of scopetype-find and -fast-alist functions
 (b* ((substs (scopes->tmplsubsts *vl-scopes->defs*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__ '__items__ 'definition 'vl-scopedef-p))
               substs))))

(make-event ;; Definition of scopetype-find and -fast-alist functions
 (b* ((substs (scopes->tmplsubsts *vl-scopes->pkgs*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__ '__items__ 'package 'vl-package-p))
               substs))))

(make-event ;; Definition of scopetype-find and -fast-alist functions
 (b* ((substs (scopes->tmplsubsts *vl-scopes->portdecls*)))
   `(progn . ,(template-proj
               '(make-event
                 (def-scopetype-find '__type__ '__items__ 'portdecl 'vl-portdecl-p))
               substs))))


(define vl-scopestack-p (x)
  (if (atom x)
      t
    (and (vl-scope-p (car x))
         (vl-scopestack-p (cdr x)))))

(define vl-scopestack-fix ((x vl-scopestack-p))
  :returns (new-x vl-scopestack-p)
  :hooks nil
  :inline t
  (mbe :logic (if (vl-scopestack-p x)
                  x
                nil)
       :exec x)
  ///
  (defthm vl-scopestack-fix-when-vl-scopestack-p
    (implies (vl-scopestack-p x)
             (equal (vl-scopestack-fix x) x)))

  (fty::deffixtype vl-scopestack :pred vl-scopestack-p :fix vl-scopestack-fix
    :equiv vl-scopestack-equiv :define t :forward t))

(define vl-scopestack-push ((scope vl-scope-p)
                            (ss    vl-scopestack-p))
  :returns (new-ss vl-scopestack-p)
  :prepwork ((local (in-theory (enable vl-scopestack-p))))
  (cons (vl-scope-fix scope)
        (vl-scopestack-fix ss)))



(local (defun def-vl-scope-find (table result resulttype stackp)
         (declare (xargs :mode :program))
         (b* ((substs (scopes->tmplsubsts table))
              (template
                `(progn
                   (define vl-scope-find-__result__
                     :short "Look up a plain identifier to find an __result__ in a scope."
                     ((name  stringp)
                      (scope vl-scope-p))
                     :returns (__result__ (iff (__resulttype__ __result__) __result__))
                     (b* ((scope (vl-scope-fix scope)))
                       (case (tag scope)
                         ,@(template-append '((:@ :has-items (:vl-__type__ (vl-__type__-scope-find-__result__ name scope)))) substs)
                         (otherwise nil))))


                   (define vl-scope-__result__-alist
                     :short "Make a fast lookup table for __result__s in a scope.  Memoized."
                     ((scope vl-scope-p))
                     :returns (alist)
                     (b* ((scope (vl-scope-fix scope)))
                       (case (tag scope)
                         ,@(template-append '((:@ :has-items (:vl-__type__ (vl-__type__-scope-__result__-alist scope)))) substs)
                         (otherwise nil)))
                     ///
                     (local (in-theory (enable vl-scope-find-__result__)))
                     (defthm vl-scope-__result__-alist-correct
                       (implies (stringp name)
                                (equal (hons-assoc-equal name (vl-scope-__result__-alist scope))
                                       (if (vl-scope-find-__result__ name scope)
                                           (cons name (vl-scope-find-__result__ name scope))
                                         nil))))

                     (memoize 'vl-scope-__result__-alist))

                   (define vl-scope-find-__result__-fast
                     :short "Like @(see vl-scope-find-__result__), but uses a fast lookup table"
                     ((name stringp)
                      (scope vl-scope-p))
                     :enabled t
                     (mbe :logic (vl-scope-find-__result__ name scope)
                          :exec (cdr (hons-get name (vl-scope-__result__-alist scope)))))

                   ,@(and stackp
                          `((define vl-scopestack-find-__result__
                              :short "Look up a plain identifier in the current scope stack."
                              ((name stringp)
                               (ss   vl-scopestack-p))
                              :hints (("goal" :expand ((vl-scopestack-fix ss))))
                              :guard-hints (("goal" :expand ((vl-scopestack-p ss))))
                              :returns (__result__ (iff (__resulttype__ __result__) __result__))
                              (b* ((ss (vl-scopestack-fix ss)))
                                (if (atom ss)
                                    nil
                                  (or (vl-scope-find-__result__-fast name (car ss))
                                      (vl-scopestack-find-__result__ name (cdr ss))))))

                            (define vl-scopestack-find-__result__/ss
                              :short "Look up a plain identifier in the current scope stack."
                              ((name stringp)
                               (ss   vl-scopestack-p))
                              :hints (("goal" :expand ((vl-scopestack-fix ss))))
                              :guard-hints (("goal" :expand ((vl-scopestack-p ss))))
                              :returns (mv (__result__ (iff (__resulttype__ __result__) __result__))
                                           (ss vl-scopestack-p))
                              (b* ((ss (vl-scopestack-fix ss)))
                                (if (atom ss)
                                    (mv nil nil)
                                  (let ((res (vl-scope-find-__result__-fast name (car ss))))
                                    (if res
                                        (mv res ss)
                                      (vl-scopestack-find-__result__/ss name (cdr ss))))))))))))
           (acl2::template-subst-fn template nil nil nil nil
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

 (def-vl-scope-find *vl-scopes->items* 'item 'vl-scopeitem-p t))

(make-event
#||
  (define vl-scope-find-definition ...)
  (define vl-scope-definition-alist ...)
  (define vl-scope-find-definition-fast ...)
  (define vl-scopestack-find-definition ...)
||#
 (def-vl-scope-find *vl-scopes->defs* 'definition 'vl-scopedef-p t))

(make-event
#||
  (define vl-scope-find-package ...)
  (define vl-scope-package-alist ...)
  (define vl-scope-find-package-fast ...)
  (define vl-scopestack-find-package ...)
||#
 (def-vl-scope-find *vl-scopes->pkgs* 'package 'vl-package-p t))

(make-event
#||
  (define vl-scope-find-portdecl ...)
  (define vl-scope-portdecl-alist ...)
  (define vl-scope-find-portdecl-fast ...)
||#
 (def-vl-scope-find *vl-scopes->portdecls* 'portdecl 'vl-portdecl-p nil))



(define vl-scopestack-init
  :short "Create an initial scope stack for an entire design."
  ((design vl-design-p))
  :returns (ss vl-scopestack-p)
  :prepwork ((local (in-theory (enable vl-scopestack-p))))
  (list (vl-design-fix design)))

(define vl-scopestacks-free ()
  (progn$ (clear-memoize-table 'vl-scope-item-alist)
          (clear-memoize-table 'vl-scope-definition-alist)
          (clear-memoize-table 'vl-scope-package-alist)
          (clear-memoize-table 'vl-scope-portdecl-alist)))
