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
(include-book "../parsetree")
(local (include-book "tools/templates" :dir :system))
;(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable alistp acl2::alistp-when-keyval-alist-p-rewrite
                           acl2::subsetp-when-atom-right
                           double-containment
                           default-cdr
                           acl2::subsetp-member
                           acl2::str-fix-default
                           (:t member-equal)
                           member-equal
                           default-car
                           consp-when-member-equal-of-vl-gencaselist-p
                           consp-when-member-equal-of-vl-caselist-p
                           consp-when-member-equal-of-vl-commentmap-p
                           ;; consp-when-member-equal-of-vl-atts-p
                           acl2::consp-when-member-equal-of-keyval-alist-p
                           acl2::consp-of-car-when-alistp
                           (tau-system)
                           not
                           )))


; Missing Name Functions ------------------------------------------------------
;
; To keep parsetree.lisp lighter we don't include some of the vl-foolist->names
; style functions.  So, we fill these in to start with.

;; (define vl-blockitem->name ((x vl-blockitem-p))
;;   :parents (vl-blockitem)
;;   :returns (name stringp :rule-classes :type-prescription)
;;   :prepwork ((local (defthm tag-when-vl-blockitem-p
;;                       (implies (vl-blockitem-p x)
;;                                (or (equal (tag x) :vl-vardecl)
;;                                    (equal (tag x) :vl-paramdecl)))
;;                       :rule-classes :forward-chaining))
;;              (local (defthm vl-blockitem-p-of-vl-blockitem-fix-forward
;;                       (vl-blockitem-p (vl-blockitem-fix x))
;;                       :rule-classes ((:forward-chaining :trigger-terms ((vl-blockitem-fix x)))))))
;;   (b* ((x (vl-blockitem-fix x)))
;;     (case (tag x)
;;       (:vl-vardecl (vl-vardecl->name x))
;;       (otherwise   (vl-paramdecl->name x)))))

;; (defprojection vl-blockitemlist->names ((x vl-blockitemlist-p))
;;   :returns (names string-listp)
;;   :parents (vl-blockitemlist-p)
;;   (vl-blockitem->name x))

(defprojection vl-paramdecllist->names ((x vl-paramdecllist-p))
  :returns (names string-listp)
  :parents (vl-paramdecllist-p)
  (vl-paramdecl->name x))

(defprojection vl-portdecllist->names ((x vl-portdecllist-p))
  :returns (names string-listp)
  :parents (vl-portdecllist-p)
  (vl-portdecl->name x))

(defprojection vl-vardecllist->names ((x vl-vardecllist-p))
  :returns (names string-listp)
  :parents (vl-vardecllist-p)
  (vl-vardecl->name x))

(defprojection vl-modportlist->names ((x vl-modportlist-p))
  :returns (names string-listp)
  :parents (vl-modportlist-p)
  (vl-modport->name x))

(defprojection vl-interfaceportlist->names ((x vl-interfaceportlist-p))
  :returns (names string-listp)
  :parents (vl-interfaceportlist-p)
  (vl-interfaceport->name x))

(defprojection vl-dpiimportlist->names ((x vl-dpiimportlist-p))
  :returns (names string-listp)
  :parents (vl-dpiimportlist-p)
  (vl-dpiimport->name x))

(defprojection vl-genvarlist->names ((x vl-genvarlist-p))
  :returns (names string-listp)
  :parents (vl-genvarlist-p)
  (vl-genvar->name x))

(defprojection vl-modinstlist->modnames ((x vl-modinstlist-p))
  :parents (vl-modinstlist-p)
  :short "Collect all module names (not instance names!) from a
          @(see vl-modinstlist-p)."
  :returns (modnames string-listp)
  (vl-modinst->modname x))

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
  :parents (vl-modinstlist-p)
  :short "Collect all instance names (not module names!) from a @(see
vl-modinstlist-p)."
  :long "<p>The Verilog-2005 Standard requires that module instances be named,
but we relaxed that restriction in our definition of @(see vl-modinst-p)
because of user-defined primitives, which may be unnamed.  So, as with @(see
vl-gateinstlist->names), here we simply skip past any unnamed module
instances.</p>"
  :verify-guards nil
  :returns (names string-listp)
  (mbe :logic (if (consp x)
                  (if (vl-modinst->instname (car x))
                      (cons (vl-modinst->instname (car x))
                            (vl-modinstlist->instnames (cdr x)))
                    (vl-modinstlist->instnames (cdr x)))
                nil)
       :exec (if (atom x)
                 nil
               (with-local-nrev (vl-modinstlist->instnames-nrev x nrev))))
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
    :event-name vl-modinstlist->instnames-preserves-list-equiv
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (vl-modinstlist->instnames-of-list-fix))
            :use ((:instance vl-modinstlist->instnames-of-list-fix)
                  (:instance vl-modinstlist->instnames-of-list-fix
                   (x x-equiv))))))

  (defthm vl-modinstlist->instnames-of-append
    (equal (vl-modinstlist->instnames (append x y))
           (append (vl-modinstlist->instnames x)
                   (vl-modinstlist->instnames y))))

  (defthm vl-modinstlist->instnames-of-rev
    (equal (vl-modinstlist->instnames (rev x))
           (rev (vl-modinstlist->instnames x)))))

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
  :parents (vl-gateinstlist-p)
  :short "Collect all instance names declared in a @(see vl-gateinstlist-p)."
  :long "<p>Note that gate instances may be unnamed, in which case we do not
add anything.  In other words, the list of names returned may be shorter than
the number of gate instances in the list.</p>"
  :verify-guards nil
  :returns (names string-listp)
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
    :event-name vl-gateinstlist->names-preserves-list-equiv
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (vl-gateinstlist->names-of-list-fix))
            :use ((:instance vl-gateinstlist->names-of-list-fix (x x))
                  (:instance vl-gateinstlist->names-of-list-fix (x x-equiv))))))

  (defthm vl-gateinstlist->names-of-append
    (equal (vl-gateinstlist->names (append x y))
           (append (vl-gateinstlist->names x)
                   (vl-gateinstlist->names y))))

  (defthm vl-gateinstlist->names-of-rev
    (equal (vl-gateinstlist->names (rev x))
           (rev (vl-gateinstlist->names x)))))

(define vl-genelement->blockname ((x vl-genelement-p))
  :returns (blockname vl-maybe-scopeid-p)
  :parents (vl-genelement-p)
  (vl-genelement-case x
    ;; BOZO should we be harvesting names from other kinds of generates?
    :vl-genbegin (vl-genblock->name x.block)
    :vl-genarray x.name
    :otherwise nil))

(define vl-genelementlist->blocknames-nrev ((x vl-genelementlist-p) nrev)
  :parents (vl-genelementlist->blocknames)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (name (vl-genelement->blockname (car x)))
       (nrev (if (stringp name)
                 (nrev-push name nrev)
               nrev)))
    (vl-genelementlist->blocknames-nrev (cdr x) nrev)))

(define vl-genelementlist->blocknames ((x vl-genelementlist-p))
  :parents (vl-genelementlist-p)
  :short "Collect all resolved block names in a @(see vl-genelementlist-p)."
  :long "<p>Note the elements may be unresolved or may not be blocks at all, in
which case we do not add anything.  In other words, the list of names returned
may be shorter than the number of elements in the list.</p>"
  :verify-guards nil
  :returns (names string-listp)
  (mbe :logic (if (consp x)
                  (if (stringp (vl-genelement->blockname (car x)))
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
           (if (stringp (vl-genelement->blockname a))
               (cons (vl-genelement->blockname a)
                     (vl-genelementlist->blocknames x))
             (vl-genelementlist->blocknames x))))

  (defthm vl-genelementlist->blocknames-of-list-fix
    (equal (vl-genelementlist->blocknames (list-fix x))
           (vl-genelementlist->blocknames x)))

  (defcong list-equiv equal (vl-genelementlist->blocknames x) 1
    :event-name vl-genelementlist->blocknames-preserves-list-equiv
    :hints(("Goal"
            :in-theory (e/d (list-equiv)
                            (vl-genelementlist->blocknames-of-list-fix))
            :use ((:instance vl-genelementlist->blocknames-of-list-fix (x x))
                  (:instance vl-genelementlist->blocknames-of-list-fix (x x-equiv))))))

  (defthm vl-genelementlist->blocknames-of-append
    (equal (vl-genelementlist->blocknames (append x y))
           (append (vl-genelementlist->blocknames x)
                   (vl-genelementlist->blocknames y))))

  (defthm vl-genelementlist->blocknames-of-rev
    (equal (vl-genelementlist->blocknames (rev x))
           (rev (vl-genelementlist->blocknames x)))))


(defxdoc finding-by-name
  :parents (mlib)
  :short "Functions for looking up and reordering parsed objects by their
names."

  :long "<p>These are low-level functions that allow you to find parsed
objects (e.g., variables, modules, parameters) by their names, or to use names
to rearrange lists of objects.</p>

<box><p><b>Note</b>: these functions do not have any proper understanding of
scoping issues.  If you just want to look up a name and see what it refers to,
you should not use these functions; see @(see scopestack) instead.</p></box>

<p>One way to do find elements by name is to naively scan through the list of
items and retrieve the first one that matches the name.  Our simple lookup
functions just do this for various types of objects.  For instance, we provide
functions to \"find a portdecl with the following name in this list of
portdecls.\"</p>

<p>If many items are going to be looked up from the same list, as is often the
case, then a faster approach is to construct a fast alist that maps the item
names to the items themselves, and then use @(see hons-get) to do hash table
lookups.  See @(see fast-finding-by-name) for functions related to constructing
fast alists binding names to items that can be used for this purpose.</p>")

(local (xdoc::set-default-parents finding-by-name))

(defxdoc fast-finding-by-name
  :parents (finding-by-name)
  :short "Utilities for building alists for doing fast-alist lookups.")

(defconst *find-by-name-template*
  ;; Template for defining find functions.
  ;;
  ;; Parameters              Example
  ;; -----------------------------------------------------
  ;;   __find__              vl-find-modinst-by-instname
  ;;   __type__              modinst
  ;;   __name__              instname
  ;;   __element->name__     vl-modinst->instname
  ;;   __list->names__       vl-modinstlist->instnames
  ;;   __suffix__            -by-instname
  ;; -----------------------------------------------------
  ;;
  ;; Features
  ;;
  ;;   :maybe-stringp    --> T if the name may be nil (e.g., modinst->instname),
  ;;                         NIL otherwise (e.g., module->name can't be nil)
  ;;
  ;;   :sum-type         --> T if this is a sum type (suppress tag theorems)
  ;;                         NIL otherwise (prove tag theorems)
  ;;
  ;;   :alist            --> T if you want to introduce alist-based creation
  ;;                         and lookup functions.
  '(progn

     (define __find__
       :parents (finding-by-name vl-__type__list-p)
       :short (cat "Naive, O(n) lookup of a @(see VL-" (symbol-name
                    '__type__) ") in a list by its name.")
       ((name stringp)
        (x    vl-__type__list-p))
       :returns (__type__? (iff (vl-__type__-p __type__?)
                                __type__?)
                           :hints(("Goal" :in-theory (disable (:d __find__))
                                   :induct (__find__ name x)
                                   :expand ((:free (name) (__find__ name x))))))
       :guard-hints (("goal" :in-theory (disable __find__)))
       (cond ((atom x)
              nil)
             ((equal (string-fix name)
                     (__element->name__ (car x)))
              (vl-__type__-fix (car x)))
             (t
              (__find__ name (cdr x))))
       ///
       (local (in-theory (disable (force) (:d __find__))))
       (local (set-default-hints
               '((and (equal (car id) '(0))
                      '(:induct (__find__ name x)
                        :expand ((:free (name) (__find__ name x))))))))

       (defthm __find__-under-iff
         (iff (__find__ name x)
              (member-equal (string-fix name) (__list->names__ x))))

       (defthm __element->name__-of-__find__
         (implies (__find__ name x)
                  (equal (__element->name__ (__find__ name x))
                         (string-fix name))))

       (:@ (not :sum-type)
        (local (defthm tag-when-vl-__type__-p-strong
                 (implies (vl-__type__-p x)
                          (equal (tag x)
                                 :vl-__type__))
                 :hints(("Goal" :in-theory (enable tag-when-vl-__type__-p)))))

        (defthm tag-of-__find__
          (equal (tag (__find__ name x))
                 (if (__find__ name x)
                     :vl-__type__
                   nil))))

       (defthm member-equal-of-__find__
         (implies (force (vl-__type__list-p x))
                  (iff (member-equal (__find__ name x) x)
                       (__find__ name x)))
         :hints (("goal" :induct (__find__ name x)
                  :expand ((:free (name) (__find__ name x))
                           (:free (name) (__find__ name nil))))))

       (defthm consp-of-__find__-when-member-equal
         (implies (and (member-equal name (__list->names__ x))
                       (force (stringp name)))
                  (consp (__find__ name x))))

       ;; BOZO why??
       (local (set-default-hints nil)))


     (:@ :alist

      (encapsulate
        ()
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

        (local (xdoc::set-default-parents fast-finding-by-name))

        (fty::defalist vl-__type__-alist
          :key-type stringp
          :val-type vl-__type__-p
          :keyp-of-nil nil
          :valp-of-nil nil)

        (define vl-__type__list-alist ((x vl-__type__list-p) acc)
          :returns (alist (equal (vl-__type__-alist-p alist)
                                 (vl-__type__-alist-p acc)))
          :short (cat "Extend an alist by binding the names of @(see VL-"
                      (symbol-name '__type__)
                      ")s to their definitions.")
          :long (cat "<p>This can be used as an alternative to @(see " (symbol-name '__find__)
                     ") when you need to perform a lot of lookups.</p>")
          (:@ :maybe-stringp
           (b* (((when (atom x))
                 acc)
                (name (hons-copy (__element->name__ (car x))))
                ((when (stringp name))
                 (cons (cons name (vl-__type__-fix (car x)))
                       (vl-__type__list-alist (cdr x) acc))))
             (vl-__type__list-alist (cdr x) acc)))
          (:@ (not :maybe-stringp)
           (if (atom x)
               acc
             (cons (cons (__element->name__ (car x))
                         (vl-__type__-fix (car x)))
                   (vl-__type__list-alist (cdr x) acc))))
          ///
          ;; (:@ :scopetype
          ;;  (more-returns
          ;;   (alist :name vl-__scopetype__-alist-p-of-vl-__type__list-alist
          ;;          (equal (vl-__scopetype__-alist-p alist)
          ;;                 (vl-__scopetype__-alist-p acc))
          ;;          :hints(("Goal" :in-theory (enable vl-__scopetype__-alist-p))))))
          (defthm lookup-in-vl-__type__list-alist-acc-elim
            (implies (syntaxp (not (equal acc ''nil)))
                     (equal (hons-assoc-equal name (vl-__type__list-alist x acc))
                            (or (hons-assoc-equal name (vl-__type__list-alist x nil))
                                (hons-assoc-equal name acc)))))
          (defthm lookup-in-vl-__type__list-alist-fast
            (implies (stringp name)
                     (equal (hons-assoc-equal name (vl-__type__list-alist x nil))
                            (let ((val (__find__ name x)))
                              (and val
                                   (cons name val)))))
            :hints(("Goal" :in-theory (disable (:d vl-__type__list-alist))
                    :induct (vl-__type__list-alist x nil)
                    :expand ((vl-__type__list-alist x nil)
                             (__find__ name x))))))))

     ))

(defmacro def-vl-finder (type
                         &key
                         (name 'name)
                         (alist 't)
                         find
                         element->name
                         list->names
                         maybe-stringp
                         sum-type)
  (let* ((type          (symbol-name type))
         (name          (symbol-name name))
         (find          (if find          (symbol-name find)          (cat "VL-FIND-" type)))
         (element->name (if element->name (symbol-name element->name) (cat "VL-" type "->NAME")))
         (list->names   (if list->names   (symbol-name list->names)   (cat "VL-" type "LIST->NAMES"))))
    `(make-event
      (template-subst *find-by-name-template*
                      :features (append (and ,sum-type      '(:sum-type))
                                        (and ,maybe-stringp '(:maybe-stringp))
                                        (and ,alist         '(:alist)))
                      :str-alist ',(list (cons "__FIND__"          find)
                                         (cons "__TYPE__"          type)
                                         (cons "__NAME__"          name)
                                         (cons "__ELEMENT->NAME__" element->name)
                                         (cons "__LIST->NAMES__"   list->names))
                      :pkg-sym (pkg-witness "VL")))))

(def-vl-finder module)
(def-vl-finder udp)
(def-vl-finder interface)
(def-vl-finder program)
(def-vl-finder class)
(def-vl-finder package)
(def-vl-finder config)
(def-vl-finder vardecl)
(def-vl-finder taskdecl)
(def-vl-finder fundecl)
(def-vl-finder paramdecl)
(def-vl-finder typedef)
(def-vl-finder dpiimport)
(def-vl-finder genvar)

(def-vl-finder modinst
  :name          instname
  :element->name vl-modinst->instname
  :list->names   vl-modinstlist->instnames
  :maybe-stringp t)

(def-vl-finder gateinst
  :maybe-stringp t)

(def-vl-finder portdecl)

(def-vl-finder modport)
(def-vl-finder interfaceport)

(def-vl-finder genelement
  :name          blockname
  :element->name vl-genelement->blockname
  :list->names   vl-genelementlist->blocknames
  :maybe-stringp t
  :sum-type      t)

;; (def-vl-finder blockitem
;;   :sum-type t)



;; --------------------------- BOZO, compatibility wrappers ------------------------

; Stuff that used to be in find-item.lisp ------------

; These functions were around before we redid the find code... we probably
; don't really need this stuff, but we leave it for now in case old code is
; using it.

(define vl-make-portdecl-alist ((x vl-portdecllist-p))
  :returns (palist vl-portdecl-alist-p :hyp :guard)
  :short "Build a fast alist associating the name of each port declaration with
the whole @(see vl-portdecl-p) object."
  (make-fast-alist (vl-portdecllist-alist x nil))
  ///
  (local (defthm l0
           (implies (alistp acc)
                    (alistp (vl-portdecllist-alist x acc)))
           :hints(("Goal" :in-theory (enable vl-portdecllist-alist)))))

  (defthm alistp-of-vl-make-portdecl-alist
    (alistp (vl-make-portdecl-alist x)))

  (defthm hons-assoc-equal-of-vl-make-portdecl-alist
    (implies (stringp k)
             (equal (hons-assoc-equal k (vl-make-portdecl-alist x))
                    (and (vl-find-portdecl k x)
                         (cons k (vl-find-portdecl k x)))))
    :hints(("Goal" :in-theory (e/d (vl-find-portdecl
                                    vl-portdecllist-alist)
                                   (vl-find-portdecl-under-iff))))))

(define vl-fast-find-portdecl
  ((name      stringp)
   (portdecls vl-portdecllist-p)
   (alist     (equal alist (vl-make-portdecl-alist portdecls))))
  :short "Faster version of @(see vl-find-portdecl), where the search is done
  as an fast-alist lookup rather than as string search."
  :enabled t
  :hooks nil
  (mbe :logic (vl-find-portdecl name portdecls)
       :exec (cdr (hons-get name alist))))




; Compatibility stuff that used to be in find-module.lisp -----------------




; find-module.lisp -- basic functions for looking up modules.
;
; Note: this just includes very basic tools.  See also hierarchy.lisp, which
; includes several others.

(defmacro vl-modalist-p (x)
  `(vl-module-alist-p ,x))

(defmacro vl-modalist-fix (x)
  `(vl-module-alist-fix ,x))


(define vl-modalist
  :short "Legacy. Build a fast alist mapping module names to modules."
  ((mods vl-modulelist-p))
  :returns (modalist vl-module-alist-p)
  (make-fast-alist (vl-modulelist-alist mods nil))
  ///
  (local (in-theory (enable vl-modulelist-alist)))

  (defthm vl-modalist-when-not-consp
    (implies (not (consp x))
             (equal (vl-modalist x)
                    nil)))

  (defthm vl-modalist-of-cons
    (equal (vl-modalist (cons a x))
           (cons (cons (vl-module->name a)
                       (vl-module-fix a))
                 (vl-modalist x))))

  (defthm alistp-of-vl-modalist
    (alistp (vl-modalist x)))

  (defthm strip-cars-of-vl-modalist
    (equal (strip-cars (vl-modalist x))
           (vl-modulelist->names x)))

  (defthm strip-cdrs-of-vl-modalist
    (equal (strip-cdrs (vl-modalist x))
           (vl-modulelist-fix (list-fix x))))

  (defthm hons-assoc-equal-of-vl-modalist
    (implies (stringp name)
             (equal (hons-assoc-equal name (vl-modalist x))
                    (if (vl-find-module name x)
                        (cons name (vl-find-module name x))
                      nil)))))

(define vl-fast-find-module
  :short "Legacy. @(see vl-modalist)-optimized version of @(see vl-find-module)."
  ((name     stringp)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :inline t
  :enabled t
  (mbe :logic (vl-find-module (string-fix name) mods)
       :exec (cdr (hons-get name modalist))))

(deffixequiv vl-find-module)



;; Removing this, preferring use vl-reorder-modules instead.

;; (defprojection vl-find-modules ((x    string-listp)
;;                                 (mods vl-modulelist-p))
;;   (vl-find-module x mods)
;;   :short "Legacy. @(call vl-find-modules) gathers every module in named in
;; @('x') from @('mods') and returns them as a list."

;;   :long "<p>This is a simple projection over @(see vl-find-module), and is our
;; logically simplest way of gathering modules by name.</p>

;; <p>This function is not efficient.  It carries out a linear search over the
;; module list for each module in @('x'), making it quadratic.  For better
;; performance, see @(see vl-fast-find-modules).</p>")

;; (define vl-fast-find-modules
;;   :short "@(see vl-modalist)-optimized version of @(see vl-find-modules)."
;;   ((x        string-listp)
;;    (mods     vl-modulelist-p)
;;    (modalist (equal modalist (vl-modalist mods))))
;;   :enabled t
;;   (mbe :logic (vl-find-modules x mods)
;;        :exec (if (atom x)
;;                  nil
;;                (cons (vl-fast-find-module (car x) mods modalist)
;;                      (vl-fast-find-modules (cdr x) mods modalist)))))
