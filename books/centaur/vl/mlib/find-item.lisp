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
(include-book "modnamespace")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection find-item
  :parents (mlib)
  :short "Functions for looking up module items (e.g., nets, ports, registers,
etc.) within a module."

  :long "<p>We often need to look up a module item (i.e., a net or port or
register declaration) inside of a module by name.</p>

<p>One way to do this is to naively scan through the module's items and stop at
the first one that matches the name.  We provide a number of routines for doing
this, for particular types of items (e.g., \"find a portdecl with the following
name\"), and also for any arbitrary item in the namespace.</p>

<p>If many items are going to be looked up from the same module, as is often
the case, then a faster approach is to construct a fast-alist that maps the
item names to their items, and scan through it.  We provide a mechanism for
making this alist and for using it to do lookups, and prove that it is
equivalent to the naive method of doing lookups.</p>")

(local (xdoc::set-default-parents find-item))

(defmacro def-vl-find-moditem (type
                               &key
                               element->name
                               list->names
                               names-may-be-nil)

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
       :returns (,type? (equal (,element-p ,type?)
                               (if ,type?
                                   t
                                 nil)))
       (cond ((atom x)
              nil)
             ((equal name (,element->name (car x)))
              (,fix (car x)))
             (t
              (,fn name (cdr x))))
       ///
       (local (in-theory (disable (force))))

       (defthm ,(mksym fn '-under-iff)
         (implies ,(if names-may-be-nil
                       '(force (stringp name))
                     t)
                  (iff (,fn name x)
                       (member-equal name (,list->names x)))))

       (defthm ,(mksym element->name '-of- fn)
         (implies (,fn name x)
                  (equal (,element->name (,fn name x))
                         name)))

       (defthm ,(mksym 'tag-of- fn)
         (equal (tag (,fn name x))
                (if (,fn name x)
                    ,tag
                  nil)))

       (defthm ,(mksym 'member-equal-of- fn)
         (implies (force (,list-p x))
                  (iff (member-equal (,fn name x) x)
                       (,fn name x))))

       (defthm ,(mksym 'consp-of- fn '-when-member-equal)
         (implies (and (member-equal name (,list->names x))
                       (force (stringp name)))
                  (consp (,fn name x)))))))

(def-vl-find-moditem portdecl)


(defalist vl-portdecl-alist-p (x)
  :key (stringp x)
  :val (vl-portdecl-p x)
  :keyp-of-nil nil
  :valp-of-nil nil)

(define vl-portdecl-alist ((x vl-portdecllist-p))
  :returns (palist vl-portdecl-alist-p :hyp :guard)
  :short "Build a fast alist associating the name of each port declaration with
the whole @(see vl-portdecl-p) object."
  (if (atom x)
      nil
    (hons-acons (vl-portdecl->name (car x))
                (vl-portdecl-fix (car x))
                (vl-portdecl-alist (cdr x))))
  ///
  (defthm alistp-of-vl-portdecl-alist
    (alistp (vl-portdecl-alist x)))

  (defthm hons-assoc-equal-of-vl-portdecl-alist
    (equal (hons-assoc-equal k (vl-portdecl-alist x))
           (and (vl-find-portdecl k x)
                (cons k (vl-find-portdecl k x))))
    :hints(("Goal" :in-theory (e/d (vl-find-portdecl)
                                   (vl-find-portdecl-under-iff))))))

(define vl-fast-find-portdecl
  ((name      stringp)
   (portdecls vl-portdecllist-p)
   (alist     (equal alist (vl-portdecl-alist portdecls))))
  :short "Faster version of @(see vl-find-portdecl), where the search is done
  as an fast-alist lookup rather than as string search."
  :enabled t
  :hooks nil
  (mbe :logic (vl-find-portdecl name portdecls)
       :exec (cdr (hons-get name alist))))


(define vl-portdecllist-names-by-direction
  ((x vl-portdecllist-p)
   (in string-listp)
   (out string-listp)
   (inout string-listp))
  :parents (vl-portdecllist-p)
  :returns (mv (in string-listp)
               (out string-listp)
               (inout string-listp))
  (b* (((when (atom x))
        (mv (string-list-fix in)
            (string-list-fix out)
            (string-list-fix inout)))
       (decl (car x))
       (name (vl-portdecl->name decl))
       (dir  (vl-portdecl->dir decl)))
    (case dir
      (:vl-input  (vl-portdecllist-names-by-direction (cdr x) (cons name in) out inout))
      (:vl-output (vl-portdecllist-names-by-direction (cdr x) in (cons name out) inout))
      (:vl-inout  (vl-portdecllist-names-by-direction (cdr x) in out (cons name inout)))
      (otherwise  (progn$ (raise "Impossible")
                          (mv nil nil nil))))))


(def-vl-find-moditem vardecl)
(def-vl-find-moditem netdecl)
(def-vl-find-moditem paramdecl)
(def-vl-find-moditem fundecl)
(def-vl-find-moditem taskdecl)

(def-vl-find-moditem modinst
  :element->name vl-modinst->instname
  :list->names   vl-modinstlist->instnames
  :names-may-be-nil t)

(def-vl-find-moditem gateinst
  :names-may-be-nil t)



(define vl-find-moduleitem
  :short "A (naive) lookup operation that can find any name in the module's namespace."

  :long "<p>This is our main, naive spec for what it means to look up a name in
a module's namespace.  Note that we don't look for port declarations!  (But
typically this <i>will</i> find the corresponding net/reg declaration for a
port.)</p>

<p>Typically you will want to use @(see vl-fast-find-moduleitem) when looking
up multiple items.</p>"

  ((name stringp)
   (x    vl-module-p))

  :returns item?
  :hooks ((:fix :args ((x vl-module-p))))

  (b* (((vl-module x) x))
    (or (vl-find-netdecl   name x.netdecls)
        (vl-find-vardecl   name x.vardecls)
        (vl-find-paramdecl name x.paramdecls)
        (vl-find-fundecl   name x.fundecls)
        (vl-find-taskdecl  name x.taskdecls)
        (vl-find-modinst   name x.modinsts)
        (vl-find-gateinst  name x.gateinsts)))

  ///

  (defthm vl-find-moduleitem-type-when-nothing-else
    (implies (and (vl-find-moduleitem name x)
                  (not (vl-netdecl-p   (vl-find-moduleitem name x)))
                  (not (vl-vardecl-p   (vl-find-moduleitem name x)))
                  (not (vl-paramdecl-p (vl-find-moduleitem name x)))
                  (not (vl-fundecl-p   (vl-find-moduleitem name x)))
                  (not (vl-taskdecl-p  (vl-find-moduleitem name x)))
                  (not (vl-modinst-p   (vl-find-moduleitem name x))))
             (vl-gateinst-p (vl-find-moduleitem name x)))
    :hints(("Goal" :in-theory (enable vl-find-moduleitem)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm type-of-vl-find-moduleitem
    ;; This is gross, but I'm not sure of a better approach.
    (and (equal (equal (tag (vl-find-moduleitem name x)) :vl-netdecl)
                (vl-netdecl-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-vardecl)
                (vl-vardecl-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-paramdecl)
                (vl-paramdecl-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-fundecl)
                (vl-fundecl-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-taskdecl)
                (vl-taskdecl-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-modinst)
                (vl-modinst-p (vl-find-moduleitem name x)))

         (equal (equal (tag (vl-find-moduleitem name x)) :vl-gateinst)
                (vl-gateinst-p (vl-find-moduleitem name x))))
    :hints(("Goal"
            :in-theory (e/d (tag-reasoning)
                            (vl-find-moduleitem
                             vl-find-moduleitem-type-when-nothing-else))
            :use ((:instance vl-find-moduleitem-type-when-nothing-else)))))

  (defthm consp-of-vl-find-moduleitem
    (equal (consp (vl-find-moduleitem name x))
           (if (vl-find-moduleitem name x)
               t
             nil))
    :hints(("Goal"
            :in-theory (disable vl-find-moduleitem-type-when-nothing-else)
            :use ((:instance vl-find-moduleitem-type-when-nothing-else)))))

  (defthm vl-find-moduleitem-when-in-namespace
    (implies (member-equal name (vl-module->modnamespace x))
             (vl-find-moduleitem name x))
    :hints(("Goal" :in-theory (enable vl-module->modnamespace vl-find-moduleitem)))))




; FAST-ALIST BASED LOOKUPS ----------------------------------------------------

(deftranssum vl-moditem
  :short "Module items are basically any named object that can occur within a
module (except that we don't support, e.g., named blocks.)"
  (vl-netdecl
   vl-vardecl
   vl-paramdecl
   vl-fundecl
   vl-taskdecl
   vl-modinst
   vl-gateinst))

(fty::deflist vl-moditemlist
  :elt-type vl-moditem-p)

(deflist vl-moditemlist-p (x)
  (vl-moditem-p x)
  :elementp-of-nil nil)

(xdoc::without-xdoc
  (fty::defalist vl-moditem-alist
    :key-type stringp
    :val-type vl-moditem-p))

(defalist vl-moditem-alist-p (x)
  :key (stringp x)
  :val (vl-moditem-p x)
  :keyp-of-nil nil
  :valp-of-nil nil
  :already-definedp t
  :guard t)


(defmacro vl-def-moditemlist-alist (type &key
                                         element->name
                                         names-may-be-nil)
  (let* ((mksym-package-symbol 'vl::foo)

         (fn            (mksym 'vl- type 'list-alist))
         (fast-fn       (mksym 'vl-fast- type 'list-alist))
         (find-fn       (mksym 'vl-find- type))
         (list-p        (mksym 'vl- type 'list-p))
         (alist-p       (mksym 'vl- type 'alist-p))
         (elt-p         (mksym 'vl- type '-p))
         (elt-fix       (mksym 'vl- type '-fix))
         (element->name (or element->name (mksym 'vl- type '->name))))
    `(encapsulate
       ()
       (xdoc::without-xdoc
         (fty::defalist ,alist-p
           :key-type stringp
           :val-type ,elt-p))

       (defalist ,alist-p (x)
         :key (stringp x)
         :val (,elt-p x)
         :keyp-of-nil nil
         :valp-of-nil nil)

       (define ,fast-fn ((x ,list-p) acc)
         :parents (,fn)
         (if (consp x)
             ,(if names-may-be-nil
                  `(let ((name (,element->name (car x))))
                     (if name
                         (hons-acons name
                                     (,elt-fix (car x))
                                     (,fast-fn (cdr x) acc))
                       (,fast-fn (cdr x) acc)))
                `(hons-acons (,element->name (car x))
                             (,elt-fix (car x))
                             (,fast-fn (cdr x) acc)))
           acc))

       (define ,fn ((x ,list-p))
         :verify-guards nil
         :short "Construct a fast alist binding names to items."
         :returns (fast-alist ,alist-p :hyp :fguard)
         (mbe :logic (if (consp x)
                         ,(if names-may-be-nil
                              `(let ((name (,element->name (car x))))
                                 (if name
                                     (cons (cons name (,elt-fix (car x)))
                                           (,fn (cdr x)))
                                   (,fn (cdr x))))
                            `(cons (cons (,element->name (car x))
                                         (,elt-fix (car x)))
                                   (,fn (cdr x))))
                       nil)
              :exec (,fast-fn x nil))
         ///
         (defthm ,(mksym 'vl-moditem-alist-p-of- fn)
           (vl-moditem-alist-p (,fn x))
           :hints(("Goal" :in-theory (enable vl-moditem-p))))

         (defthm ,(mksym 'hons-assoc-equal-of- fn)
           (implies ,(if names-may-be-nil
                         '(force (stringp name))
                       t)
                    (equal (hons-assoc-equal name (,fn x))
                           (if (,find-fn name x)
                               (cons name (,find-fn name x))
                             nil)))
           :hints(("Goal" :in-theory (enable ,find-fn)))))

       (defsection ,(mksym fast-fn '-removal)
         :extension ,fast-fn

         (local (in-theory (enable ,fn ,fast-fn)))

         (defthm ,(mksym fast-fn '-removal)
           (equal (,fast-fn x acc)
                  (append (,fn x) acc)))

         (verify-guards ,fn)))))

(vl-def-moditemlist-alist netdecl)
(vl-def-moditemlist-alist vardecl)
(vl-def-moditemlist-alist paramdecl)
(vl-def-moditemlist-alist fundecl)
(vl-def-moditemlist-alist taskdecl)
(vl-def-moditemlist-alist modinst
                          :element->name vl-modinst->instname
                          :names-may-be-nil t)
(vl-def-moditemlist-alist gateinst :names-may-be-nil t)


(define vl-moditem-alist ((x vl-module-p))
  :short "Main routine for building an fast alist for looking up module items."

  :long "<p>Note that the alist is constructed in is particularly important: we
want it to agree, completely, with the naive @(see vl-find-moduleitem).  The
alist can be constructed in a one pass, using our fast builder functions.</p>"

  (b* (((vl-module x) x))
    (mbe :logic
         (append (vl-netdecllist-alist x.netdecls)
                 (vl-vardecllist-alist x.vardecls)
                 (vl-paramdecllist-alist x.paramdecls)
                 (vl-fundecllist-alist x.fundecls)
                 (vl-taskdecllist-alist x.taskdecls)
                 (vl-modinstlist-alist x.modinsts)
                 (vl-gateinstlist-alist x.gateinsts))
         :exec
         ;; Reverse order from the above
         (b* ((acc (vl-fast-gateinstlist-alist x.gateinsts nil))
              (acc (vl-fast-modinstlist-alist x.modinsts acc))
              (acc (vl-fast-taskdecllist-alist x.taskdecls acc))
              (acc (vl-fast-fundecllist-alist x.fundecls acc))
              (acc (vl-fast-paramdecllist-alist x.paramdecls acc))
              (acc (vl-fast-vardecllist-alist x.vardecls acc)))
           (vl-fast-netdecllist-alist x.netdecls acc))))
  ///
  (defthm vl-moditem-alist-p-of-vl-moditem-alist
    (vl-moditem-alist-p (vl-moditem-alist x)))

  (defthm hons-assoc-equal-of-vl-moditem-alist
    (implies (force (stringp name))
             (equal (hons-assoc-equal name (vl-moditem-alist x))
                    (if (vl-find-moduleitem name x)
                        (cons name (vl-find-moduleitem name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-moduleitem)))))


(define vl-fast-find-moduleitem
  ((name stringp)
   (x    vl-module-p)
   (itemalist (equal itemalist (vl-moditem-alist x))))
  :short "Alternative to @(see vl-find-moduleitem) using fast alist lookups."
  :enabled t
  :hooks nil
  (mbe :logic (vl-find-moduleitem name x)
       :exec (cdr (hons-get name itemalist))))

