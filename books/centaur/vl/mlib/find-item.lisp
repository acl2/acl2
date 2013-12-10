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
(include-book "modnamespace")
(local (include-book "../util/arithmetic"))


;                           FINDING MODULE ITEMS
;
; We often need to look up a module item (i.e., a net or port or register
; declaration) inside of a module by name.
;
; One way to do this is to naively scan through the module's items and stop at
; the first one that matches the name.  We provide a number of routines for
; doing this, for particular types of items (e.g., "find a portdecl with the
; following name"), and also for any arbitrary item in the namespace.
;
; If many items are going to be looked up from the same module, as is often the
; case, then a faster approach is to construct a fast-alist that maps the item
; names to their items, and scan through it.  We provide a mechanism for making
; this alist and for using it to do lookups, and prove that it is equivalent to
; the naive method of doing lookups.

(defmacro def-vl-find-moditem (type
                               &key
                               element->name
                               list->names
                               names-may-be-nil)

  (let* ((mksym-package-symbol 'vl::foo)
         (fn            (mksym 'vl-find- type))
         (element-p     (mksym 'vl- type '-p))
         (tag           (intern (cat "VL-" (symbol-name type)) "KEYWORD"))
         (list-p        (mksym 'vl- type 'list-p))
         (element->name (or element->name
                            (mksym 'vl- type '->name)))
         (list->names   (or list->names
                            (mksym 'vl- type 'list->names))))

    `(defsection ,fn

       (defund ,fn (name x)
         (declare (xargs :guard (and (stringp name)
                                     (,list-p x))))
         (cond ((atom x)
                nil)
               ((equal name (,element->name (car x)))
                (car x))
               (t
                (,fn name (cdr x)))))

       (local (in-theory (e/d (,fn) ((force)))))

       (defthm ,(mksym fn '-under-iff)
         (implies (and (force (,list-p x))
                       ,(if names-may-be-nil
                            '(force (stringp name))
                          t))
                  (iff (,fn name x)
                       (member-equal name (,list->names x)))))

       (defthm ,(mksym element-p '-of- fn)
         (implies (force (,list-p x))
                  (equal (,element-p (,fn name x))
                         (if (,fn name x)
                             t
                           nil))))

       (defthm ,(mksym element->name '-of- fn)
         (equal (,element->name (,fn name x))
                (and (,fn name x)
                     name)))

       (defthm ,(mksym 'tag-of- fn)
         (implies (force (,list-p x))
                  (equal (tag (,fn name x))
                         (if (,fn name x)
                             ,tag
                           nil))))

       (defthm ,(mksym 'member-equal-of- fn)
         (implies (force (,list-p x))
                  (iff (member-equal (,fn name x) x)
                       (,fn name x))))

       (defthm ,(mksym 'consp-of- fn '-when-member-equal)
         (implies (and (member-equal name (,list->names x))
                       (force (,list-p x)))
                  (consp (,fn name x)))))))

(def-vl-find-moditem portdecl)


(defsection vl-fast-find-portdecl

  (defund vl-portdecl-alist (x)
    ;; Build a fast alist associating the name of each port declaration with
    ;; the whole vl-portdecl-p object.
    (declare (xargs :guard (vl-portdecllist-p x)))
    (if (consp x)
        (hons-acons (vl-portdecl->name (car x))
                    (car x)
                    (vl-portdecl-alist (cdr x)))
      nil))

  (local (in-theory (enable vl-portdecl-alist)))

  (defthm alistp-of-vl-portdecl-alist
    (alistp (vl-portdecl-alist x)))

  (defalist vl-portdecl-alist-p (x)
    :key (stringp x)
    :val (vl-portdecl-p x)
    :keyp-of-nil nil
    :valp-of-nil nil)

  (defthm hons-assoc-equal-of-vl-portdecl-alist
    (implies (force (vl-portdecllist-p x))
             (equal (hons-assoc-equal k (vl-portdecl-alist x))
                    (and (vl-find-portdecl k x)
                         (cons k (vl-find-portdecl k x)))))
    :hints(("Goal" :in-theory (e/d (vl-find-portdecl)
                                   (vl-find-portdecl-under-iff)))))


  (defthm vl-portdecl-alist-p-of-vl-portdecl-alist
    (implies (vl-portdecllist-p portdecls)
             (vl-portdecl-alist-p (vl-portdecl-alist portdecls))))

  (defun vl-fast-find-portdecl (name portdecls alist)
    ;; This is just a faster version of vl-find-portdecl, where the search is
    ;; done as an fast-alist lookup rather than as string search.
    (declare (xargs :guard (and (stringp name)
                                (vl-portdecllist-p portdecls)
                                (equal alist (vl-portdecl-alist portdecls)))
                    :verify-guards nil))
    (mbe :logic (vl-find-portdecl name portdecls)
         :exec (cdr (hons-get name alist))))

  (verify-guards vl-fast-find-portdecl))



(defsection vl-portdecllist-names-by-direction

  (defund vl-portdecllist-names-by-direction (x in out inout)
    (declare (xargs :guard (and (vl-portdecllist-p x)
                                (string-listp in)
                                (string-listp out)
                                (string-listp inout))))
    (if (atom x)
        (mv in out inout)
      (let* ((decl (car x))
             (name (vl-portdecl->name decl))
             (dir  (vl-portdecl->dir decl)))
        (case dir
          (:vl-input  (vl-portdecllist-names-by-direction (cdr x) (cons name in) out inout))
          (:vl-output (vl-portdecllist-names-by-direction (cdr x) in (cons name out) inout))
          (:vl-inout  (vl-portdecllist-names-by-direction (cdr x) in out (cons name inout)))
          (otherwise  (prog2$
                       (er hard? 'vl-portdecllist-names-by-direction "Impossible")
                       (mv nil nil nil)))))))

  (local (in-theory (enable vl-portdecllist-names-by-direction)))

  (defthm string-listp-of-vl-portdecllist-names-by-direction-0
    (implies (and (force (vl-portdecllist-p x))
                  (force (string-listp in)))
             (string-listp (mv-nth 0 (vl-portdecllist-names-by-direction x in out inout)))))

  (defthm string-listp-of-vl-portdecllist-names-by-direction-1
    (implies (and (force (vl-portdecllist-p x))
                  (force (string-listp out)))
             (string-listp (mv-nth 1 (vl-portdecllist-names-by-direction x in out inout)))))

  (defthm string-listp-of-vl-portdecllist-names-by-direction-2
    (implies (and (force (vl-portdecllist-p x))
                  (force (string-listp inout)))
             (string-listp (mv-nth 2 (vl-portdecllist-names-by-direction x in out inout))))))




(def-vl-find-moditem regdecl)
(def-vl-find-moditem vardecl)
(def-vl-find-moditem netdecl)
(def-vl-find-moditem eventdecl)
(def-vl-find-moditem paramdecl)
(def-vl-find-moditem fundecl)
(def-vl-find-moditem taskdecl)

(def-vl-find-moditem modinst
  :element->name vl-modinst->instname
  :list->names   vl-modinstlist->instnames
  :names-may-be-nil t)

(def-vl-find-moditem gateinst
  :names-may-be-nil t)



(defsection vl-find-moduleitem

; This can be used to look up any name in the modnamespace.  This is the main
; "naive" routine.  Note that this does not look for portdecls!

  (defund vl-find-moduleitem (name x)
    (declare (xargs :guard (and (stringp name)
                                (vl-module-p x))))
    (or (vl-find-netdecl name (vl-module->netdecls x))
        (vl-find-regdecl name (vl-module->regdecls x))
        (vl-find-vardecl name (vl-module->vardecls x))
        (vl-find-eventdecl name (vl-module->eventdecls x))
        (vl-find-paramdecl name (vl-module->paramdecls x))
        (vl-find-fundecl name (vl-module->fundecls x))
        (vl-find-taskdecl name (vl-module->taskdecls x))
        (vl-find-modinst name (vl-module->modinsts x))
        (vl-find-gateinst name (vl-module->gateinsts x))))

  (defthm vl-find-moduleitem-type-when-nothing-else
    (implies (and (vl-find-moduleitem name x)
                  (not (vl-netdecl-p (vl-find-moduleitem name x)))
                  (not (vl-regdecl-p (vl-find-moduleitem name x)))
                  (not (vl-vardecl-p (vl-find-moduleitem name x)))
                  (not (vl-eventdecl-p (vl-find-moduleitem name x)))
                  (not (vl-paramdecl-p (vl-find-moduleitem name x)))
                  (not (vl-fundecl-p (vl-find-moduleitem name x)))
                  (not (vl-taskdecl-p (vl-find-moduleitem name x)))
                  (not (vl-modinst-p (vl-find-moduleitem name x)))
                  (force (stringp name))
                  (force (vl-module-p x)))
             (vl-gateinst-p (vl-find-moduleitem name x)))
    :hints(("Goal" :in-theory (enable vl-find-moduleitem)))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm type-of-vl-find-moduleitem
    ;; This is gross, but I'm not sure of a better approach.
    (and (implies (and (equal (tag (vl-find-moduleitem name x)) :vl-netdecl)
                       (force (stringp name))
                       (force (vl-module-p x)))
                  (vl-netdecl-p (vl-find-moduleitem name x)))

         (implies (and (equal (tag (vl-find-moduleitem name x)) :vl-regdecl)
                       (force (stringp name))
                       (force (vl-module-p x)))
                  (vl-regdecl-p (vl-find-moduleitem name x)))

         (implies (and (equal (tag (vl-find-moduleitem name x)) :vl-vardecl)
                       (force (stringp name))
                       (force (vl-module-p x)))
                  (vl-vardecl-p (vl-find-moduleitem name x)))

         (implies (and (equal (tag (vl-find-moduleitem name x)) :vl-eventdecl)
                       (force (stringp name))
                       (force (vl-module-p x)))
                  (vl-eventdecl-p (vl-find-moduleitem name x)))

         (implies (and (equal (tag (vl-find-moduleitem name x)) :vl-paramdecl)
                       (force (stringp name))
                       (force (vl-module-p x)))
                  (vl-paramdecl-p (vl-find-moduleitem name x)))

         (implies (and (equal (tag (vl-find-moduleitem name x)) :vl-fundecl)
                       (force (stringp name))
                       (force (vl-module-p x)))
                  (vl-fundecl-p (vl-find-moduleitem name x)))

         (implies (and (equal (tag (vl-find-moduleitem name x)) :vl-taskdecl)
                       (force (stringp name))
                       (force (vl-module-p x)))
                  (vl-taskdecl-p (vl-find-moduleitem name x)))

         (implies (and (equal (tag (vl-find-moduleitem name x)) :vl-modinst)
                       (force (stringp name))
                       (force (vl-module-p x)))
                  (vl-modinst-p (vl-find-moduleitem name x)))

         (implies (and (equal (tag (vl-find-moduleitem name x)) :vl-gateinst)
                       (force (stringp name))
                       (force (vl-module-p x)))
                  (vl-gateinst-p (vl-find-moduleitem name x))))

    :hints(("Goal"
            :in-theory (disable vl-find-moduleitem-type-when-nothing-else)
            :use ((:instance vl-find-moduleitem-type-when-nothing-else)))))

  (defthm consp-of-vl-find-moduleitem
    (implies (and (force (stringp name))
                  (force (vl-module-p x)))
             (equal (consp (vl-find-moduleitem name x))
                    (if (vl-find-moduleitem name x)
                        t
                      nil)))
    :hints(("Goal"
            :in-theory (disable vl-find-moduleitem-type-when-nothing-else)
            :use ((:instance vl-find-moduleitem-type-when-nothing-else)))))

  (defthm vl-find-moduleitem-when-in-namespace
    (implies (and (member-equal name (vl-module->modnamespace x))
                  (force (vl-module-p x)))
             (vl-find-moduleitem name x))
    :hints(("Goal" :in-theory (enable vl-module->modnamespace vl-find-moduleitem)))))





; FAST-ALIST BASED LOOKUPS ----------------------------------------------------

(defund vl-moditem-p (x)
  (declare (xargs :guard t))
  (or (vl-netdecl-p x)
      (vl-regdecl-p x)
      (vl-vardecl-p x)
      (vl-eventdecl-p x)
      (vl-paramdecl-p x)
      (vl-fundecl-p x)
      (vl-taskdecl-p x)
      (vl-modinst-p x)
      (vl-gateinst-p x)))

(deflist vl-moditemlist-p (x)
  (vl-moditem-p x)
  :elementp-of-nil nil
  :guard t)

(defalist vl-moditem-alist-p (x)
  :key (stringp x)
  :val (vl-moditem-p x)
  :keyp-of-nil nil
  :valp-of-nil nil
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
         (element->name (or element->name
                            (mksym 'vl- type '->name))))
    `(defsection ,fn

       (defund ,fast-fn (x acc)
         (declare (xargs :guard (,list-p x)))
         (if (consp x)
             ,(if names-may-be-nil
                  `(let ((name (,element->name (car x))))
                     (if name
                         (hons-acons name (car x)
                                     (,fast-fn (cdr x) acc))
                       (,fast-fn (cdr x) acc)))
                `(hons-acons (,element->name (car x))
                             (car x)
                             (,fast-fn (cdr x) acc)))
           acc))

       (defund ,fn (x)
         (declare (xargs :guard (,list-p x)
                         :verify-guards nil))
         (mbe :logic (if (consp x)
                         ,(if names-may-be-nil
                              `(let ((name (,element->name (car x))))
                                 (if name
                                     (cons (cons name (car x))
                                           (,fn (cdr x)))
                                   (,fn (cdr x))))
                            `(cons (cons (,element->name (car x))
                                         (car x))
                                   (,fn (cdr x))))
                       nil)
              :exec (,fast-fn x nil)))

       (local (in-theory (enable ,fast-fn ,fn)))

       (defthm ,(mksym fast-fn '-removal)
         (equal (,fast-fn x acc)
                (append (,fn x) acc)))

       (verify-guards ,fn)

       (defthm ,(mksym 'vl-moditem-alist-p-of- fn)
         (implies (force (,list-p x))
                  (vl-moditem-alist-p (,fn x)))
         :hints(("Goal" :in-theory (enable vl-moditem-p))))

       (defalist ,alist-p (x)
         :key (stringp x)
         :val (,elt-p x)
         :keyp-of-nil nil
         :valp-of-nil nil)

       (defthm ,(mksym alist-p '-of- fn)
         (implies (force (,list-p x))
                  (,alist-p (,fn x))))

       (defthm ,(mksym 'hons-assoc-equal-of- fn)
         (implies (and (force (,list-p x))
                       ,(if names-may-be-nil
                            '(force (stringp name))
                          t))
                  (equal (hons-assoc-equal name (,fn x))
                         (if (,find-fn name x)
                             (cons name (,find-fn name x))
                           nil)))
         :hints(("Goal" :in-theory (enable ,find-fn)))))))


(vl-def-moditemlist-alist netdecl)
(vl-def-moditemlist-alist regdecl)
(vl-def-moditemlist-alist vardecl)
(vl-def-moditemlist-alist eventdecl)
(vl-def-moditemlist-alist paramdecl)
(vl-def-moditemlist-alist fundecl)
(vl-def-moditemlist-alist taskdecl)
(vl-def-moditemlist-alist modinst
                          :element->name vl-modinst->instname
                          :names-may-be-nil t)
(vl-def-moditemlist-alist gateinst :names-may-be-nil t)



(defsection vl-moditem-alist

  (defund vl-moditem-alist (x)
    (declare (xargs :guard (vl-module-p x)))

; This is our main routine for building an alist for the module items.  Note
; that the alist is constructed in is particularly important: we want it to
; agree, completely, with the naive vl-find-moduleitem.  The alist can be
; constructed in a one pass, using our fast builder functions.

    (mbe :logic
         (append (vl-netdecllist-alist (vl-module->netdecls x))
                 (vl-regdecllist-alist (vl-module->regdecls x))
                 (vl-vardecllist-alist (vl-module->vardecls x))
                 (vl-eventdecllist-alist (vl-module->eventdecls x))
                 (vl-paramdecllist-alist (vl-module->paramdecls x))
                 (vl-fundecllist-alist (vl-module->fundecls x))
                 (vl-taskdecllist-alist (vl-module->taskdecls x))
                 (vl-modinstlist-alist (vl-module->modinsts x))
                 (vl-gateinstlist-alist (vl-module->gateinsts x)))
         :exec
         ;; Reverse order from the above
         (b* ((acc (vl-fast-gateinstlist-alist (vl-module->gateinsts x) nil))
              (acc (vl-fast-modinstlist-alist (vl-module->modinsts x) acc))
              (acc (vl-fast-taskdecllist-alist (vl-module->taskdecls x) acc))
              (acc (vl-fast-fundecllist-alist (vl-module->fundecls x) acc))
              (acc (vl-fast-paramdecllist-alist (vl-module->paramdecls x) acc))
              (acc (vl-fast-eventdecllist-alist (vl-module->eventdecls x) acc))
              (acc (vl-fast-vardecllist-alist (vl-module->vardecls x) acc))
              (acc (vl-fast-regdecllist-alist (vl-module->regdecls x) acc)))
           (vl-fast-netdecllist-alist (vl-module->netdecls x) acc))))

  (local (in-theory (enable vl-moditem-alist)))

  (defthm vl-moditem-alist-p-of-vl-moditem-alist
    (implies (force (vl-module-p x))
             (vl-moditem-alist-p (vl-moditem-alist x))))

  (local (defthm lemma
           (implies (stringp a)
                    (equal (hons-assoc-equal a (append x y))
                           (or (hons-assoc-equal a x)
                               (hons-assoc-equal a y))))
           :hints(("Goal" :in-theory (enable assoc-equal)))))

  (defthm hons-assoc-equal-of-vl-moditem-alist
    (implies (and (force (stringp name))
                  (force (vl-module-p x)))
             (equal (hons-assoc-equal name (vl-moditem-alist x))
                    (if (vl-find-moduleitem name x)
                        (cons name (vl-find-moduleitem name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-moduleitem)))))


(defun vl-fast-find-moduleitem (name x itemalist)
  (declare (xargs :guard (and (stringp name)
                              (vl-module-p x)
                              (equal itemalist (vl-moditem-alist x)))))
  (mbe :logic (vl-find-moduleitem name x)
       :exec (cdr (hons-get name itemalist))))


