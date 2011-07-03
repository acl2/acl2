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
;

(defund vl-find-portdecl (name x)
  (declare (xargs :guard (and (stringp name)
                              (vl-portdecllist-p x))))
  (cond ((atom x)
         nil)
        ((equal name (vl-portdecl->name (car x)))
         (car x))
        (t
         (vl-find-portdecl name (cdr x)))))

(defthm vl-find-portdecl-under-iff
  (implies (force (vl-portdecllist-p x))
           (iff (vl-find-portdecl name x)
                (member-equal name (vl-portdecllist->names x))))
  :hints(("Goal" :in-theory (enable vl-find-portdecl))))

(defthm vl-portdecl-p-of-vl-find-portdecl
  (implies (force (vl-portdecllist-p x))
           (equal (vl-portdecl-p (vl-find-portdecl name x))
                  (if (vl-find-portdecl name x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-portdecl))))

(defthm vl-portdecl->name-of-vl-find-portdecl
  (equal (vl-portdecl->name (vl-find-portdecl name x))
         (and (vl-find-portdecl name x)
              name))
  :hints(("Goal" :in-theory (enable vl-find-portdecl))))

(defthm tag-of-vl-find-portdecl
  (implies (force (vl-portdecllist-p x))
           (equal (tag (vl-find-portdecl name x))
                  (if (vl-find-portdecl name x)
                      :vl-portdecl
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-portdecl))))

(defthm member-equal-of-vl-find-portdecl
  (implies (force (vl-portdecllist-p x))
           (iff (member-equal (vl-find-portdecl name x) x)
                (vl-find-portdecl name x)))
  :hints(("Goal" :in-theory (enable vl-find-portdecl))))




(defund vl-portdecl-alist (x)
  (declare (xargs :guard (vl-portdecllist-p x)))

; Build a fast alist associating the name of each port declaration with the
; whole vl-portdecl-p object.

  (if (consp x)
      (hons-acons (vl-portdecl->name (car x))
                  (car x)
                  (vl-portdecl-alist (cdr x)))
    nil))

(defun vl-fast-find-portdecl (name portdecls alist)
  (declare (xargs :guard (and (stringp name)
                              (vl-portdecllist-p portdecls)
                              (equal alist (vl-portdecl-alist portdecls)))
                  :verify-guards nil))

; This is just a faster version of vl-find-portdecl, where the search is done
; as an fast-alist lookup rather than as string search.

  (mbe :logic (vl-find-portdecl name portdecls)
       :exec (cdr (hons-get name alist))))

(defthm alistp-of-vl-portdecl-alist
  (alistp (vl-portdecl-alist x))
  :hints(("Goal" :in-theory (enable vl-portdecl-alist))))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (vl-portdecllist-p portdecls)
                        (stringp name))
                   (equal (vl-find-portdecl name portdecls)
                          (cdr (hons-assoc-equal name (vl-portdecl-alist portdecls)))))
          :hints(("Goal" :in-theory (enable vl-portdecl-alist vl-find-portdecl)))))

 (verify-guards vl-fast-find-portdecl))


;; (defsection vl-find-port-direction

;; This is subsumed by the new vl-port-direction function

;; ;; BOZO move to mu-find-moditem

;;   (defund vl-find-port-direction (x portdecls palist)
;;     "Returns (MV SUCCESSP DIR)"
;;     (declare (xargs :guard (and (vl-port-p x)
;;                                 (vl-portdecllist-p portdecls)
;;                                 (equal palist (vl-portdecl-alist portdecls)))))
;;     (b* ((name (vl-port->name x))
;;          ((unless name)
;;           (mv nil nil))
;;          (decl (vl-fast-find-portdecl name portdecls palist))
;;          ((unless decl)
;;           (mv nil nil)))
;;         (mv t (vl-portdecl->dir decl))))

;;   (local (in-theory (enable vl-find-port-direction)))

;;   (defthm booleanp-of-vl-find-port-direction
;;     (booleanp (mv-nth 0 (vl-find-port-direction x portdecls palist)))
;;     :rule-classes :type-prescription)

;;   (defthm vl-direction-p-of-vl-find-port-direction
;;     (implies (and (force (vl-port-p x))
;;                   (force (vl-portdecllist-p portdecls))
;;                   (force (equal palist (vl-portdecl-alist portdecls))))
;;              (equal (vl-direction-p
;;                      (mv-nth 1 (vl-find-port-direction x portdecls palist)))
;;                     (if (mv-nth 0 (vl-find-port-direction x portdecls palist))
;;                         t
;;                       nil)))))



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





(defund vl-find-regdecl (name x)
  (declare (xargs :guard (and (stringp name)
                              (vl-regdecllist-p x))))
  (cond ((atom x)
         nil)
        ((equal name (vl-regdecl->name (car x)))
         (car x))
        (t
         (vl-find-regdecl name (cdr x)))))

(defthm vl-find-regdecl-under-iff
  (implies (force (vl-regdecllist-p x))
           (iff (vl-find-regdecl name x)
                (member-equal name (vl-regdecllist->names x))))
  :hints(("Goal" :in-theory (enable vl-find-regdecl))))

(defthm vl-regdecl-p-of-vl-find-regdecl
  (implies (force (vl-regdecllist-p x))
           (equal (vl-regdecl-p (vl-find-regdecl name x))
                  (if (vl-find-regdecl name x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-regdecl))))

(defthm vl-regdecl->name-of-vl-find-regdecl
  (equal (vl-regdecl->name (vl-find-regdecl name x))
         (and (vl-find-regdecl name x)
              name))
  :hints(("Goal" :in-theory (enable vl-find-regdecl))))

(defthm tag-of-vl-find-regdecl
  (implies (force (vl-regdecllist-p x))
           (equal (tag (vl-find-regdecl name x))
                  (if (vl-find-regdecl name x)
                      :vl-regdecl
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-regdecl))))

(defthm member-equal-of-vl-find-regdecl
  (implies (force (vl-regdecllist-p x))
           (iff (member-equal (vl-find-regdecl name x) x)
                (vl-find-regdecl name x)))
  :hints(("Goal" :in-theory (enable vl-find-regdecl))))

(defthm consp-of-vl-find-regdecl-when-member-equal
  (implies (and (member-equal name (vl-regdecllist->names decls))
                (force (vl-regdecllist-p decls)))
           (consp (vl-find-regdecl name decls)))
  :hints(("Goal" :in-theory (enable vl-find-regdecl))))



(defund vl-find-vardecl (name x)
  (declare (xargs :guard (and (stringp name)
                              (vl-vardecllist-p x))))
  (cond ((atom x)
         nil)
        ((equal name (vl-vardecl->name (car x)))
         (car x))
        (t
         (vl-find-vardecl name (cdr x)))))

(defthm vl-find-vardecl-under-iff
  (implies (force (vl-vardecllist-p x))
           (iff (vl-find-vardecl name x)
                (member-equal name (vl-vardecllist->names x))))
  :hints(("Goal" :in-theory (enable vl-find-vardecl))))

(defthm vl-vardecl-p-of-vl-find-vardecl
  (implies (force (vl-vardecllist-p x))
           (equal (vl-vardecl-p (vl-find-vardecl name x))
                  (if (vl-find-vardecl name x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-vardecl))))

(defthm vl-vardecl->name-of-vl-find-vardecl
  (equal (vl-vardecl->name (vl-find-vardecl name x))
         (and (vl-find-vardecl name x)
              name))
  :hints(("Goal" :in-theory (enable vl-find-vardecl))))

(defthm tag-of-vl-find-vardecl
  (implies (force (vl-vardecllist-p x))
           (equal (tag (vl-find-vardecl name x))
                  (if (vl-find-vardecl name x)
                      :vl-vardecl
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-vardecl))))

(defthm member-equal-of-vl-find-vardecl
  (implies (force (vl-vardecllist-p x))
           (iff (member-equal (vl-find-vardecl name x) x)
                (vl-find-vardecl name x)))
  :hints(("Goal" :in-theory (enable vl-find-vardecl))))

(defthm consp-of-vl-find-vardecl-when-member-equal
  (implies (and (member-equal name (vl-vardecllist->names decls))
                (force (vl-vardecllist-p decls)))
           (consp (vl-find-vardecl name decls)))
  :hints(("Goal" :in-theory (enable vl-find-vardecl))))




(defund vl-find-netdecl (name x)
  (declare (xargs :guard (and (stringp name)
                              (vl-netdecllist-p x))))
  (cond ((atom x)
         nil)
        ((equal name (vl-netdecl->name (car x)))
         (car x))
        (t
         (vl-find-netdecl name (cdr x)))))

(defthm vl-find-netdecl-under-iff
  (implies (force (vl-netdecllist-p x))
           (iff (vl-find-netdecl name x)
                (member-equal name (vl-netdecllist->names x))))
  :hints(("Goal" :in-theory (enable vl-find-netdecl))))

(defthm vl-netdecl-p-of-vl-find-netdecl
  (implies (force (vl-netdecllist-p x))
           (equal (vl-netdecl-p (vl-find-netdecl name x))
                  (if (vl-find-netdecl name x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-netdecl))))

(defthm vl-netdecl->name-of-vl-find-netdecl
  (equal (vl-netdecl->name (vl-find-netdecl name x))
         (and (vl-find-netdecl name x)
              name))
  :hints(("Goal" :in-theory (enable vl-find-netdecl))))

(defthm tag-of-vl-find-netdecl
  (implies (force (vl-netdecllist-p x))
           (equal (tag (vl-find-netdecl name x))
                  (if (vl-find-netdecl name x)
                      :vl-netdecl
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-netdecl))))

(defthm member-equal-of-vl-find-netdecl
  (implies (force (vl-netdecllist-p x))
           (iff (member-equal (vl-find-netdecl name x) x)
                (vl-find-netdecl name x)))
  :hints(("Goal" :in-theory (enable vl-find-netdecl))))

(defthm consp-of-vl-find-netdecl-when-member-equal
  (implies (and (member-equal name (vl-netdecllist->names decls))
                (force (vl-netdecllist-p decls)))
           (consp (vl-find-netdecl name decls)))
  :hints(("Goal" :in-theory (enable vl-find-netdecl))))




(defund vl-find-eventdecl (name x)
  (declare (xargs :guard (and (stringp name)
                              (vl-eventdecllist-p x))))
  (cond ((atom x)
         nil)
        ((equal name (vl-eventdecl->name (car x)))
         (car x))
        (t
         (vl-find-eventdecl name (cdr x)))))

(defthm vl-find-eventdecl-under-iff
  (implies (force (vl-eventdecllist-p x))
           (iff (vl-find-eventdecl name x)
                (member-equal name (vl-eventdecllist->names x))))
  :hints(("Goal" :in-theory (enable vl-find-eventdecl))))

(defthm vl-eventdecl-p-of-vl-find-eventdecl
  (implies (force (vl-eventdecllist-p x))
           (equal (vl-eventdecl-p (vl-find-eventdecl name x))
                  (if (vl-find-eventdecl name x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-eventdecl))))

(defthm vl-eventdecl->name-of-vl-find-eventdecl
  (equal (vl-eventdecl->name (vl-find-eventdecl name x))
         (and (vl-find-eventdecl name x)
              name))
  :hints(("Goal" :in-theory (enable vl-find-eventdecl))))

(defthm tag-of-vl-find-eventdecl
  (implies (force (vl-eventdecllist-p x))
           (equal (tag (vl-find-eventdecl name x))
                  (if (vl-find-eventdecl name x)
                      :vl-eventdecl
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-eventdecl))))

(defthm member-equal-of-vl-find-eventdecl
  (implies (force (vl-eventdecllist-p x))
           (iff (member-equal (vl-find-eventdecl name x) x)
                (vl-find-eventdecl name x)))
  :hints(("Goal" :in-theory (enable vl-find-eventdecl))))

(defthm consp-of-vl-find-eventdecl-when-member-equal
  (implies (and (member-equal name (vl-eventdecllist->names decls))
                (force (vl-eventdecllist-p decls)))
           (consp (vl-find-eventdecl name decls)))
  :hints(("Goal" :in-theory (enable vl-find-eventdecl))))





(defund vl-find-paramdecl (name x)
  (declare (xargs :guard (and (stringp name)
                              (vl-paramdecllist-p x))))
  (cond ((atom x)
         nil)
        ((equal name (vl-paramdecl->name (car x)))
         (car x))
        (t
         (vl-find-paramdecl name (cdr x)))))

(defthm vl-find-paramdecl-under-iff
  (implies (force (vl-paramdecllist-p x))
           (iff (vl-find-paramdecl name x)
                (member-equal name (vl-paramdecllist->names x))))
  :hints(("Goal" :in-theory (enable vl-find-paramdecl))))

(defthm vl-paramdecl-p-of-vl-find-paramdecl
  (implies (force (vl-paramdecllist-p x))
           (equal (vl-paramdecl-p (vl-find-paramdecl name x))
                  (if (vl-find-paramdecl name x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-paramdecl))))

(defthm vl-paramdecl->name-of-vl-find-paramdecl
  (equal (vl-paramdecl->name (vl-find-paramdecl name x))
         (and (vl-find-paramdecl name x)
              name))
  :hints(("Goal" :in-theory (enable vl-find-paramdecl))))

(defthm tag-of-vl-find-paramdecl
  (implies (force (vl-paramdecllist-p x))
           (equal (tag (vl-find-paramdecl name x))
                  (if (vl-find-paramdecl name x)
                      :vl-paramdecl
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-paramdecl))))

(defthm member-equal-of-vl-find-paramdecl
  (implies (force (vl-paramdecllist-p x))
           (iff (member-equal (vl-find-paramdecl name x) x)
                (vl-find-paramdecl name x)))
  :hints(("Goal" :in-theory (enable vl-find-paramdecl))))

(defthm consp-of-vl-find-paramdecl-when-member-equal
  (implies (and (member-equal name (vl-paramdecllist->names decls))
                (force (vl-paramdecllist-p decls)))
           (consp (vl-find-paramdecl name decls)))
  :hints(("Goal" :in-theory (enable vl-find-paramdecl))))



(defund vl-find-modinst (name x)
  (declare (xargs :guard (and (stringp name)
                              (vl-modinstlist-p x))))
  (cond ((atom x)
         nil)
        ((equal name (vl-modinst->instname (car x)))
         (car x))
        (t
         (vl-find-modinst name (cdr x)))))

(defthm vl-modinst-p-of-vl-find-modinst
  (implies (force (vl-modinstlist-p x))
           (equal (vl-modinst-p (vl-find-modinst name x))
                  (if (vl-find-modinst name x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-modinst))))

(defthm vl-modinst->instname-of-vl-find-modinst
  (equal (vl-modinst->instname (vl-find-modinst name x))
         (and (vl-find-modinst name x)
              name))
  :hints(("Goal" :in-theory (enable vl-find-modinst))))

(defthm vl-find-modinst-under-iff
  (implies (force (and (vl-modinstlist-p x)
                       (stringp name)))
           (iff (vl-find-modinst name x)
                (member-equal name (vl-modinstlist->instnames x))))
  :hints(("Goal" :in-theory (enable vl-find-modinst))))

(defthm tag-of-vl-find-modinst
  (implies (and (force (vl-modinstlist-p x))
                (force (stringp name)))
           (equal (tag (vl-find-modinst name x))
                  (if (vl-find-modinst name x)
                      :vl-modinst
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-modinst))))

(defthm member-equal-of-vl-find-modinst
  (implies (force (vl-modinstlist-p x))
           (iff (member-equal (vl-find-modinst name x) x)
                (vl-find-modinst name x)))
  :hints(("Goal" :in-theory (enable vl-find-modinst))))

(defthm consp-of-vl-find-modinst-when-member-equal
  (implies (and (member-equal name (vl-modinstlist->instnames decls))
                (force (vl-modinstlist-p decls)))
           (consp (vl-find-modinst name decls)))
  :hints(("Goal" :in-theory (enable vl-find-modinst))))




(defund vl-find-gateinst (name x)
  (declare (xargs :guard (and (stringp name)
                              (vl-gateinstlist-p x))))
  (cond ((atom x)
         nil)
        ((equal name (vl-gateinst->name (car x)))
         (car x))
        (t
         (vl-find-gateinst name (cdr x)))))

(defthm vl-gateinst-p-of-vl-find-gateinst
  (implies (force (vl-gateinstlist-p x))
           (equal (vl-gateinst-p (vl-find-gateinst name x))
                  (if (vl-find-gateinst name x)
                      t
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-gateinst))))

(defthm vl-gateinst->name-of-vl-find-gateinst
  (equal (vl-gateinst->name (vl-find-gateinst name x))
         (and (vl-find-gateinst name x)
              name))
  :hints(("Goal" :in-theory (enable vl-find-gateinst))))

(defthm vl-find-gateinst-under-iff
  (implies (force (and (vl-gateinstlist-p x)
                       (stringp name)))
           (iff (vl-find-gateinst name x)
                (member-equal name (vl-gateinstlist->names x))))
  :hints(("Goal" :in-theory (enable vl-find-gateinst))))

(defthm tag-of-vl-find-gateinst
  (implies (and (force (vl-gateinstlist-p x))
                (force (stringp name)))
           (equal (tag (vl-find-gateinst name x))
                  (if (vl-find-gateinst name x)
                      :vl-gateinst
                    nil)))
  :hints(("Goal" :in-theory (enable vl-find-gateinst))))

(defthm member-equal-of-vl-find-gateinst
  (implies (force (vl-gateinstlist-p x))
           (iff (member-equal (vl-find-gateinst name x) x)
                (vl-find-gateinst name x)))
  :hints(("Goal" :in-theory (enable vl-find-gateinst))))

(defthm consp-of-vl-find-gateinst-when-member-equal
  (implies (and (member-equal name (vl-gateinstlist->names decls))
                (force (vl-gateinstlist-p decls)))
           (consp (vl-find-gateinst name decls)))
  :hints(("Goal" :in-theory (enable vl-find-gateinst))))



(defund vl-find-moduleitem (name x)
  (declare (xargs :guard (and (stringp name)
                              (vl-module-p x))))

; This can be used to look up any name in the modnamespace.  This is the main
; "naive" routine.  Note that this does not look for portdecls!

  (or (vl-find-netdecl name (vl-module->netdecls x))
      (vl-find-regdecl name (vl-module->regdecls x))
      (vl-find-vardecl name (vl-module->vardecls x))
      (vl-find-eventdecl name (vl-module->eventdecls x))
      (vl-find-paramdecl name (vl-module->paramdecls x))
      (vl-find-modinst name (vl-module->modinsts x))
      (vl-find-gateinst name (vl-module->gateinsts x))))

(defthm vl-find-moduleitem-type-when-nothing-else
  (implies (and (vl-find-moduleitem name x)
                (not (vl-netdecl-p (vl-find-moduleitem name x)))
                (not (vl-regdecl-p (vl-find-moduleitem name x)))
                (not (vl-vardecl-p (vl-find-moduleitem name x)))
                (not (vl-eventdecl-p (vl-find-moduleitem name x)))
                (not (vl-paramdecl-p (vl-find-moduleitem name x)))
                (not (vl-modinst-p (vl-find-moduleitem name x)))
                (force (stringp name))
                (force (vl-module-p x)))
           (vl-gateinst-p (vl-find-moduleitem name x)))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints(("Goal" :in-theory (enable vl-find-moduleitem))))

(defthm type-of-vl-find-moduleitem

; This is gross, but I'm not sure of a better approach.

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




;                          FAST-ALIST BASED LOOKUPS
;
; When repeated item lookups in the same module are going to be needed, it is
; more efficient to construct a fast-alist which maps the module item names to
; their definitions.  We now introduce routines to do this.
;

(defund vl-moditem-p (x)
  (declare (xargs :guard t))
  (or (vl-netdecl-p x)
      (vl-regdecl-p x)
      (vl-vardecl-p x)
      (vl-eventdecl-p x)
      (vl-paramdecl-p x)
      (vl-modinst-p x)
      (vl-gateinst-p x)))

(deflist vl-moditemlist-p (x)
  (vl-moditem-p x)
  :elementp-of-nil nil
  :guard t)

(defund vl-moditem-alist-p (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (stringp (caar x))
           (vl-moditem-p (cdar x))
           (vl-moditem-alist-p (cdr x)))
    (eq x nil)))

(defthm vl-moditem-alist-p-when-not-consp
  (implies (not (consp x))
           (equal (vl-moditem-alist-p x)
                  (not x)))
  :hints(("Goal" :in-theory (enable vl-moditem-alist-p))))

(defthm vl-moditem-alist-p-of-cons
  (equal (vl-moditem-alist-p (cons a x))
         (and (consp a)
              (stringp (car a))
              (vl-moditem-p (cdr a))
              (vl-moditem-alist-p x)))
  :hints(("Goal" :in-theory (enable vl-moditem-alist-p))))

(defthm vl-moditem-alist-p-of-append
  (implies (and (force (vl-moditem-alist-p x))
                (force (vl-moditem-alist-p y)))
           (vl-moditem-alist-p (append x y)))
  :hints(("Goal" :induct (len x))))

(defthm alistp-when-vl-moditem-alist-p
  (implies (vl-moditem-alist-p x)
           (alistp x))
  :hints(("Goal" :induct (len x))))



(defsection vl-netdecl-alist

  (defund vl-fast-netdecllist-alist (x acc)
    (declare (xargs :guard (vl-netdecllist-p x)))
    (if (consp x)
        (hons-acons (vl-netdecl->name (car x))
                    (car x)
                    (vl-fast-netdecllist-alist (cdr x) acc))
      acc))

  (defund vl-netdecllist-alist (x)
    (declare (xargs :guard (vl-netdecllist-p x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (cons (cons (vl-netdecl->name (car x)) (car x))
                          (vl-netdecllist-alist (cdr x)))
                  nil)
         :exec (vl-fast-netdecllist-alist x nil)))

  (local (in-theory (enable vl-fast-netdecllist-alist
                            vl-netdecllist-alist)))

  (defthm vl-fast-netdecllist-alist-removal
    (equal (vl-fast-netdecllist-alist x acc)
           (append (vl-netdecllist-alist x) acc))
    :hints(("Goal" :in-theory (enable vl-fast-netdecllist-alist
                                      vl-netdecllist-alist))))

  (verify-guards vl-netdecllist-alist)

  (defthm vl-moditem-alist-p-of-vl-netdecllist-alist
    (implies (force (vl-netdecllist-p x))
             (vl-moditem-alist-p (vl-netdecllist-alist x)))
    :hints(("Goal" :in-theory (enable vl-moditem-p))))

  (defthm hons-assoc-equal-of-vl-netdecllist-alist
    (implies (force (vl-netdecllist-p x))
             (equal (hons-assoc-equal name (vl-netdecllist-alist x))
                    (if (vl-find-netdecl name x)
                        (cons name (vl-find-netdecl name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-netdecl))))

  )



(defsection vl-regdecl-alist

  (defund vl-fast-regdecllist-alist (x acc)
    (declare (xargs :guard (vl-regdecllist-p x)))
    (if (consp x)
        (hons-acons (vl-regdecl->name (car x))
                    (car x)
                    (vl-fast-regdecllist-alist (cdr x) acc))
      acc))

  (defund vl-regdecllist-alist (x)
    (declare (xargs :guard (vl-regdecllist-p x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (cons (cons (vl-regdecl->name (car x)) (car x))
                          (vl-regdecllist-alist (cdr x)))
                  nil)
         :exec (vl-fast-regdecllist-alist x nil)))

  (local (in-theory (enable vl-fast-regdecllist-alist
                            vl-regdecllist-alist)))

  (defthm vl-fast-regdecllist-alist-removal
    (equal (vl-fast-regdecllist-alist x acc)
           (append (vl-regdecllist-alist x) acc))
    :hints(("Goal" :in-theory (enable vl-fast-regdecllist-alist
                                      vl-regdecllist-alist))))

  (verify-guards vl-regdecllist-alist)

  (defthm vl-moditem-alist-p-of-vl-regdecllist-alist
    (implies (force (vl-regdecllist-p x))
             (vl-moditem-alist-p (vl-regdecllist-alist x)))
    :hints(("Goal" :in-theory (enable vl-moditem-p))))

  (defthm hons-assoc-equal-of-vl-regdecllist-alist
    (implies (force (vl-regdecllist-p x))
             (equal (hons-assoc-equal name (vl-regdecllist-alist x))
                    (if (vl-find-regdecl name x)
                        (cons name (vl-find-regdecl name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-regdecl))))

  )


(defsection vl-vardecl-alist

  (defund vl-fast-vardecllist-alist (x acc)
    (declare (xargs :guard (vl-vardecllist-p x)))
    (if (consp x)
        (hons-acons (vl-vardecl->name (car x))
                    (car x)
                    (vl-fast-vardecllist-alist (cdr x) acc))
      acc))

  (defund vl-vardecllist-alist (x)
    (declare (xargs :guard (vl-vardecllist-p x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (cons (cons (vl-vardecl->name (car x)) (car x))
                          (vl-vardecllist-alist (cdr x)))
                  nil)
         :exec (vl-fast-vardecllist-alist x nil)))

  (local (in-theory (enable vl-fast-vardecllist-alist
                            vl-vardecllist-alist)))

  (defthm vl-fast-vardecllist-alist-removal
    (equal (vl-fast-vardecllist-alist x acc)
           (append (vl-vardecllist-alist x) acc))
    :hints(("Goal" :in-theory (enable vl-fast-vardecllist-alist
                                      vl-vardecllist-alist))))

  (verify-guards vl-vardecllist-alist)

  (defthm vl-moditem-alist-p-of-vl-vardecllist-alist
    (implies (force (vl-vardecllist-p x))
             (vl-moditem-alist-p (vl-vardecllist-alist x)))
    :hints(("Goal" :in-theory (enable vl-moditem-p))))

  (defthm hons-assoc-equal-of-vl-vardecllist-alist
    (implies (force (vl-vardecllist-p x))
             (equal (hons-assoc-equal name (vl-vardecllist-alist x))
                    (if (vl-find-vardecl name x)
                        (cons name (vl-find-vardecl name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-vardecl))))
  )


(defsection vl-eventdecl-alist

  (defund vl-fast-eventdecllist-alist (x acc)
    (declare (xargs :guard (vl-eventdecllist-p x)))
    (if (consp x)
        (hons-acons (vl-eventdecl->name (car x))
                    (car x)
                    (vl-fast-eventdecllist-alist (cdr x) acc))
      acc))

  (defund vl-eventdecllist-alist (x)
    (declare (xargs :guard (vl-eventdecllist-p x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (cons (cons (vl-eventdecl->name (car x)) (car x))
                          (vl-eventdecllist-alist (cdr x)))
                  nil)
         :exec (vl-fast-eventdecllist-alist x nil)))

  (local (in-theory (enable vl-fast-eventdecllist-alist
                            vl-eventdecllist-alist)))

  (defthm vl-fast-eventdecllist-alist-removal
    (equal (vl-fast-eventdecllist-alist x acc)
           (append (vl-eventdecllist-alist x) acc))
    :hints(("Goal" :in-theory (enable vl-fast-eventdecllist-alist
                                      vl-eventdecllist-alist))))

  (verify-guards vl-eventdecllist-alist)

  (defthm vl-moditem-alist-p-of-vl-eventdecllist-alist
    (implies (force (vl-eventdecllist-p x))
             (vl-moditem-alist-p (vl-eventdecllist-alist x)))
    :hints(("Goal" :in-theory (enable vl-moditem-p))))

  (defthm hons-assoc-equal-of-vl-eventdecllist-alist
    (implies (force (vl-eventdecllist-p x))
             (equal (hons-assoc-equal name (vl-eventdecllist-alist x))
                    (if (vl-find-eventdecl name x)
                        (cons name (vl-find-eventdecl name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-eventdecl))))
  )



(defsection vl-paramdecl-alist

  (defund vl-fast-paramdecllist-alist (x acc)
    (declare (xargs :guard (vl-paramdecllist-p x)))
    (if (consp x)
        (hons-acons (vl-paramdecl->name (car x))
                    (car x)
                    (vl-fast-paramdecllist-alist (cdr x) acc))
      acc))

  (defund vl-paramdecllist-alist (x)
    (declare (xargs :guard (vl-paramdecllist-p x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (cons (cons (vl-paramdecl->name (car x)) (car x))
                          (vl-paramdecllist-alist (cdr x)))
                  nil)
         :exec (vl-fast-paramdecllist-alist x nil)))

  (local (in-theory (enable vl-fast-paramdecllist-alist
                            vl-paramdecllist-alist)))

  (defthm vl-fast-paramdecllist-alist-removal
    (equal (vl-fast-paramdecllist-alist x acc)
           (append (vl-paramdecllist-alist x) acc))
    :hints(("Goal" :in-theory (enable vl-fast-paramdecllist-alist
                                      vl-paramdecllist-alist))))

  (verify-guards vl-paramdecllist-alist)

  (defthm vl-moditem-alist-p-of-vl-paramdecllist-alist
    (implies (force (vl-paramdecllist-p x))
             (vl-moditem-alist-p (vl-paramdecllist-alist x)))
    :hints(("Goal" :in-theory (enable vl-moditem-p))))

  (defthm cdr-of-hons-assoc-equal-of-vl-paramdecllist-alist
    (equal (cdr (hons-assoc-equal name (vl-paramdecllist-alist x)))
           (vl-find-paramdecl name x))
    :hints(("Goal" :in-theory (enable vl-find-paramdecl))))

  (defthm hons-assoc-equal-of-vl-paramdecllist-alist
    (implies (force (vl-paramdecllist-p x))
             (equal (hons-assoc-equal name (vl-paramdecllist-alist x))
                    (if (vl-find-paramdecl name x)
                        (cons name (vl-find-paramdecl name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-paramdecl))))

  )



(defsection vl-modinstlist-alist

  (defund vl-fast-modinstlist-alist (x acc)
    (declare (xargs :guard (vl-modinstlist-p x)))
    (if (consp x)
        (let ((name (vl-modinst->instname (car x))))
          (if name
              (hons-acons name (car x)
                          (vl-fast-modinstlist-alist (cdr x) acc))
            (vl-fast-modinstlist-alist (cdr x) acc)))
      acc))

  (defund vl-modinstlist-alist (x)
    (declare (xargs :guard (vl-modinstlist-p x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (let ((name (vl-modinst->instname (car x))))
                      (if name
                          (cons (cons name (car x))
                                (vl-modinstlist-alist (cdr x)))
                        (vl-modinstlist-alist (cdr x))))
                  nil)
         :exec (vl-fast-modinstlist-alist x nil)))

  (local (in-theory (enable vl-fast-modinstlist-alist
                            vl-modinstlist-alist)))

  (defthm vl-fast-modinstlist-alist-removal
    (equal (vl-fast-modinstlist-alist x acc)
           (append (vl-modinstlist-alist x) acc)))

  (verify-guards vl-modinstlist-alist)

  (defthm vl-moditem-alist-p-of-vl-modinstlist-alist
    (implies (force (vl-modinstlist-p x))
             (vl-moditem-alist-p (vl-modinstlist-alist x)))
    :hints(("Goal"
            :in-theory (enable vl-moditem-p)
            ;; Gross.  Why isn't type-of-vl-modinst->instname forcing?
            ;; Why aren't we doing destructor elim?
            :expand (vl-modinstlist-p x))))

  (defthm hons-assoc-equal-of-vl-modinstlist-alist
    (implies (and (force (stringp name))
                  (force (vl-modinstlist-p x)))
             (equal (hons-assoc-equal name (vl-modinstlist-alist x))
                    (if (vl-find-modinst name x)
                        (cons name (vl-find-modinst name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-modinst))))
  )



(defsection vl-gateinstlist-alist

  (defund vl-fast-gateinstlist-alist (x acc)
    (declare (xargs :guard (vl-gateinstlist-p x)))
    (if (consp x)
        (let ((name (vl-gateinst->name (car x))))
          (if name
              (hons-acons name (car x)
                          (vl-fast-gateinstlist-alist (cdr x) acc))
            (vl-fast-gateinstlist-alist (cdr x) acc)))
      acc))

  (defund vl-gateinstlist-alist (x)
    (declare (xargs :guard (vl-gateinstlist-p x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (let ((name (vl-gateinst->name (car x))))
                      (if name
                          (cons (cons name (car x))
                                (vl-gateinstlist-alist (cdr x)))
                        (vl-gateinstlist-alist (cdr x))))
                  nil)
         :exec (vl-fast-gateinstlist-alist x nil)))

  (local (in-theory (enable vl-fast-gateinstlist-alist
                            vl-gateinstlist-alist)))

  (defthm vl-fast-gateinstlist-alist-removal
    (equal (vl-fast-gateinstlist-alist x acc)
           (append (vl-gateinstlist-alist x) acc)))

  (verify-guards vl-gateinstlist-alist)

  (defthm vl-moditem-alist-p-of-vl-gateinstlist-alist
    (implies (force (vl-gateinstlist-p x))
             (vl-moditem-alist-p (vl-gateinstlist-alist x)))
    :hints(("Goal"
            :in-theory (enable vl-moditem-p)
            ;; Gross, same questions as in the vl-modinstlist theorem
            :expand (vl-gateinstlist-p x))))

  (defthm hons-assoc-equal-of-vl-gateinstlist-alist
    (implies (and (force (stringp name))
                  (force (vl-gateinstlist-p x)))
             (equal (hons-assoc-equal name (vl-gateinstlist-alist x))
                    (if (vl-find-gateinst name x)
                        (cons name (vl-find-gateinst name x))
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-gateinst))))

  )



(defund vl-moditem-alist (x)
  (declare (xargs :guard (vl-module-p x)))

; This is our main routine for building an alist for the module items.  Note
; that the alist is constructed in is particularly important: we want it to
; agree, completely, with the naive vl-find-moduleitem.  The alist can be
; constructed in a one pass, using our fast builder functions.

  (mbe :logic (append (vl-netdecllist-alist (vl-module->netdecls x))
                      (vl-regdecllist-alist (vl-module->regdecls x))
                      (vl-vardecllist-alist (vl-module->vardecls x))
                      (vl-eventdecllist-alist (vl-module->eventdecls x))
                      (vl-paramdecllist-alist (vl-module->paramdecls x))
                      (vl-modinstlist-alist (vl-module->modinsts x))
                      (vl-gateinstlist-alist (vl-module->gateinsts x)))
       :exec (vl-fast-netdecllist-alist (vl-module->netdecls x)
              (vl-fast-regdecllist-alist (vl-module->regdecls x)
               (vl-fast-vardecllist-alist (vl-module->vardecls x)
                (vl-fast-eventdecllist-alist (vl-module->eventdecls x)
                 (vl-fast-paramdecllist-alist (vl-module->paramdecls x)
                  (vl-fast-modinstlist-alist (vl-module->modinsts x)
                   (vl-fast-gateinstlist-alist (vl-module->gateinsts x) nil)))))))))

(defthm vl-moditem-alist-p-of-vl-moditem-alist
  (implies (force (vl-module-p x))
           (vl-moditem-alist-p (vl-moditem-alist x)))
  :hints(("Goal" :in-theory (enable vl-moditem-alist))))

(encapsulate
 ()
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
  :hints(("Goal" :in-theory (enable vl-moditem-alist vl-find-moduleitem)))))

(defun vl-fast-find-moduleitem (name x itemalist)
   (declare (xargs :guard (and (stringp name)
                               (vl-module-p x)
                               (equal itemalist (vl-moditem-alist x)))))
   (mbe :logic (vl-find-moduleitem name x)
        :exec (cdr (hons-get name itemalist))))

(defthm vl-find-moduleitem-when-in-namespace
  (implies (and (member-equal name (vl-module->modnamespace x))
                (force (vl-module-p x)))
           (vl-find-moduleitem name x))
  :hints(("Goal" :in-theory (enable vl-module->modnamespace
                                    vl-find-moduleitem))))




