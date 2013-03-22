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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))



;                           A MODULE'S NAMESPACE
;
; Namespaces are discussed in Section 4.11 of the spec.  In particular, note
; that ports and port declarations are given special treatment: they are said
; to be in a separate namespace which "overlaps" the regular module namespace.
;
; I think this distinction is only made so that you can refer to both ports and
; to items in the regular module namespace from expressions, etc.  The
; important consequence of this is that it is legal to write things such as:
;
;     input x ;
;     wire x ;
;
; Even though it would be illegal to declare x to be a wire twice, or as both a
; wire and a reg, and so on.
;
; At any rate, in this file we introduce a number of routines for extracting
; the names from lists of port declarations, net declarations, and so on.  These
; culminate in
;
;    (VL-MODULE->MODNAMESPACE X) : MODULE -> STRING LIST
;
; Which returns a list of all names found the module's namespace.  Note that
; any reasonable module is required to have a unique modnamespace.
;
; BOZO this does not get named blocks.  Unclear how nested blocks are supposed
; to be handled.  We get function and task names -- good.  We get names from
; events -- good.  BOZO really this all needs to be properly documented and
; explained.



(defprojection vl-namedarglist->names (x)
  ;; Collect all names from a vl-namedarglist-p.
  (vl-namedarg->name x)
  :guard (vl-namedarglist-p x)
  :result-type string-listp
  :nil-preservingp t)

(defprojection vl-paramdecllist->names (x)
  ;; Collect all names from a vl-paramdecllist-p.
  (vl-paramdecl->name x)
  :guard (vl-paramdecllist-p x)
  :result-type string-listp
  :nil-preservingp t)

(defprojection vl-modinstlist->modnames (x)
  ;; Collect all modnames (not instnames!) from a vl-modinstlist-p
  (vl-modinst->modname x)
  :guard (vl-modinstlist-p x)
  :result-type string-listp
  :nil-preservingp t)

(defprojection vl-portdecllist->names (x)
  ;; Collect all names from a vl-portinstlist-p
  (vl-portdecl->name x)
  :guard (vl-portdecllist-p x)
  :result-type string-listp
  :nil-preservingp t)

(defprojection vl-netdecllist->names (x)
  ;; Collect all names from a vl-netdecllist-p
  (vl-netdecl->name x)
  :guard (vl-netdecllist-p x)
  :result-type string-listp
  :nil-preservingp t)

(defprojection vl-vardecllist->names (x)
  ;; Collect all names from a vl-vardecllist-p
  (vl-vardecl->name x)
  :guard (vl-vardecllist-p x)
  :result-type string-listp
  :nil-preservingp t)

(defprojection vl-regdecllist->names (x)
  ;; Collect all names from a vl-regdecllist-p
  (vl-regdecl->name x)
  :guard (vl-regdecllist-p x)
  :result-type string-listp
  :nil-preservingp t)

(defprojection vl-eventdecllist->names (x)
  ;; Collect all names from a vl-eventdecllist-p
  (vl-eventdecl->name x)
  :guard (vl-eventdecllist-p x)
  :result-type string-listp
  :nil-preservingp t)



(defsection vl-gateinstlist->names

  (defund vl-gateinstlist->names-exec (x acc)
    (declare (xargs :guard (vl-gateinstlist-p x)))
    (if (consp x)
        (vl-gateinstlist->names-exec (cdr x)
                                     (let ((name (vl-gateinst->name (car x))))
                                       (if name
                                           (cons name acc)
                                         acc)))
      acc))

  (defund vl-gateinstlist->names (x)
    ;; Collect all instance names from a vl-gateinstlist-p; note that gate
    ;; instances may be unnamed, in which case we do not add anything.  In
    ;; other words, the list of names returned may be shorter than the number
    ;; of gate instances in the list.
    (declare (xargs :guard (vl-gateinstlist-p x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (if (vl-gateinst->name (car x))
                        (cons (vl-gateinst->name (car x))
                              (vl-gateinstlist->names (cdr x)))
                      (vl-gateinstlist->names (cdr x)))
                  nil)
         :exec (reverse (vl-gateinstlist->names-exec x nil))))

  (defthm vl-gateinstlist->names-exec-removal
    (equal (vl-gateinstlist->names-exec x acc)
           (revappend (vl-gateinstlist->names x) acc))
    :hints(("Goal" :in-theory (enable vl-gateinstlist->names-exec
                                      vl-gateinstlist->names))))

  (verify-guards vl-gateinstlist->names
                 :hints(("Goal" :in-theory (enable vl-gateinstlist->names))))

  (defthm vl-gateinstlist->names-when-not-consp
    (implies (not (consp x))
             (equal (vl-gateinstlist->names x)
                    nil))
    :hints(("Goal" :in-theory (enable vl-gateinstlist->names))))

  (defthm vl-gateinstlist->names-of-cons
    (equal (vl-gateinstlist->names (cons a x))
           (if (vl-gateinst->name a)
               (cons (vl-gateinst->name a)
                     (vl-gateinstlist->names x))
             (vl-gateinstlist->names x)))
    :hints(("Goal" :in-theory (enable vl-gateinstlist->names))))

  (defthm vl-gateinstlist->names-of-list-fix
    (equal (vl-gateinstlist->names (list-fix x))
           (vl-gateinstlist->names x))
    :hints(("Goal" :induct (len x))))

  (defthm vl-gateinstlist->names-of-append
    (equal (vl-gateinstlist->names (append x y))
           (append (vl-gateinstlist->names x)
                   (vl-gateinstlist->names y)))
    :hints(("Goal" :induct (len x))))

  (defthm vl-gateinstlist->names-of-rev
    (equal (vl-gateinstlist->names (rev x))
           (rev (vl-gateinstlist->names x)))
    :hints(("Goal" :induct (len x))))

  (defthm string-listp-of-vl-gateinstlist->names
    (implies (force (vl-gateinstlist-p x))
             (string-listp (vl-gateinstlist->names x)))
    :hints(("Goal" :induct (len x)))))




(defsection vl-modinstlist->instnames

  (defund vl-modinstlist->instnames-exec (x acc)
    (declare (xargs :guard (vl-modinstlist-p x)))
    (if (consp x)
        (vl-modinstlist->instnames-exec (cdr x)
                                        (let ((name (vl-modinst->instname (car x))))
                                          (if name
                                              (cons name acc)
                                            acc)))
      acc))

  (defund vl-modinstlist->instnames (x)
    ;; Collect all instnames (not modnames!!) from a list of module instances.
    ;; The Verilog specification requires that module instances be named, but
    ;; we relaxed that restriction because of spdflop, which we treat as a
    ;; module but which speedsim seems to permit as an unnamed gate.  So, as
    ;; with vl-gateinstlist->names, we simply skip past any unnamed module
    ;; instances.
    (declare (xargs :guard (vl-modinstlist-p x)
                    :verify-guards nil))
    (mbe :logic (if (consp x)
                    (if (vl-modinst->instname (car x))
                        (cons (vl-modinst->instname (car x))
                              (vl-modinstlist->instnames (cdr x)))
                      (vl-modinstlist->instnames (cdr x)))
                  nil)
         :exec (reverse (vl-modinstlist->instnames-exec x nil))))

  (defthm vl-modinstlist->instnames-exec-removal
    (equal (vl-modinstlist->instnames-exec x acc)
           (revappend (vl-modinstlist->instnames x) acc))
    :hints(("Goal" :in-theory (enable vl-modinstlist->instnames-exec
                                      vl-modinstlist->instnames))))

  (verify-guards vl-modinstlist->instnames
                 :hints(("Goal" :in-theory (enable vl-modinstlist->instnames))))

  (defthm vl-modinstlist->instnames-when-not-consp
    (implies (not (consp x))
             (equal (vl-modinstlist->instnames x)
                    nil))
    :hints(("Goal" :in-theory (enable vl-modinstlist->instnames))))

  (defthm vl-modinstlist->instnames-of-cons
    (equal (vl-modinstlist->instnames (cons a x))
           (if (vl-modinst->instname a)
               (cons (vl-modinst->instname a)
                     (vl-modinstlist->instnames x))
             (vl-modinstlist->instnames x)))
    :hints(("Goal" :in-theory (enable vl-modinstlist->instnames))))

  (defthm vl-modinstlist->instnames-of-list-fix
    (equal (vl-modinstlist->instnames (list-fix x))
           (vl-modinstlist->instnames x))
    :hints(("Goal" :induct (len x))))

  (defthm vl-modinstlist->instnames-of-append
    (equal (vl-modinstlist->instnames (append x y))
           (append (vl-modinstlist->instnames x)
                   (vl-modinstlist->instnames y)))
    :hints(("Goal" :induct (len x))))

  (defthm vl-modinstlist->instnames-of-rev
    (equal (vl-modinstlist->instnames (rev x))
           (rev (vl-modinstlist->instnames x)))
    :hints(("Goal" :induct (len x))))

  (defthm string-listp-of-vl-modinstlist->instnames
    (implies (force (vl-modinstlist-p x))
             (string-listp (vl-modinstlist->instnames x)))
    :hints(("Goal" :induct (len x)))))




(defund vl-module->modnamespace-exec (x)
  (declare (xargs :guard (vl-module-p x)))

; This is sort of an inherently inefficient operation, since we are to perform
; a cons for every object in the module.  But we can at least cut down on
; garbage by doing everything tail recursively, etc.

  (b* (((vl-module x) x)
       (acc (vl-netdecllist->names-exec     x.netdecls   nil))
       (acc (vl-regdecllist->names-exec     x.regdecls   acc))
       (acc (vl-vardecllist->names-exec     x.vardecls   acc))
       (acc (vl-eventdecllist->names-exec   x.eventdecls acc))
       (acc (vl-paramdecllist->names-exec   x.paramdecls acc))
       (acc (vl-fundecllist->names-exec     x.fundecls   acc))
       (acc (vl-taskdecllist->names-exec    x.taskdecls   acc))
       (acc (vl-modinstlist->instnames-exec x.modinsts   acc))
       (acc (vl-gateinstlist->names-exec    x.gateinsts  acc)))
    acc))

(defund vl-module->modnamespace (x)
  (declare (xargs :guard (vl-module-p x)
                  :verify-guards nil))

; This is our main function for gathering up the names that are declared as
; parameters, wires, variables, registers, and so on.
;
; This function DOES NOT include the names of ports, because as noted above they
; are considered to be in their own namespace which is "separate but overlapping"
; the main namespace in the module.
;
; If this function returns a list that is not duplicate-free, it means the module
; illegally declares those duplicated names more than once.

  (mbe :logic
       (b* (((vl-module x) x))
         (append (vl-netdecllist->names     x.netdecls)
                 (vl-regdecllist->names     x.regdecls)
                 (vl-vardecllist->names     x.vardecls)
                 (vl-eventdecllist->names   x.eventdecls)
                 (vl-paramdecllist->names   x.paramdecls)
                 (vl-fundecllist->names     x.fundecls)
                 (vl-taskdecllist->names    x.taskdecls)
                 (vl-modinstlist->instnames x.modinsts)
                 (vl-gateinstlist->names    x.gateinsts)))
       :exec
       (reverse (vl-module->modnamespace-exec x))))

(defttag vl-optimize)
(never-memoize vl-module->modnamespace-exec)
(progn! (set-raw-mode t)
        (defun vl-module->modnamespace (x)
          (nreverse (vl-module->modnamespace-exec x)))
        (defttag nil))
(defttag nil)



(defthm vl-module->modnamespace-exec-removal
  (equal (vl-module->modnamespace-exec x)
         (reverse (vl-module->modnamespace x)))
  :hints(("Goal" :in-theory (enable vl-module->modnamespace-exec
                                    vl-module->modnamespace))))

(verify-guards vl-module->modnamespace
               :hints(("Goal"
                       :in-theory (enable vl-module->modnamespace-exec
                                          vl-module->modnamespace))))

(defthm string-listp-of-vl-module->modnamespace
  (implies (force (vl-module-p x))
           (string-listp (vl-module->modnamespace x)))
  :hints(("Goal" :in-theory (enable vl-module->modnamespace))))

(defthm true-listp-of-vl-module->modnamespace
  (true-listp (vl-module->modnamespace x))
  :rule-classes :type-prescription)


;; These aren't part of the module's namespace, but are just utilities for
;; collecting up various names.

(defund vl-blockitem->name (x)
  (declare (xargs :guard (vl-blockitem-p x)
                  :guard-hints (("goal" :in-theory (enable vl-blockitem-p)))))
  (mbe :logic (cond ((vl-regdecl-p x) (vl-regdecl->name x))
                    ((vl-vardecl-p x) (vl-vardecl->name x))
                    ((vl-eventdecl-p x) (vl-eventdecl->name x))
                    (t                  (vl-paramdecl->name x)))
       :exec (case (tag x)
               (:vl-regdecl (vl-regdecl->name x))
               (:vl-vardecl (vl-vardecl->name x))
               (:vl-eventdecl (vl-eventdecl->name x))
               (otherwise (vl-paramdecl->name x)))))

(defthm stringp-of-vl-blockitem->name
  (implies (vl-blockitem-p x)
           (stringp (vl-blockitem->name x)))
  :hints(("Goal" :in-theory (enable vl-blockitem-p vl-blockitem->name))))

(defprojection vl-blockitemlist->names (x)
  (vl-blockitem->name x)
  :guard (vl-blockitemlist-p x)
  :result-type string-listp)

;; namespace of a fundecl
(defund vl-fundecl->namespace (x)
  (declare (xargs :guard (vl-fundecl-p x)))
  (b* (((vl-fundecl x) x))
    (append (vl-taskportlist->names x.inputs)
            (vl-blockitemlist->names x.decls))))

(defthm string-listp-of-vl-fundecl->namespace
  (implies (vl-fundecl-p x)
           (string-listp (vl-fundecl->namespace x)))
  :hints(("Goal" :in-theory (enable vl-fundecl->namespace))))

(defmapappend vl-fundecllist->namespaces (x)
  (vl-fundecl->namespace x)
  :guard (vl-fundecllist-p x)
  :rest
  ((defthm string-listp-of-vl-fundecllist->namespaces
     (implies (vl-fundecllist-p x)
              (string-listp (vl-fundecllist->namespaces x))))))

