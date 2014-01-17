; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(defxdoc modnamespace
  :parents (mlib)
  :short "Functions related to a module's namespace."

  :long "<p>Namespaces are discussed in Section 4.11 of the Verilog-2005
standard.  In particular, note that ports and port declarations are given
special treatment: they are said to be in a separate namespace which
\"overlaps\" the regular module namespace.</p>

<p>I think this distinction is only made so that you can refer to both ports and
 to items in the regular module namespace from expressions, etc.  The
 important consequence of this is that it is legal to write things such as:</p>

@({
     input x ;
     wire x ;
})

<p>Even though it would be illegal to declare x to be a wire twice, or as both a
wire and a reg, and so on.</p>

<p>At any rate, in this file we introduce a number of routines for extracting
the names from lists of port declarations, net declarations, and so on.  These
culminate in</p>

@({
    (VL-MODULE->MODNAMESPACE X) : MODULE -> STRING LIST
})

<p>Which returns a list of all names found the module's namespace.  Note that
any reasonable module is required to have a unique modnamespace.</p>

<p>BOZO this does not get named blocks.  Unclear how nested blocks are supposed
to be handled.  We do at least get function and task names, and names from
events.</p>")

(defprojection vl-namedarglist->names (x)
  ;; BOZO this function is somewhat misplaced, it doesn't really have anything
  ;; to do with the modnamespace.
  (vl-namedarg->name x)
  :guard (vl-namedarglist-p x)
  :result-type string-listp
  :nil-preservingp t
  :parents (vl-namedarglist-p)
  :short "Collect all names from a @(see vl-namedarglist-p).")

(defprojection vl-modinstlist->modnames (x)
  ;; BOZO also somewhat misplaced -- doesn't have to do with the namespace.
  (vl-modinst->modname x)
  :guard (vl-modinstlist-p x)
  :result-type string-listp
  :nil-preservingp t
  :parents (vl-modinstlist-p)
  :short "Collect all module names (not instance names!) from a
          @(see vl-modinstlist-p).")

(defprojection vl-paramdecllist->names (x)
  (vl-paramdecl->name x)
  :guard (vl-paramdecllist-p x)
  :result-type string-listp
  :nil-preservingp t
  :parents (vl-paramdecllist-p modnamespace)
  :short "Collect all names declared in a @(see vl-paramdecllist-p).")

(defprojection vl-portdecllist->names (x)
  (vl-portdecl->name x)
  :guard (vl-portdecllist-p x)
  :result-type string-listp
  :nil-preservingp t
  :parents (vl-portdecllist-p modnamespace)
  :short "Collect all names declared in a @(see vl-portdecllist-p).")

(defprojection vl-netdecllist->names (x)
  (vl-netdecl->name x)
  :guard (vl-netdecllist-p x)
  :result-type string-listp
  :nil-preservingp t
  :parents (vl-netdecllist-p modnamespace)
  :short "Collect all names declared in a @(see vl-netdecllist-p).")

(defprojection vl-vardecllist->names (x)
  (vl-vardecl->name x)
  :guard (vl-vardecllist-p x)
  :result-type string-listp
  :nil-preservingp t
  :parents (vl-vardecllist-p modnamespace)
  :short "Collect all names declared in a @(see vl-vardecllist-p).")

(defprojection vl-regdecllist->names (x)
  (vl-regdecl->name x)
  :guard (vl-regdecllist-p x)
  :result-type string-listp
  :nil-preservingp t
  :parents (vl-regdecllist-p modnamespace)
  :short "Collect all names declared in a @(see vl-regdecllist-p).")

(defprojection vl-eventdecllist->names (x)
  (vl-eventdecl->name x)
  :guard (vl-eventdecllist-p x)
  :result-type string-listp
  :nil-preservingp t
  :parents (vl-eventdecllist-p modnamespace)
  :short "Collect all names declared in a @(see vl-eventdecllist-p).")



(define vl-gateinstlist->names-exec ((x vl-gateinstlist-p) acc)
  :parents (vl-gateinstlist->names)
  (b* (((when (atom x))
        acc)
       (name (vl-gateinst->name (car x)))
       (acc  (if name (cons name acc) acc)))
    (vl-gateinstlist->names-exec (cdr x) acc)))

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
       :exec (reverse (vl-gateinstlist->names-exec x nil)))
  ///
  (defthm vl-gateinstlist->names-exec-removal
    (equal (vl-gateinstlist->names-exec x acc)
           (revappend (vl-gateinstlist->names x) acc))
    :hints(("Goal" :in-theory (enable vl-gateinstlist->names-exec))))

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
    (implies (force (vl-gateinstlist-p x))
             (string-listp (vl-gateinstlist->names x)))))


(define vl-modinstlist->instnames-exec ((x vl-modinstlist-p) acc)
  :parents (vl-modinstlist->instnames)
  (b* (((when (atom x))
        acc)
       (name (vl-modinst->instname (car x)))
       (acc  (if name (cons name acc) acc)))
    (vl-modinstlist->instnames-exec (cdr x) acc)))

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
       :exec (reverse (vl-modinstlist->instnames-exec x nil)))
  ///
  (defthm vl-modinstlist->instnames-exec-removal
    (equal (vl-modinstlist->instnames-exec x acc)
           (revappend (vl-modinstlist->instnames x) acc))
    :hints(("Goal" :in-theory (enable vl-modinstlist->instnames-exec))))

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
    (implies (force (vl-modinstlist-p x))
             (string-listp (vl-modinstlist->instnames x)))))


(define vl-module->modnamespace-exec ((x vl-module-p))
  :parents (modnamespace)
  :short "Tail-recursive implementation of @(see vl-module->modnamespace)."
  :long "<p>This is sort of an inherently inefficient operation, since we are
to perform a cons for every object in the module.  But we can at least do
everything tail recursively, etc.</p>"
  (b* (((vl-module x) x)
       (acc (vl-netdecllist->names-exec     x.netdecls   nil))
       (acc (vl-regdecllist->names-exec     x.regdecls   acc))
       (acc (vl-vardecllist->names-exec     x.vardecls   acc))
       (acc (vl-eventdecllist->names-exec   x.eventdecls acc))
       (acc (vl-paramdecllist->names-exec   x.paramdecls acc))
       (acc (vl-fundecllist->names-exec     x.fundecls   acc))
       (acc (vl-taskdecllist->names-exec    x.taskdecls  acc))
       (acc (vl-modinstlist->instnames-exec x.modinsts   acc))
       (acc (vl-gateinstlist->names-exec    x.gateinsts  acc)))
    acc)
  ///
  (defthm true-listp-of-vl-module->modnamespace-exec
    (true-listp (vl-module->modnamespace-exec x))
    :rule-classes :type-prescription))


(define vl-module->modnamespace ((x vl-module-p))
  :returns (names string-listp :hyp :fguard)
  :parents (modnamespace)
  :short "Main function for gathering up the names that are declared as
parameters, wires, variables, registers, and so on."

  :long "<p>Note: this function <b>does not</b> include the names of ports,
because as noted above they are considered to be in their own namespace which
is \"separate but overlapping\" the main namespace in the module; see @(see
modnamespace) for details.</p>

<p>If this function returns a list that is not duplicate-free, it means the
module illegally declares those duplicated names more than once.</p>

<p>To reduce memory usage, we optimize this function using @('nreverse').</p>"
  :verify-guards nil
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
       (reverse (vl-module->modnamespace-exec x)))

  ///
  (defthm vl-module->modnamespace-exec-removal
    (equal (vl-module->modnamespace-exec x)
           (rev (vl-module->modnamespace x)))
    :hints(("Goal" :in-theory (enable vl-module->modnamespace-exec))))

  (verify-guards vl-module->modnamespace)

  (defttag vl-optimize)
  (never-memoize vl-module->modnamespace-exec)
  (progn! (set-raw-mode t)
          (defun vl-module->modnamespace (x)
            (nreverse (vl-module->modnamespace-exec x)))
          (defttag nil))
  (defttag nil)

  (defthm true-listp-of-vl-module->modnamespace
    (true-listp (vl-module->modnamespace x))
    :rule-classes :type-prescription))



;; These aren't part of the module's namespace, but are just utilities for
;; collecting up various names.

(define vl-blockitem->name ((x vl-blockitem-p))
  :parents (vl-blockitem-p)
  :returns (name stringp :hyp :guard)
  :short "Get the name declared by any @(see vl-blockitem-p)."
  :guard-hints(("Goal" :in-theory (enable vl-blockitem-p)))
  (mbe :logic (cond ((vl-regdecl-p x)   (vl-regdecl->name x))
                    ((vl-vardecl-p x)   (vl-vardecl->name x))
                    ((vl-eventdecl-p x) (vl-eventdecl->name x))
                    (t                  (vl-paramdecl->name x)))
       :exec (case (tag x)
               (:vl-regdecl   (vl-regdecl->name x))
               (:vl-vardecl   (vl-vardecl->name x))
               (:vl-eventdecl (vl-eventdecl->name x))
               (otherwise     (vl-paramdecl->name x)))))

(defprojection vl-blockitemlist->names (x)
  (vl-blockitem->name x)
  :guard (vl-blockitemlist-p x)
  :result-type string-listp
  :parents (vl-blockitemlist-p)
  :short "Collect the names declared in a @(see vl-blockitemlist-p).")


(define vl-fundecl->namespace-exec ((x vl-fundecl-p) acc)
  :parents (vl-fundecl->namespace)
  (b* (((vl-fundecl x) x)
       (acc (vl-taskportlist->names-exec x.inputs acc)))
    (vl-blockitemlist->names-exec x.decls acc)))

(define vl-fundecl->namespace ((x vl-fundecl-p))
  :parents (vl-fundecl-p modnamespace)
  :short "Compute the namespace of a function declaration."
  :returns (names string-listp :hyp :guard)
  :verify-guards nil
  (mbe :logic
       (b* (((vl-fundecl x) x))
         (append (vl-taskportlist->names x.inputs)
                 (vl-blockitemlist->names x.decls)))
       :exec
       (reverse (vl-fundecl->namespace-exec x nil)))
  ///
  (defthm vl-fundecl->namespace-exec-removal
    (equal (vl-fundecl->namespace-exec x acc)
           (append (rev (vl-fundecl->namespace x)) acc))
    :hints(("Goal" :in-theory (enable vl-fundecl->namespace-exec))))

  (verify-guards vl-fundecl->namespace))


(defmapappend vl-fundecllist->namespaces (x)
  (vl-fundecl->namespace x)
  :guard (vl-fundecllist-p x)
  :transform-exec vl-fundecl->namespace-exec
  :rest
  ((defthm string-listp-of-vl-fundecllist->namespaces
     (implies (vl-fundecllist-p x)
              (string-listp (vl-fundecllist->namespaces x))))))

