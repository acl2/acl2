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
(include-book "allexprs")
(include-book "context")
(local (include-book "../util/arithmetic"))

(defxdoc ctxexprs
  :parents (mlib)
  :short "Functions for gathering expressions and the context in which they
occur."

  :long "<p>Like the @(see allexprs) family of functions, these functions
gather up what we regard as the \"top level\" expressions used throughout some
module.  But whereas the <tt>allexprs</tt> functions just return flat lists of
expressions, we return a @(see vl-exprctxalist-p) that associates each
expression with a @(see vl-context-p) describing its origin.</p>")



(defsection vl-exprctxalist-p
  :parents (ctxexprs)
  :short "An alist binding @(see vl-expr-p)s to @(see vl-context-p)s."
  :long "<p>These alists are produced by our @(see ctxexprs) functions, and
essentially say where some expressions are from.</p>"

  (defund vl-exprctxalist-p (x)
    (declare (xargs :guard t))
    (or (atom x)
        (and (consp (car x))
             (vl-expr-p (caar x))
             (vl-context-p (cdar x))
             (vl-exprctxalist-p (cdr x)))))

  (local (in-theory (enable vl-exprctxalist-p)))

  (defthm vl-exprctxalist-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprctxalist-p x)
                    t)))

  (defthm vl-exprctxalist-p-of-cons
    (equal (vl-exprctxalist-p (cons a x))
           (and (consp a)
                (vl-expr-p (car a))
                (vl-context-p (cdr a))
                (vl-exprctxalist-p x))))

  (defthm vl-exprctxalist-p-of-append
    (implies (and (force (vl-exprctxalist-p x))
                  (force (vl-exprctxalist-p y)))
             (vl-exprctxalist-p (append x y))))

  (defthm vl-exprlist-p-of-strip-cars-when-vl-exprctxalist-p
    (implies (vl-exprctxalist-p x)
             (vl-exprlist-p (strip-cars x))))

  (defthm alistp-when-vl-exprctxalist-p
    (implies (vl-exprctxalist-p x)
             (equal (alistp x)
                    (true-listp x)))))



(defsection vl-make-exprctxalist

  (defund vl-make-exprctxalist (exprs ctx)
    (declare (xargs :guard (and (vl-exprlist-p exprs)
                                (vl-context-p ctx))))
    (if (atom exprs)
        nil
      (cons (cons (car exprs) ctx)
            (vl-make-exprctxalist (cdr exprs) ctx))))

  (local (in-theory (enable vl-make-exprctxalist)))

  (defthm vl-exprctxalist-p-of-vl-make-exprctxalist
    (implies (and (force (vl-exprlist-p exprs))
                  (force (vl-context-p ctx)))
             (vl-exprctxalist-p (vl-make-exprctxalist exprs ctx)))))


(defmacro def-vl-ctxexprs (&key type)
  (let* ((mksym-package-symbol 'vl)
         (type-p   (mksym type '-p))
         (collect  (mksym type '-ctxexprs))
         (allexprs (mksym type '-allexprs))
         (type-thm (mksym 'vl-exprctxalist-p-of- collect))
         (true-thm (mksym 'true-listp-of- collect)))
    `(defsection ,collect

       (defund ,collect (mod x)
         (declare (xargs :guard (and (stringp mod)
                                     (,type-p x))))
         (vl-make-exprctxalist (,allexprs x)
                               (make-vl-context :mod mod :elem x)))

       (local (in-theory (enable ,collect)))

       (defthm ,type-thm
         (implies (and (force (stringp mod))
                       (force (,type-p x)))
                  (vl-exprctxalist-p (,collect mod x))))

       (defthm ,true-thm
         (true-listp (,collect mod x))
         :rule-classes :type-prescription))))


(defmacro def-vl-ctxexprs-list (&key element list)
  (let* ((mksym-package-symbol 'vl)
         (list-type-p  (mksym list '-p))
         (collect-list (mksym list '-ctxexprs))
         (collect-elem (mksym element '-ctxexprs))
         (type-thm     (mksym 'vl-exprctxalist-p-of- collect-list)))

    `(defsection ,collect-list

       (defmapappend ,collect-list (mod x)
         (,collect-elem mod x)
         :guard
         (and (stringp mod)
              (,list-type-p x)))

       (local (in-theory (enable ,collect-list)))

       (defthm ,type-thm
         (implies (and (force (stringp mod))
                       (force (,list-type-p x)))
                  (vl-exprctxalist-p (,collect-list mod x)))))))

(def-vl-ctxexprs :type vl-port)
(def-vl-ctxexprs :type vl-portdecl)
(def-vl-ctxexprs :type vl-assign)
(def-vl-ctxexprs :type vl-netdecl)
(def-vl-ctxexprs :type vl-vardecl)
(def-vl-ctxexprs :type vl-regdecl)
(def-vl-ctxexprs :type vl-eventdecl)
(def-vl-ctxexprs :type vl-paramdecl)
(def-vl-ctxexprs :type vl-fundecl)
(def-vl-ctxexprs :type vl-taskdecl)
(def-vl-ctxexprs :type vl-modinst)
(def-vl-ctxexprs :type vl-gateinst)
(def-vl-ctxexprs :type vl-always)
(def-vl-ctxexprs :type vl-initial)

(def-vl-ctxexprs-list :element vl-port      :list vl-portlist)
(def-vl-ctxexprs-list :element vl-portdecl  :list vl-portdecllist)
(def-vl-ctxexprs-list :element vl-assign    :list vl-assignlist)
(def-vl-ctxexprs-list :element vl-netdecl   :list vl-netdecllist)
(def-vl-ctxexprs-list :element vl-vardecl   :list vl-vardecllist)
(def-vl-ctxexprs-list :element vl-regdecl   :list vl-regdecllist)
(def-vl-ctxexprs-list :element vl-eventdecl :list vl-eventdecllist)
(def-vl-ctxexprs-list :element vl-paramdecl :list vl-paramdecllist)
(def-vl-ctxexprs-list :element vl-fundecl   :list vl-fundecllist)
(def-vl-ctxexprs-list :element vl-taskdecl  :list vl-taskdecllist)
(def-vl-ctxexprs-list :element vl-modinst   :list vl-modinstlist)
(def-vl-ctxexprs-list :element vl-gateinst  :list vl-gateinstlist)
(def-vl-ctxexprs-list :element vl-always    :list vl-alwayslist)
(def-vl-ctxexprs-list :element vl-initial   :list vl-initiallist)

(defsection vl-module-ctxexprs

  (defund vl-module-ctxexprs (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x))
      (mbe :logic
           (append (vl-portlist-ctxexprs x.name x.ports)
                   (vl-portdecllist-ctxexprs x.name x.portdecls)
                   (vl-assignlist-ctxexprs x.name x.assigns)
                   (vl-netdecllist-ctxexprs x.name x.netdecls)
                   (vl-vardecllist-ctxexprs x.name x.vardecls)
                   (vl-regdecllist-ctxexprs x.name x.regdecls)
                   (vl-eventdecllist-ctxexprs x.name x.eventdecls)
                   (vl-paramdecllist-ctxexprs x.name x.paramdecls)
                   (vl-fundecllist-ctxexprs x.name x.fundecls)
                   (vl-taskdecllist-ctxexprs x.name x.taskdecls)
                   (vl-modinstlist-ctxexprs x.name x.modinsts)
                   (vl-gateinstlist-ctxexprs x.name x.gateinsts)
                   (vl-alwayslist-ctxexprs x.name x.alwayses)
                   (vl-initiallist-ctxexprs x.name x.initials))
           :exec
           (b* ((acc nil)
                (acc (vl-portlist-ctxexprs-exec x.name x.ports acc))
                (acc (vl-portdecllist-ctxexprs-exec x.name x.portdecls acc))
                (acc (vl-assignlist-ctxexprs-exec x.name x.assigns acc))
                (acc (vl-netdecllist-ctxexprs-exec x.name x.netdecls acc))
                (acc (vl-vardecllist-ctxexprs-exec x.name x.vardecls acc))
                (acc (vl-regdecllist-ctxexprs-exec x.name x.regdecls acc))
                (acc (vl-eventdecllist-ctxexprs-exec x.name x.eventdecls acc))
                (acc (vl-paramdecllist-ctxexprs-exec x.name x.paramdecls acc))
                (acc (vl-fundecllist-ctxexprs-exec x.name x.fundecls acc))
                (acc (vl-taskdecllist-ctxexprs-exec x.name x.taskdecls acc))
                (acc (vl-modinstlist-ctxexprs-exec x.name x.modinsts acc))
                (acc (vl-gateinstlist-ctxexprs-exec x.name x.gateinsts acc))
                (acc (vl-alwayslist-ctxexprs-exec x.name x.alwayses acc))
                (acc (vl-initiallist-ctxexprs-exec x.name x.initials acc)))
             (reverse acc)))))

  (local (in-theory (enable vl-module-ctxexprs)))

  (defthm vl-exprlist-p-of-vl-module-ctxexprs
    (implies (vl-module-p x)
             (vl-exprctxalist-p (vl-module-ctxexprs x))))

  (defthm true-listp-of-vl-module-ctxexprs
    (true-listp (vl-module-ctxexprs x))
    :rule-classes :type-prescription))

