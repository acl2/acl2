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
(include-book "../../primitives")
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/expr-building")
(include-book "../../mlib/range-tools")
(include-book "../../mlib/namefactory")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))

; BOZO find me a home

(deflist vl-exprlistlist-p (x)
  (vl-exprlist-p x)
  :elementp-of-nil t
  :guard t)

(defthm vl-exprlistlist-p-of-pairlis$
  (implies (and (vl-exprlist-p a)
                (vl-exprlistlist-p x))
           (vl-exprlistlist-p (pairlis$ a x)))
  :hints(("Goal" :in-theory (enable pairlis$))))




(defsection vl-occform-mkwire
  :parents (occform)
  :short "Helper function for creating ports in generated modules."

  :long "<p><b>Signature:</b> @(call vl-occform-mkwire) returns <tt>(mv expr
netdecl)</tt>.</p>

<p>Imagine that we are trying to programmatically generate a module, and we
want to add a wire with the given name and width.  This function just generates
the corresponding expression and net declaration.  The expression is unsigned
and is \"already sized.\"</p>"

  (defund vl-occform-mkwire (name width)
    "Returns (MV EXPR NETDECL)"
    (declare (xargs :guard (and (stringp name)
                                (posp width))))
    (b* ((name     (hons-copy name))
         (expr     (vl-idexpr name width :vl-unsigned))
         (range    (vl-make-n-bit-range width))
         (netdecl  (make-vl-netdecl :name name :type :vl-wire :range range :loc *vl-fakeloc*)))
      (mv expr netdecl)))

  (local (in-theory (enable vl-occform-mkwire)))

  (defthm vl-occform-mkwire-basics
    (implies (and (force (stringp name))
                  (force (posp width)))
             (let ((ret (vl-occform-mkwire name width)))
               (and (vl-expr-p        (mv-nth 0 ret))
                    (vl-netdecl-p     (mv-nth 1 ret)))))))



(defsection vl-occform-mkport
  :parents (occform)
  :short "Helper for creating ports in generated modules."

  :long "<p><b>Signature:</b> @(call vl-occform-mkport) returns <tt>(mv expr
port portdecl netdecl)</tt>.</p>

<p>Imagine that we are trying to programmatically generate a module, and we
want to add a port with the given name, direction, and width.  This function
just generates the corresponding expression, range, port, port declaration, and
net declaration.  The expression is unsigned and is \"already sized.\"</p>"

  (defund vl-occform-mkport (name dir width)
    "Returns (MV EXPR PORT PORTDECL NETDECL)"
    (declare (xargs :guard (and (stringp name)
                                (vl-direction-p dir)
                                (posp width))))
    (b* ((name     (hons-copy name))
         (expr     (vl-idexpr name width :vl-unsigned))
         (range    (and width (vl-make-n-bit-range width)))
         (port     (make-vl-port :name name :expr expr :loc *vl-fakeloc*))
         (portdecl (make-vl-portdecl :name name :dir dir :range range :loc *vl-fakeloc*))
         (netdecl  (make-vl-netdecl :name name :type :vl-wire :range range :loc *vl-fakeloc*)))
      (mv expr port portdecl netdecl)))

  (local (in-theory (enable vl-occform-mkport)))

  (defthm vl-occform-mkport-basics
    (implies (and (force (stringp name))
                  (force (vl-direction-p dir))
                  (force (posp width)))
             (let ((ret (vl-occform-mkport name dir width)))
               (and (vl-expr-p        (mv-nth 0 ret))
                    (vl-port-p        (mv-nth 1 ret))
                    (vl-portdecl-p    (mv-nth 2 ret))
                    (vl-netdecl-p     (mv-nth 3 ret)))))))


(defmacro def-vl-modgen (name formals
                              &key
                              (parents '(occform))
                              (short '"")
                              (long '"")
                              body
                              (guard 't)
                              (verify-guards 't)
                              guard-debug)
  (declare (xargs :guard (and (symbolp name)
                              (symbol-listp formals))))
  (let ((mksym-package-symbol name))
    `(defsection ,name
       :parents ,parents
       :short ,short
       :long ,(str::cat "<p><b>Signature:</b> @(call " (symbol-name name) ")
returns a non-empty module list.  The first module in the list is the desired
module; the other modules are any necessary supporting modules.</p>" long)

       (defund ,name ,formals
         (declare (xargs :guard ,guard
                         :guard-debug ,guard-debug
                         :verify-guards ,verify-guards))
         ,body)

       (local (in-theory (enable ,name)))

       (defthm ,(mksym 'vl-modulelist-p-of- name)
         (implies (force ,guard)
                  (vl-modulelist-p (,name . ,formals))))

       (defthm ,(mksym 'type-of- name)
         (and (true-listp (,name . ,formals))
              (consp (,name . ,formals)))
         :rule-classes :type-prescription))))



(defsection vl-simple-instantiate

  (defund vl-simple-instantiate-args-main (args ports portdecls)
    (declare (xargs :guard (and (vl-exprlist-p args)
                                (vl-portlist-p ports)
                                (same-lengthp args ports)
                                (vl-portdecllist-p portdecls))))
    (b* (((when (atom args))
          nil)
         ((vl-port port) (car ports))
         ((unless port.name)
          (er hard? 'vl-simple-instantiate-args-main "Port too complicated: ~x0.~%" (car ports)))

         (decl (vl-find-portdecl port.name portdecls))
         ((unless decl)
          (er hard? 'vl-simple-instantiate-args-main "Port is not declared: ~x0.~%" port.name))

         (dir (vl-portdecl->dir decl)))
      (cons (make-vl-plainarg :expr (car args) :dir dir :portname port.name)
            (vl-simple-instantiate-args-main (cdr args) (cdr ports) portdecls))))

  (defthm vl-plainarglist-p-of-vl-simple-instantiate-args-main
    (implies (and (force (vl-exprlist-p args))
                  (force (vl-portlist-p ports))
                  (force (same-lengthp args ports))
                  (force (vl-portdecllist-p portdecls)))
             (vl-plainarglist-p (vl-simple-instantiate-args-main args ports portdecls)))
    :hints(("Goal" :in-theory (enable vl-simple-instantiate-args-main))))

  (defund vl-simple-instantiate-fn (x instname args loc)
    (declare (xargs :guard (and (vl-module-p x)
                                (stringp instname)
                                (vl-exprlist-p args)
                                (vl-location-p loc))))
    (b* (((vl-module x) x)
         (plainargs
          (if (same-lengthp args x.ports)
              (vl-simple-instantiate-args-main args x.ports x.portdecls)
            (er hard? 'vl-simple-instantiate "Wrong number of arguments for ~x0.~%" x.name))))
      (make-vl-modinst :modname x.name
                       :instname instname
                       :paramargs (vl-arguments nil nil)
                       :portargs (vl-arguments nil plainargs)
                       :loc loc)))

  (defmacro vl-simple-instantiate (x instname args &key (loc '*vl-fakeloc*))
    `(vl-simple-instantiate-fn ,x ,instname ,args ,loc))

  (add-macro-alias vl-simple-instantiate vl-simple-instantiate-fn)

  (defthm vl-modinst-p-of-vl-simple-instantiate-fn
    (implies (and (force (vl-module-p x))
                  (force (stringp instname))
                  (force (vl-exprlist-p args))
                  (force (vl-location-p loc)))
             (vl-modinst-p (vl-simple-instantiate-fn x instname args loc)))
    :hints(("Goal" :in-theory (enable vl-simple-instantiate-fn)))))


(defmacro vl-simple-inst (x instname &rest args)
  `(vl-simple-instantiate ,x ,instname (list . ,args)))


(defsection vl-simple-instantiate-list

  (defund vl-simple-instantiate-list-fn (x prefix arglists n loc)
    (declare (xargs :guard (and (vl-module-p x)
                                (stringp prefix)
                                (vl-exprlistlist-p arglists)
                                (natp n)
                                (vl-location-p loc))))
    (if (atom arglists)
        nil
      (cons (vl-simple-instantiate x (str::cat prefix (str::natstr n)) (car arglists)
                                   :loc loc)
            (vl-simple-instantiate-list-fn x prefix (cdr arglists) (+ 1 n) loc))))

  (defthm vl-modinstlist-p-of-vl-simple-instantiate-list-fn
    (implies (and (force (vl-module-p x))
                  (force (stringp prefix))
                  (force (vl-exprlistlist-p arglists))
                  (force (natp n))
                  (force (vl-location-p loc)))
             (vl-modinstlist-p (vl-simple-instantiate-list-fn x prefix arglists n loc)))
    :hints(("Goal" :in-theory (enable vl-simple-instantiate-list-fn))))

  (defmacro vl-simple-instantiate-list (mod prefix arglists &key (n '0) (loc '*vl-fakeloc*))
    `(vl-simple-instantiate-list-fn ,mod ,prefix ,arglists ,n ,loc))

  (add-macro-alias vl-simple-instantiate-list vl-simple-instantiate-list-fn))

;; BOZO could optimize these to avoid the unnecessary pairlis$'ing in the common
;; cases of 2-3 args.

(defund fold-pairlist (x)
  (declare (xargs :guard (true-list-listp x)))
  (if (atom x)
      nil
    (pairlis$ (car x)
              (fold-pairlist (cdr x)))))

(defthm vl-exprlistlist-p-of-fold-pairlist
  (implies (vl-exprlistlist-p x)
           (vl-exprlistlist-p (fold-pairlist x)))
  :hints(("Goal" :in-theory (enable fold-pairlist))))

(defmacro vl-simple-inst-list (x prefix &rest arg-lists)
  `(vl-simple-instantiate-list ,x ,prefix (fold-pairlist (list . ,arg-lists))))



