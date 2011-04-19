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
(include-book "../../mlib/expr-tools")
(include-book "../../mlib/expr-building")
(include-book "../../mlib/range-tools")
(include-book "../../mlib/namefactory")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))


(defconst |*occform-1'b0*|
  ;; An already-sized one-bit zero, for use only in occform.
  (hons-copy (make-vl-atom :guts (make-vl-constint :value 0
                                                   :origwidth 1
                                                   :origtype :vl-unsigned)
                           :finalwidth 1
                           :finaltype :vl-unsigned)))


(defconst |*occform-1'b1*|
  ;; An already-sized one-bit one, for use only in occform.
  (hons-copy (make-vl-atom :guts (make-vl-constint :value 1
                                                   :origwidth 1
                                                   :origtype :vl-unsigned)
                           :finalwidth 1
                           :finaltype :vl-unsigned)))


(defconst |*occform-1'bx*|
  ;; An already-sized one-bit X, for use only in occform.
  (hons-copy (make-vl-atom :guts (make-vl-weirdint :bits (list :vl-xval)
                                                   :origwidth 1
                                                   :origtype :vl-unsigned)
                           :finalwidth 1
                           :finaltype :vl-unsigned)))

(defconst |*occform-1'bz*|
  ;; An already-sized one-bit Z, for use only in occform.
  (hons-copy (make-vl-atom :guts (make-vl-weirdint :bits (list :vl-zval)
                                                   :origwidth 1
                                                   :origtype :vl-unsigned)
                           :finalwidth 1
                           :finaltype :vl-unsigned)))



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