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


(define vl-occform-mkwire ((name stringp)
                           (width posp)
                           &key
                           ((loc vl-location-p) '*vl-fakeloc*))
  :returns (mv (expr    vl-expr-p    :hyp :fguard
                        "already sized, unsigned")
               (netdecl vl-netdecl-p :hyp :fguard))
  :parents (occform)
  :short "Helper function for creating ports in generated modules."
  :long "<p>Imagine that we are trying to programmatically generate a module,
and we want to add a wire with the given name and width.  This function just
generates the corresponding expression and net declaration.</p>"

  (b* ((name     (hons-copy name))
       (expr     (vl-idexpr name width :vl-unsigned))
       (range    (vl-make-n-bit-range width))
       (netdecl  (make-vl-netdecl :name name
                                  :type :vl-wire
                                  :range range
                                  :loc loc)))
    (mv expr netdecl)))


(define vl-occform-mkport ((name  stringp)
                           (dir   vl-direction-p)
                           (width posp))
  :returns (mv (expr     vl-expr-p     :hyp :fguard
                         "already sized, unsigned")
               (port     vl-port-p     :hyp :fguard)
               (portdecl vl-portdecl-p :hyp :fguard)
               (netdecl  vl-netdecl-p  :hyp :fguard))
  :parents (occform)
  :short "Helper for creating ports in generated modules."
  :long "<p>Imagine that we are trying to programmatically generate a module,
and we want to add a port with the given name, direction, and width.  This
function just generates the corresponding expression, port, port declaration,
and net declaration.</p>"

  (b* ((name     (hons-copy name))
       (expr     (vl-idexpr name width :vl-unsigned))
       (range    (and width (vl-make-n-bit-range width)))
       (port     (make-vl-port :name name :expr expr :loc *vl-fakeloc*))
       (portdecl (make-vl-portdecl :name  name
                                   :dir   dir
                                   :range range
                                   :loc   *vl-fakeloc*))
       (netdecl  (make-vl-netdecl :name  name
                                  :type  :vl-wire
                                  :range range
                                  :loc   *vl-fakeloc*)))
      (mv expr port portdecl netdecl)))


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
       :long ,(cat "<p><b>Signature:</b> @(call " (symbol-name name) ")
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


(define vl-simple-instantiate-args-main
  ((actuals   vl-exprlist-p)
   (ports     vl-portlist-p)
   (portdecls vl-portdecllist-p "for figuring out directions"))
  :guard (same-lengthp actuals ports)
  :returns (args vl-plainarglist-p :hyp :fguard)
  :parents (vl-simple-instantiate)
  :short "Create plainargs binding some actuals to their ports, filling in the
portnames and directions."

  (b* (((when (atom actuals))
        nil)
       ((vl-port port) (car ports))
       ((unless (and port.name
                     port.expr
                     (vl-idexpr-p port.expr)
                     (equal (vl-idexpr->name port.expr) port.name)))
        (er hard? 'vl-simple-instantiate-args-main
            "Port too complicated: ~x0.~%" (car ports)))

       (decl (vl-find-portdecl port.name portdecls))
       ((unless decl)
        (er hard? 'vl-simple-instantiate-args-main
            "Port is not declared: ~x0.~%" port.name))

       (dir (vl-portdecl->dir decl))
       (arg (make-vl-plainarg :expr     (car actuals)
                              :dir      dir
                              :portname port.name)))
    (cons arg
          (vl-simple-instantiate-args-main (cdr actuals) (cdr ports)
                                           portdecls))))

(define vl-simple-instantiate
  ((x        "submodule to create an instance of" vl-module-p)
   (instname "name for the new instance"          stringp)
   (actuals  "expressions to bind to the module's ports in port order"
             vl-exprlist-p)
   &key
   ((loc vl-location-p) '*vl-fakeloc*))
  :returns (inst vl-modinst-p :hyp :fguard)
  :parents (occform)
  :short "Convenient way to generating module instances."

  :long "<p>If you are writing code to generate modules (as we often are in
@(see occform)), it can be particularly onerous to generate module instances
because you have to build @(see vl-plainarg-p) structures for all of the
arguments and wrap these up in a @(see vl-arguments-p).</p>

<p>@('vl-simple-instantiate') automates this, at least for instantiating simple
modules.  You tell it the module you want to instantiate, @('x'), and the
expressions you want to use as the @('actuals').  It pairs up these actuals
with the submodule's ports, figuring out the directions/names of the plainargs,
etc., and gives you back the new instance.  As an added bonus, you get basic
arity checking.</p>"

  (b* (((vl-module x) x)
       (plainargs
        (if (same-lengthp actuals x.ports)
            (vl-simple-instantiate-args-main actuals x.ports x.portdecls)
          (er hard? 'vl-simple-instantiate
              "Wrong number of arguments for ~x0.~%" x.name))))
    (make-vl-modinst :modname   x.name
                     :instname  instname
                     :paramargs (vl-arguments nil nil)
                     :portargs  (vl-arguments nil plainargs)
                     :loc       loc)))


(defsection vl-simple-inst
  :parents (vl-simple-instantiate)
  :short "Like @(see vl-simple-instantiate) except it's a nice macro so that
you don't have to put the actuals in a list."
  :long "<p>On the down-side, you can't give a location.</p>
@(def vl-simple-inst)"

  (defmacro vl-simple-inst (x instname &rest args)
    `(vl-simple-instantiate ,x ,instname (list . ,args))))


(define vl-simple-instantiate-list
  ((x        "module to instantiate" vl-module-p)
   (prefix   "base name for instances, e.g., prefix_3, prefix_2" stringp)
   (arglists "actuals for each instance" vl-exprlistlist-p)
   &key
   ((n natp "name index, counts up") '0)
   ((loc vl-location-p) '*vl-fakeloc*))
  :returns (insts vl-modinstlist-p :hyp :fguard)
  :parents (vl-simple-instantiate)
  :short "Generate a bunch of module instances."
  (if (atom arglists)
      nil
    (cons (vl-simple-instantiate x (cat prefix (natstr n)) (car arglists) :loc loc)
          (vl-simple-instantiate-list-fn x prefix (cdr arglists) (+ 1 n) loc))))



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



(define vl-occform-mkwires ((prefix stringp "name prefix for each wire")
                            (i      natp "starting index, <b>inclusive!</b>")
                            (n      natp "ending index, <b>non-inclusive!</b>")
                            &key
                            (width  posp "width of each wire")
                            ((loc vl-location-p) '*vl-fakeloc*))
  :guard   (<= i n)
  :returns (mv (exprs vl-exprlist-p :hyp :fguard)
               (decls vl-netdecllist-p :hyp :fguard))
  :parents (occform)
  :short "Helper function for creating lists of net declarations."
  :long "<p>We generate a list of net declarations,</p>
@({
 wire [width-1:0] prefix_i;
 ...
 wire [width-1:0] prefix_{n-1};
})

<p>And return these declarations, along with the corresponding expressions with
sizes pre-computed.</p>"

  :measure (nfix (- (nfix n) (nfix i)))

  (b* (((when (zp (- (lnfix n) (lnfix i))))
        (mv nil nil))
       (name  (hons-copy (cat prefix (natstr i))))
       (expr  (vl-idexpr name width :vl-unsigned))
       (decl  (make-vl-netdecl :name  name
                               :type  :vl-wire
                               :range (vl-make-n-bit-range width)
                               :loc   loc))
       ((mv rest-exprs rest-decls)
        (vl-occform-mkwires prefix (+ 1 (lnfix i)) n
                            :width width :loc loc)))
    (mv (cons expr rest-exprs)
        (cons decl rest-decls)))

  ///
  (defmvtypes vl-occform-mkwires-fn (true-listp true-listp))

  (defthm len-of-vl-occform-mkwires
    (b* (((mv exprs decls) (vl-occform-mkwires prefix i n
                                               :width width
                                               :loc loc)))
      (and (equal (len exprs) (nfix (- (nfix n) (nfix i))))
           (equal (len decls) (nfix (- (nfix n) (nfix i)))))))

  (defthm vl-occform-mkwires-under-iff
    (b* (((mv exprs decls) (vl-occform-mkwires prefix i n
                                               :width width
                                               :loc loc)))
      (and (iff exprs (posp (- (nfix n) (nfix i))))
           (iff decls (posp (- (nfix n) (nfix i))))))))
