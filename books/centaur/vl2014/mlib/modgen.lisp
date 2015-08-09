; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "range-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))
(local (xdoc::set-default-parents occform))

(define vl-occform-mkwire
  :short "Helper function for creating ports in generated modules."
  ((name stringp)
   (width posp)
   &key
   ((loc vl-location-p) '*vl-fakeloc*))
  :returns (mv (expr    vl-expr-p "already sized, unsigned")
               (vardecl vl-vardecl-p))
  :verbosep t
  :long "<p>Imagine that we are trying to programmatically generate a module,
and we want to add a wire with the given name and width.  This function just
generates the corresponding expression and net declaration.</p>"
  (b* ((name     (hons-copy (string-fix name)))
       (width    (lposfix width))
       (expr     (vl-idexpr name width :vl-unsigned))
       (range    (vl-make-n-bit-range width))
       (type     (hons-copy
                  (make-vl-coretype :name :vl-logic :signedp nil
                                    :pdims (list range))))
       (vardecl  (make-vl-vardecl :name name :type type :nettype :vl-wire :loc loc)))
    (mv expr vardecl)))

(define vl-occform-mkport ((name  stringp)
                           (dir   vl-direction-p)
                           (width posp))
  :returns (mv (expr     vl-expr-p)
               (port     vl-port-p)
               (portdecl vl-portdecl-p)
               (vardecl  vl-vardecl-p))
  :short "Helper for creating ports in generated modules."
  :long "<p>Imagine that we are trying to programmatically generate a module,
and we want to add a port with the given name, direction, and width.  This
function just generates the corresponding expression, port, port declaration,
and net declaration.</p>"

  (b* ((name     (hons-copy (string-fix name)))
       (width    (lposfix width))
       (expr     (vl-idexpr name width :vl-unsigned))
       (range    (vl-make-n-bit-range width))
       (type     (hons-copy (make-vl-coretype :name :vl-logic :signedp nil
                                              :pdims (list range))))
       (port     (make-vl-regularport :name name :expr expr :loc *vl-fakeloc*))
       (portdecl (make-vl-portdecl :name  name :type type :dir dir :loc *vl-fakeloc*))
       (vardecl  (make-vl-vardecl  :name  name :type type :nettype :vl-wire :loc *vl-fakeloc* :atts '(("VL_PORT_IMPLICIT")))))
    (mv expr port portdecl vardecl)))

(defun def-vl-modgen-fn (name raw-formals
                              parents short long
                              body
                              guard verify-guards guard-debug
                              state)
  (declare (xargs :mode :program :stobjs state))
  (let* ((world (w state))
         (mksym-package-symbol name)
         (parsed-formals (std::parse-formals `(def-vl-modgen ,name) raw-formals '(:type) world))
         (plain-formals  (std::formallist->names parsed-formals)))
    `(define ,name
       :parents ,parents
       :short ,short
       ,raw-formals
       :guard ,guard
       :guard-debug ,guard-debug
       :verify-guards ,verify-guards
       :returns (mods vl-modulelist-p
                      "A non-empty module list.  The first module in the list
                       is the desired module; the other modules are any
                       necessary supporting modules.")
       :long ,long
       ,body
       ///
       (defthm ,(mksym 'type-of- name)
         (and (true-listp (,name . ,plain-formals))
              (consp (,name . ,plain-formals)))
         :rule-classes :type-prescription))))

(defmacro def-vl-modgen (name raw-formals
                              &key
                              (parents '(occform))
                              (short '"")
                              (long '"")
                              body
                              (guard 't)
                              (verify-guards 't)
                              guard-debug)
  `(make-event
    (def-vl-modgen-fn ',name ',raw-formals
      ',parents ',short ',long
      ',body
      ',guard ',verify-guards ',guard-debug
      state)))

(define vl-simple-instantiate-args-main
  :short "Create plainargs binding some actuals to their ports, filling in the
portnames and directions."
  ((actuals   vl-exprlist-p)
   (ports     vl-regularportlist-p)
   (portdecls vl-portdecllist-p "for figuring out directions"))
  :guard (same-lengthp actuals ports)
  :returns (args vl-plainarglist-p)
  :parents (vl-simple-instantiate)
  (b* (((when (atom actuals))
        nil)
       ((vl-regularport port) (car ports))
       ((unless (and port.name
                     port.expr
                     (vl-idexpr-p port.expr)
                     (equal (vl-idexpr->name port.expr) port.name)))
        (raise "Port too complicated: ~x0.~%" (car ports)))

       (decl (vl-find-portdecl port.name portdecls))
       ((unless decl)
        (raise "Port is not declared: ~x0.~%" port.name))

       (actual (vl-expr-fix (car actuals)))
       (dir    (vl-portdecl->dir decl))
       (arg    (make-vl-plainarg :expr     actual
                                 :dir      dir
                                 :portname port.name)))
    (cons arg
          (vl-simple-instantiate-args-main (cdr actuals) (cdr ports)
                                           portdecls))))


(define vl-simple-instantiate
  ((x        vl-module-p   "submodule to create an instance of")
   (instname stringp       "name for the new instance")
   (actuals  vl-exprlist-p "expressions to bind to the module's ports in port order")
   &key
   ((loc vl-location-p) '*vl-fakeloc*))
  :returns (inst vl-modinst-p)
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
        (if (and (not x.ifports)
                 (same-lengthp actuals x.ports))
            (vl-simple-instantiate-args-main actuals x.ports x.portdecls)
          (raise "Wrong number of arguments for ~x0.~%" x.name))))
    (make-vl-modinst :modname   x.name
                     :instname  (string-fix instname)
                     :paramargs (make-vl-paramargs-plain :args nil)
                     :portargs  (make-vl-arguments-plain :args plainargs)
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
  :returns (insts vl-modinstlist-p)
  :parents (vl-simple-instantiate)
  :short "Generate a bunch of module instances."
  (if (atom arglists)
      nil
    (cons (vl-simple-instantiate x (cat prefix (natstr n)) (car arglists) :loc loc)
          (vl-simple-instantiate-list-fn x prefix (cdr arglists) (+ 1 (lnfix n)) loc))))



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
  :returns (mv (exprs vl-exprlist-p)
               (decls vl-vardecllist-p))
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

  (b* (((when (mbe :logic (zp (- (lnfix n) (lnfix i)))
                   :exec (eql i n)))
        (mv nil nil))
       (width (lposfix width))
       (name  (hons-copy (cat prefix (natstr i))))
       (expr  (vl-idexpr name width :vl-unsigned))
       (type  (make-vl-coretype :name :vl-logic
                                :pdims (list (vl-make-n-bit-range width))))
       (decl  (make-vl-vardecl :name  name
                               :type  type
                               :nettype :vl-wire
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


(define vl-occform-mkports ((prefix stringp "name prefix for each port")
                            (i      natp    "starting index, <b>inclusive!</b>")
                            (n      natp    "ending index, <b>non-inclusive!</b>")
                            &key
                            (dir    vl-direction-p "direction of each port")
                            (width  posp           "width of each port")
                            ((loc vl-location-p)   '*vl-fakeloc*))
  :guard   (<= i n)
  :returns (mv (exprs     vl-exprlist-p)
               (ports     vl-portlist-p)
               (portdecls vl-portdecllist-p)
               (vardecls  vl-vardecllist-p))
  :short "Helper function for creating lists of port declarations."
  :measure (nfix (- (nfix n) (nfix i)))

  (b* (((when (mbe :logic (zp (- (lnfix n) (lnfix i)))
                   :exec (eql i n)))
        (mv nil nil nil nil))
       (name1 (hons-copy (cat prefix (natstr i))))
       ((mv expr1 port1 portdecl1 vardecl1)
        (vl-occform-mkport name1 dir width))
       ((mv exprs2 ports2 portdecls2 vardecls2)
        (vl-occform-mkports prefix (+ 1 (lnfix i)) n :dir dir :width width :loc loc)))
    (mv (cons expr1 exprs2)
        (cons port1 ports2)
        (cons portdecl1 portdecls2)
        (cons vardecl1 vardecls2)))
  ///
  (defmvtypes vl-occform-mkports-fn
    (true-listp true-listp true-listp true-listp))

  (defthm len-of-vl-occform-mkports
    (b* (((mv exprs ports portdecls vardecls)
          (vl-occform-mkports prefix i n :dir dir :width width :loc loc))
         (len (nfix (- (nfix n) (nfix i)))))
      (and (equal (len exprs) len)
           (equal (len ports) len)
           (equal (len portdecls) len)
           (equal (len vardecls) len))))

  (defthm vl-occform-mkports-under-iff
    (b* (((mv exprs ports portdecls vardecls)
          (vl-occform-mkports prefix i n :dir dir :width width :loc loc))
         (len (- (nfix n) (nfix i))))
      (and (iff exprs     (posp len))
           (iff ports     (posp len))
           (iff portdecls (posp len))
           (iff vardecls  (posp len))))))
