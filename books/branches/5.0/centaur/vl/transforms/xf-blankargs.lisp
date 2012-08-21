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
(include-book "../mlib/find-module")
(include-book "../mlib/namefactory")
(include-book "../mlib/range-tools")
(include-book "../mlib/port-tools")
(local (include-book "../util/arithmetic"))


(defxdoc blankargs
  :parents (transforms)
  :short "A transformation which \"fills in\" blank arguments."

  :long "<p>Verilog permits the use of \"blank\" expressions as arguments to
module and gate instances.  See @(see vl-port-p) and @(see vl-plainarg-p) for
some additional discussion.</p>

<p>This transformation \"fills in\" any blank arguments that are connected to
non-blank ports with new, fresh wires.  A related (but separate) transformation
is @(see drop-blankports) which eliminates any blank ports and their
corresponding arguments.</p>

<p>If a blank argument is given to a submodule's non-blank input port, it is
the equivalent of passing in a Z value.  If a blank argument is given to a
submodule's non-blank output port, the value being emitted on that port is
simply inaccessible in the superior module.</p>

<p>In either case, we simply replace the blank argument with a new, fresh,
otherwise undriven wire of the appropriate size.  This approach works equally
well for inputs and outputs.  We give these wires names such as
<tt>blank_27</tt>.</p>

<p>Unlike @(see drop-blankports) which can be applied at any time after @(see
argresolve), the blankargs transformation requires that expression sizes have
been computed (see @(see selfsize) and @(see ctxsize)) since the new wires need
to have the appropriate size.  We also expect that the @(see replicate) transform
has been run to ensure that no instances have ranges.</p>")




(defsection vl-modinst-plainarglist-blankargs
  :parents (blankargs)
  :short "Fill in any blank arguments in a module instance's argument list."

  :long "<p>Signature: @(call vl-modinst-plainarglist-blankargs) returns <tt>(mv
warnings args-prime netdecls nf-prime)</tt>.</p>

<p>As inputs:</p>

<ul>

<li><tt>args</tt> should be a list of @(see vl-plainarg-p)s for a module
instance,</li>

<li><tt>ports</tt> should be the corresponding ports from the submodule being
instantiated,</li>

<li><tt>nf</tt> is a @(see vl-namefactory-p) for fresh name generation in the
superior module,</li>

<li><tt>warnings</tt> is an @(see warnings) accumulator for the superior module,</li>

<li><tt>inst</tt> is semantically meaningless and is only used for warning
messages; it's the actual module instance that these arguments come from.</li>

</ul>

<p>We replace any blank arguments with fresh wires of the appropriate size.
The rewritten arguments are returned as <tt>args-prime</tt>, and any new
netdecls are that should be added to the superior module are returned as
<tt>netdecls</tt>.</p>"

  (defund vl-modinst-plainarglist-blankargs (args ports nf warnings inst)
    "Returns (MV WARNINGS ARGS-PRIME NETDECLS NF')"
    (declare (xargs :guard (and (vl-plainarglist-p args)
                                (vl-portlist-p ports)
                                (same-lengthp args ports)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings)
                                (vl-modinst-p inst))))
    (b* (((when (atom args))
          (mv warnings nil nil nf))
         ((mv warnings cdr-prime cdr-netdecls nf)
          (vl-modinst-plainarglist-blankargs (cdr args) (cdr ports) nf warnings inst))

         (arg1 (car args))
         ((vl-plainarg arg1) arg1)
         ((when arg1.expr)
          ;; Not a blank argument, leave it alone.
          (mv warnings (cons arg1 cdr-prime) cdr-netdecls nf))

         ;; Else, a blank.  Figure out the port width.
         (port1 (car ports))
         ((vl-port port1) port1)
         ((unless (and port1.expr (posp (vl-expr->finalwidth port1.expr))))
          (b* ((w (make-vl-warning
                   :type :vl-blankargs-fail
                   :msg "~a0: expected all ports to have expressions with ~
                         their widths, but a blank argument is connected to ~
                         port ~a1, which has expression ~a2 and width ~x3."
                   :args (list inst
                               port1
                               port1.expr
                               (and port1.expr
                                    (vl-expr->finalwidth port1.expr)))
                   :fatalp t
                   :fn 'vl-modinst-plainarglist-blankargs)))
            (mv (cons w warnings)
                (cons arg1 cdr-prime)
                cdr-netdecls
                nf)))

         ;; Make a new netdecl, say blank_37, with the appropriate range.
         (port-width      (vl-expr->finalwidth port1.expr))
         ((mv newname nf) (vl-namefactory-indexed-name "blank" nf))
         (range           (vl-make-n-bit-range port-width))
         (new-netdecl     (make-vl-netdecl :name newname
                                           :type :vl-wire
                                           :range range
                                           :loc (vl-modinst->loc inst)))

         ;; Replace this blank argument with the new blank_37 wire
         (new-expr        (vl-idexpr newname port-width :vl-unsigned))
         (arg1-prime      (change-vl-plainarg arg1 :expr new-expr)))
      (mv warnings
          (cons arg1-prime cdr-prime)
          (cons new-netdecl cdr-netdecls)
          nf)))

  (defmvtypes vl-modinst-plainarglist-blankargs (nil true-listp true-listp))

  (local (in-theory (enable vl-modinst-plainarglist-blankargs)))

  (defthm vl-warninglist-p-of-vl-modinst-plainarglist-blankargs
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-modinst-plainarglist-blankargs args ports nf warnings inst)))))

  (defthm vl-modinst-plainarglist-blankargs-basics
    (implies (and (force (vl-plainarglist-p args))
                  (force (vl-portlist-p ports))
                  (force (same-lengthp args ports))
                  (force (vl-namefactory-p nf))
                  (force (vl-modinst-p inst)))
             (let ((ret (vl-modinst-plainarglist-blankargs args ports nf warnings inst)))
               (and (vl-plainarglist-p (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-namefactory-p (mv-nth 3 ret)))))))



(defsection vl-modinst-blankargs
  :parents (blankargs)
  :short "Apply the @(see blankargs) transform to a module instance."

  :long "<p><b>Signature:</b> @(call vl-modinst-blankargs) returns <tt>(mv
warnings x-prime netdecls nf-prime)</tt></p>

<p>This is just a thin wrapper around @(see vl-modinst-plainarglist-blankargs) that
takes care of looking up the ports for the module being instanced.</p>"

  (defund vl-modinst-blankargs (x mods modalist nf warnings)
    "Returns (MV WARNINGS' X' NETDECLS NF')"
    (declare (xargs :guard (and (vl-modinst-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (vl-arguments-blankfree-p (vl-modinst->portargs x)))
          ;; Oprimization.  There aren't any blanks in our arguments, so
          ;; there's nothing to do.
          (mv warnings x nil nf))

         ((vl-modinst x) x)

         ((when (vl-arguments->namedp x.portargs))
          (mv (cons (make-vl-warning
                     :type :vl-programming-error
                     :msg "~a0: expected arguments to be plain argument lists, ~
                           but found named arguments.  Did you forget to run ~
                           the argresolve transform first?"
                     :args (list x)
                     :fatalp t
                     :fn 'vl-modinst-blankargs)
                    warnings)
              x nil nf))

         ((when x.range)
          ;; Important soundness check: need to know there's no range or else
          ;; we'd potentially be connecting the same new blank wire to several
          ;; instances.
          (mv (cons (make-vl-warning
                     :type :vl-programming-error
                     :msg "~a0: expected all instances to be replicated, but ~
                           this instance has range ~a1.  Did you forget to run ~
                           the replicate transform first?"
                     :args (list x x.range)
                     :fatalp t
                     :fn 'vl-modinst-blankargs)
                    warnings)
              x nil nf))

         (plainargs (vl-arguments->args x.portargs))

         (target-mod (vl-fast-find-module x.modname mods modalist))
         ((unless target-mod)
          (mv (cons (make-vl-warning :type :vl-bad-instance
                                     :msg "~a0 refers to undefined module ~m1."
                                     :args (list x x.modname)
                                     :fatalp t
                                     :fn 'vl-modinst-blankargs)
                    warnings)
              x nil nf))

         (ports (vl-module->ports target-mod))

         ((unless (same-lengthp plainargs ports))
          (mv (cons (make-vl-warning
                     :type :vl-bad-instance
                     :msg "~a0: expected ~x1 arguments, but found ~x2 arguments."
                     :args (list x (len ports) (len plainargs))
                     :fatalp t
                     :fn 'vl-modinst-blankargs)
                    warnings)
              x nil nf))

         ((mv warnings new-plainargs netdecls nf)
          (vl-modinst-plainarglist-blankargs plainargs ports nf warnings x))

         (new-args (vl-arguments nil new-plainargs))
         (x-prime  (change-vl-modinst x :portargs new-args)))

      (mv warnings x-prime netdecls nf)))

  (defmvtypes vl-modinst-blankargs (nil nil true-listp))

  (local (in-theory (enable vl-modinst-blankargs)))

  (defthm vl-warninglist-p-of-vl-modinst-blankargs
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-modinst-blankargs x mods modalist nf warnings)))))

  (defthm vl-modinst-blankargs-basics
    (implies (and (force (vl-modinst-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-namefactory-p nf)))
             (let ((ret (vl-modinst-blankargs x mods modalist nf warnings)))
               (and (vl-modinst-p (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-namefactory-p (mv-nth 3 ret)))))))




(defsection vl-modinstlist-blankargs
  :parents (blankargs)
  :short "Extends @(see vl-modinst-blankargs) across a @(see vl-modinstlist-p)."

  (defund vl-modinstlist-blankargs (x mods modalist nf warnings)
    "Returns (MV WARNINGS' X' NETDECLS NF')"
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nil nf))
         ((mv warnings car-prime car-netdecls nf)
          (vl-modinst-blankargs (car x) mods modalist nf warnings))
         ((mv warnings cdr-prime cdr-netdecls nf)
          (vl-modinstlist-blankargs (cdr x) mods modalist nf warnings))
         (x-prime (cons car-prime cdr-prime))
         (netdecls (append car-netdecls cdr-netdecls)))
      (mv warnings x-prime netdecls nf)))

  (defmvtypes vl-modinstlist-blankargs (nil true-listp true-listp))

  (local (in-theory (enable vl-modinstlist-blankargs)))

  (defthm vl-warninglist-p-of-vl-modinstlist-blankargs
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-modinstlist-blankargs x mods modalist nf warnings)))))

  (defthm vl-modinstlist-blankargs-basics
    (implies (and (force (vl-modinstlist-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-namefactory-p nf)))
             (let ((ret (vl-modinstlist-blankargs x mods modalist nf warnings)))
               (and (vl-modinstlist-p (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-namefactory-p (mv-nth 3 ret)))))))




(defsection vl-gateinst-plainarglist-blankargs
  :parents (blankargs)
  :short "Replace any blank arguments in a gate instance with fresh wires."

  :long "<p>Signature: @(call vl-gateinst-plainarglist-blankargs) returns
<tt>(mv args-prime netdecls nf-prime)</tt>.</p>

<p>As inputs, <tt>args</tt> should be a list of @(see vl-plainarg-p)s for a
gate instance, and <tt>nf</tt> should be a @(see vl-namefactory-p) for fresh
name generation in the module.  The <tt>inst</tt> is the gate instance for
these arguments, and is only used for location information.</p>

<p>This function is simpler than @(see vl-plainarglist-blankargs) because we do
not have to consider ports: we know that every \"port\" of a gate exists and
has size 1.  We just replace any blank arguments with fresh wires of size 1.
The rewritten arguments are returned as <tt>args-prime</tt>, and any new net
declarations that should be added are returned as <tt>netdecls</tt>.</p>"

  (defund vl-gateinst-plainarglist-blankargs (args nf inst)
    "Returns (MV ARGS-PRIME NETDECLS NF)"
    (declare (xargs :guard (and (vl-plainarglist-p args)
                                (vl-namefactory-p nf)
                                (vl-gateinst-p inst))))
    (b* (((when (atom args))
          (mv nil nil nf))

         ((mv cdr-prime cdr-netdecls nf)
          (vl-gateinst-plainarglist-blankargs (cdr args) nf inst))

         (arg1 (car args))
         ((vl-plainarg arg1) arg1)

         ((when arg1.expr)
          ;; Not a blank arg, nothing needs to be done.
          (mv (cons arg1 cdr-prime) cdr-netdecls nf))

         ;; Otherwise, need to replace it with a new one-bit wire.
         ((mv newname nf) (vl-namefactory-indexed-name "blank" nf))
         (new-netdecl     (make-vl-netdecl :name newname
                                           :type :vl-wire
                                           :loc (vl-gateinst->loc inst)))
         (new-expr        (vl-idexpr newname 1 :vl-unsigned))
         (arg1-prime      (change-vl-plainarg arg1 :expr new-expr)))
      (mv (cons arg1-prime cdr-prime)
          (cons new-netdecl cdr-netdecls)
          nf)))

  (defmvtypes vl-gateinst-plainarglist-blankargs (nil true-listp))

  (local (in-theory (enable vl-gateinst-plainarglist-blankargs)))

  (defthm vl-gateinst-plainarglist-blankargs-basics
    (implies (and (force (vl-plainarglist-p args))
                  (force (vl-namefactory-p nf))
                  (force (vl-gateinst-p inst)))
             (let ((ret (vl-gateinst-plainarglist-blankargs args nf inst)))
               (and (vl-plainarglist-p (mv-nth 0 ret))
                    (vl-netdecllist-p (mv-nth 1 ret))
                    (vl-namefactory-p (mv-nth 2 ret)))))))


(defsection vl-gateinst-blankargs
  :parents (blankargs)
  :short "Apply the @(see blankargs) transform to a gate instance."

  :long "<p><b>Signature:</b> @(call vl-gateinst-blankargs) returns <tt>(mv
warnings x-prime netdecls nf-prime)</tt>.</p>

<p>This is a thin wrapper around @(see vl-gateinst-plainarglist-blankargs).</p>"

  (defund vl-gateinst-blankargs (x nf warnings)
    "Returns (MV WARNINGS' X' NETDECLS NF')"
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (vl-plainarglist-blankfree-p (vl-gateinst->args x)))
          ;; Oprimization.  There aren't any blanks in our arguments, so
          ;; there's nothing to do.
          (mv warnings x nil nf))

         ((vl-gateinst x) x)

         ((when x.range)
          ;; Important soundness check: need to know there's no range or else
          ;; we'd potentially be connecting the same new blank wire to several
          ;; instances.
          (mv (cons (make-vl-warning
                     :type :vl-programming-error
                     :msg "~a0: expected all instance arrays to be replicated, ~
                           but this gate instance has range ~a1."
                     :args (list x x.range)
                     :fatalp t
                     :fn 'vl-gateinst-blankargs)
                    warnings)
              x nil nf))

         ((mv new-args netdecls nf)
          (vl-gateinst-plainarglist-blankargs x.args nf x))

         (x-prime  (change-vl-gateinst x :args new-args)))

      (mv warnings x-prime netdecls nf)))

  (defmvtypes vl-gateinst-blankargs (nil nil true-listp))

  (local (in-theory (enable vl-gateinst-blankargs)))

  (defthm vl-warninglist-p-of-vl-gateinst-blankargs
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-gateinst-blankargs x nf warnings)))))

  (defthm vl-gateinst-blankargs-basics
    (implies (and (force (vl-gateinst-p x))
                  (force (vl-namefactory-p nf)))
             (let ((ret (vl-gateinst-blankargs x nf warnings)))
               (and (vl-gateinst-p (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-namefactory-p (mv-nth 3 ret)))))))



(defsection vl-gateinstlist-blankargs
  :parents (blankargs)
  :short "Extends @(see vl-gateinst-blankargs) across a @(see vl-gateinstlist-p)."

  (defund vl-gateinstlist-blankargs (x nf warnings)
    "Returns (MV WARNINGS' X' NETDECLS NF')"
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv warnings nil nil nf))
         ((mv warnings car-prime car-netdecls nf)
          (vl-gateinst-blankargs (car x) nf warnings))
         ((mv warnings cdr-prime cdr-netdecls nf)
          (vl-gateinstlist-blankargs (cdr x) nf warnings))
         (x-prime  (cons car-prime cdr-prime))
         (netdecls (append car-netdecls cdr-netdecls)))
      (mv warnings x-prime netdecls nf)))

  (defmvtypes vl-gateinstlist-blankargs (nil true-listp true-listp))

  (local (in-theory (enable vl-gateinstlist-blankargs)))

  (defthm vl-warninglist-p-of-vl-gateinstlist-blankargs
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-gateinstlist-blankargs x nf warnings)))))

  (defthm vl-gateinstlist-blankargs-basics
    (implies (and (force (vl-gateinstlist-p x))
                  (force (vl-namefactory-p nf)))
             (let ((ret (vl-gateinstlist-blankargs x nf warnings)))
               (and (vl-gateinstlist-p (mv-nth 1 ret))
                    (vl-netdecllist-p (mv-nth 2 ret))
                    (vl-namefactory-p (mv-nth 3 ret)))))))



(defsection vl-module-blankargs
  :parents (blankargs)
  :short "Fill in blank arguments throughout a @(see vl-module-p)."

  :long "<p>We rewrite all module instances with @(see vl-modinst-blankargs)
and all gate instances with @(see vl-gateinst-blankargs).</p>"

  (defund vl-module-blankargs (x mods modalist)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods)))))
    (b* (((when (vl-module->hands-offp x))
          x)

         ((vl-module x) x)

         (warnings (vl-module->warnings x))
         (nf       (vl-starting-namefactory x))

         ((mv warnings modinsts netdecls1 nf)
          (vl-modinstlist-blankargs x.modinsts mods modalist nf warnings))

         ((mv warnings gateinsts netdecls2 nf)
          (vl-gateinstlist-blankargs x.gateinsts nf warnings))

         (- (vl-free-namefactory nf))

         (all-netdecls (append netdecls1 netdecls2 x.netdecls)))

        (change-vl-module x
                          :modinsts modinsts
                          :gateinsts gateinsts
                          :netdecls all-netdecls
                          :warnings warnings)))

  (local (in-theory (enable vl-module-blankargs)))

  (defthm vl-module-p-of-vl-module-blankargs
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-module-p (vl-module-blankargs x mods modalist))))

  (defthm vl-module->name-of-vl-module-blankargs
    (equal (vl-module->name (vl-module-blankargs x mods modalist))
           (vl-module->name x))))


(defsection vl-modulelist-blankargs-aux
  :parents (blankargs)
  :short "Projects @(see vl-module-blankargs) across a module list."
  :long "@(def vl-modulelist-blankargs-aux)"

  (defprojection vl-modulelist-blankargs-aux (x mods modalist)
    (vl-module-blankargs x mods modalist)
    :guard (and (vl-modulelist-p x)
                (vl-modulelist-p mods)
                (equal modalist (vl-modalist mods)))
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-blankargs-aux)))

  (defthm vl-modulelist->names-of-vl-modulelist-blankargs-aux
    (equal (vl-modulelist->names (vl-modulelist-blankargs-aux x mods modalist))
           (vl-modulelist->names x))))



(defsection vl-modulelist-blankargs
  :parents (blankargs)
  :short "Top-level @(see blankargs) transformation."

  (defund vl-modulelist-blankargs (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((modalist (vl-modalist x))
         (x-prime  (vl-modulelist-blankargs-aux x x modalist))
         (-        (fast-alist-free modalist)))
      x-prime))

  (local (in-theory (enable vl-modulelist-blankargs)))

  (defthm vl-modulelist-p-of-vl-modulelist-blankargs
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-blankargs x))))

  (defthm vl-modulelist->names-of-vl-modulelist-blankargs
    (equal (vl-modulelist->names (vl-modulelist-blankargs x))
           (vl-modulelist->names x))))

