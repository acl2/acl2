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
(include-book "../mlib/namefactory")
(include-book "../mlib/range-tools")
(include-book "../mlib/port-tools")
(include-book "../mlib/expr-building")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

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
@('blank_27').</p>

<p>Unlike @(see drop-blankports) which can be applied at any time after @(see
argresolve), the blankargs transformation requires that expression sizes have
been computed (see @(see expression-sizing)) since the new wires need to have
the appropriate size.  We also expect that the @(see replicate-insts) transform
has been run to ensure that no instances have ranges.</p>")

(local (xdoc::set-default-parents blankargs))

(define vl-modinst-plainarglist-blankargs
  :short "Fill in any blank arguments in a module instance's argument list."
  ((args     vl-plainarglist-p "Arguments to a module instance")
   (ports    vl-portlist-p     "Corresponding ports of the submodule.")
   (nf       vl-namefactory-p  "Name factory for the superior module.")
   (warnings vl-warninglist-p  "Ordinary @(see warnings) accumulator.")
   (inst     vl-modinst-p      "Semantically meaningless, context for warnings."))
  :guard (same-lengthp args ports)
  :verify-guards nil
  :prepwork ((local (in-theory (disable cons-equal))))
  :hooks ((:fix :hints (("goal" :induct (vl-modinst-plainarglist-blankargs
                                         args ports nf warnings inst)
                         :in-theory (disable (:d vl-modinst-plainarglist-blankargs)))
                        (and stable-under-simplificationp
                             (flag::expand-calls-computed-hint
                              clause '(vl-modinst-plainarglist-blankargs))))))
  :returns
  (mv (warnings   vl-warninglist-p)
      (new-args   vl-plainarglist-p
                  "Copy of @('args') except that blank arguments have been
                   replaced with fresh wires of the appropriate sizes.")
      (vardecls   vl-vardecllist-p
                  "Any fresh wire declarations we've added.")
      (nf         vl-namefactory-p))
  (b* ((nf   (vl-namefactory-fix nf))
       (inst (vl-modinst-fix inst))
       ((when (atom args))
        (mv (ok) nil nil nf))
       ((mv warnings cdr-prime cdr-vardecls nf)
        (vl-modinst-plainarglist-blankargs (cdr args) (cdr ports) nf warnings inst))

       (arg1 (vl-plainarg-fix (car args)))
       ((vl-plainarg arg1) arg1)
       ((when arg1.expr)
        ;; Not a blank argument, leave it alone.
        (mv (ok) (cons arg1 cdr-prime) cdr-vardecls nf))

       ;; Else, a blank.  Figure out the port width.
       (port1 (vl-port-fix (car ports)))
       ((when (eq (tag port1) :vl-interfaceport))
        (mv (fatal :type :vl-blankargs-fail
                   :msg "~a0: blank argument is connected to interface port ~s1."
                   :args (list inst (vl-interfaceport->name port1)))
            (cons arg1 cdr-prime)
            cdr-vardecls
            nf))
       ((vl-regularport port1 ))
       ((unless (and port1.expr (posp (vl-expr->finalwidth port1.expr))))
        (mv (fatal :type :vl-blankargs-fail
                   :msg "~a0: expected all ports to have expressions with ~
                         their widths, but a blank argument is connected to ~
                         port ~a1, which has expression ~a2 and width ~x3."
                   :args (list inst
                               port1
                               port1.expr
                               (and port1.expr
                                    (vl-expr->finalwidth port1.expr))))
            (cons arg1 cdr-prime)
            cdr-vardecls
            nf))

       ;; Make a new vardecl, say blank_37, with the appropriate range.
       (port-width      (vl-expr->finalwidth port1.expr))
       ((mv newname nf) (vl-namefactory-indexed-name "blank" nf))
       (range           (vl-make-n-bit-range port-width))
       (new-nettype     (make-vl-coretype :name :vl-logic
                                          :pdims (list range)
                                          :signedp nil))
       (new-vardecl     (make-vl-vardecl :name newname
                                         :type new-nettype
                                         :nettype :vl-wire
                                         :loc (vl-modinst->loc inst)))
       ;; Replace this blank argument with the new blank_37 wire
       (new-expr        (vl-idexpr newname port-width :vl-unsigned))
       (arg1-prime      (change-vl-plainarg arg1 :expr new-expr)))
    (mv (ok)
        (cons arg1-prime cdr-prime)
        (cons new-vardecl cdr-vardecls)
        nf))
  ///
  (defmvtypes vl-modinst-plainarglist-blankargs (nil nil true-listp))
  (verify-guards vl-modinst-plainarglist-blankargs))

(define vl-modinst-blankargs
  :short "Apply the @(see blankargs) transform to a module instance."
  ((x        vl-modinst-p)
   (ss       vl-scopestack-p)
   (nf       vl-namefactory-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-modinst-p)
      (vardecls vl-vardecllist-p)
      (nf       vl-namefactory-p))
  :long "<p>This is just a wrapper for @(see vl-modinst-plainarglist-blankargs)
that takes care of looking up the ports for the module being instanced.</p>"

  (b* ((x  (vl-modinst-fix x))
       (nf (vl-namefactory-fix nf))
       ((when (vl-arguments-blankfree-p (vl-modinst->portargs x)))
        ;; Oprimization.  There aren't any blanks in our arguments, so
        ;; there's nothing to do.
        (mv (ok) x nil nf))

       ((vl-modinst x) x)

       ((when (eq (vl-arguments-kind x.portargs) :vl-arguments-named))
        (mv (fatal :type :vl-programming-error
                   :msg "~a0: expected arguments to be plain argument lists, ~
                         but found named arguments.  Did you forget to run ~
                         the argresolve transform first?"
                   :args (list x))
            x nil nf))

       ((when x.range)
        ;; Important soundness check: need to know there's no range or else
        ;; we'd potentially be connecting the same new blank wire to several
        ;; instances.
        (mv (fatal :type :vl-programming-error
                   :msg "~a0: expected all instances to be replicated, but ~
                         this instance has range ~a1.  Did you forget to run ~
                         the replicate transform first?"
                   :args (list x x.range))
            x nil nf))

       (plainargs (vl-arguments-plain->args x.portargs))

       (target-mod (vl-scopestack-find-definition x.modname ss))
       ((unless (and target-mod (eq (tag target-mod) :vl-module)))
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0 refers to undefined module ~m1."
                   :args (list x x.modname))
            x nil nf))

       (ports (vl-module->ports target-mod))
       ((unless (same-lengthp plainargs ports))
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: expected ~x1 arguments, but found ~x2 arguments."
                   :args (list x (len ports) (len plainargs)))
            x nil nf))

       ((mv warnings new-plainargs vardecls nf)
        (vl-modinst-plainarglist-blankargs plainargs ports nf warnings x))

       (new-args (make-vl-arguments-plain :args new-plainargs))
       (x-prime  (change-vl-modinst x :portargs new-args)))
    (mv warnings x-prime vardecls nf))
  ///
  (defmvtypes vl-modinst-blankargs (nil nil true-listp)))


(define vl-modinstlist-blankargs
  :short "Extends @(see vl-modinst-blankargs) across a @(see vl-modinstlist-p)."
  ((x        vl-modinstlist-p)
   (ss       vl-scopestack-p)
   (nf       vl-namefactory-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-modinstlist-p)
      (vardecls vl-vardecllist-p)
      (nf       vl-namefactory-p))
  (b* (((when (atom x))
        (mv (ok) nil nil (vl-namefactory-fix nf)))
       ((mv warnings car-prime car-vardecls nf)
        (vl-modinst-blankargs (car x) ss nf warnings))
       ((mv warnings cdr-prime cdr-vardecls nf)
        (vl-modinstlist-blankargs (cdr x) ss nf warnings))
       (x-prime (cons car-prime cdr-prime))
       (vardecls (append car-vardecls cdr-vardecls)))
    (mv warnings x-prime vardecls nf))
  ///
  (defmvtypes vl-modinstlist-blankargs (nil true-listp true-listp)))


(define vl-gateinst-plainarglist-blankargs
  :short "Replace any blank arguments in a gate instance with fresh wires."
  ((args vl-plainarglist-p "Arguments to a gate instance.")
   (nf   vl-namefactory-p)
   (inst vl-gateinst-p     "For locations of new wires."))
  :returns
  (mv (new-args vl-plainarglist-p "With any blank arguments replaced by fresh wires.")
      (vardecls vl-vardecllist-p  "Declaration for the new fresh wires.")
      (nf       vl-namefactory-p))
  :long "<p>This is simpler than @(see vl-modinst-plainarglist-blankargs)
because we do not have to consider ports: we know that every \"port\" of a gate
exists and has size 1.  We just replace any blank arguments with fresh wires of
size 1.</p>"
  (b* ((nf   (vl-namefactory-fix nf))
       (inst (vl-gateinst-fix inst))
       ((when (atom args))
        (mv nil nil nf))
       ((mv cdr-prime cdr-vardecls nf)
        (vl-gateinst-plainarglist-blankargs (cdr args) nf inst))
       (arg1 (vl-plainarg-fix (car args)))
       ((vl-plainarg arg1) arg1)
       ((when arg1.expr)
        ;; Not a blank arg, nothing needs to be done.
        (mv (cons arg1 cdr-prime) cdr-vardecls nf))
       ;; Otherwise, need to replace it with a new one-bit wire.
       ((mv newname nf) (vl-namefactory-indexed-name "blank" nf))
       (new-vardecl     (make-vl-vardecl :name newname
                                         :type *vl-plain-old-wire-type*
                                         :nettype :vl-wire
                                         :loc (vl-gateinst->loc inst)))
       (new-expr        (vl-idexpr newname 1 :vl-unsigned))
       (arg1-prime      (change-vl-plainarg arg1 :expr new-expr)))
    (mv (cons arg1-prime cdr-prime)
        (cons new-vardecl cdr-vardecls)
        nf))
  ///
  (defmvtypes vl-gateinst-plainarglist-blankargs (nil true-listp)))


(define vl-gateinst-blankargs
  :short "Apply the @(see blankargs) transform to a gate instance."
  ((x        vl-gateinst-p)
   (nf       vl-namefactory-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-gateinst-p)
      (vardecls vl-vardecllist-p)
      (nf       vl-namefactory-p))
  (b* ((x  (vl-gateinst-fix x))
       (nf (vl-namefactory-fix nf))
       ((when (vl-plainarglist-blankfree-p (vl-gateinst->args x)))
        ;; Oprimization.  There aren't any blanks in our arguments, so
        ;; there's nothing to do.
        (mv (ok) x nil nf))

       ((vl-gateinst x) x)

       ((when x.range)
        ;; Important soundness check: need to know there's no range or else
        ;; we'd potentially be connecting the same new blank wire to several
        ;; instances.
        (mv (fatal :type :vl-programming-error
                   :msg "~a0: expected all instance arrays to be replicated, ~
                         but this gate instance has range ~a1."
                   :args (list x x.range))
            x nil nf))

       ((mv new-args vardecls nf)
        (vl-gateinst-plainarglist-blankargs x.args nf x))
       (x-prime  (change-vl-gateinst x :args new-args)))
    (mv (ok) x-prime vardecls nf))
  ///
  (defmvtypes vl-gateinst-blankargs (nil nil true-listp)))


(define vl-gateinstlist-blankargs
  :short "Extends @(see vl-gateinst-blankargs) across a @(see vl-gateinstlist-p)."
  ((x        vl-gateinstlist-p)
   (nf       vl-namefactory-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-gateinstlist-p)
      (vardecls vl-vardecllist-p)
      (nf       vl-namefactory-p))
  (b* (((when (atom x))
        (mv (ok) nil nil (vl-namefactory-fix nf)))
       ((mv warnings car-prime car-vardecls nf)
        (vl-gateinst-blankargs (car x) nf warnings))
       ((mv warnings cdr-prime cdr-vardecls nf)
        (vl-gateinstlist-blankargs (cdr x) nf warnings))
       (x-prime  (cons car-prime cdr-prime))
       (vardecls (append car-vardecls cdr-vardecls)))
    (mv warnings x-prime vardecls nf))
  ///
  (defmvtypes vl-gateinstlist-blankargs (nil true-listp true-listp)))


(define vl-module-blankargs
  :short "Fill in blank arguments throughout a @(see vl-module-p)."
  ((x        vl-module-p)
   (ss       vl-scopestack-p))
  :returns (new-x vl-module-p)
  :long "<p>We rewrite all module instances with @(see vl-modinst-blankargs)
and all gate instances with @(see vl-gateinst-blankargs).</p>"

  (b* ((x (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)
       ((vl-module x) x)
       (ss  (vl-scopestack-push x ss))
       (warnings (vl-module->warnings x))
       (nf       (vl-starting-namefactory x))

       ((mv warnings modinsts vardecls1 nf)
        (vl-modinstlist-blankargs x.modinsts ss nf warnings))
       ((mv warnings gateinsts vardecls2 nf)
        (vl-gateinstlist-blankargs x.gateinsts nf warnings))

       (- (vl-free-namefactory nf))
       (all-vardecls (append vardecls1 vardecls2 x.vardecls)))

    (change-vl-module x
                      :modinsts modinsts
                      :gateinsts gateinsts
                      :vardecls all-vardecls
                      :warnings warnings)))

(defprojection vl-modulelist-blankargs ((x        vl-modulelist-p)
                                        (ss       vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-blankargs x ss))

(define vl-design-blankargs ((x vl-design-p))
  :short "Top-level @(see blankargs) transformation."
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (mods (vl-modulelist-blankargs x.mods ss)))
    (vl-scopestacks-free)
    (change-vl-design x :mods mods)))
