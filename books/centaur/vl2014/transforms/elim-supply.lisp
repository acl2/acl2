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
(include-book "../mlib/subst")
(include-book "../mlib/find")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc elim-supplies
  :parents (transforms)
  :short "Elimination of @('supply0') and @('supply1') wires"

  :long "<p>In this transformation, we throw away declarations like @('supply0
a') and @('supply1 b'), and replace occurrences of @('a') and @('b') throughout
expressions with @('0') and @('1'), respectively.</p>

<p><b>BOZO.</b> This transformation is sort of okay, but we should come up with
something better.  As it turns out, something as simple as eliminating supplies
actually has some subtleties.</p>

<p>A deficiency of our current approach is: what if someone tries to assign to
a supply?  At best, they'll get some kind of message that says they're trying
to assign to a constant, which won't be very informative.  Our approach also
completely throws away the overwhelming strength of a supply, in case we ever
want to try to do anything with that.</p>

<p>We do not throw out any supply0 or supply1 wires which are also inputs or
outputs to the module.  Instead, we convert them into regular wires!  This is
crazy.  What are the semantics of an input that is a supply?  What if someone
hooks up something that isn't supply-like to it?</p>

<p>We annotate inputs that we convert in this way with the property VL_SUPPLY_0
or VL_SUPPLY_1, so that some day we might do the most basic kind of checks that
you haven't hooked up a bad wire to a supply, and so that the verification
person may at least see that this input is supposed to have a particular
value.</p>")

(local (xdoc::set-default-parents elim-supplies))

(define vl-collect-supplies
  ((x         vl-vardecllist-p)
   (portdecls vl-portdecllist-p)
   (palist    (equal palist (vl-make-portdecl-alist portdecls)))
   (warnings  vl-warninglist-p))
  :verify-guards nil
  :returns
  (mv (warnings vl-warninglist-p)
      (vardecls vl-vardecllist-p "The non-supply netdecls, which should be kept.")
      (supply0s string-listp "Names of supply0 wires.")
      (supply1s string-listp "Names of supply1 wires."))
  :hooks ((:fix :hints (("goal" :induct (vl-collect-supplies x portdecls palist warnings)
                         :expand ((:free (portdecls palist warnings)
                                   (vl-collect-supplies x portdecls palist warnings))
                                  (vl-collect-supplies (vl-vardecllist-fix x)
                                                       portdecls palist warnings))
                         :in-theory (disable (:d vl-collect-supplies))))))
  :prepwork ((local (in-theory (disable double-containment))))
  (b* (((when (atom x))
        (mv (ok) nil nil nil))
       ((mv warnings rest-decls rest-supply0 rest-supply1)
        (vl-collect-supplies (cdr x) portdecls palist warnings))
       ((vl-vardecl x1) (vl-vardecl-fix (car x)))
       ((unless (member x1.nettype '(:vl-supply0 :vl-supply1)))
        ;; Not a supply.  Don't mess with it.
        (mv (ok) (cons x1 rest-decls) rest-supply0 rest-supply1))

       ((unless (eq (vl-datatype-kind x1.type) :vl-coretype))
        (mv (fatal :type :vl-bad-supply
                   :msg "~a0: bad wire declared as a supply"
                   :args (list x1))
            (cons x1 rest-decls)
            rest-supply0
            rest-supply1))
       ((vl-coretype x1.type))

       ((when (or (consp x1.type.pdims)
                  (consp x1.type.udims)))
        ;; Our simple-minded substitution won't work if the supply is an array
        ;; of supplies.  Fortunately, this is probably something that no sane
        ;; person would ever try to write.  We don't eliminate the supply, we
        ;; just leave it as is, but we add a warning.
        (mv (fatal :type :vl-bad-supply
                   :msg "~a0: we do not support supplies with ranges."
                   :args (list x1))
            (cons x1 rest-decls)
            rest-supply0
            rest-supply1))

       ;; We originally just tried to throw away all supplies.  But we ran into
       ;; problems because some inputs are declared to be supplies, and if we
       ;; throw them away then they no longer have wire declarations.  So,
       ;; let's find out if this is a port.
       (portdecl (vl-fast-find-portdecl x1.name portdecls palist))
       ((unless portdecl)
        ;; Not a port, so we can go ahead and eliminate it.
        (mv warnings
            rest-decls
            (if (eq x1.nettype :vl-supply0) (cons x1.name rest-supply0) rest-supply0)
            (if (eq x1.nettype :vl-supply1) (cons x1.name rest-supply1) rest-supply1)))

       ;; What sense does it make for an input to be a supply?  None, really --
       ;; you can hook up anything to it.  We could try to make some kind of
       ;; well-formedness checks to ensure that only 1/0 are given to supply
       ;; inputs, but for now we just are going to convert the wire declaration
       ;; into a plain declaration.
       ((unless (eq (vl-portdecl->dir portdecl) :vl-input))
        (mv (fatal :type :vl-bad-supply
                   :msg "~a0: we do not support supplies as ports."
                   :args (list x1))
            (cons x1 rest-decls)
            rest-supply0
            rest-supply1))

       ;; Well, convert it into a wire, I guess.
       (new-atts (cons (if (eq x1.nettype :vl-supply0)
                           (cons "VL_SUPPLY_0" nil)
                         (cons "VL_SUPPLY_1" nil))
                       x1.atts))
       (new-x1   (change-vl-vardecl x1 :nettype :vl-wire :atts new-atts)))
    (mv (ok) (cons new-x1 rest-decls) rest-supply0 rest-supply1))
  ///
  (defmvtypes vl-collect-supplies
    (nil true-listp true-listp true-listp))
  (verify-guards vl-collect-supplies))

(define vl-module-elim-supplies ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x) (vl-module-fix x))
       ((when (vl-module->hands-offp x))
        x)

       (palist (vl-make-portdecl-alist x.portdecls))
       ((mv warnings new-decls supply0s supply1s)
        (vl-collect-supplies x.vardecls x.portdecls palist x.warnings))
       (- (fast-alist-free palist))

       ((when (and (not supply0s)
                   (not supply1s)
                   (equal warnings x.warnings)))
        x)

       (x (change-vl-module x
                            :vardecls new-decls
                            :warnings warnings))

       (zeroes (replicate (length supply0s)
                          (make-vl-atom :guts (make-vl-constint :origwidth 1
                                                                :origtype :vl-unsigned
                                                                :value 0)
                                        ;; BOZO is this width stuff right??
                                        :finalwidth 1
                                        :finaltype :vl-unsigned)))
       (ones (replicate (length supply1s)
                        (make-vl-atom :guts (make-vl-constint :origwidth 1
                                                              :origtype :vl-unsigned
                                                              :value 1)
                                      ;; BOZO is this width stuff right??
                                      :finalwidth 1
                                      :finaltype :vl-unsigned)))
       (sigma  (revappend (pairlis$ supply0s zeroes)
                          (pairlis$ supply1s ones))))
    (with-fast-alist sigma
      (vl-module-subst x sigma))))

(defprojection vl-modulelist-elim-supplies ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-elim-supplies x))

(define vl-design-elim-supplies ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-elim-supplies x.mods))))
