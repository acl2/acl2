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
(include-book "../mlib/subst")
(include-book "../mlib/find-item")
(local (include-book "../util/arithmetic"))

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
  ((x         vl-netdecllist-p)
   (portdecls vl-portdecllist-p)
   (palist    (equal palist (vl-portdecl-alist portdecls)))
   (warnings  vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (netdecls vl-netdecllist-p
                "The non-supply netdecls, which should be kept."
                :hyp (vl-netdecllist-p x)
                :hints(("Goal" :in-theory (disable (force)))))
      (supply0s string-listp "Names of supply0 wires."
                :hyp (vl-netdecllist-p x)
                :hints(("Goal" :in-theory (disable (force)))))
      (supply1s string-listp "Names of supply1 wires."
                :hyp (vl-netdecllist-p x)
                :hints(("Goal" :in-theory (disable (force))))))
  (b* (((when (atom x))
        (mv (ok) nil nil nil))
       ((mv warnings rest-decls rest-supply0 rest-supply1)
        (vl-collect-supplies (cdr x) portdecls palist warnings))
       (type  (vl-netdecl->type (car x)))
       (name  (vl-netdecl->name (car x)))
       (range (vl-netdecl->range (car x))))
    (case type
      ((:vl-supply0 :vl-supply1)

       (if range

; Our simple-minded substitution won't work if the supply is an array of
; supplies.  Fortunately, this is probably something that no sane person would
; ever try to write.  We don't eliminate the supply, we just leave it as is,
; but we add a warning.

           (mv (fatal :type :vl-bad-supply
                      :msg "~a0: we do not support supplies with ranges."
                      :args (list (car x)))
               (cons (car x) rest-decls)
               rest-supply0
               rest-supply1)

         (let ((portdecl (vl-fast-find-portdecl name portdecls palist)))
           (if portdecl

; We originally just tried to throw away all supplies.  But we ran into
; problems because some inputs are declared to be supplies, and if we throw
; them away then they no longer have wire declarations.

; What sense does it make for an input to be a supply?  None, really -- you can
; hook up anything to it.  We could try to make some kind of well-formedness
; checks to ensure that only 1/0 are given to supply inputs, but for now we
; just are going to convert the wire declaration into a plain declaration.

               (if (not (eq (vl-portdecl->dir portdecl) :vl-input))
                   (mv (fatal :type :vl-bad-supply
                              :msg "~a0: we do not support supplies as ports."
                              :args (list (car x)))
                       (cons (car x) rest-decls)
                       rest-supply0
                       rest-supply1)

                 (mv warnings
                     (cons (change-vl-netdecl (car x)
                                              :type :vl-wire
                                              :atts (cons (if (eq type :vl-supply0)
                                                              (cons "VL_SUPPLY_0" nil)
                                                            (cons "VL_SUPPLY_1" nil))
                                                          (vl-netdecl->atts (car x))))
                           rest-decls)
                     rest-supply0
                     rest-supply1))

; Otherwise, this is not a port, and we are going to go ahead and eliminate it
; everywhere with 1 or 0.

             (mv warnings
                 rest-decls
                 (if (eq type :vl-supply0) (cons name rest-supply0) rest-supply0)
                 (if (eq type :vl-supply1) (cons name rest-supply1) rest-supply1))))))

; Finally, we have the case where this is an ordinary net declaration, not a
; supply wire.

      (otherwise (mv warnings
                     (cons (car x) rest-decls)
                     rest-supply0
                     rest-supply1))))

  ///
  (local (in-theory (disable vl-find-portdecl-under-iff)))
  (defmvtypes vl-collect-supplies
    (nil true-listp true-listp true-listp)))


(define vl-module-elim-supplies ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  (b* (((when (vl-module->hands-offp x))
        x)
       (warnings  (vl-module->warnings x))
       (netdecls  (vl-module->netdecls x))
       (portdecls (vl-module->portdecls x))
       (palist    (vl-portdecl-alist portdecls))
       ((mv warnings-prime new-decls supply0s supply1s)
        (vl-collect-supplies netdecls portdecls palist warnings))
       (- (fast-alist-free  palist))
       ((when (and (not supply0s)
                   (not supply1s)
                   (equal warnings warnings-prime)))
        x)
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
                          (pairlis$ supply1s ones)))
       ((with-fast sigma))
       (x-prime (change-vl-module x
                                  :netdecls new-decls
                                  :warnings warnings-prime)))
      (vl-module-subst x-prime sigma)))

(defprojection vl-modulelist-elim-supplies (x)
  (vl-module-elim-supplies x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-elim-supplies ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-elim-supplies x.mods))))

