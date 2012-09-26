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
(include-book "xf-subst")
(include-book "../mlib/find-item")
(local (include-book "../util/arithmetic"))



(defxdoc elim-supplies
  :parents (transforms)
  :short "Elimination of <tt>supply0</tt> and <tt>supply1</tt> wires"

  :long "<p>In this transformation, we throw away declarations like <tt>supply0
a</tt> and <tt>supply1 b</tt>, and replace occurrences of <tt>a</tt> and
<tt>b</tt> throughout expressions with <tt>0</tt> and <tt>1</tt>,
respectively.</p>

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


(defsection vl-collect-supplies

  (defund vl-collect-supplies (x portdecls palist warnings)
    (declare (xargs :guard (and (vl-netdecllist-p x)
                                (vl-portdecllist-p portdecls)
                                (equal palist (vl-portdecl-alist portdecls))
                                (vl-warninglist-p warnings))))


; Returns (MV WARNINGS-PRIME NETDECLS SUPPLY0S SUPPLY1S)
;   - NETDECLS are the non-supply netdecls, which should be kept
;   - SUPPLY0S are the names of the supply0 wires (a string list)
;   - SUPPLY1S are the names of the supply1 wires (a string list)

    (if (atom x)
        (mv warnings nil nil nil)
      (b* (((mv warnings rest-decls rest-supply0 rest-supply1)
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

               (mv (cons (make-vl-warning
                          :type :vl-bad-supply
                          :msg "~a0: we do not support supplies with ranges."
                          :args (list (car x))
                          :fatalp t
                          :fn 'vl-collect-supplies)
                         warnings)
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
                       (mv (cons (make-vl-warning
                                  :type :vl-bad-supply
                                  :msg "~a0: we do not support supplies as ports."
                                  :args (list (car x))
                                  :fatalp t)
                                 warnings)
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
                         rest-supply1))))))

  (local (in-theory (enable vl-collect-supplies)))

  (local (in-theory (disable vl-find-portdecl-under-iff)))

  (defthm true-listp-of-vl-collect-supplies-1
    (true-listp (mv-nth 1 (vl-collect-supplies x portdecls palist warnings)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-collect-supplies-2
    (true-listp (mv-nth 2 (vl-collect-supplies x portdecls palist warnings)))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-collect-supplies-3
    (true-listp (mv-nth 3 (vl-collect-supplies x portdecls palist warnings)))
    :rule-classes :type-prescription)

  (defthm vl-warninglist-p-of-vl-collect-supplies
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-collect-supplies x portdecl palist warnings)))))

  (defthm vl-netdecllist-p-of-vl-collect-supplies
    (implies (and (force (vl-netdecllist-p x))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls))))
             (vl-netdecllist-p (mv-nth 1 (vl-collect-supplies x portdecls palist warnings)))))

  (defthm string-listp-of-vl-collect-supplies-2
    (implies (and (force (vl-netdecllist-p x))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls))))
             (string-listp (mv-nth 2 (vl-collect-supplies x portdecls palist warnings)))))

  (defthm string-listp-of-vl-collect-supplies-3
    (implies (and (force (vl-netdecllist-p x))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls))))
             (string-listp (mv-nth 3 (vl-collect-supplies x portdecls palist warnings))))))




(defund vl-module-elim-supplies (x)
  (declare (xargs :guard (vl-module-p x)))
  (b* (((when (vl-module->hands-offp x))
        x)
       (warnings  (vl-module->warnings x))
       (netdecls  (vl-module->netdecls x))
       (portdecls (vl-module->portdecls x))
       (palist    (vl-portdecl-alist portdecls))
       ((mv warnings-prime new-decls supply0s supply1s)
        (vl-collect-supplies netdecls portdecls palist warnings))
       (-
        (flush-hons-get-hash-table-link palist))
       ((when (and (not supply0s)
                   (not supply1s)
                   (equal warnings warnings-prime)))
        x)
       (zeroes (repeat (make-vl-atom :guts (make-vl-constint :origwidth 1
                                                             :origtype :vl-unsigned
                                                             :value 0)
                                     ;; BOZO is this width stuff right??
                                     :finalwidth 1
                                     :finaltype :vl-unsigned)
                       (length supply0s)))
       (ones (repeat (make-vl-atom :guts (make-vl-constint :origwidth 1
                                                           :origtype :vl-unsigned
                                                           :value 1)
                                   ;; BOZO is this width stuff right??
                                   :finalwidth 1
                                   :finaltype :vl-unsigned)
                     (length supply1s)))
       (sigma  (revappend (pairlis$ supply0s zeroes)
                          (pairlis$ supply1s ones)))
       ((with-fast sigma))
       (x-prime (change-vl-module x
                                  :netdecls new-decls
                                  :warnings warnings-prime)))
      (vl-module-subst x-prime sigma)))

(defthm vl-module-p-of-vl-module-elim-supplies
  (implies (force (vl-module-p x))
           (vl-module-p (vl-module-elim-supplies x)))
  :hints(("Goal" :in-theory (enable vl-module-elim-supplies))))

(defthm vl-module->name-of-vl-module-elim-supplies
  (equal (vl-module->name (vl-module-elim-supplies x))
         (vl-module->name x))
  :hints(("Goal" :in-theory (enable vl-module-elim-supplies))))


(defprojection vl-modulelist-elim-supplies (x)
  (vl-module-elim-supplies x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(defthm vl-modulelist->names-of-vl-modulelist-elim-supplies
  (equal (vl-modulelist->names (vl-modulelist-elim-supplies x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))
