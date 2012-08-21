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
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(defxdoc portdecl-sign
  :parents (transforms)
  :short "Cross-propagate signedness between net/reg and port declarations."

  :long "<p>This transformation ensures that each port declaration and its
corresponding net declaration have the same signedness.</p>

<p>A Verilog module may include both a port declaration and a net/reg
declaration for the same wire.  For instance, the following is valid:</p>

<code>
module mymod (a, b, c, ...) ;
  input [3:0] a;   // &lt;-- port declaration
  wire [3:0] a;    // &lt;-- net declaration
endmodule
</code>

<p>Indeed, if a port is not also given a net declaration, we infer one
in the @(see make-implicit-wires) transform.</p>

<p>According to the Verilog specification (page 175),</p>

<box>
<p>\"The signed attribute can be attached to either a port declaration or to
the corresponding net or reg declaration or to both.  If either the port or
the net/reg is declared as signed, then the other shall also be considered
signed.\"</p>
</box>

<p>Our @(see parser) does not do this cross-checking, so in this transformation
we cross-check the port declarations against the net/reg declarations and
propagate any signed attributes to ensure they are found in both
declarations.</p>")



(defsection vl-signed-portdecls
  :parents (portdecl-sign)
  :short "Gather the names of any signed port declarations."

  :long "<p>@(call vl-signed-portdecls) is given a @(see vl-portdecllist-p),
and returns the names of any signed port declarations as a list of strings.</p>"

  (defund vl-signed-portdecls (x)
    (declare (xargs :guard (vl-portdecllist-p x)))
    (cond ((atom x)
           nil)
          ((vl-portdecl->signedp (car x))
           (cons (vl-portdecl->name (car x))
                 (vl-signed-portdecls (cdr x))))
          (t
           (vl-signed-portdecls (cdr x)))))

  (local (in-theory (enable vl-signed-portdecls)))

  (defthm string-listp-of-vl-signed-portdecls
    (implies (force (vl-portdecllist-p x))
             (string-listp (vl-signed-portdecls x)))))



(defsection vl-signed-netdecls
  :parents (portdecl-sign)
  :short "Gather the names of any signed net declarations."

  :long "<p>@(call vl-signed-netdecls) is given a @(see vl-netdecllist-p),
and returns the names of any signed net declarations as a list of strings.</p>"

  (defund vl-signed-netdecls (x)
    (declare (xargs :guard (vl-netdecllist-p x)))
    (cond ((atom x)
           nil)
          ((vl-netdecl->signedp (car x))
           (cons (vl-netdecl->name (car x))
                 (vl-signed-netdecls (cdr x))))
          (t
           (vl-signed-netdecls (cdr x)))))

  (local (in-theory (enable vl-signed-netdecls)))

  (defthm string-listp-of-vl-signed-netdecls
    (implies (force (vl-netdecllist-p x))
             (string-listp (vl-signed-netdecls x)))))



(defsection vl-signed-regdecls
  :parents (portdecl-sign)
  :short "Gather the names of any signed reg declarations."

  :long "<p>@(call vl-signed-regdecls) is given a @(see vl-regdecllist-p),
and returns the names of any signed reg declarations as a list of strings.</p>"

  (defund vl-signed-regdecls (x)
    (declare (xargs :guard (vl-regdecllist-p x)))
    (cond ((atom x)
           nil)
          ((vl-regdecl->signedp (car x))
           (cons (vl-regdecl->name (car x))
                 (vl-signed-regdecls (cdr x))))
          (t
           (vl-signed-regdecls (cdr x)))))

  (local (in-theory (enable vl-signed-regdecls)))

  (defthm string-listp-of-vl-signed-regdecls
    (implies (force (vl-regdecllist-p x))
             (string-listp (vl-signed-regdecls x)))))




(defsection vl-make-portdecls-signed
  :parents (portdecl-sign)
  :short "Change some port declarations to make them signed."

  :long "<p><b>Signature:</b> @(call vl-make-portdecls-signed) returns
<tt>x-prime</tt>.</p>

<ul>

<li><tt>names</tt> is a list of strings that names any port declarations which
should be made signed, and </li>

<li><tt>x</tt> is the original list of port declarations.</li>

</ul>

<p>We walk through <tt>x</tt>, marking all of the named ports as signed, and
return the updated port declarations as <tt>x-prime</tt>.</p>"

  (defund vl-make-portdecls-signed (names x)
    (declare (xargs :guard (and (string-listp names)
                                (vl-portdecllist-p x))))
    (if (atom x)
        nil
      (let ((name (vl-portdecl->name (car x))))
        (cons
         (if (member-equal name names)
             (change-vl-portdecl (car x) :signedp t)
           (car x))
         (vl-make-portdecls-signed names (cdr x))))))

  (local (in-theory (enable vl-make-portdecls-signed)))

  (defthm vl-portdecllist-p-of-vl-make-portdecls-signed
    (implies (force (vl-portdecllist-p x))
             (vl-portdecllist-p (vl-make-portdecls-signed names x)))))




(defsection vl-make-netdecls-signed
  :parents (portdecl-sign)
  :short "Change some net declarations to make them signed."

  :long "<p><b>Signature:</b> @(call vl-make-netdecls-signed) returns
<tt>x-prime</tt>.</p>

<ul>

<li><tt>names</tt> is a list of strings that names any net declarations which
should be made signed, and </li>

<li><tt>x</tt> is the original list of net declarations.</li>

</ul>

<p>We walk through <tt>x</tt>, marking all of the named nets as signed, and
return the updated net declarations as <tt>x-prime</tt>.</p>"

  (defund vl-make-netdecls-signed (names x)
    (declare (xargs :guard (and (string-listp names)
                                (vl-netdecllist-p x))))
    (if (atom x)
        nil
      (let ((name (vl-netdecl->name (car x))))
        (cons
         (if (member-equal name names)
             (change-vl-netdecl (car x) :signedp t)
           (car x))
         (vl-make-netdecls-signed names (cdr x))))))

  (local (in-theory (enable vl-make-netdecls-signed)))

  (defthm vl-netdecllist-p-of-vl-make-netdecls-signed
    (implies (force (vl-netdecllist-p x))
             (vl-netdecllist-p (vl-make-netdecls-signed names x)))))




(defsection vl-make-regdecls-signed
  :parents (portdecl-sign)
  :short "Change some reg declarations to make them signed."

  :long "<p><b>Signature:</b> @(call vl-make-regdecls-signed) returns
<tt>x-prime</tt>.</p>

<ul>

<li><tt>names</tt> is a list of strings that names any reg declarations which
should be made signed, and </li>

<li><tt>x</tt> is the original list of reg declarations.</li>

</ul>

<p>We walk through <tt>x</tt>, marking all of the named regs as signed, and
return the updated reg declarations as <tt>x-prime</tt>.</p>"

  (defund vl-make-regdecls-signed (names x)
    (declare (xargs :guard (and (string-listp names)
                                (vl-regdecllist-p x))))
    (if (atom x)
        nil
      (let ((name (vl-regdecl->name (car x))))
        (cons
         (if (member-equal name names)
             (change-vl-regdecl (car x) :signedp t)
           (car x))
         (vl-make-regdecls-signed names (cdr x))))))

  (local (in-theory (enable vl-make-regdecls-signed)))

  (defthm vl-regdecllist-p-of-vl-make-regdecls-signed
    (implies (force (vl-regdecllist-p x))
             (vl-regdecllist-p (vl-make-regdecls-signed names x)))))




(defsection vl-module-portdecl-sign
  :parents (portdecl-sign)
  :short "Cross-check <tt>signed</tt> declarations between port declarations
and net/reg declarations in a module."

  :long "<p>@(call vl-module-portdecl-sign) is given a module, <tt>x</tt>, and
returns an updated module, <tt>x-prime</tt>, where the @(see portdecl-sign)
transformation has been carried out.</p>"

  (defund vl-module-portdecl-sign (x)
    (declare (xargs :guard (vl-module-p x)))

; I'm really happy with how simple and efficient this is. I particularly like
; how we aren't trying to match up particular ports with the corresponding
; net/reg declarations.

    (b* (((when (vl-module->hands-offp x))
          x)

         (portdecls    (vl-module->portdecls x))
         (netdecls     (vl-module->netdecls x))
         (regdecls     (vl-module->regdecls x))

; We begin by just collecting all the ports, nets, and regs that are signed.
; At Centaur, signed stuff is almost never used, so in practice the following
; often just does a quick scan of the declarations and doesn't result in any
; consing at all.

         (signed-ports (mergesort (vl-signed-portdecls portdecls)))
         (signed-nets  (mergesort (vl-signed-netdecls netdecls)))
         (signed-regs  (mergesort (vl-signed-regdecls regdecls)))

; Optimization.  If nothing is signed, nothing needs to be done.

         ((unless (or signed-ports signed-nets signed-regs))
          x)

; Otherwise there are at least some signed wires, so we need to do the checks.
; Any ports whose corresponding reg/net is declared to be signed, but which is
; not itself signed, needs to be fixed.

         (ports-to-fix (union (difference signed-nets signed-ports)
                              (difference signed-regs signed-ports)))

; Any net or reg whose corresponding port is signed, but which is not itself
; signed, needs to be fixed.

         (nets-to-fix  (difference signed-ports signed-nets))
         (regs-to-fix  (difference signed-ports signed-regs))

; Optimization.  We may have found that nothing needs to be fixed because the
; signedness for all port and net/reg declarations already agrees.  In this
; case, we don't need to change the module at all, so we can stop now and do no
; more consing.

         ((unless (or ports-to-fix nets-to-fix regs-to-fix))
          x))

; Otherwise, we can't avoid the re-consing, so carry out the fixes and return
; the updated module.

        (change-vl-module x
                          :portdecls (if ports-to-fix
                                         (vl-make-portdecls-signed ports-to-fix portdecls)
                                       portdecls)
                          :netdecls  (if nets-to-fix
                                         (vl-make-netdecls-signed nets-to-fix netdecls)
                                       netdecls)
                          :regdecls  (if regs-to-fix
                                         (vl-make-regdecls-signed regs-to-fix regdecls)
                                       regdecls))))

  (local (in-theory (enable vl-module-portdecl-sign)))

  (defthm vl-module-p-of-vl-module-portdecl-sign
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-portdecl-sign x))))

  (defthm vl-module->name-of-vl-module-portdecl-sign
    (equal (vl-module->name (vl-module-portdecl-sign x))
           (vl-module->name x))))



(defsection vl-modulelist-portdecl-sign
  :parents (portdecl-sign)
  :short "Cross-check <tt>signed</tt> declarations between port declarations
and net/reg declarations in a module list."
  :long "<p>Simple projection of @(see vl-module-portdecl-sign)
across a list of modules.</p>"

  (defprojection vl-modulelist-portdecl-sign (x)
    (vl-module-portdecl-sign x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-portdecl-sign)))

  (defthm vl-modulelist->names-of-vl-modulelist-portdecl-sign
    (equal (vl-modulelist->names (vl-modulelist-portdecl-sign x))
           (vl-modulelist->names x))))

