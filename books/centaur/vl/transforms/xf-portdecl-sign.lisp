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

@({
module mymod (a, b, c, ...) ;
  input [3:0] a;   // <-- port declaration
  wire [3:0] a;    // <-- net declaration
endmodule
})

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

(local (xdoc::set-default-parents portdecl-sign))

(define vl-signed-portdecls ((x vl-portdecllist-p))
  :returns (names string-listp :hyp :fguard)
  :short "Gather the names of any signed port declarations."
  (cond ((atom x)
         nil)
        ((vl-portdecl->signedp (car x))
         (cons (vl-portdecl->name (car x))
               (vl-signed-portdecls (cdr x))))
        (t
         (vl-signed-portdecls (cdr x)))))

(define vl-signed-netdecls ((x vl-netdecllist-p))
  :returns (names string-listp :hyp :fguard)
  :short "Gather the names of any signed net declarations."
  (cond ((atom x)
         nil)
        ((vl-netdecl->signedp (car x))
         (cons (vl-netdecl->name (car x))
               (vl-signed-netdecls (cdr x))))
        (t
         (vl-signed-netdecls (cdr x)))))

(define vl-signed-regdecls ((x vl-regdecllist-p))
  :returns (names string-listp :hyp :fguard)
  :short "Gather the names of any signed reg declarations."
  (cond ((atom x)
         nil)
        ((vl-regdecl->signedp (car x))
         (cons (vl-regdecl->name (car x))
               (vl-signed-regdecls (cdr x))))
        (t
         (vl-signed-regdecls (cdr x)))))

(define vl-make-portdecls-signed
  ((names "names of portdecls to make signed" string-listp)
   (x     "original portdecls"                vl-portdecllist-p))
  :returns (new-x vl-portdecllist-p :hyp :fguard)
  :short "Change some port declarations to make them signed."
  (b* (((when (atom x))
        nil)
       (name    (vl-portdecl->name (car x)))
       (new-car (if (member-equal name names)
                    (change-vl-portdecl (car x) :signedp t)
                  (car x))))
    (cons new-car (vl-make-portdecls-signed names (cdr x)))))

(define vl-make-netdecls-signed
  ((names "names of netdecls to make signed" string-listp)
   (x     "original netdecls"                vl-netdecllist-p))
  :returns (new-x vl-netdecllist-p :hyp :fguard)
  :short "Change some net declarations to make them signed."
  (b* (((when (atom x))
        nil)
       (name (vl-netdecl->name (car x)))
       (new-car (if (member-equal name names)
                    (change-vl-netdecl (car x) :signedp t)
                  (car x))))
    (cons new-car (vl-make-netdecls-signed names (cdr x)))))

(define vl-make-regdecls-signed
  ((names "names of regdecls to make signed" string-listp)
   (x     "original regdecls"                vl-regdecllist-p))
  :returns (new-x vl-regdecllist-p :hyp :fguard)
  :short "Change some reg declarations to make them signed."
  (b* (((when (atom x))
        nil)
       (name (vl-regdecl->name (car x)))
       (new-car (if (member-equal name names)
                    (change-vl-regdecl (car x) :signedp t)
                  (car x))))
    (cons new-car (vl-make-regdecls-signed names (cdr x)))))

(define vl-module-portdecl-sign ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)
  :short "Cross-propagate @('signed') declarations between port declarations
and net/reg declarations in a module."

; I'm really happy with how simple and efficient this is. I particularly like
; how we aren't trying to match up particular ports with the corresponding
; net/reg declarations.

    (b* (((vl-module x) x)

         ((when (vl-module->hands-offp x))
          x)

; We begin by just collecting all the ports, nets, and regs that are signed.
; At Centaur, signed stuff is almost never used, so in practice the following
; often just does a quick scan of the declarations and doesn't result in any
; consing at all.

         (signed-ports (mergesort (vl-signed-portdecls x.portdecls)))
         (signed-nets  (mergesort (vl-signed-netdecls x.netdecls)))
         (signed-regs  (mergesort (vl-signed-regdecls x.regdecls)))

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
          x)

; Otherwise, we can't avoid the re-consing, so carry out the fixes and return
; the updated module.

         (new-portdecls (if ports-to-fix
                            (vl-make-portdecls-signed ports-to-fix x.portdecls)
                          x.portdecls))
         (new-netdecls (if nets-to-fix
                           (vl-make-netdecls-signed nets-to-fix x.netdecls)
                         x.netdecls))
         (new-regdecls (if regs-to-fix
                           (vl-make-regdecls-signed regs-to-fix x.regdecls)
                         x.regdecls)))

      (change-vl-module x
                        :portdecls new-portdecls
                        :netdecls  new-netdecls
                        :regdecls  new-regdecls))

    ///
    (defthm vl-module->name-of-vl-module-portdecl-sign
      (equal (vl-module->name (vl-module-portdecl-sign x))
             (vl-module->name x))))

(defprojection vl-modulelist-portdecl-sign (x)
  (vl-module-portdecl-sign x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-portdecl-sign
  :short "Top-level @(see portdecl-sign) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-portdecl-sign x.mods))))
