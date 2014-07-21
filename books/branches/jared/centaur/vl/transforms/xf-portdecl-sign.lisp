; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "VL")
(include-book "../mlib/range-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))

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

<p>According to the Verilog-2005 specification (page 175),</p>

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
  :returns (names string-listp)
  :short "Gather the names of any signed port declarations."
  (cond ((atom x)
         nil)
        ((vl-portdecl->signedp (car x))
         (cons (vl-portdecl->name (car x))
               (vl-signed-portdecls (cdr x))))
        (t
         (vl-signed-portdecls (cdr x)))))

(define vl-signed-netdecls ((x vl-netdecllist-p))
  :returns (names string-listp)
  :short "Gather the names of any signed net declarations."
  (cond ((atom x)
         nil)
        ((vl-netdecl->signedp (car x))
         (cons (vl-netdecl->name (car x))
               (vl-signed-netdecls (cdr x))))
        (t
         (vl-signed-netdecls (cdr x)))))

(define vl-signed-vardecls ((x vl-vardecllist-p))
  :returns (names string-listp)
  :short "Gather the names of any signed reg declarations."
  :long "<p>Note that we really only look at @('reg') declarations here.  While
things like @('integer') variables are signed, they can't be used as ports in
Verilog-2005.  (Is that still true in SystemVerilog?)</p>

<p>BOZO probably this isn't correct at all for SystemVerilog, but we're going
to have to really extend ports to deal with modports stuff anyway, so let's
just go with it for now.</p>"
  (cond ((atom x)
         nil)
        ((and (vl-simplereg-p (car x))
              (vl-simplereg->signedp (car x)))
         (cons (vl-vardecl->name (car x))
               (vl-signed-vardecls (cdr x))))
        (t
         (vl-signed-vardecls (cdr x)))))

(define vl-make-portdecls-signed
  ((names "names of portdecls to make signed" string-listp)
   (x     "original portdecls"                vl-portdecllist-p))
  :returns (new-x vl-portdecllist-p)
  :short "Change some port declarations to make them signed."
  (b* ((names   (string-list-fix names))
       ((when (atom x))
        nil)
       (x1     (vl-portdecl-fix (car x)))
       (new-x1 (if (member-equal (vl-portdecl->name x1) names)
                   (change-vl-portdecl x1 :signedp t)
                 x1)))
    (cons new-x1 (vl-make-portdecls-signed names (cdr x)))))

(define vl-make-netdecls-signed
  ((names "names of netdecls to make signed" string-listp)
   (x     "original netdecls"                vl-netdecllist-p))
  :returns (new-x vl-netdecllist-p)
  :short "Change some net declarations to make them signed."
  (b* ((names (string-list-fix names))
       ((when (atom x))
        nil)
       (x1     (vl-netdecl-fix (car x)))
       (new-x1 (if (member-equal (vl-netdecl->name x1) names)
                   (change-vl-netdecl x1 :signedp t)
                 x1)))
    (cons new-x1 (vl-make-netdecls-signed names (cdr x)))))

(define vl-make-vardecls-signed
  ((names "names of vardecls to make signed" string-listp)
   (x     "original vardecls"                vl-vardecllist-p))
  :returns (new-x vl-vardecllist-p)
  :short "Change some variable declarations to make them signed."
  :guard-hints(("Goal" :in-theory (enable vl-simplereg-p)))
  :measure (len x)
  (b* ((names (string-list-fix names))
       ((when (atom x))
        nil)
       (x1     (vl-vardecl-fix (car x)))
       ((unless (member-equal (vl-vardecl->name x1) names))
        (cons x1 (vl-make-vardecls-signed names (cdr x))))
       ((unless (vl-simplereg-p x1))
        (raise "Expected a simple register but found ~x0." x1))
       (new-x1 (change-vl-vardecl x1
                                  :vartype (change-vl-coretype (vl-vardecl->vartype x1)
                                                               :signedp t))))
    (cons new-x1 (vl-make-vardecls-signed names (cdr x)))))

(define vl-module-portdecl-sign ((x vl-module-p))
  :returns (new-x vl-module-p)
  :short "Cross-propagate @('signed') declarations between port declarations
and net/reg declarations in a module."

; I'm really happy with how simple and efficient this is. I particularly like
; how we aren't trying to match up particular ports with the corresponding
; net/reg declarations.

    (b* ((x (vl-module-fix x))
         ((vl-module x) x)

         ((when (vl-module->hands-offp x))
          x)

; We begin by just collecting all the ports, nets, and regs that are signed.
; At Centaur, signed stuff is almost never used, so in practice the following
; often just does a quick scan of the declarations and doesn't result in any
; consing at all.

         (signed-ports (mergesort (vl-signed-portdecls x.portdecls)))
         (signed-nets  (mergesort (vl-signed-netdecls x.netdecls)))
         (signed-vars  (mergesort (vl-signed-vardecls x.vardecls)))

; Optimization.  If nothing is signed, nothing needs to be done.

         ((unless (or signed-ports signed-nets signed-vars))
          x)

; Otherwise there are at least some signed wires, so we need to do the checks.
; Any ports whose corresponding reg/net is declared to be signed, but which is
; not itself signed, needs to be fixed.

         (ports-to-fix (union (difference signed-nets signed-ports)
                              (difference signed-vars signed-ports)))

; Any net or reg whose corresponding port is signed, but which is not itself
; signed, needs to be fixed.

         (nets-to-fix  (difference signed-ports signed-nets))
         (vars-to-fix  (difference signed-ports signed-vars))

; Optimization.  We may have found that nothing needs to be fixed because the
; signedness for all port and net/reg declarations already agrees.  In this
; case, we don't need to change the module at all, so we can stop now and do no
; more consing.

         ((unless (or ports-to-fix nets-to-fix vars-to-fix))
          x)

; Otherwise, we can't avoid the re-consing, so carry out the fixes and return
; the updated module.

         (new-portdecls (if ports-to-fix
                            (vl-make-portdecls-signed ports-to-fix x.portdecls)
                          x.portdecls))
         (new-netdecls (if nets-to-fix
                           (vl-make-netdecls-signed nets-to-fix x.netdecls)
                         x.netdecls))
         (new-vardecls (if vars-to-fix
                           (vl-make-vardecls-signed vars-to-fix x.vardecls)
                         x.vardecls)))

      (change-vl-module x
                        :portdecls new-portdecls
                        :netdecls  new-netdecls
                        :vardecls  new-vardecls))

    ///
    (defthm vl-module->name-of-vl-module-portdecl-sign
      (equal (vl-module->name (vl-module-portdecl-sign x))
             (vl-module->name x))))

(defprojection vl-modulelist-portdecl-sign ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-portdecl-sign x))

(define vl-design-portdecl-sign
  :short "Top-level @(see portdecl-sign) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-portdecl-sign x.mods))))
