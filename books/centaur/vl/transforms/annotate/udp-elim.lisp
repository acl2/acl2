; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "../../mlib/port-tools")
(local (include-book "../../util/arithmetic"))

(defsection udp-elim
  :parents (annotate)
  :short "Eliminate user-defined primitives (UDPs), replacing them with
equivalent modules."

  :long "<p>This transform eliminates all user-defined primitives from
a design, replacing them with modules.  When the UDPs are simple enough
to support, we can create replace them with equivalent modules.  In other
cases, e.g., when the UDP includes scary, nonsensical X behavior, we may
simply create a shell module that includes fatal @(see warnings).</p>")

(local (xdoc::set-default-parents udp-elim))

(define vl-udp-vardecl-from-portdecl ((x vl-portdecl-p))
  :returns (vardecl vl-vardecl-p)
  (b* (((vl-portdecl x)))
    (make-vl-vardecl :name x.name
                     :type x.type
                     :nettype :vl-wire
                     :atts (cons (cons "VL_PORT_IMPLICIT" nil) x.atts)
                     :loc x.loc)))

(defprojection vl-udp-vardecls-from-portdecls ((x vl-portdecllist-p))
  :returns (vardecls vl-vardecllist-p)
  (vl-udp-vardecl-from-portdecl x))


(define vl-udpline-match-expr
  ((inexprs  vl-exprlist-p     "Expressions for the input variables, in order.")
   (entries  vl-udpentrylist-p "Inputs from the UDP table, in corresponding order.")
   (warnings vl-warninglist-p))
  :guard (and (consp inexprs)
              (same-lengthp inexprs entries))
  :returns (mv (okp        booleanp :rule-classes :type-prescription)
               (warnings   vl-warninglist-p)
               (match-expr vl-expr-p))
  :prepwork
  ((local (defthm l0
         (implies (vl-udpentry-p x)
                  (equal (equal (vl-udpedge-p x)
                                (consp x))
                         t))
         :hints(("Goal" :in-theory (enable vl-udpentry-p))))))
  (b* ((in1    (vl-expr-fix     (car inexprs)))
       (entry1 (vl-udpentry-fix (car entries)))

       ((when (mbe :logic (vl-udpedge-p entry1)
                   :exec (consp entry1)))
        (mv nil
            (fatal :type :vl-bad-udp-entry
                   :msg "Expected no edges in combinational UDP lines, but found ~a0."
                   :args (list entry1))
            |*sized-1'bx*|))

       ((unless (or (eq entry1 :vl-udp-0)
                    (eq entry1 :vl-udp-1)
                    (eq entry1 :vl-udp-?)
                    (eq entry1 :vl-udp-b)))
        ;; BOZO could we handle b/x entries?
        (mv nil
            (fatal :type :vl-bad-udp-entry
                   :msg "UDP levels other than 0/1/?/b are not supported, but found ~a0."
                   :args (list entry1))
            |*sized-1'bx*|))

       (match-expr1 (case entry1
                      (:vl-udp-1 in1)
                      (:vl-udp-0 (make-vl-unary :op :vl-unary-bitnot :arg in1))
                      (:vl-udp-?
                       ;; Recognize 0, 1, or X -- always true in the context of a UDP
                       |*sized-1'b1*|)
                      (:vl-udp-b
                       ;; Recognize 0 or 1 -- same as (in1 | ~in1), Xes will still be X.
                       (make-vl-binary :op :vl-binary-bitor
                                       :left in1
                                       :right (make-vl-unary :op :vl-unary-bitnot
                                                             :arg in1)))))

       ((when (atom (cdr inexprs)))
        ;; Last expression, nothing more to require
        (mv t (ok) match-expr1))

       ((mv okp warnings rest-expr)
        (vl-udpline-match-expr (cdr inexprs) (cdr entries) warnings))
       ((unless okp)
        (mv nil warnings rest-expr)))
    (mv t warnings (make-vl-binary :op :vl-binary-bitand
                                   :left match-expr1
                                   :right rest-expr))))

(define vl-udptable-assignrhs ((inexprs  vl-exprlist-p)
                               (lines    vl-udptable-p)
                               (warnings vl-warninglist-p))
  :guard (consp inexprs)
  :returns (mv (okp      booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (expr     vl-expr-p))
  :verify-guards nil
  (b* (((when (atom lines))
        ;; End of lines -- no lines match.  The Verilog standard says that if
        ;; no lines match, the output gets driven to X.
        (mv t (ok) |*sized-1'bx*|))
       ((vl-udpline line1) (car lines))

       ((when line1.current)
        (mv nil
            (fatal :type :vl-bad-udp-line
                   :msg "Combinational UDP, but line has a current state? ~x0."
                   :args (list line1))
            |*sized-1'bx*|))

       ((unless (same-lengthp inexprs line1.inputs))
        (mv nil
            (fatal :type :vl-bad-udp-line
                   :msg "UDP has ~x0 inputs, but line has ~x1: ~x2."
                   :args (list (len inexprs) (len line1.inputs) line1.inputs))
            |*sized-1'bx*|))

       ((mv okp warnings match-expr)
        (vl-udpline-match-expr inexprs line1.inputs warnings))
       ((unless okp)
        ;; Already warned
        (mv nil warnings |*sized-1'bx*|))

       (then-expr (case line1.output
                    (:vl-udp-0 |*sized-1'b0*|)
                    (:vl-udp-1 |*sized-1'b1*|)
                    (:vl-udp-x |*sized-1'bx*|)
                    (otherwise nil)))

       ((unless then-expr)
        (mv nil
            (fatal :type :vl-bad-udp-output
                   :msg "UDP line output must be 0/1/x, but is ~x0."
                   :args (list line1.output))
            |*sized-1'bx*|))

       ((mv okp warnings else-expr)
        (vl-udptable-assignrhs inexprs (cdr lines) warnings))
       ((unless okp)
        ;; Already warned
        (mv nil warnings |*sized-1'bx*|))

       (rhs (make-vl-qmark :test match-expr
                           :then then-expr
                           :else else-expr)))
    (mv t (ok) rhs))
  ///
  (verify-guards vl-udptable-assignrhs))

(define vl-combinational-udptable-synth
  :short "Translate a combinational UDP table into an assignment."
  ((output   vl-portdecl-p)
   (inputs   vl-portdecllist-p)
   (loc      vl-location-p)
   (x        vl-udptable-p)
   (warnings vl-warninglist-p))
  :returns (mv (okp      booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (assigns  vl-assignlist-p))
  (b* ((outname (vl-portdecl->name output))
       (outexpr (vl-idexpr outname))
       (innames (vl-portdecllist->names inputs))
       (inexprs (vl-make-idexpr-list innames))
       ((unless (consp inexprs))
        (mv nil
            (fatal :type :vl-bad-udp
                   :msg "UDP has no inputs?")
            nil))

       ((mv okp warnings rhs)
        (vl-udptable-assignrhs inexprs x warnings))
       ((unless okp)
        ;; Already warned
        (mv nil warnings nil))

       (assign (make-vl-assign :lvalue outexpr
                               :expr   rhs
                               :loc    loc)))
    (mv t (ok) (list assign))))

(define vl-udp-to-module
  :short "Convert a UDP into a module."
  ((x vl-udp-p))
  :returns (mod vl-module-p)
  :long "<p>We always produce a new module.  If the UDP is not something we can
support, the resulting module will have fatal @(see warnings).</p>"
  (b* (((vl-udp x))
       (portdecls (cons x.output x.inputs))
       (ports     (vl-ports-from-portdecls portdecls))
       (vardecls  (vl-udp-vardecls-from-portdecls portdecls))
       (atts      (list* (list "VL_CONVERTED_UDP")
                         (if x.sequentialp
                             (list "VL_SEQUENTIAL_UDP")
                           (list "VL_COMBINATIONAL_UDP"))
                         x.atts))
       (warnings  x.warnings)
       (warnings  (if x.sequentialp
                      (fatal :type :vl-sequential-udp
                             :msg "Sequential UDPs are not yet supported."
                             :args nil)
                    warnings))

       ((mv ?okp warnings assigns)
        (if x.sequentialp
            (mv nil warnings nil)
          (vl-combinational-udptable-synth x.output x.inputs x.maxloc x.table warnings))))

    (make-vl-module :name x.name
                    :origname x.name
                    :minloc x.minloc
                    :maxloc x.maxloc
                    :comments x.comments
                    :ports ports
                    :portdecls portdecls
                    :vardecls vardecls
                    :warnings warnings
                    :assigns assigns
                    :atts atts)))

(defprojection vl-udps-to-modules ((x vl-udplist-p))
  :returns (mods vl-modulelist-p)
  (vl-udp-to-module x))

(define vl-design-udp-elim ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) (vl-design-fix x))
       (new-mods      (vl-udps-to-modules x.udps)))
    ;; I considered causing some kind of error here if there was a name
    ;; clash between the new modules and x.mods.  However, I think it's more
    ;; sensible to just go ahead and append the new modules anyway.  If
    ;; there really is a name clash, it was *already* a problem, so it's not
    ;; our fault, so at any rate we're doing no harm.
    (change-vl-design x
                      :mods (append new-mods x.mods)
                      :udps nil)))


