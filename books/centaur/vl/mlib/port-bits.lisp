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
(include-book "wirealist")
(local (include-book "../util/arithmetic"))


; Gate Instances -------------------------------------------------------------

(defsection vl-plainarg-lsb-bits
  :parents (make-defm-command)
  :short "Build the list of @(see vl-emodwire-p)s for a @(see vl-plainarg-p),
in <b>LSB-first</b> order."

  :long "<p><b>Signature:</b> @(call vl-plainarg-lsb-bits) returns <tt>(mv
successp warnings lsb-bits)</tt>.</p>

<p>See @(see vl-msb-expr-bitlist).  This function just makes sure a @(see
vl-plainarg-p) isn't blank and then calls <tt>vl-msb-expr-bitlist</tt> to do
the work.  We return the bits in LSB-first order to match the convention
throughout E.</p>"

  (defund vl-plainarg-lsb-bits (x walist warnings)
    "Returns (MV SUCCESSP WARNINGS LSB-BITS)"
    (declare (xargs :guard (and (vl-plainarg-p x)
                                (vl-wirealist-p walist)
                                (vl-warninglist-p warnings))))
    (b* ((expr (vl-plainarg->expr x))
         ((unless expr)
          (b* ((w (make-vl-warning
                   :type :vl-unsupported
                   :msg "In vl-plainarg-lsb-bits, expected no blank ports."
                   :fatalp t
                   :fn 'vl-plainarg-lsb-bits)))
            (mv nil (cons w warnings) nil)))
         ((mv successp warnings bits)
          (vl-msb-expr-bitlist expr walist warnings)))
        (mv successp warnings (reverse bits))))

  (defmvtypes vl-plainarg-lsb-bits (nil nil true-listp))

  (local (in-theory (enable vl-plainarg-lsb-bits)))

  (defthm vl-warninglist-p-of-vl-plainarg-lsb-bits
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-plainarg-lsb-bits x walist warnings)))))

  (defthm vl-emodwirelist-p-of-vl-plainarg-lsb-bits
    (implies (and (force (vl-plainarg-p x))
                  (force (vl-wirealist-p walist)))
             (vl-emodwirelist-p (mv-nth 2 (vl-plainarg-lsb-bits x walist warnings))))))


(defsection vl-plainarglist-lsb-pattern
  :parents (vl-gateinst-to-eocc)
  :short "Build lists of @(see vl-emodwire-p)s for a @(see vl-plainarglist-p)."

  :long "<p><b>Signature:</b> @(call vl-plainarglist-lsb-pattern) returns
<tt>(mv successp warnings pattern)</tt>.</p>

<p>We project @(see vl-plainarg-lsb-bits) across a list of arguments, and cons
together the resulting bits to produce an <tt>vl-emodwirelistlist-p</tt> where
each sub-list is in LSB-order.  Please see @(see vl-emodwirelistlist-p) for
some additional examples and discussion.</p>"

  (defund vl-plainarglist-lsb-pattern (x walist warnings)
    "Returns (MV SUCCESSP WARNINGS PATTERN)"
    (declare (xargs :guard (and (vl-plainarglist-p x)
                                (vl-wirealist-p walist)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv t warnings nil))
         ((mv car-successp warnings car-lsb-bits)
          (vl-plainarg-lsb-bits (car x) walist warnings))
         ((mv cdr-successp warnings cdr-lsb-pattern)
          (vl-plainarglist-lsb-pattern (cdr x) walist warnings)))
      (mv (and car-successp cdr-successp)
          warnings
          (cons car-lsb-bits cdr-lsb-pattern))))

  (defmvtypes vl-plainarglist-lsb-pattern (booleanp nil true-listp))

  (local (in-theory (enable vl-plainarglist-lsb-pattern)))

  (defthm vl-warninglist-p-of-vl-plainarglist-lsb-pattern
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1
               (vl-plainarglist-lsb-pattern x walist warnings)))))

  (defthm true-list-listp-of-vl-plainarglist-lsb-pattern
    (true-list-listp
     (mv-nth 2 (vl-plainarglist-lsb-pattern x walist warnings))))

  (defthm vl-emodwirelistlist-p-of-vl-plainarglist-lsb-pattern
    (implies (and (force (vl-plainarglist-p x))
                  (force (vl-wirealist-p walist)))
             (vl-emodwirelistlist-p
              (mv-nth 2 (vl-plainarglist-lsb-pattern x walist warnings))))))


(defsection vl-plainargs-with-dir
  :parents (vl-gateinst-to-eocc)
  :short "Collect @(see vl-plainarg-p)s with a particular direction."

  :long "<p>@(call vl-plainargs-with-dir) just collects all arguments from
<tt>x</tt> whose <tt>:dir</tt> is <tt>dir</tt>.</p>

<p>Recall that @(see argresolve) annotates the arguments of gate instances with
their directions, so this is a convenient way to extract the inputs and outputs
of a gate instance.  However, this should typically <b>not</b> be used on
module instances, because their <tt>:dir</tt> fields are not reliable; see
@(see argresolve) for details.</p>"

  (defund vl-plainargs-with-dir (x dir)
    (declare (xargs :guard (and (vl-plainarglist-p x)
                                (vl-direction-p dir))))
    (cond ((atom x)
           nil)
          ((equal (vl-plainarg->dir (car x)) dir)
           (cons (car x)
                 (vl-plainargs-with-dir (cdr x) dir)))
          (t
           (vl-plainargs-with-dir (cdr x) dir))))

  (local (in-theory (enable vl-plainargs-with-dir)))

  (defthm vl-plainarglist-p-of-vl-plainargs-with-dir
    (implies (force (vl-plainarglist-p x))
             (vl-plainarglist-p (vl-plainargs-with-dir x dir)))))



; Port Declarations ----------------------------------------------------------

(defsection vl-portdecls-to-i/o
  :parents (make-defm-command)
  :short "Compute the <tt>:i</tt> and <tt>:o</tt> fields for a module."

  :long "<p><b>Signature:</b> @(call vl-portdecls-to-i/o) returns
<tt>(mv successp warnings in-wires out-wires)</tt>.</p>

<p>We don't take a warnings accumulator because we memoize this function.</p>

<p>See @(see vl-emodwirelistlist-p) for some discussion about the kinds of
patterns we generate.</p>

<p>Historic note.  We originally based our <tt>:i</tt> and <tt>:o</tt> patterns
on the order of a module's ports.  We now instead use the order of the port
declarations.  This is particularly nice for ports whose expressions are
concatenations such as <tt>{foo, bar, baz}</tt>, since the individual
components might not even have the same direction.</p>"

  (defund vl-portdecls-to-i/o (portdecls walist)
    "Returns (MV SUCCESSP WARNINGS IN-WIRES OUT-WIRES)"
    (declare (xargs :guard (and (vl-portdecllist-p portdecls)
                                (vl-wirealist-p walist))))
    (b* (((when (atom portdecls))
          (mv t nil nil nil))

         (decl1 (car portdecls))
         ((vl-portdecl decl1) decl1)

         ((unless (or (eq decl1.dir :vl-input)
                      (eq decl1.dir :vl-output)))
          (b* ((w (make-vl-warning
                     :type :vl-bad-portdecl
                     :msg "~a0: port declaration has unsupported direction ~x1."
                     :args (list decl1 (vl-direction-string decl1.dir))
                     :fatalp t
                     :fn 'vl-portdecls-to-i/o)))
            (mv nil (list w) nil nil)))

         (entry (hons-get decl1.name walist))
         ((unless entry)
          (b* ((w (make-vl-warning
                     :type :vl-bad-portdecl
                     :msg "~a0: no wire alist entry for ~w1."
                     :args (list decl1 decl1.name)
                     :fatalp t
                     :fn 'vl-portdecls-to-i/o)))
            (mv nil (list w) nil nil)))

         (msb-wires (mbe :logic (list-fix (cdr entry)) :exec (cdr entry)))
         (lsb-wires (reverse msb-wires))

         ;; Probably unnecessary sanity check: make sure that we found the
         ;; right number of wires.
         ((unless (and (vl-maybe-range-resolved-p decl1.range)
                       (= (length lsb-wires)
                          (vl-maybe-range-size decl1.range))))
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: wire-alist has ~x1 wires for ~w2, but its ~
                         range is ~a3."
                   :args (list decl1 (length lsb-wires) decl1.name decl1.range)
                   :fatalp t
                   :fn 'vl-portdecls-to-i/o)))
            (mv nil (list w) nil nil)))

         ;; Process all the other port declarations.
         ((mv successp warnings in-wires out-wires)
          (vl-portdecls-to-i/o (cdr portdecls) walist))

         ((unless successp)
          (mv nil warnings in-wires out-wires))

         ((mv in-wires out-wires)
          (case decl1.dir
            (:vl-input  (mv (cons lsb-wires in-wires) out-wires))
            (:vl-output (mv in-wires (cons lsb-wires out-wires)))
            (otherwise
             (prog2$ (er hard? 'vl-portdecls-to-i/o "Provably impossible.")
                     (mv in-wires out-wires))))))

      (mv t warnings in-wires out-wires)))

  ;; We want to memoize top-level calls because this will be invoked repeatedly
  ;; from other modules when we're trying to build the E occurrences for module
  ;; instances.
  (memoize 'vl-portdecls-to-i/o :recursive nil)

  (defmvtypes vl-portdecls-to-i/o (booleanp nil true-listp true-listp))

  (local (in-theory (enable vl-portdecls-to-i/o)))

  (defthm vl-warninglist-p-of-vl-portdecls-to-i/o
    (vl-warninglist-p (mv-nth 1 (vl-portdecls-to-i/o portdecls walist))))

  (defthm vl-portdecls-to-i/o-basics
    (implies (and (force (vl-portdecllist-p portdecls))
                  (force (vl-wirealist-p walist)))
             (let ((ret (vl-portdecls-to-i/o portdecls walist)))
               (and (vl-emodwirelistlist-p (mv-nth 2 ret))
                    (vl-emodwirelistlist-p (mv-nth 3 ret)))))))



; Module instances ------------------------------------------------------------

(defsection vl-port-msb-bits
  :parents (vl-portlist-msb-bit-pattern)
  :short "Compute the port pattern for a single port."
  :long "<p><b>Signature:</b> @(call vl-port-msb-bits) returns <tt>(mv successp
warnings msb-bits)</tt>.</p>"

  (defund vl-port-msb-bits (x walist)
    "Returns (MV SUCCESSP WARNINGS MSB-BITS)"
    (declare (xargs :guard (and (vl-port-p x)
                                (vl-wirealist-p walist))))
    (b* ((expr (vl-port->expr x))
         ((unless expr)
          (b* ((w (make-vl-warning
                   :type :vl-bad-port
                   :msg "~a0: expected no blank ports."
                   :args (list x)
                   :fatalp t
                   :fn 'vl-port-msb-bits)))
            (mv nil (list w) nil)))

         ((mv successp warnings msb-bits)
          (vl-msb-expr-bitlist expr walist nil))

         ((unless successp)
          (b* ((w (make-vl-warning
                   :type :vl-bad-port
                   :msg "~a0: failed to generate wires for this port."
                   :args (list x)
                   :fatalp t
                   :fn 'vl-port-msb-bits)))
            (mv nil (cons w warnings) nil))))

      (mv t warnings msb-bits)))

  (defmvtypes vl-port-msb-bits (booleanp nil true-listp))

  (local (in-theory (enable vl-port-msb-bits)))

  (defthm vl-warninglist-p-of-vl-port-msb-bits
    (vl-warninglist-p (mv-nth 1 (vl-port-msb-bits x walist))))

  (defthm vl-emodwirelist-p-of-vl-port-msb-bits
    (implies (and (force (vl-port-p x))
                  (force (vl-wirealist-p walist)))
             (vl-emodwirelist-p (mv-nth 2 (vl-port-msb-bits x walist))))))


(defsection vl-portlist-msb-bit-pattern
  :parents (make-defm-command)
  :short "Compute the port pattern for a module."

  :long "<p><b>Signature:</b> @(call vl-portlist-msb-bit-pattern) returns
<tt>(mv successp warnings pattern)</tt>.</p>

<p>See @(see make-defm-command) for a description of port patterns.</p>

<p>We memoize top-level calls of this function since it will be called once for
every instance of the module.  To make this memoization more effective, we
prefer not to take a warnings accumulator.</p>"

  (defund vl-portlist-msb-bit-pattern (x walist)
    "Returns (MV SUCCESSP WARNINGS PATTERN)"
    (declare (xargs :guard (and (vl-portlist-p x)
                                (vl-wirealist-p walist))))
    (b* (((when (atom x))
          (mv t nil nil))
         ((mv successp1 warnings1 wires1)
          (vl-port-msb-bits (car x) walist))
         ((mv successp2 warnings2 wires2)
          (vl-portlist-msb-bit-pattern (cdr x) walist)))
      (mv (and successp1 successp2)
          (append-without-guard warnings1 warnings2)
          (cons wires1 wires2))))

  (memoize 'vl-portlist-msb-bit-pattern
           :recursive nil)

  (defmvtypes vl-portlist-msb-bit-pattern (booleanp nil true-listp))

  (local (in-theory (enable vl-portlist-msb-bit-pattern)))

  (defthm vl-warninglist-p-of-vl-portlist-msb-bit-pattern
    (vl-warninglist-p (mv-nth 1 (vl-portlist-msb-bit-pattern x walist))))

  (defthm true-list-listp-of-vl-portlist-msb-bit-pattern
    (true-list-listp (mv-nth 2 (vl-portlist-msb-bit-pattern x walist))))

  (defthm vl-emodwirelistlist-p-of-vl-portlist-msb-bit-pattern
    (implies (and (force (vl-portlist-p x))
                  (force (vl-wirealist-p walist)))
             (vl-emodwirelistlist-p (mv-nth 2 (vl-portlist-msb-bit-pattern x walist))))))




(defsection vl-modinst-to-eocc-bindings
  :parents (make-defm-command)
  :short "Build a (slow) alist binding the \"formals\" for a module to the
\"actuals\" from an instance."

  :long "<p><b>Signature:</b> @(call vl-modinst-to-eocc-bindings) returns
<tt>(mv successp warnings binding-alist)</tt>.</p>

<p>Inputs:</p>

<ul>

<li><tt>actuals</tt> are the arguments in the module instance.</li>

<li><tt>portpat</tt> is the port pattern for the module being instanced.  See
@(see make-defm-command).  We assume it is the same length as the
actuals (i.e., the module instance has the proper arity), but we still have to
check the lengths on the sub-lists.</li>

<li>The <tt>walist</tt> is the wire alist for the superior module, so that we
can generate the E wires for the actuals.</li>

<li>The <tt>warnings</tt> is a @(see warnings) accumulator for the superior
module.</li>

<li>The <tt>inst</tt> is the module instance we're processing.  It is
semantically irrelevant and is only used as a context for warnings.</li>

</ul>"

  (defund vl-modinst-to-eocc-bindings (actuals portpat walist warnings inst)
    "Returns (MV SUCCESSP WARNINGS BINDING-ALIST)"
    (declare (xargs :guard (and (vl-plainarglist-p actuals)
                                (true-list-listp portpat)
                                (vl-emodwirelistlist-p portpat)
                                (same-lengthp actuals portpat)
                                (vl-wirealist-p walist)
                                (vl-warninglist-p warnings)
                                (vl-modinst-p inst))))
    (b* (((when (atom actuals))
          (mv t warnings nil))

         ((vl-modinst inst) inst)
         (expr1 (vl-plainarg->expr (car actuals)))

         ((unless expr1)
          ;; Shouldn't happen if we've properly converted blanks to Zs.
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "~a0: expected all arguments to be non-blank."
                   :args (list inst)
                   :fatalp t
                   :fn 'vl-modinst-to-eocc-bindings)))
            (mv nil (cons w warnings) nil)))

         ((mv successp warnings expr1-msb-bits)
          (vl-msb-expr-bitlist expr1 walist warnings))

         ((unless successp)
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0: error generating wires for ~a1."
                   :args (list inst.loc expr1)
                   :fatalp t
                   :fn 'vl-modinst-to-eocc-bindings)))
            (mv nil (cons w warnings) nil)))

         (formal1-msb-bits (car portpat))

         ((unless (same-lengthp expr1-msb-bits formal1-msb-bits))
          (b* ((nactuals (length expr1-msb-bits))
               (nformals (length formal1-msb-bits))
               (w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0: we produced ~x1 wires~s2 for an argument whose ~
                         corresponding port has ~x3 wire~s4.  ~
                         Argument wires: ~x5; ~
                         Port wires: ~x6."
                   :args (list inst
                               nactuals (if (= nactuals 1) "" "s")
                               nformals (if (= nformals 1) "" "s")
                               (symbol-list-names expr1-msb-bits)
                               (symbol-list-names formal1-msb-bits))
                   :fatalp t
                   :fn 'vl-modinst-to-eocc-bindings)))
            (mv nil (cons w warnings) nil)))

         ((mv successp warnings binding-alist)
          (vl-modinst-to-eocc-bindings (cdr actuals) (cdr portpat)
                                       walist warnings inst))

         (binding-alist (append (pairlis$ formal1-msb-bits expr1-msb-bits)
                                binding-alist)))

      (mv successp warnings binding-alist)))

  (defmvtypes vl-modinst-to-eocc-bindings (booleanp nil true-listp))

  (local (in-theory (enable vl-modinst-to-eocc-bindings)))

  (defthm vl-warninglist-p-of-vl-modinst-to-eocc-bindings
    (implies (vl-warninglist-p warnings)
             (vl-warninglist-p
              (mv-nth 1 (vl-modinst-to-eocc-bindings actuals portpat walist warnings inst)))))

  (defthm alistp-of-vl-modinst-to-eocc-bindings
    (alistp
     (mv-nth 2 (vl-modinst-to-eocc-bindings actuals portpat walist warnings
                                            inst))))
  
  (local (defthm alist-keys-pairlis$
           (equal (alist-keys (pairlis$ a b))
                  (list-fix a))
           :hints(("Goal" :in-theory (enable alist-keys pairlis$)))))

  (defthm vl-emodwirelist-p-alist-keys-eocc-bindings
    (implies (vl-emodwirelistlist-p portpat)
             (vl-emodwirelist-p (alist-keys (mv-nth 2 (vl-modinst-to-eocc-bindings actuals portpat walist warnings
                                                                                   inst)))))
    :hints(("Goal" :in-theory (enable vl-modinst-to-eocc-bindings))))

  (defthm vl-emodwirelist-p-alist-vals-eocc-bindings
    (implies (vl-wirealist-p walist)
             (vl-emodwirelist-p (alist-vals (mv-nth 2 (vl-modinst-to-eocc-bindings
                                                       actuals portpat walist warnings inst)))))
    :hints(("Goal" :in-theory (enable vl-modinst-to-eocc-bindings)))))
