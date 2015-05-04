; ESIM Symbolic Hardware Simulator
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


; esim-primitives.lisp - Definitions of primitive E modules for Verilog modeling
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "plist")

(defsection esim-primitives
  :parents (esim)
  :short "The @(see esim) modules that implement @(see vl2014::vl2014)'s @(see
vl2014::primitives)."

  :long "<p>The patterns used for the :i and :o ports here might look strange.
For instance, why do we use @('((|a|) (|b|))') as the input pattern for an AND
gate instead of @('(|a| |b|)')?  This allows our primitives to be directly
compatible with VL's primitives, as far as @(see vl2014::vl-portdecls-to-i/o) is
concerned.</p>

<p><b>BOZO</b> Things to consider:</p>

<ul>

<li>Do we want to add NAND and NOR primitives to @(see 4v-sexprs)?  We
currently implement them as @('(not (and a b))') and @('(not (or a b))').</li>

<li>Do we want to change LATCH and FLOP to use @(see 4v-ite*) instead of @(see
4v-ite)?  It probably won't help with combinational loops at all, but it may
make our modeling more conservative.  If it doesn't cause problems, it might
be worth doing.</li>

<li>Is there any good reason to keep PULLUP and ID in @(see 4v-sexprs)?  We
aren't using them for anything.</li>

<li>Eventaully implement WOR and WAND resolution</li>

</ul>")


(defmacro def-esim-primitive (name &key x i o
                                   (parents '(esim-primitives))
                                   (short '"")
                                   (long '""))
  (declare (xargs :guard (and (symbolp name)
                              (stringp short)
                              (stringp long))))
  (b* (((unless x)
        (er hard? 'def-esim-primitive
            "Only use this for modules with :x definitions."))
       (body `(:n ,name :x ,x :i ,i :o ,o)))
    `(defsection ,name
       :parents ,parents
       :short ,short
       :long ,(concatenate 'string long
                           "<h3>Definition:</h3> @(def " (symbol-name name) ")")
       (defconst ,name ',body))))

(def-esim-primitive *esim-t*
  :short "Primitive E module for producing T."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-t*).</p>"
  :i ()
  :o ((|out|))
  :x (:out ((|out| . (t)))))

(def-esim-primitive *esim-f*
  :short "Primitive E module for producing F."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-f*).</p>"
  :i ()
  :o ((|out|))
  :x (:out ((|out| . (f)))))

(def-esim-primitive *esim-x*
  :short "Primitive E module for producing X."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-x*).</p>"
  :i ()
  :o ((|out|))
  :x (:out ((|out| . (x)))))

(def-esim-primitive *esim-z*
  :short "Primitive E module for producing Z."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-z*).</p>"
  :i ()
  :o ((|out|))
  :x (:out ((|out| . (z)))))

(def-esim-primitive *esim-id*
  :short "Primitive E module for identity assignment."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-assign*).  This
differs from a BUF in that it does not coerce Z into X.  There is probably not
any way to actually implement this in hardware.</p>"
  :i ((|in|))
  :o ((|out|))
  :x (:out ((|out| . |in|))))

(def-esim-primitive *esim-del*
  :short "Primitive E module for a delayed assignment."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-delay-1*).  However,
really esim has no concept of delays and this is no different @(see
*esim-id*).</p>"
  :i ((|in|))
  :o ((|out|))
  :x (:out ((|out| . |in|))))

(def-esim-primitive *esim-buf*
  :short "Primitive E module for a BUF gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-buf*).  This is used
for real BUF gates, not for ordinary assignments; see also @(see
*esim-id*).</p>"
  :i ((|in|))
  :o ((|out|))
  :x (:out ((|out| . (buf |in|)))))

(def-esim-primitive *esim-not*
  :short "Primitive E module for a NOT gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-not*).</p>"
  :i ((|in|))
  :o ((|out|))
  :x (:out ((|out| . (not |in|)))))

(def-esim-primitive *esim-and*
  :short "Primitive E module for an AND gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-and*).</p>"
  :i ((|a|) (|b|))
  :o ((|out|))
  :x (:out ((|out| . (and |a| |b|)))))

(def-esim-primitive *esim-or*
  :short "Primitive E module for an OR gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-or*).</p>"
  :i ((|a|) (|b|))
  :o ((|out|))
  :x (:out ((|out| . (or |a| |b|)))))

(def-esim-primitive *esim-xor*
  :short "Primitive E module for an XOR gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-xor*).</p>"
  :i ((|a|) (|b|))
  :o ((|out|))
  :x (:out ((|out| . (xor |a| |b|)))))

(def-esim-primitive *esim-nand*
  :short "Primitive E module for a NAND gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-nand*).</p>"
  :i ((|a|) (|b|))
  :o ((|out|))
  :x (:out ((|out| . (not (and |a| |b|))))))

(def-esim-primitive *esim-nor*
  :short "Primitive E module for a NOR gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-nor*).</p>"
  :i ((|a|) (|b|))
  :o ((|out|))
  :x (:out ((|out| . (not (or |a| |b|))))))

(def-esim-primitive *esim-xnor*
  :short "Primitive E module for an XNOR gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-xnor*).</p>"
  :i ((|a|) (|b|))
  :o ((|out|))
  :x (:out ((|out| . (iff |a| |b|)))))

(def-esim-primitive *esim-ceq*
  :short "Primitive E module for a Verilog @('===') operator."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-ceq*).</p>

<p>However, the @('===') operator is inherently unsound and cannot be modeled
in esim because it is violates @(see 4v-monotonicity).  We just conservatively
approximate @('===') with an xnor gate.  That is, this module is nothing more
than a @(see *esim-xnor*).</p>"

  :i ((|a|) (|b|))
  :o ((|out|))
  :x (:out ((|out| . (iff |a| |b|)))))

(def-esim-primitive *esim-safe-mux*
  :short "Primitive E module for a (more conservative) mux."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-approx-mux*).</p>"
  :i ((|sel|) (|a|) (|b|))
  :o ((|out|))
  :x (:out ((|out| . (ite* |sel| |a| |b|)))))

(def-esim-primitive *esim-unsafe-mux*
  :short "Primitive E module for a (less conservative) mux."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-mux*).</p>"
  :i ((|sel|) (|a|) (|b|))
  :o ((|out|))
  :x (:out ((|out| . (ite |sel| |a| |b|)))))


;; Note: VL now generates RES modules directly, see the vl/toe directory.
;; BOZO perhaps rework how that's done, and perhaps WOR, WAND, etc.

(def-esim-primitive *esim-tri*
  :short "Primitive E module for a tri-state buffer."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-zmux*).</p>"
  :i ((|sel|) (|a|))
  :o ((|out|))
  :x (:out ((|out| . (tristate |sel| |a|)))))

;; VL now generates its own flop primitives.

;; (def-esim-primitive *esim-flop*
;;   :short "Primitive E module for a register."
;;   :long "<p>We use this to implement @(see vl2014::*vl-1-bit-flop*).</p>"
;;   :i ((|clk|) (|d|))
;;   :o ((|q|))
;;   :x (:out ((|q|  . (ite |clk| s- s+)))
;;       :nst ((s- . (ite |clk| s- |d|))
;;             (s+ . (ite |clk| s- s+)))))

(def-esim-primitive *esim-latch*
  :short "Primitive E module for a latch."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-latch*).</p>"
  :i ((|clk|) (|d|))
  :o ((|q|))
  :x (:out ((|q| . (ite |clk| |d| s)))
      :nst ((s   . (ite |clk| |d| s)))))

(def-esim-primitive *esim-fsmreg*
  :short "Primitive E module for an unclocked register."
  :long "<p>This is an FSM-style register that always updates its state bit to
its input value at each step.</p>"
  :i ((|d|))
  :o ((|q|))
  :x (:out ((|q| . s))
      :nst ((s   . |d|))))

(def-esim-primitive *esim-zif*
  :short "Primitive E module for a kind of pass-gate style mux."
  :long "<p>This is a special kind of mux that can preserve Z values on its
inputs, used to support experimental esim decomposition.</p>"
  :i ((|sel|) (|a|) (|b|))
  :o ((|o|))
  :x (:out ((|o| . (zif |sel| |a| |b|)))))

(def-esim-primitive *esim-bufif0*
  :short "Primitive E module for a kind of bufif0 gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-bufif0*).</p>"
  :i ((|data|) (|ctrl|))
  :o ((|out|))
  :x (:out ((|out| . (tristate (not |ctrl|) |data|)))))

(def-esim-primitive *esim-bufif1*
  :short "Primitive E module for a kind of bufif1 gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-bufif1*).</p>"
  :i ((|data|) (|ctrl|))
  :o ((|out|))
  :x (:out ((|out| . (tristate |ctrl| |data|)))))

(def-esim-primitive *esim-notif0*
  :short "Primitive E module for a kind of notif0 gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-notif0*).</p>"
  :i ((|data|) (|ctrl|))
  :o ((|out|))
  :x (:out ((|out| . (tristate (not |ctrl|) (not |data|))))))

(def-esim-primitive *esim-notif1*
  :short "Primitive E module for a kind of notif1 gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-notif1*).</p>"
  :i ((|data|) (|ctrl|))
  :o ((|out|))
  :x (:out ((|out| . (tristate |ctrl| (not |data|))))))

(def-esim-primitive *esim-nmos*
  :short "Primitive E module for a kind of nmos gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-nmos*).</p>"
  :i ((|data|) (|ctrl|))
  :o ((|out|))
  :x (:out ((|out| . (zif |ctrl| |data| (z))))))

(def-esim-primitive *esim-pmos*
  :short "Primitive E module for a kind of pmos gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-pmos*).</p>"
  :i ((|data|) (|ctrl|))
  :o ((|out|))
  :x (:out ((|out| . (zif |ctrl| (z) |data|)))))

(def-esim-primitive *esim-cmos*
  :short "Primitive E module for a kind of cmos gate."
  :long "<p>We use this to implement @(see vl2014::*vl-1-bit-cmos*).</p>"
  :i ((|data|) (|nctrl|) (|pctrl|))
  :o ((|out|))
  :x (:out ((|out| . (res (zif |nctrl| |data| (z))
                          (zif |pctrl| (z) |data|))))))





(defsection *esim-primitives*
  :parents (esim-primitives)
  :short "A list of all esim primitives."
  :long "@(def *esim-primitives*)"

  (defconst *esim-primitives*
    (list *esim-t*
          *esim-f*
          *esim-x*
          *esim-z*
          *esim-id*
          *esim-del*
          *esim-buf*
          *esim-not*
          *esim-and*
          *esim-or*
          *esim-xor*
          *esim-nand*
          *esim-nor*
          *esim-xnor*
          *esim-ceq*
          ;; *esim-res*
          *esim-tri*
          ;; *esim-flop*
          *esim-latch*
          *esim-fsmreg*
          *esim-zif*

          *esim-bufif0*
          *esim-bufif1*
          *esim-notif0*
          *esim-notif1*
          *esim-nmos*
          *esim-pmos*
          *esim-cmos*)))

