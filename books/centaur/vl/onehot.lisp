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
(include-book "transforms/occform/gen-simple")
(local (include-book "util/arithmetic"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))


(defxdoc onehot
  :parents (transforms)
  :short "Support for one-hot detection."
  :long "<p>It is difficult to write a parameterized module that detects
one-hotness for an arbitrary-sized wire using only synthesizable constructs.
Instead, we define the module @('VL_N_BIT_ONEHOT') (see @('VL_N_BIT_ONEHOT.v')
in the VL directory), which uses a for-loop to iterate over the bits of the
input wire, and produces:</p>

<ul>

<li>@('1'), if @('in') is definitely one-hot, </li>

<li>@('0'), if @('in') is definitely not one-hot, and</li>

<li>@('X'), if @('in') contains X or Z values that make its one-hotness
uncertain.</li>

</ul>

<p>We have built this module into VL in a deep way.  When @(see
unparameterization) encounters an instance of this module, instead of
specializing it in the normal way, we produce a new module, say
@('VL_3_BIT_ONEHOT'), that performs the same function but uses only
synthesizable constructs.</p>")

(defsection *vl-1-bit-onehot*
  :parents (onehot)
  :short "Special case one-hot detector for single-bit wires."
  :long "<p>@(srclink *vl-1-bit-onehot*) is a @(see vl-module-p) whose Verilog
definition is the following:</p>

@({
module VL_1_BIT_ONEHOT (out, in);
  output out;
  input in;
  buf (out, in);
endmodule
})

<p>It is useful as a base case in @(see vl-make-n-bit-onehot).</p>"

  (defconst *vl-1-bit-onehot*
    (b* ( ;; module VL_1_BIT_ONEHOT (out, in) ;
         (name         (hons-copy "VL_1_BIT_ONEHOT"))

         ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
         ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input 1))

         ;; buf impl (out, in) ;
         (out-gate (vl-make-unary-gateinst :vl-buf out-expr in-expr nil nil)))

      (make-vl-module :name      name
                      :origname  name
                      :ports     (list out-port in-port)
                      :portdecls (list out-portdecl in-portdecl)
                      :netdecls  (list out-netdecl in-netdecl)
                      :gateinsts (list out-gate)
                      :minloc    *vl-fakeloc*
                      :maxloc    *vl-fakeloc*))))


(defsection *vl-2-bit-onehot*
  :parents (onehot)
  :short "Special case one-hot detector for two-bit wires."
  :long "<p>@(srclink *vl-2-bit-onehot*) is a @(see vl-module-p) whose Verilog
definition is the following:</p>

@({
module VL_2_BIT_ONEHOT (out, in);
  output out;
  input [1:0] in;
  assign out = ^in;
endmodule
})

<p>It is useful as a base case in @(see vl-make-n-bit-onehot).</p>"

  (defconst *vl-2-bit-onehot*

    (b* (;; module VL_2_BIT_ONEHOT (out, in) ;
         (name         (hons-copy "VL_2_BIT_ONEHOT"))

         ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
         ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in" :vl-input 2))

         ;; assign out = ^in;
         (assign       (make-vl-assign :lvalue out-expr
                                       :expr (make-vl-nonatom :op :vl-unary-xor
                                                              :args (list in-expr))
                                       :loc *vl-fakeloc*)))

      (make-vl-module :name      name
                      :origname  name
                      :ports     (list out-port in-port)
                      :portdecls (list out-portdecl in-portdecl)
                      :netdecls  (list out-netdecl in-netdecl)
                      :assigns   (list assign)
                      :minloc    *vl-fakeloc*
                      :maxloc    *vl-fakeloc*))))




(defsection vl-make-n-bit-onehot
  :parents (onehot)
  :short "Generate an N-bit one-hot detector."

  :long "<p><b>Signature:</b> @(call vl-make-n-bit-onehot) returns a list of
modules, where the first-module is the one-hot detector for the requested N,
and the subsequent modules are perhaps some smaller one-hot checkers that are
recursively needed by this module.  Note that this list typically contains
duplicates!</p>

<p>Given one-hot detectors of size A and B, we can easily construct a
one-hot detector for a wire of size A + B.  The basic approach is as follows.</p>

<ul>

<li>Let @('LEFT') be the highest A bits of the input wire.</li>

<li>Let @('RIGHT') be the lowest B bits of the input wire.</li>

<li>Use an A-bit one-hot detector to determine if @('LEFT') is one-hot.</li>

<li>Use a B-bit one-hot detector to determine if @('RIGHT') is one-hot.</li>

<li>Use @('~|left') to determine if any bit of @('LEFT') is set.</li>

<li>Use @('~|right') to determine if any bit of @('RIGHT') is set.</li>

</ul>

<p>The entire input wire is now one-hot exactly when either:</p>

<ul>

<li>@('LEFT') is one-hot and no bits of @('RIGHT') are set, or</li>

<li>@('RIGHT') is one-hot and no bits of @('LEFT') are set.</li>

</ul>

<p>We now implement a scheme that uses this approach to generate a one-hot
checker for an arbitrary sized N.  The basic idea is to recursively generate
one-hot checkers for sizes B = N/2 and A = (N - N/2), and then follow the above
pattern.</p>"

  (local (include-book "arithmetic-5/top" :dir :system))

  ;; Loops
  (local (in-theory (disable acl2::functional-commutativity-of-minus-*-left)))

  (defund vl-make-n-bit-onehot (n)
    (declare (xargs :guard (posp n)
                    :verify-guards nil
                    :measure (nfix n)))

    (b* ((n    (mbe :logic (if (zp n) 1 n) :exec n))

         ((when (= n 1)) (list *vl-1-bit-onehot*))
         ((when (= n 2)) (list *vl-2-bit-onehot*))

         ;; Determine a suitable A and B for this particular N.  Using N/2 style
         ;; submodules gives us a hierarchy of size log2(n).
         (B    (floor n 2))
         (A    (- n B))

         ;; Generate submodules.
         (sub-A      (vl-make-n-bit-onehot A))
         (sub-B      (vl-make-n-bit-onehot B))
         (submodules (append sub-A sub-B))

         ;; module VL_N_BIT_ONEHOT (out, in);
         (name (hons-copy (cat "VL_" (coerce (explode-atom n 10) 'string) "_BIT_ONEHOT")))

         ((mv out-expr out-port out-portdecl out-netdecl) (vl-occform-mkport "out" :vl-output 1))
         ((mv in-expr in-port in-portdecl in-netdecl)     (vl-occform-mkport "in"  :vl-input  n))

         (|in[n-1:B]|  (vl-make-partselect in-expr (- n 1) B))    ; The "left" bits
         (|in[B-1:0]|  (vl-make-partselect in-expr (- B 1) 0))    ; The "right" bits

         ;; wire left_onehot;
         ;; VL_A_BIT_ONEHOT mk_left_onehot (left_onehot, in[n-1:B]);
         ((mv leftone-expr leftone-netdecl) (vl-occform-mkwire "left_onehot" 1))
         (leftone-args (list (make-vl-plainarg :expr leftone-expr :dir :vl-output :portname (hons-copy "out"))
                             (make-vl-plainarg :expr |in[n-1:B]|  :dir :vl-input  :portname (hons-copy "in"))))
         (leftone-inst (make-vl-modinst :modname   (vl-module->name (car sub-A))
                                        :instname  (hons-copy "mk_left_onehot")
                                        :paramargs (vl-arguments nil nil)
                                        :portargs  (vl-arguments nil leftone-args)
                                        :loc       *vl-fakeloc*))

         ;; wire right_onehot;
         ;; VL_B_BIT_ONEHOT mk_right_onehot (right_onehot, right);
         ((mv rightone-expr rightone-netdecl) (vl-occform-mkwire "right_onehot" 1))
         (rightone-args (list (make-vl-plainarg :expr rightone-expr :dir :vl-output :portname (hons-copy "out"))
                              (make-vl-plainarg :expr |in[B-1:0]|   :dir :vl-input  :portname (hons-copy "in"))))
         (rightone-inst (make-vl-modinst :instname  (hons-copy "mk_right_onehot")
                                         :modname   (vl-module->name (car sub-B))
                                         :paramargs (vl-arguments nil nil)
                                         :portargs  (vl-arguments nil rightone-args)
                                         :loc       *vl-fakeloc*))

         ;; wire left_zero = ~(|in[n-1:B]);
         ((mv leftzero-expr leftzero-netdecl) (vl-occform-mkwire "left_zero" 1))
         (leftzero-assign  (make-vl-assign :lvalue leftzero-expr
                                           :expr (make-vl-nonatom :op :vl-unary-bitnot
                                                                  :args (list (make-vl-nonatom :op :vl-unary-bitor
                                                                                               :args (list |in[n-1:B]|))))
                                           :loc *vl-fakeloc*))

         ;; wire right_zero = ~(|in[B-1:0]);
         ((mv rightzero-expr rightzero-netdecl) (vl-occform-mkwire "right_zero" 1))
         (rightzero-assign  (make-vl-assign :lvalue rightzero-expr
                                            :expr (make-vl-nonatom :op :vl-unary-bitnot
                                                                   :args (list (make-vl-nonatom :op :vl-unary-bitor
                                                                                                :args (list |in[B-1:0]|))))
                                            :loc *vl-fakeloc*))

         ;; assign out = (left_onehot & right_zero) | (right_onehot & left_zero);
         (option1  (make-vl-nonatom :op :vl-binary-bitand :args (list leftone-expr rightzero-expr)))
         (option2  (make-vl-nonatom :op :vl-binary-bitand :args (list rightone-expr leftzero-expr)))
         (out-assign (make-vl-assign :lvalue out-expr
                                     :expr (make-vl-nonatom :op :vl-binary-bitor
                                                            :args (list option1 option2))
                                     :loc *vl-fakeloc*))

         (module (make-vl-module :name      name
                                 :origname  name
                                 :ports     (list out-port in-port)
                                 :portdecls (list out-portdecl in-portdecl)
                                 :netdecls  (list out-netdecl in-netdecl
                                                  leftone-netdecl rightone-netdecl
                                                  leftzero-netdecl rightzero-netdecl)
                                 :assigns   (list leftzero-assign rightzero-assign
                                                  out-assign)
                                 :modinsts  (list leftone-inst rightone-inst)
                                 :minloc    *vl-fakeloc*
                                 :maxloc    *vl-fakeloc*)))

        (cons module submodules)))

  (local (in-theory (enable vl-make-n-bit-onehot)))

  (defthm consp-of-vl-make-n-bit-onehot
    (consp (vl-make-n-bit-onehot n))
    :rule-classes :type-prescription)

  (defthm vl-modulelist-p-of-vl-make-n-bit-onehot
    (vl-modulelist-p (vl-make-n-bit-onehot n)))

  (verify-guards vl-make-n-bit-onehot))




#||

;; For testing using a Verilog simulator

(include-book
   "writer")

(let* ((mods (vl-make-n-bit-onehot 1))
       (mods (append (vl-make-n-bit-onehot 2) mods))
       (mods (append (vl-make-n-bit-onehot 3) mods))
       (mods (append (vl-make-n-bit-onehot 4) mods))
       (mods (append (vl-make-n-bit-onehot 5) mods))
       (mods (append (vl-make-n-bit-onehot 6) mods))
       ;; Repeat as desired
       (mods (mergesort mods)))
  (vl-pps-modulelist mods))

||#




