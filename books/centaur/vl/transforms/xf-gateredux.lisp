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
(include-book "occform/gen-simple")
(local (include-book "../util/arithmetic"))


(defxdoc gateredux
  :parents (transforms)
  :short "Eliminate gates like @('bufif0'), @('nmos'), etc."
  :long "<p>We implement a module rewrite which eliminates \"complicated\"
 gates, namely</p>

<ul>
 <li>@('bufif0') and @('bufif1'),</li>
 <li>@('notif0') and @('notif1'),</li>
 <li>@('nmos'), @('rnmos'), @('pmos'), and @('rpmos'),</li>
 <li>@('cmos') and @('rcmos'),</li>
 <li>@('pullup') and @('pulldown'),</li>
</ul>

<p>and replaces them with instances of modules that are written entirely in
terms of the simple gates (buf, not, ...) and @('VL_1_BIT_MUX'), which we
regard as a primitive.</p>

<p>The true semantics of these \"complicated\" above cannot be perfectly
understood in an ordinary, four-valued Verilog simulation, because in certain
cases they emit special values, @('L') and @('H'), that are not among the four
primitive values of Verilog, namely @('{ 0, 1, X, Z }').</p>

<p>Because of this, our rewrites only conservatively approximate these gates.
See test-redux.v for Cadence tests that establish the correspondence between
our new modules and the primitive gates they are named after.  This
approximation allows us to at least deal with modules that are written using
these gates, but in our E model, we may at some point wish to substitute
primitives that are more faithful to the true Verilog semantics.</p>

<p>The other gates, such as @('tran'), @('tranif1'), etc., are not yet
supported, since they are trickier.</p>

<h3>Ordering notes.</h3>

<p>This transformation doesn't really have any prerequisites and should be
usable any time.  However, since it may add modules with widths already
defined, it probably needs to be done after first assigning widths. Also, since
it may introduce VL_1_BIT_ZMUX, we need to do it after occforming to prevent
VL_1_BIT_ZMUX from being redefined.  Ugly ugly!  Maybe add attributes like
\"hands-off\" or something to fix this.</p>")



; An Apology.
;
; Writing out parse trees using our constructors is ugly and verbose.  We do it
; anyway, because it allows us to explicitly specify the widths and otherwise
; describe a fully transformed parse tree, so that these new modules do not
; need to be transformed in any way.
;
; To see what the corresponding Verilog source code looks like, you can write:
;   (vl-pps-module *vl-1-bit-bufif0*)

(defconst *vl-1-bit-bufif0*
  ;; VL_1_BIT_BUFIF0(out, data, ctrl);
  (b* ((name "VL_1_BIT_BUFIF0")

       ((mv out-expr out-port out-portdecl out-netdecl)     (vl-occform-mkport "out" :vl-output 1))
       ((mv data-expr data-port data-portdecl data-netdecl) (vl-occform-mkport "data" :vl-input 1))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-netdecl) (vl-occform-mkport "ctrl" :vl-input 1))

       ;; not(ctrl_bar, ctrl);
       ;; buf(data_buf, data);
       ((mv ctrlbar-expr ctrlbar-netdecl) (vl-occform-mkwire "ctrl_bar" 1))
       ((mv databuf-expr databuf-netdecl) (vl-occform-mkwire "data_buf" 1))
       (ctrlbar-gate (vl-make-unary-gateinst :vl-not ctrlbar-expr ctrl-expr nil nil))
       (databuf-gate (vl-make-unary-gateinst :vl-buf databuf-expr data-expr nil nil))

       ;; VL_1_BIT_ZMUX mux (out, ctrl_bar, data_buf);
       (mux-args (list (make-vl-plainarg :expr out-expr     :dir :vl-output :portname (hons-copy "out"))
                       (make-vl-plainarg :expr ctrlbar-expr :dir :vl-input  :portname (hons-copy "sel"))
                       (make-vl-plainarg :expr databuf-expr :dir :vl-input  :portname (hons-copy "a"))))
       (mux-inst (make-vl-modinst :modname   (vl-module->name *vl-1-bit-zmux*)
                                  :instname  "mux"
                                  :paramargs (vl-arguments nil nil)
                                  :portargs  (vl-arguments nil mux-args)
                                  :loc       *vl-fakeloc*)))
    (make-vl-module :name      name
                    :origname  name
                    :ports     (list out-port data-port ctrl-port)
                    :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                    :netdecls  (list out-netdecl data-netdecl ctrl-netdecl ctrlbar-netdecl databuf-netdecl)
                    :gateinsts (list databuf-gate ctrlbar-gate)
                    :modinsts  (list mux-inst)
                    :minloc    *vl-fakeloc*
                    :maxloc    *vl-fakeloc*)))

(defconst *vl-1-bit-bufif1*
  ;; VL_1_BIT_BUFIF1(out, data, ctrl);
  (b* ((name "VL_1_BIT_BUFIF1")

       ((mv out-expr out-port out-portdecl out-netdecl)     (vl-occform-mkport "out" :vl-output 1))
       ((mv data-expr data-port data-portdecl data-netdecl) (vl-occform-mkport "data" :vl-input 1))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-netdecl) (vl-occform-mkport "ctrl" :vl-input 1))

       ;; buf(data_buf, data);
       ((mv databuf-expr databuf-netdecl) (vl-occform-mkwire "data_buf" 1))
       (databuf-gate (vl-make-unary-gateinst :vl-buf databuf-expr data-expr nil nil))

       ;; VL_1_BIT_ZMUX mux (out, ctrl, data_buf);
       (mux-args (list (make-vl-plainarg :expr out-expr     :dir :vl-output :portname (hons-copy "out"))
                       (make-vl-plainarg :expr ctrl-expr    :dir :vl-input  :portname (hons-copy "sel"))
                       (make-vl-plainarg :expr databuf-expr :dir :vl-input  :portname (hons-copy "a"))))
       (mux-inst (make-vl-modinst :modname   (vl-module->name *vl-1-bit-zmux*)
                                  :instname  "mux"
                                  :paramargs (vl-arguments nil nil)
                                  :portargs  (vl-arguments nil mux-args)
                                  :loc       *vl-fakeloc*)))
    (make-vl-module :name      name
                    :origname  name
                    :ports     (list out-port data-port ctrl-port)
                    :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                    :netdecls  (list out-netdecl data-netdecl ctrl-netdecl databuf-netdecl)
                    :gateinsts (list databuf-gate)
                    :modinsts  (list mux-inst)
                    :minloc    *vl-fakeloc*
                    :maxloc    *vl-fakeloc*)))

(defconst *vl-1-bit-notif0*
  ;; VL_1_BIT_NOTIF0(out, data, ctrl);
  (b* ((name "VL_1_BIT_NOTIF0")

       ((mv out-expr out-port out-portdecl out-netdecl)     (vl-occform-mkport "out" :vl-output 1))
       ((mv data-expr data-port data-portdecl data-netdecl) (vl-occform-mkport "data" :vl-input 1))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-netdecl) (vl-occform-mkport "ctrl" :vl-input 1))

       ;; not(ctrl_bar, ctrl);
       ;; not(data_bar, data);
       ((mv ctrlbar-expr ctrlbar-netdecl) (vl-occform-mkwire "ctrl_bar" 1))
       ((mv databar-expr databar-netdecl) (vl-occform-mkwire "data_bar" 1))
       (ctrlbar-gate (vl-make-unary-gateinst :vl-not ctrlbar-expr ctrl-expr nil nil))
       (databar-gate (vl-make-unary-gateinst :vl-not databar-expr data-expr nil nil))

       ;; VL_1_BIT_ZMUX mux (out, ctrl_bar, data_bar);
       (mux-args (list (make-vl-plainarg :expr out-expr     :dir :vl-output :portname (hons-copy "out"))
                       (make-vl-plainarg :expr ctrlbar-expr :dir :vl-input  :portname (hons-copy "sel"))
                       (make-vl-plainarg :expr databar-expr :dir :vl-input  :portname (hons-copy "a"))))
       (mux-inst (make-vl-modinst :modname   (vl-module->name *vl-1-bit-zmux*)
                                  :instname  "mux"
                                  :paramargs (vl-arguments nil nil)
                                  :portargs  (vl-arguments nil mux-args)
                                  :loc       *vl-fakeloc*)))
    (make-vl-module :name      name
                    :origname  name
                    :ports     (list out-port data-port ctrl-port)
                    :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                    :netdecls  (list out-netdecl data-netdecl ctrl-netdecl ctrlbar-netdecl databar-netdecl)
                    :gateinsts (list databar-gate ctrlbar-gate)
                    :modinsts  (list mux-inst)
                    :minloc    *vl-fakeloc*
                    :maxloc    *vl-fakeloc*)))

(defconst *vl-1-bit-notif1*
  ;; VL_1_BIT_NOTIF1(out, data, ctrl);
  (b* ((name "VL_1_BIT_NOTIF1")

       ((mv out-expr out-port out-portdecl out-netdecl)     (vl-occform-mkport "out" :vl-output 1))
       ((mv data-expr data-port data-portdecl data-netdecl) (vl-occform-mkport "data" :vl-input 1))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-netdecl) (vl-occform-mkport "ctrl" :vl-input 1))

       ;; not(data_bar, data);
       ((mv databar-expr databar-netdecl) (vl-occform-mkwire "data_bar" 1))
       (databar-gate (vl-make-unary-gateinst :vl-not databar-expr data-expr nil nil))

       ;; VL_1_BIT_ZMUX mux (out, ctrl, data_buf);
       (mux-args (list (make-vl-plainarg :expr out-expr     :dir :vl-output :portname (hons-copy "out"))
                       (make-vl-plainarg :expr ctrl-expr    :dir :vl-input  :portname (hons-copy "sel"))
                       (make-vl-plainarg :expr databar-expr :dir :vl-input  :portname (hons-copy "a"))))
       (mux-inst (make-vl-modinst :modname   (vl-module->name *vl-1-bit-zmux*)
                                  :instname  "mux"
                                  :paramargs (vl-arguments nil nil)
                                  :portargs  (vl-arguments nil mux-args)
                                  :loc       *vl-fakeloc*)))
    (make-vl-module :name      name
                    :origname  name
                    :ports     (list out-port data-port ctrl-port)
                    :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                    :netdecls  (list out-netdecl data-netdecl ctrl-netdecl databar-netdecl)
                    :gateinsts (list databar-gate)
                    :modinsts  (list mux-inst)
                    :minloc    *vl-fakeloc*
                    :maxloc    *vl-fakeloc*)))

(defconst *vl-1-bit-nmos*
  ;; VL_1_BIT_NMOS(out, data, ctrl);
  (b* ((name "VL_1_BIT_NMOS")

       ((mv out-expr out-port out-portdecl out-netdecl)     (vl-occform-mkport "out" :vl-output 1))
       ((mv data-expr data-port data-portdecl data-netdecl) (vl-occform-mkport "data" :vl-input 1))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-netdecl) (vl-occform-mkport "ctrl" :vl-input 1))

       ;; VL_1_BIT_ZMUX mux (out, ctrl, data);
       (mux-args (list (make-vl-plainarg :expr out-expr  :dir :vl-output :portname (hons-copy "out"))
                       (make-vl-plainarg :expr ctrl-expr :dir :vl-input  :portname (hons-copy "sel"))
                       (make-vl-plainarg :expr data-expr :dir :vl-input  :portname (hons-copy "a"))))
       (mux-inst (make-vl-modinst :modname   (vl-module->name *vl-1-bit-zmux*)
                                  :instname  "mux"
                                  :paramargs (vl-arguments nil nil)
                                  :portargs  (vl-arguments nil mux-args)
                                  :loc       *vl-fakeloc*)))
    (make-vl-module :name      name
                    :origname  name
                    :ports     (list out-port data-port ctrl-port)
                    :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                    :netdecls  (list out-netdecl data-netdecl ctrl-netdecl)
                    :modinsts  (list mux-inst)
                    :minloc    *vl-fakeloc*
                    :maxloc    *vl-fakeloc*)))

(defconst *vl-1-bit-pmos*
  ;; VL_1_BIT_PMOS(out, data, ctrl);
  (b* ((name "VL_1_BIT_PMOS")

       ((mv out-expr out-port out-portdecl out-netdecl)     (vl-occform-mkport "out" :vl-output 1))
       ((mv data-expr data-port data-portdecl data-netdecl) (vl-occform-mkport "data" :vl-input 1))
       ((mv ctrl-expr ctrl-port ctrl-portdecl ctrl-netdecl) (vl-occform-mkport "ctrl" :vl-input 1))

       ;; not(ctrl_bar, ctrl);
       ((mv ctrlbar-expr ctrlbar-netdecl) (vl-occform-mkwire "ctrl_bar" 1))
       (ctrlbar-gate (vl-make-unary-gateinst :vl-not ctrlbar-expr ctrl-expr nil nil))

       ;; VL_1_BIT_ZMUX mux (out, ctrl_bar, data);
       (mux-args (list (make-vl-plainarg :expr out-expr     :dir :vl-output :portname (hons-copy "out"))
                       (make-vl-plainarg :expr ctrlbar-expr :dir :vl-input  :portname (hons-copy "sel"))
                       (make-vl-plainarg :expr data-expr    :dir :vl-input  :portname (hons-copy "a"))))
       (mux-inst (make-vl-modinst :modname   (vl-module->name *vl-1-bit-zmux*)
                                  :instname  "mux"
                                  :paramargs (vl-arguments nil nil)
                                  :portargs  (vl-arguments nil mux-args)
                                  :loc       *vl-fakeloc*)))
    (make-vl-module :name      name
                    :origname  name
                    :ports     (list out-port data-port ctrl-port)
                    :portdecls (list out-portdecl data-portdecl ctrl-portdecl)
                    :netdecls  (list out-netdecl data-netdecl ctrl-netdecl ctrlbar-netdecl)
                    :gateinsts (list ctrlbar-gate)
                    :modinsts  (list mux-inst)
                    :minloc    *vl-fakeloc*
                    :maxloc    *vl-fakeloc*)))

(defconst *vl-1-bit-cmos*
  ;; VL_1_BIT_CMOS(out, data, nctrl, pctrl);
  (b* ((name "VL_1_BIT_CMOS")

       ((mv out-expr out-port out-portdecl out-netdecl)         (vl-occform-mkport "out" :vl-output 1))
       ((mv data-expr data-port data-portdecl data-netdecl)     (vl-occform-mkport "data" :vl-input 1))
       ((mv nctrl-expr nctrl-port nctrl-portdecl nctrl-netdecl) (vl-occform-mkport "nctrl" :vl-input 1))
       ((mv pctrl-expr pctrl-port pctrl-portdecl pctrl-netdecl) (vl-occform-mkport "pctrl" :vl-input 1))

       ;; not(pctrl_bar, pctrl);
       ((mv pctrlbar-expr pctrlbar-netdecl) (vl-occform-mkwire "pctrl_bar" 1))
       (pctrlbar-gate (vl-make-unary-gateinst :vl-not pctrlbar-expr pctrl-expr nil nil))

       ;; VL_1_BIT_ZMUX mux1 (out, nctrl, data);
       (mux1-args (list (make-vl-plainarg :expr out-expr   :dir :vl-output :portname (hons-copy "out"))
                        (make-vl-plainarg :expr nctrl-expr :dir :vl-input  :portname (hons-copy "sel"))
                        (make-vl-plainarg :expr data-expr  :dir :vl-input  :portname (hons-copy "a"))))
       (mux1-inst (make-vl-modinst :modname   (vl-module->name *vl-1-bit-zmux*)
                                   :instname  "mux1"
                                   :paramargs (vl-arguments nil nil)
                                   :portargs  (vl-arguments nil mux1-args)
                                   :loc       *vl-fakeloc*))

       ;; VL_1_BIT_ZMUX mux2 (out, pctrl_bar, data);
       (mux2-args (list (make-vl-plainarg :expr out-expr      :dir :vl-output :portname (hons-copy "out"))
                        (make-vl-plainarg :expr pctrlbar-expr :dir :vl-input  :portname (hons-copy "sel"))
                        (make-vl-plainarg :expr data-expr     :dir :vl-input  :portname (hons-copy "a"))))
       (mux2-inst (make-vl-modinst :instname  "mux2"
                                   :modname   (vl-module->name *vl-1-bit-zmux*)
                                   :paramargs (vl-arguments nil nil)
                                   :portargs  (vl-arguments nil mux2-args)
                                   :loc       *vl-fakeloc*)))
    (make-vl-module :name      name
                    :origname  name
                    :ports     (list out-port data-port nctrl-port pctrl-port)
                    :portdecls (list out-portdecl data-portdecl nctrl-portdecl pctrl-portdecl)
                    :netdecls  (list out-netdecl data-netdecl nctrl-netdecl pctrl-netdecl pctrlbar-netdecl)
                    :gateinsts (list pctrlbar-gate)
                    :modinsts  (list mux1-inst mux2-inst)
                    :minloc    *vl-fakeloc*
                    :maxloc    *vl-fakeloc*)))



(defconst *vl-gateinst-gateredux-map*
  (list (cons :vl-bufif0 *vl-1-bit-bufif0*)
        (cons :vl-bufif1 *vl-1-bit-bufif1*)
        (cons :vl-notif0 *vl-1-bit-notif0*)
        (cons :vl-notif1 *vl-1-bit-notif1*)
        (cons :vl-nmos   *vl-1-bit-nmos*)
        (cons :vl-rnmos  *vl-1-bit-nmos*)
        (cons :vl-pmos   *vl-1-bit-pmos*)
        (cons :vl-rpmos  *vl-1-bit-pmos*)
        (cons :vl-cmos   *vl-1-bit-cmos*)
        (cons :vl-rcmos  *vl-1-bit-cmos*)))



(defsection vl-gateinst-gateredux
  :parents (gateredux)
  :short "Maybe transform a complex gate into something simpler."

  :long "<p><b>Signature:</b> @(call vl-gateinst-gateredux) returns @('(mv
warnings new-gateinsts new-modinsts add-mods)').</p>

<p>@('X') is a gate instance, which belongs to some module, say @('M');
@('warnings') is an accumulator for warnings.</p>

<p>Our job is to return a lists of gate and module instances,
@('new-gateinsts') and @('new-modinsts'), which can be used to replace @('X')
in @('M').  Assuming that @('add-mods') can be added to the module list, the
resulting module will be a conservative approximation of @('M').</p>"

  (defund vl-gateinst-gateredux (x warnings)
    "Returns (MV WARNINGS NEW-GATEINSTS NEW-MODINSTS ADD-MODS)"
    (declare (xargs :guard (and (vl-warninglist-p warnings)
                                (vl-gateinst-p x))
                    :verify-guards nil))

    (b* (((vl-gateinst x) x))

      (case x.type

        ((:vl-buf :vl-not :vl-and :vl-or :vl-nand :vl-nor :vl-xor :vl-xnor)
         ;; Basic gates, no need to simplify these.
         (mv warnings (list x) nil nil))

        ((:vl-tran :vl-rtran :vl-tranif0 :vl-rtranif0 :vl-tranif1 :vl-rtranif1)
         ;; These gates are too complicated for now.
         (b* ((w (make-vl-warning :type :vl-unsupported-gate
                                  :msg "~a0: gates of type ~s1 are not yet supported."
                                  :args (list x x.type)
                                  :fatalp t
                                  :fn 'vl-gateinst-gateredux)))
           (mv (cons w warnings) (list x) nil nil)))

        ((:vl-pulldown :vl-pullup)
         (b* (((unless (= (len x.args) 1))
               ;; Basic sanity check.
               (b* ((w (make-vl-warning :type :vl-bad-gate
                                        :msg "~a0: expected 1 argument but found ~x1."
                                        :args (list x (len x.args))
                                        :fatalp t
                                        :fn 'vl-gateinst-gateredux)))
                 (mv (cons w warnings) (list x) nil nil)))

              ;; The name and range and everything can just stay the same.  We go
              ;; ahead and just convert into a buf of the appropriate form.  This
              ;; won't have the right strength, but it's as good as we can do.
              (val-expr (if (eq x.type :vl-pullup)
                            |*sized-1'b1*|
                          |*sized-1'b0*|))
              (val-arg  (make-vl-plainarg :expr val-expr :dir :vl-input))
              (new-inst (change-vl-gateinst x
                                            :type :vl-buf
                                            :args (list (car x.args) val-arg)
                                            :atts (cons (list "VL_GATE_REDUX") x.atts))))
             (mv warnings (list new-inst) nil nil)))

        ((:vl-bufif0 :vl-bufif1
          :vl-notif0 :vl-notif1
          :vl-nmos :vl-rnmos
          :vl-pmos :vl-rpmos
          :vl-cmos :vl-rcmos)
         (b* ((mod     (cdr (assoc x.type *vl-gateinst-gateredux-map*)))
              (modname (vl-module->name mod))
              (formals (vl-module->ports mod))

              ((unless (same-lengthp formals x.args))
               (b* ((w (make-vl-warning :type :vl-bad-gate
                                        :msg "~a0: expected ~x1 arguments, but found ~x2."
                                        :args (list x (len formals) (len x.args))
                                        :fatalp t
                                        :fn 'vl-gateinst-gateredux)))
                 (mv (cons w warnings) (list x) nil nil)))

              (inst (make-vl-modinst :modname   modname
                                     :instname  x.name
                                     :range     x.range
                                     :paramargs (vl-arguments nil nil)
                                     :portargs  (vl-arguments nil x.args)
                                     :atts      (cons (list "VL_GATE_REDUX") x.atts)
                                     :loc       x.loc)))
             (mv warnings
                 nil
                 (list inst)
                 (list mod *vl-1-bit-zmux*))))

        (t
         (prog2$
          (er hard 'vl-gateinst-gateredux "Provably impossible case.")
          (mv warnings nil nil nil))))))

  (defmvtypes vl-gateinst-gateredux (nil true-listp true-listp true-listp))

  (local (in-theory (enable vl-gateinst-gateredux)))

  (with-output
   :off :all
   (verify-guards vl-gateinst-gateredux
                  :hints(("Goal"
                          :use ((:instance VL-GATETYPE-P-OF-VL-GATEINST->TYPE))
                          :in-theory (e/d (vl-gatetype-p)
                                          (VL-GATETYPE-P-OF-VL-GATEINST->TYPE))))))

  (defthm vl-warninglist-p-of-vl-gateinst-gateredux
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gateinst-gateredux x warnings)))))

  (defthm vl-gateinstlist-p-of-vl-gateinst-gateredux
    (implies (force (vl-gateinst-p x))
             (vl-gateinstlist-p (mv-nth 1 (vl-gateinst-gateredux x warnings)))))

  (defthm vl-modinstlist-p-of-vl-gateinst-gateredux
    (implies (force (vl-gateinst-p x))
             (vl-modinstlist-p (mv-nth 2 (vl-gateinst-gateredux x warnings)))))

  (defthm vl-modulelist-p-of-vl-gateinst-gateredux
    (implies (force (vl-gateinst-p x))
             (vl-modulelist-p (mv-nth 3 (vl-gateinst-gateredux x warnings))))))


(defsection vl-gateinstlist-gateredux

  (defund vl-gateinstlist-gateredux (x warnings)
    "Returns (MV WARNINGS NEW-GATEINSTS NEW-MODINSTS ADD-MODS)"
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-warninglist-p warnings))))

; This just applies our reduction throughout a list of gate instances, and
; combines all of the results.  If a single reduction is sound, then the
; combined reduction is also sound by induction.

    (b* (((when (atom x))
          (mv warnings nil nil nil))
         ((mv warnings gateinsts1 modinsts1 addmods1) (vl-gateinst-gateredux (car x) warnings))
         ((mv warnings gateinsts2 modinsts2 addmods2) (vl-gateinstlist-gateredux (cdr x) warnings))
         (gateinsts (append gateinsts1 gateinsts2))
         (modinsts  (append modinsts1 modinsts2))
         (addmods   (append addmods1 addmods2)))
      (mv warnings gateinsts modinsts addmods)))

  (defmvtypes vl-gateinstlist-gateredux (nil true-listp true-listp true-listp))

  (local (in-theory (enable vl-gateinstlist-gateredux)))

  (defthm vl-warninglist-p-of-vl-gateinstlist-gateredux-0
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gateinstlist-gateredux x warnings)))))

  (defthm vl-gateinstlist-p-of-vl-gateinstlist-gateredux-1
    (implies (force (vl-gateinstlist-p x))
             (vl-gateinstlist-p (mv-nth 1 (vl-gateinstlist-gateredux x warnings)))))

  (defthm vl-modinstlist-p-of-vl-gateinstlist-gateredux-2
    (implies (force (vl-gateinstlist-p x))
             (vl-modinstlist-p (mv-nth 2 (vl-gateinstlist-gateredux x warnings)))))

  (defthm vl-modulelist-p-of-vl-gateinstlist-gateredux-3
    (implies (force (vl-gateinstlist-p x))
             (vl-modulelist-p (mv-nth 3 (vl-gateinstlist-gateredux x warnings))))))



(defsection vl-module-gateredux

  (defund vl-module-gateredux (x)
    "Returns (MV X-PRIME ADD-MODS)"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          (mv x nil))
         (warnings  (vl-module->warnings x))
         (gateinsts (vl-module->gateinsts x))
         (modinsts  (vl-module->modinsts x))
         ((mv warnings new-gateinsts new-modinsts add-mods)
          (vl-gateinstlist-gateredux gateinsts warnings))
         (new-mod   (change-vl-module x
                                      :gateinsts new-gateinsts
                                      :modinsts (append new-modinsts modinsts)
                                      :warnings warnings)))
        (mv new-mod add-mods)))

  (defmvtypes vl-module-gateredux (nil true-listp))

  (local (in-theory (enable vl-module-gateredux)))

  (defthm vl-module-p-of-vl-module-gateredux-0
    (implies (vl-module-p x)
             (vl-module-p (mv-nth 0 (vl-module-gateredux x)))))

  (defthm vl-modulelist-p-of-vl-module-gateredux-1
    (implies (vl-module-p x)
             (vl-modulelist-p (mv-nth 1 (vl-module-gateredux x))))))



(defsection vl-modulelist-gateredux-aux

  (defund vl-modulelist-gateredux-aux (x)
    "Returns (MV X-PRIME ADD-MODS)"
    (declare (xargs :guard (vl-modulelist-p x)))
    (if (atom x)
        (mv nil nil)
      (b* (((mv car-prime car-mods) (vl-module-gateredux (car x)))
           ((mv cdr-prime cdr-mods) (vl-modulelist-gateredux-aux (cdr x))))
          (mv (cons car-prime cdr-prime)
              (append car-mods cdr-mods)))))

  (defmvtypes vl-modulelist-gateredux-aux (true-listp true-listp))

  (local (in-theory (enable vl-modulelist-gateredux-aux)))

  (defthm vl-modulelist-p-of-vl-modulelist-gateredux-aux-0
    (implies (vl-modulelist-p x)
             (vl-modulelist-p (mv-nth 0 (vl-modulelist-gateredux-aux x)))))

  (defthm vl-modulelist-p-of-vl-modulelist-gateredux-aux-1
    (implies (vl-modulelist-p x)
             (vl-modulelist-p (mv-nth 1 (vl-modulelist-gateredux-aux x))))))



(defsection vl-modulelist-gateredux

  (defund vl-modulelist-gateredux (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* (((mv x-prime add-mods) (vl-modulelist-gateredux-aux x))
         (combined              (revappend add-mods x-prime))
         (combined-sort         (mergesort combined))
         (names                 (vl-modulelist->names combined-sort)))
        (if (not (uniquep names))
            (prog2$
             ;; I could change this to return an error flag.  But I think you
             ;; won't run into this unless someone tries to define one of the
             ;; modules like VL_1_BIT_BUFIF0, which they just shouldn't do, so
             ;; I'm just going to cause an error.
             (er hard? 'vl-modulelist-gateredux "Conflicting versions of ~x0.~%"
                 (duplicated-members names))
             (list-fix x))
          combined-sort)))

  (local (in-theory (enable vl-modulelist-gateredux)))

  (defthm vl-modulelist-p-of-vl-modulelist-gateredux
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-gateredux x))))

  (defthm true-listp-of-vl-modulelist-gateredux
    (true-listp (vl-modulelist-gateredux x))
    :rule-classes :type-prescription))

