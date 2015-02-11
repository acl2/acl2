; VL 2014 -- VL Verilog Toolkit, 2014 Edition
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "../primitives")
(include-book "../mlib/modgen")
(include-book "../mlib/delta")
(local (include-book "../util/arithmetic"))

(local (defthm crock
         (implies (vl-modulelist-p x)
                  (iff (first x)
                       (consp x)))))

(define vl-make-constdelay ((n natp))
  :returns (del vl-gatedelay-p)
  (let ((expr (vl-make-index n)))
    (make-vl-gatedelay :rise expr
                       :fall expr
                       :high expr)))

(defsection delayredux
  :parents (transforms)
  :short "Convert delays into explicit module instances."

  :long "<p>This transform eliminates simple delays on continuous assignments
and gate instances by turning them into explicit instances of delay
modules.</p>

<box><p>Note: @(see esim) has no notion of delays and just implements
@('*vl-1-bit-delay-1*') as a simple assignment.  Other backend tools, of
course, can treat delays in different ways.</p></box>

<p>The delayredux transform, @(see vl-design-delayredux), takes two keyword
arguments, @(':vecp') and @(':state-onlyp'), both Boolean values defaulting to
@('NIL'), whose meanings are discussed below.</p>

<p>We only target <see topic='@(url vl-simpledelay-p)'>simple delays</see> like
@('#5').  Our delay modules are based on the @(see *vl-1-bit-delay-1*) unless
the @(':vecp') option is set, in which case they are based on N-bit single-tick
delay modules (see @(see vl-make-n-bit-delay-1)).  We chain these modules in series
to generate modules that produce an arbitrary M-tick delay; see @(see
vl-make-n-bit-delay-m).</p>

<p>If the @(':state-onlyp') option is set, then delay modules are only inserted
for assignments and gates annotated with the \"VL_STATE_DELAY\" attribute;
other delays are just deleted, leaving the assignments or gates delay-free.
The \"VL_STATE_DELAY\" attribute comes from always-block processing (see @(see
vl-design-always-backend)); it is applied to tick delays that are used to
implement flop or latch primitives, but not tick delays that merely affect
signal timing within a clock phase.  @(':state-onlyp') is therefore useful in
frameworks that are not delay-sensitive, but that make use of the definitions
of VL latch and flop modules rather than considering them to be primitives.</p>

<p>The following explanation applies in cases where the @(':state-onlyp')
option is not set or else the \"VL_STATE_DELAY\" annotation is present.</p>

<p>For <b>continuous assignments</b>, we basically replace assignments like</p>

@({
  assign #5 lhs = rhs;
})

<p>with an explicit delay module instance and a delay-free assignment,
e.g.,</p>

@({
  wire [6:0] tmp;                      // same width as rhs
  VL_7_BIT_DELAY_5 mkdel (tmp, rhs);
  assign lhs = tmp;
})

<p>Why bother with @('tmp')?  Couldn't we just write:</p>

@({
 VL_7_BIT_DELAY_5 mkdel (lhs, rhs);
})

<p>instead?  That would work when @('lhs') and @('rhs') are the same size, but
using the temporary wire has the nice property that, by just making @('tmp')
the same size as @('rhs'), we can just let the truncation happen in the
assignment as before.</p>

<p>For <b>gate instances</b>, we push the delays onto the inputs, e.g.,</p>

@({
 and #3 (o, a, b);
})

<p>gets rewritten to something like:</p>

@({
 wire del_a, del_b;
 VL_1_BIT_DELAY_3 mk_del_a (del_a, a);
 VL_1_BIT_DELAY_3 mk_del_b (del_b, b);
 and (o, del_a, del_b);
})

<p>We could perhaps instead delay the outputs.  But a nice feature of delaying
the inputs is that we can leave the rest of the gate intact.  That is, notice
that @('o') above is still being driven directly by the gate, not by some
assignment or generated instance.  This means, for instance, that its drive
strength will still be the same, in case some backend cares about those sorts
of things.</p>

<p>We only remove delays from inout-free gates.  We do now know what it means
for a gate with inouts to have a delay.</p>


<h3>Ordering Notes</h3>

<p>This transform must be run after sizing so that we can introduce delay
modules of the appropriate sizes.  It also should be run after the always
backend, which can add delays that this transform should process.</p>

<p>We generally want to do this before @(see split).  Otherwise, when we see an
assignment like:</p>

@({
 assign #1 out = ~in;
})

<p>We can end up creating:</p>

@({
 VL_1_BIT_DELAY_1 mkdel (del, ~in) ;
})

<p>And the @('~in') argument isn't split up, which can confuse later transforms
like @(see occform).</p>")

(local (xdoc::set-default-parents delayredux))

(define vl-simpledelay-p ((x vl-gatedelay-p))
  :parents (delayredux vl-gatedelay-p)
  :short "Recognize simple delays like @('#5')."

  :long "<p>Verilog lets you give much richer delay specifications, e.g., you
can specify separate delays for transitions to 1, 0, and Z, and you can even
provide different minimum, typical, and maximum delays for each kind of
transition.  See @(see vl-gatedelay-p).</p>

<p>These complex delays are generally too complicated for us to handle.
Instead, we just try to support simple delays for some fixed number of
ticks.</p>"

  (b* (((vl-gatedelay x) x))
    (and (vl-expr-resolved-p x.rise)
         (vl-expr-resolved-p x.fall)
         (eql (vl-resolved->val x.rise) (vl-resolved->val x.fall))
         (or (not x.high)
             (and (vl-expr-resolved-p x.high)
                  (eql (vl-resolved->val x.rise) (vl-resolved->val x.high)))))))

(define vl-simpledelay->amount ((x (and (vl-gatedelay-p x)
                                        (vl-simpledelay-p x))))
  :parents (vl-simpledelay-p)
  :returns (amount natp :rule-classes :type-prescription)
  (lnfix (vl-resolved->val (vl-gatedelay->rise x)))
  :short "Get the number of ticks for a simple delay."
  :prepwork ((local (in-theory (enable vl-simpledelay-p)))))


(define vl-make-m-bit-delay-insts ((n natp)
                                   (basename stringp)
                                   (modname stringp)
                                   (outs vl-exprlist-p)
                                   (ins vl-exprlist-p))
  :guard (same-lengthp outs ins)
  :returns (modinsts vl-modinstlist-p :hyp :fguard)
  :parents (vl-make-1-bit-delay-m)

  (b* (((when (atom outs))
        nil)
       (args (list (make-vl-plainarg :expr (car outs) :dir :vl-output :portname "out")
                   (make-vl-plainarg :expr (car ins)  :dir :vl-input  :portname "in"))))
    (cons (make-vl-modinst :instname  (cat basename (natstr n))
                           :modname   modname
                           :paramargs (make-vl-paramargs-plain :args nil)
                           :portargs  (make-vl-arguments-plain :args args)
                           :loc       *vl-fakeloc*)
          (vl-make-m-bit-delay-insts (+ n 1) basename modname (cdr outs) (cdr ins)))))


(define vl-make-n-bit-delay-1 ((n posp) &key vecp)
  :parents (occform)
  :short "Generate an n-bit wide, 1-tick delay module."

  :long "<p>We generate a module in terms of @(see primitives) that is
equivalent to:</p>

@({
 module VL_n_BIT_DELAY_1 (out, in) ;
   output [n-1:0] out;
   input [n-1:0] in;
   assign #1 out = in;
 endmodule
})

<p>When @('n') is 1, this is just our primitive @(see *vl-1-bit-delay-1*)
module.</p>

<p>When @('n') is something larger than 1, then if @('vecp') is true we just make
the module above.  Otherwise, we instantiate @('n') 1-bit
delays.  For instance, a four-bit delay looks like this:</p>

@({
module VL_4_BIT_DELAY_1 (out, in) ;
  output [3:0] out;
  input [3:0] in;

  VL_1_BIT_DELAY_1 del0 (out[0], in[0]);
  VL_1_BIT_DELAY_1 del1 (out[1], in[1]);
  VL_1_BIT_DELAY_1 del2 (out[2], in[2]);
  VL_1_BIT_DELAY_1 del3 (out[3], in[3]);
endmodule
})"
  :returns (mods vl-modulelist-p :hyp :guard
                 "A non-empty module list.  The first module in the list
                       is the desired module; the other modules are any
                       necessary supporting modules.")
  (b* (((when (eql n 1))
        (list *vl-1-bit-delay-1*))

       (name  (cat "VL_" (natstr n) "_BIT_DELAY_1"))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))
       ((mv in-expr  in-port  in-portdecl  in-vardecl)  (vl-occform-mkport "in" :vl-input n))

       ((when vecp)
        (b* ((assign (make-vl-assign
                      :lvalue out-expr
                      :expr in-expr
                      :delay (make-vl-gatedelay :rise (vl-make-index 1)
                                                :fall (vl-make-index 1))
                      :loc *vl-fakeloc*))
             (mod (make-vl-module :name name
                                  :origname name
                                  :ports (list out-port in-port)
                                  :portdecls (list out-portdecl in-portdecl)
                                  :vardecls (list out-vardecl in-vardecl)
                                  :assigns (list assign)
                                  :minloc *vl-fakeloc*
                                  :atts `(("VL_SVEX_PRIMITIVE" . ,(make-vl-atom :guts (vl-string "delay")))
                                          ("VL_SVEX_PRIMITIVE_WIDTH" . ,(vl-make-index n))
                                          ("VL_HANDS_OFF"))
                                  :maxloc *vl-fakeloc*)))
          (list mod)))

       (outs  (vl-make-list-of-bitselects out-expr 0 (1- n)))
       (ins   (vl-make-list-of-bitselects in-expr 0 (1- n)))
       (insts (vl-simple-inst-list *vl-1-bit-delay-1* "del" outs ins))

       (mod   (make-vl-module :name      name
                              :origname  name
                              :ports     (list out-port     in-port)
                              :portdecls (list out-portdecl in-portdecl)
                              :vardecls  (list out-vardecl  in-vardecl)
                              :modinsts  insts
                              :minloc    *vl-fakeloc*
                              :maxloc    *vl-fakeloc*)))
    (list mod *vl-1-bit-delay-1*))
  ///
  (defthm type-of-vl-make-n-bit-delay-1
    (and (true-listp (vl-make-n-bit-delay-1 n :vecp vecp))
         (consp (vl-make-n-bit-delay-1 n :vecp vecp)))
    :rule-classes :type-prescription))



(def-vl-modgen vl-make-1-bit-delay-m (m)
  :short "Generate a one-bit wide, M-tick delay module."

  :long "<p>We generate a module in terms of @(see primitives) that is
equivalent to:</p>

@({
 module VL_1_BIT_DELAY_M (out, in) ;
   output out;
   input in;
   assign #M out = in;
 endmodule
})

<p>When @('m') is 1, this is just our primitive @(see *vl-1-bit-delay-1*)
module.</p>

<p>When @('m') is something larger than 1, we chain together @('m')-many 1-tick
delays to create an @('m')-tick delay.  For instance, a four-tick delay looks
like this:</p>

@({
module VL_1_BIT_DELAY_4 (out, in) ;
  output out;
  input in;

  wire [2:0] temp;
  VL_1_BIT_DELAY_1 del1 (temp[0], in);
  VL_1_BIT_DELAY_1 del2 (temp[1], temp[0]);
  VL_1_BIT_DELAY_1 del3 (temp[2], temp[1]);
  VL_1_BIT_DELAY_1 del4 (out,     temp[2]);
endmodule
})"

  :guard (posp m)
  :body
  (b* (((when (eql m 1))
        (list *vl-1-bit-delay-1*))

       (name  (cat "VL_1_BIT_DELAY_" (natstr m)))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output 1))
       ((mv in-expr  in-port  in-portdecl  in-vardecl)  (vl-occform-mkport "in" :vl-input 1))

       ((mv temp-expr temp-vardecl) (vl-occform-mkwire "temp" (- m 1)))
       (temp-wires (vl-make-list-of-bitselects temp-expr 0 (- m 2)))

       (outs  (append temp-wires (list out-expr)))
       (ins   (cons in-expr temp-wires))
       (insts (vl-make-m-bit-delay-insts 1 "del"
                                         (vl-module->name *vl-1-bit-delay-1*)
                                         outs ins))

       (mod   (make-vl-module :name      name
                              :origname  name
                              :ports     (list out-port     in-port)
                              :portdecls (list out-portdecl in-portdecl)
                              :vardecls  (list out-vardecl  in-vardecl   temp-vardecl)
                              :modinsts  insts
                              :atts      '(("VL_HANDS_OFF"))
                              :minloc    *vl-fakeloc*
                              :maxloc    *vl-fakeloc*)))
    (list mod *vl-1-bit-delay-1*)))

#||
(include-book ;; fool dependency scanner
 "../mlib/writer")
(vl-pps-modulelist (vl-make-1-bit-delay-m 1))
(vl-pps-modulelist (vl-make-1-bit-delay-m 2))
(vl-pps-modulelist (vl-make-1-bit-delay-m 3))
||#


(define vl-make-n-bit-delay-m ((n posp) (m posp) &key vecp)
  :parents (occform)
  :short "Generate an N-bit wide, M-tick delay module."

  :long "<p>We generate a module in terms of @(see primitives) that is
equivalent to:</p>

@({
 module VL_N_BIT_DELAY_M (out, in) ;
   output [N-1:0] out;
   input [N-1:0] in;
   assign #M out = in;
 endmodule
})

<p>In the special case that @('m') is 1, we build a @('VL_N_BIT_DELAY_1')
module using @(see vl-make-n-bit-delay-1).</p>

<p>Otherwise, we just chain together a list of these modules, one for each tick.
For instance, a module that implements 4-bit wide delay for 3 ticks would look
like this:</p>

@({
 module VL_4_BIT_DELAY_3 (out, in);
   output [3:0] out;
   output [3:0] in;

   wire [3:0] temp1;
   wire [3:0] temp2;

   VL_4_BIT_DELAY_1 bit0 (temp1, in);
   VL_4_BIT_DELAY_1 bit1 (temp2, temp1);
   VL_4_BIT_DELAY_1 bit2 (out, temp2);
 endmodule
})"
  :returns (mods vl-modulelist-p :hyp :guard)

  (b* ((base (vl-make-n-bit-delay-1 n :vecp vecp))

       ((when (= m 1))
        base)

       (name (cat "VL_" (natstr n) "_BIT_DELAY_" (natstr m)))

       ((mv out-expr out-port out-portdecl out-vardecl) (vl-occform-mkport "out" :vl-output n))
       ((mv in-expr  in-port  in-portdecl  in-vardecl)  (vl-occform-mkport "in" :vl-input n))


       ((mv tmp-exprs tmp-vardecls) (vl-occform-mkwires "temp" 1 m :width n))

       (outs  (append tmp-exprs (list out-expr)))
       (ins   (cons in-expr tmp-exprs))

       (insts (vl-simple-inst-list (car base) "del" outs ins))

       (mod (make-vl-module :name      name
                            :origname  name
                            :ports     (list out-port in-port)
                            :portdecls (list out-portdecl in-portdecl)
                            :vardecls  (list* out-vardecl in-vardecl tmp-vardecls)
                            :modinsts  insts
                            :minloc    *vl-fakeloc*
                            :maxloc    *vl-fakeloc*)))
    (cons mod base))
  ///
  (defthm type-of-vl-make-n-bit-delay-m
    (and (true-listp (vl-make-n-bit-delay-m n m :vecp vecp))
         (consp (vl-make-n-bit-delay-m n m :vecp vecp)))
    :rule-classes :type-prescription))

#||
(include-book ;; fool dependency scanner
 "../mlib/writer")
(vl-pps-modulelist (vl-make-n-bit-delay-m 1 17))
(vl-pps-modulelist (vl-make-n-bit-delay-m 2 17))
(vl-pps-modulelist (vl-make-n-bit-delay-m 3 17 :vecp t))
(vl-pps-modulelist (vl-make-n-bit-delay-m 3 17))
||#


(define vl-assign-delayredux ((x vl-assign-p)
                              (delta vl-delta-p)
                              &key vecp state-onlyp)
  :returns (mv (new-x vl-assign-p :hyp :fguard)
               (delta vl-delta-p  :hyp :fguard))
  :short "Remove the delay from an assignment by introducing an explicit delay
module."

  (b* (((vl-assign x) x)

       ((unless x.delay)
        ;; No delay, leave this assignment alone.
        (mv x delta))

       ((unless (vl-simpledelay-p x.delay))
        (mv x (dwarn :type :vl-delay-toohard
                     :msg "~a0: the delay on this assignment is too complex; ~
                           we only handle plain delays for now."
                     :args (list x)
                     :fatalp t)))

       (width   (vl-expr->finalwidth x.expr))
       ((unless (posp width))
        (mv x (dwarn :type :vl-bad-assign
                     :msg "~a0: expected widths to be computed and positive, ~
                           but rhs width is ~x1."
                     :args (list x width)
                     :fatalp t)))

       (delay (vl-simpledelay->amount x.delay))

       ((when (zp delay))
        ;; Goofy, explicit zero delay -- just drop it from this assignment.
        (mv (change-vl-assign x :delay nil) delta))

       ((when (and state-onlyp (not (hons-assoc-equal "VL_STATE_DELAY" x.atts))))
        ;; Drop plain tick delays, i.e. ones that are not stateholding
        (mv (change-vl-assign x :delay nil) delta))

       ((vl-delta delta) delta)

       (addmods           (vl-make-n-bit-delay-m width delay :vecp vecp))
       ((mv temp-name nf) (vl-namefactory-indexed-name "vl_del" delta.nf))
       ((mv instname nf)  (vl-namefactory-indexed-name "vl_mkdel" nf))

       ;; wire [rhsw-1:0] tmp;
       ((mv temp-expr temp-vardecl) (vl-occform-mkwire temp-name width :loc x.loc))

       ;; VL_N_BIT_DELAY_M mkdel (tmp, rhs);
       (modinst (vl-simple-instantiate (car addmods) instname (list temp-expr x.expr)
                                       :loc x.loc))

       ;; assign lhs = del;
       (new-x
        ;; Using change-vl-assign here means we're still preserving
        ;; strengths/atts, in case that matters for anyone.
        (change-vl-assign x :expr temp-expr :delay nil))

       (delta (change-vl-delta delta
                               :nf       nf
                               :vardecls (cons temp-vardecl delta.vardecls)
                               :modinsts (cons modinst delta.modinsts)
                               :addmods  (revappend-without-guard addmods
                                                                  delta.addmods))))

    (mv new-x delta)))

(define vl-assignlist-delayredux ((x vl-assignlist-p)
                                  (delta vl-delta-p)
                                  &key vecp state-onlyp)
  :returns (mv (new-x vl-assignlist-p :hyp :fguard)
               (delta vl-delta-p      :hyp :fguard))
  (b* (((when (atom x))
        (mv nil delta))
       ((mv car delta) (vl-assign-delayredux (car x) delta :vecp vecp :state-onlyp state-onlyp))
       ((mv cdr delta) (vl-assignlist-delayredux (cdr x) delta :vecp vecp :state-onlyp state-onlyp)))
    (mv (cons car cdr) delta)))




(define vl-gatearg-ok-for-delayredux-p ((x vl-plainarg-p))
  :inline t
  (b* (((vl-plainarg x) x))
    (and
     ;; Require only inputs or outputs.  Why?  If the direction is unknown, we
     ;; won't know whether to delay it or not (we only want to delay inputs).
     ;; If the direction is :vl-inout, we don't even know what it means.
     (or (eq x.dir :vl-input)
         (eq x.dir :vl-output))
     ;; We'll allow blanks since it's easy (we just don't need to delay them).
     ;; For non-blanks, the expression must be one-bit wide, so that using a
     ;; one-bit delay module will work.
     (or (not x.expr)
         (eql (vl-expr->finalwidth x.expr) 1)))))

(define vl-why-is-gatearg-bad-for-delayredux ((x vl-plainarg-p))
  :short "For error reporting, say what the problem with this bad argument is."
  (b* (((vl-plainarg x) x)
       (width (and x.expr
                   (vl-expr->finalwidth x.expr))))
    (cond ((eq x.dir :vl-inout)
           "has direction 'inout'")
          ((not x.dir)
           "has unresolved direction")
          ((not width)
           "has uncomputed width")
          ((not (equal width 1))
           (str::cat "has width " (str::natstr width))))))

(deflist vl-gateargs-ok-for-delayredux-p (x)
  (vl-gatearg-ok-for-delayredux-p x)
  :guard (vl-plainarglist-p x)
  :elementp-of-nil nil)

(define vl-first-bad-gatearg-for-delayredux ((x vl-plainarglist-p))
  :short "For error reporting, find an arg that has a problem."
  (cond ((atom x)
         nil)
        ((vl-gatearg-ok-for-delayredux-p (car x))
         (vl-first-bad-gatearg-for-delayredux (cdr x)))
        (t
         (car x)))
  ///
  (defthm vl-first-bad-gatearg-for-delayredux-under-iff
    (implies (force (vl-plainarglist-p x))
             (iff (vl-first-bad-gatearg-for-delayredux x)
                  (not (vl-gateargs-ok-for-delayredux-p x)))))

  (defthm vl-plainarg-p-of-vl-first-bad-gatearg-for-delayredux
    (implies (force (vl-plainarglist-p x))
             (equal (vl-plainarg-p (vl-first-bad-gatearg-for-delayredux x))
                    (not (vl-gateargs-ok-for-delayredux-p x))))))

(define vl-gatearg-delayredux
  ((delaymod "A VL_1_BIT_DELAY_N module" vl-module-p)
   (x        "Gate instance argument to rewrite"
             (and (vl-plainarg-p x)
                  (vl-gatearg-ok-for-delayredux-p x)))
   (loc      vl-location-p)
   (delta    vl-delta-p))
  :returns (mv (new-x vl-plainarg-p :hyp :fguard)
               (delta vl-delta-p    :hyp :fguard))
  (b* (((vl-plainarg x) x)
       ((unless (eq x.dir :vl-input))
        ;; We only delay inputs, so there's nothing to do.
        (mv x delta))
       ((unless x.expr)
        ;; We support blanks just because it's easy -- we don't need to
        ;; change the argument at all.
        (mv x delta))

       ;; Else, we know (from vl-gatearg-ok-for-delayredux-p) that this is a
       ;; one-bit expression, so it's okay to use a one-bit delay module.

       ((vl-delta delta) delta)
       ((mv del-name nf)   (vl-namefactory-indexed-name "del" delta.nf))
       ((mv mkdel-name nf) (vl-namefactory-indexed-name "mkdel" nf))

       ;; wire del;
       ;; VL_1_BIT_DELAY_N mkdel (del, x.expr);
       ((mv del-expr del-vardecl) (vl-occform-mkwire del-name 1 :loc loc))
       (mkdel-inst (vl-simple-instantiate delaymod mkdel-name
                                          (list del-expr x.expr) :loc loc))

       (delta (change-vl-delta delta
                               :nf nf
                               :vardecls (cons del-vardecl delta.vardecls)
                               :modinsts (cons mkdel-inst delta.modinsts)))
       (new-x (change-vl-plainarg x :expr del-expr)))
    (mv new-x delta)))

(define vl-gatearglist-delayredux
  ((delaymod "A VL_1_BIT_DELAY_N module" vl-module-p)
   (x        "Gate instance arguments to rewrite"
             (and (vl-plainarglist-p x)
                  (vl-gateargs-ok-for-delayredux-p x)))
   (loc      vl-location-p)
   (delta    vl-delta-p))
  :returns (mv (new-x vl-plainarglist-p :hyp :fguard)
               (delta vl-delta-p        :hyp :fguard))
  (b* (((when (atom x))
        (mv x delta))
       ((mv car delta) (vl-gatearg-delayredux delaymod (car x) loc delta))
       ((mv cdr delta) (vl-gatearglist-delayredux delaymod (cdr x) loc delta)))
    (mv (cons car cdr) delta)))

(define vl-gateinst-delayredux ((x vl-gateinst-p)
                                (delta vl-delta-p)
                                &key vecp state-onlyp)
  :returns (mv (new-x vl-gateinst-p :hyp :fguard)
               (delta vl-delta-p    :hyp :fguard))
  (b* (((vl-gateinst x) x)
       ((unless x.delay)
        ;; No delay, nothing to do
        (mv x delta))

       ((unless (vl-simpledelay-p x.delay))
        (mv x (dwarn :type :vl-delay-toohard
                     :msg "~a0: the delay on this gate is too complex; we ~
                           only handle simple delays like #5."
                     :args (list x)
                     :fatalp t
                     :fn 'vl-gateinst-delayredux)))

       (amount (vl-simpledelay->amount x.delay))
       ((when (zp amount))
        ;; Goofy, explicit zero delay -- just drop it from this gateinst.
        ;; BOZO is this really okay?
        (mv (change-vl-gateinst x :delay nil) delta))

       ((when (and state-onlyp (not (hons-assoc-equal "VL_STATE_DELAY" x.atts))))
        ;; Drop plain tick delays, i.e. ones that are not stateholding
        ;; BOZO make this a simpconfig option
        (mv (change-vl-gateinst x :delay nil) delta))

       (badarg (vl-first-bad-gatearg-for-delayredux x.args))
       ((when badarg)
        (mv x (dwarn :type :vl-delay-toohard
                     :msg "~a0: failing to eliminate the delay on this gate ~
                           because argument ~a1 ~s2."
                     :args (list x badarg
                                 (vl-why-is-gatearg-bad-for-delayredux badarg))
                     :fatalp t
                     :fn 'vl-gateinst-delayredux)))

       (addmods  (vl-make-n-bit-delay-m 1 amount :vecp vecp))
       (delaymod (car addmods))
       ((mv new-args delta)
        (vl-gatearglist-delayredux delaymod x.args x.loc delta))
       (new-x (change-vl-gateinst x :args new-args :delay nil))
       (delta (change-vl-delta delta
                               :addmods (append addmods (vl-delta->addmods delta)))))
    (mv new-x delta)))

(define vl-gateinstlist-delayredux ((x vl-gateinstlist-p)
                                    (delta vl-delta-p)
                                    &key vecp state-onlyp)
  :returns (mv (new-x vl-gateinstlist-p :hyp :fguard)
               (delta vl-delta-p        :hyp :fguard))
  (b* (((when (atom x))
        (mv nil delta))
       ((mv car delta) (vl-gateinst-delayredux (car x) delta :vecp vecp :state-onlyp state-onlyp))
       ((mv cdr delta) (vl-gateinstlist-delayredux (cdr x) delta :vecp vecp :state-onlyp state-onlyp)))
    (mv (cons car cdr) delta)))

(define vl-module-delayredux ((x vl-module-p) &key vecp state-onlyp)
  :returns (mv (new-x   vl-module-p     :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
  (b* (((vl-module x) x)
       ((when (vl-module->hands-offp x))
        (mv x nil))

       (delta (vl-starting-delta x))
       (delta (change-vl-delta delta
                               :vardecls x.vardecls
                               :modinsts x.modinsts))
       ((mv assigns delta)   (vl-assignlist-delayredux x.assigns delta :vecp vecp :state-onlyp state-onlyp))
       ((mv gateinsts delta) (vl-gateinstlist-delayredux x.gateinsts delta :vecp vecp :state-onlyp state-onlyp))
       ((vl-delta delta)     (vl-free-delta delta))

       (new-x (change-vl-module
               x
               ;; We started the delta with the vardecls, modinsts, and warnings
               ;; from X, and extended them, so use the new, extended versions.
               :vardecls delta.vardecls
               :modinsts delta.modinsts
               :warnings delta.warnings
               ;; We rewrote all of our own assigns/gateinsts and never add any
               ;; to the delta, so we don't need to do any merging
               :assigns assigns
               :gateinsts gateinsts)))
    (mv new-x delta.addmods))
  ///
  (defthm vl-module->name-of-vl-module-delayredux
    (equal (vl-module->name (mv-nth 0 (vl-module-delayredux x :vecp vecp :state-onlyp state-onlyp)))
           (vl-module->name x))))

(define vl-modulelist-delayredux-aux ((x vl-modulelist-p) &key vecp state-onlyp)
  :returns (mv (new-x   vl-modulelist-p :hyp :fguard)
               (addmods vl-modulelist-p :hyp :fguard))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv car car-addmods) (vl-module-delayredux (car x) :vecp vecp :state-onlyp state-onlyp))
       ((mv cdr cdr-addmods) (vl-modulelist-delayredux-aux (cdr x) :vecp vecp :state-onlyp state-onlyp)))
    (mv (cons car cdr)
        (append-without-guard car-addmods cdr-addmods)))
  ///
  (defthm vl-modulelist->names-of-vl-modulelist-delayredux-aux
    (b* (((mv new-x ?addmods) (vl-modulelist-delayredux-aux x :vecp vecp :state-onlyp state-onlyp)))
      (equal (vl-modulelist->names new-x)
             (vl-modulelist->names x)))))


(define vl-modulelist-delayredux ((x vl-modulelist-p) &key vecp state-onlyp)
  :returns (new-x vl-modulelist-p :hyp :fguard)
  (b* (((mv x-prime addmods)
        (vl-modulelist-delayredux-aux x :vecp vecp :state-onlyp state-onlyp))
       (merged (union (mergesort x-prime)
                      (mergesort addmods)))
       ((unless (uniquep (vl-modulelist->names merged)))
        (raise "Name collision for ~&0."
               (duplicated-members (vl-modulelist->names merged)))))
      merged)
  ///
  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-modulelist-delayredux
    (no-duplicatesp-equal (vl-modulelist->names (vl-modulelist-delayredux x :vecp vecp :state-onlyp state-onlyp)))))


(define vl-design-delayredux ((x vl-design-p) &key vecp state-onlyp)
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-delayredux x.mods :vecp vecp :state-onlyp state-onlyp))))


