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
(include-book "../mlib/stmt-tools")
(include-book "../mlib/lvalues")
(include-book "../mlib/range-tools")
(include-book "../mlib/namefactory")
(include-book "../mlib/filter")
(include-book "occform/gen-util")
(local (include-book "../util/arithmetic"))
(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))

(defxdoc flop-inference
  :parents (transforms)
  :short "Convert certain <tt>always</tt> statements into flop-module
instances."

  :long "<p>This transformation basically looks for statements like</p>

<code>always @@(posedge clk) lhs &lt;= rhs;</code>

<p>And rewrites them into:</p>

<code>VL_N_BIT_FLOP foo ( .q(lhs), .d(rhs), .clk(clk) );</code>

<p>However, we only carry out this transformation under certain conditions that
we think makes it sound.  Note also that <tt>lhs</tt> must be simultaneously
converted from a <tt>reg</tt> into a <tt>wire</tt>.</p>")


(defsection *vl-1-bit-flop-verilog*
  :parents (flop-inference)
  :short "One-bit flop primitive, represented as a @(see vl-module-p)."

  :long "<p>Our @(see flop-inference) transform converts certain
<tt>always</tt> statements into instances of <tt>VL_1_BIT_FLOP</tt>, a special,
primitive module.  The constant @(srclink *vl-1-bit-flop-verilog*) contains our
internal (i.e., @(see vl-module-p)) representation of this module.  In Verilog,
the module might be written as follows:</p>

<code>
module VL_1_BIT_FLOP (q, clk, d) ;

  output reg q;
  input wire clk;
  input wire d;

  always @@(posedge clk)
     q &lt;= d;

endmodule
</code>"

  (defconst *vl-1-bit-flop-verilog*

    (b* ((name "VL_1_BIT_FLOP")
         (atts (acons "VL_HANDS_OFF" nil nil))

         ((mv q-expr q-port q-portdecl &)                 (vl-occform-mkport "q" :vl-output 1))
         ((mv clk-expr clk-port clk-portdecl clk-netdecl) (vl-occform-mkport "clk" :vl-input 1))
         ((mv d-expr d-port d-portdecl d-netdecl)         (vl-occform-mkport "d" :vl-input 1))

         (q-regdecl (make-vl-regdecl :name (hons-copy "q") :loc *vl-fakeloc*))

         ;; always @(posedge clk) q <= d;
         (q<=d         (make-vl-assignstmt :type :vl-nonblocking :lvalue q-expr :expr d-expr
                                           :loc *vl-fakeloc*))
         (clk-evatom   (make-vl-evatom :type :vl-posedge :expr clk-expr))
         (ctrl         (make-vl-eventcontrol :starp nil :atoms (list clk-evatom)))
         (stmt         (make-vl-timingstmt :ctrl ctrl :body q<=d))
         (always       (make-vl-always :stmt stmt :loc *vl-fakeloc*)))

      (make-vl-module :name      name
                      :origname  name
                      :atts      atts
                      :ports     (list q-port clk-port d-port)
                      :portdecls (list q-portdecl clk-portdecl d-portdecl)
                      :netdecls  (list clk-netdecl d-netdecl)
                      :regdecls  (list q-regdecl)
                      :alwayses  (list always)
                      :minloc    *vl-fakeloc*
                      :maxloc    *vl-fakeloc*))))


(defsection vl-make-1-bit-flop-instances
  :parents (vl-make-n-bit-flop)
  :short "Build a list of <tt>VL_1_BIT_FLOP</tt> instances."

  :long "<p><b>Signature:</b> @(call vl-make-1-bit-flop-instances) returns a
list of module instances.</p>

<p>We are given as inputs:</p>

<ul>
<li><tt>q-wires</tt>, a list of expressions, <tt>q[0], ..., q[n-1]</tt>,</li>
<li><tt>clk-wire</tt>, an expression, <tt>clk</tt>, </li>
<li><tt>d-wires</tt>, a list of expressions, <tt>d[0], ..., d[n-1]</tt>, and</li>
<li><tt>n</tt>, which is our current index (for nice name generation)</li>
</ul>

<p>We produce a list of module instances, i.e., </p>

<code>
   VL_1_BIT_FLOP bit_0 (q[0], clk, d[0]) ;
   VL_1_BIT_FLOP bit_1 (q[1], clk, d[1]) ;
   ...
   VL_1_BIT_FLOP bit_{n-1} (q[{n-1}], clk, d[{n-1}]) ;
</code>"

  (defund vl-make-1-bit-flop-instances (q-wires clk-wire d-wires n)
    (declare (xargs :guard (and (vl-exprlist-p q-wires)
                                (vl-expr-p clk-wire)
                                (vl-exprlist-p d-wires)
                                (same-lengthp q-wires d-wires)
                                (natp n))))
    (b* (((when (atom q-wires))
          nil)
         (args (list (make-vl-plainarg :expr (car q-wires) :dir :vl-output :portname (hons-copy "q"))
                     (make-vl-plainarg :expr clk-wire      :dir :vl-input  :portname (hons-copy "clk"))
                     (make-vl-plainarg :expr (car d-wires) :dir :vl-input  :portname (hons-copy "d"))))
         (inst (make-vl-modinst :modname   (vl-module->name *vl-1-bit-flop-verilog*)
                                :instname  (hons-copy (str::cat "bit_" (str::natstr n)))
                                :paramargs (vl-arguments nil nil)
                                :portargs  (vl-arguments nil args)
                                :loc       *vl-fakeloc*)))
      (cons inst
            (vl-make-1-bit-flop-instances (cdr q-wires) clk-wire (cdr d-wires) (+ n 1)))))

  (local (in-theory (enable vl-make-1-bit-flop-instances)))

  (defthm vl-modinstlist-p-of-vl-make-1-bit-flop-instances
    (implies (and (force (vl-exprlist-p q-wires))
                  (force (vl-expr-p clk-wire))
                  (force (vl-exprlist-p d-wires))
                  (force (same-lengthp q-wires d-wires))
                  (force (natp n)))
             (vl-modinstlist-p (vl-make-1-bit-flop-instances q-wires clk-wire d-wires n)))))



(defsection vl-make-n-bit-flop
  ;; BOZO maybe switch to def-vl-modgen
  :parents (flop-inference)
  :short "Generate <tt>VL_<i>N</i>_BIT_FLOP</tt> for some <i>N</i>."

  :long "<p><b>Signature:</b> @(call vl-make-n-bit-flop) returns a list of
modules.</p>

<p>The first module in the list is the requested module, whose name will be
<tt>VL_<i>N</i>_BIT_FLOP</tt>.  The other modules in the list include any
submodules of <tt>VL_<i>N</i>_BIT_FLOP</tt> (typically <tt>VL_1_BIT_FLOP</tt>)
that need to be added to the module list for completeness.</p>"

  (defund vl-make-n-bit-flop (n)
    (declare (xargs :guard (posp n)))
    (b* (((when (= n 1))
          (list *vl-1-bit-flop-verilog*))

         (name (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_FLOP")))

         ((mv q-expr q-port q-portdecl q-netdecl)         (vl-occform-mkport "q" :vl-output n))
         ((mv clk-expr clk-port clk-portdecl clk-netdecl) (vl-occform-mkport "clk" :vl-input 1))
         ((mv d-expr d-port d-portdecl d-netdecl)         (vl-occform-mkport "d" :vl-input n))

         (q-wires  (vl-make-list-of-bitselects q-expr 0 (- n 1)))
         (d-wires  (vl-make-list-of-bitselects d-expr 0 (- n 1)))
         (modinsts (vl-make-1-bit-flop-instances q-wires clk-expr d-wires 0)))

      (list (make-vl-module :name      name
                            :origname  name
                            :ports     (list q-port clk-port d-port)
                            :portdecls (list q-portdecl clk-portdecl d-portdecl)
                            :netdecls  (list q-netdecl clk-netdecl d-netdecl)
                            :modinsts  modinsts
                            :atts      (acons "VL_HANDS_OFF" nil nil) ;; <-- maybe not needed with the new sizing code now
                            :minloc    *vl-fakeloc*
                            :maxloc    *vl-fakeloc*)
            *vl-1-bit-flop-verilog*)))

  (local (in-theory (enable vl-make-n-bit-flop)))

  (defthm vl-modulelist-p-of-vl-make-n-bit-flop
    (implies (posp n)
             (vl-modulelist-p (vl-make-n-bit-flop n)))))



(defsection vl-pattern-match-flop
  :parents (flop-inference)
  :short "Recognize and deconstruct <tt>always</tt> statements that might be
suitable for flop inference."

  :long "<p><b>Signature:</b> @(call vl-pattern-match-flop) returns
<tt>(mv successp clk-expr lhs-expr rhs-expr)</tt>.</p>

<p><tt>x</tt> is an always statement (see @(see vl-always-p)).  We try to
determine if <tt>x</tt> has the form:</p>

<code>
always @@(posedge clk)
   lhs [&lt;]= rhs;  // i.e., \"lhs &lt;=rhs\" or \"lhs = rhs\"
</code>

<p>Where <tt>clk</tt> and <tt>lhs</tt> are simple identifier expressions.  If
so, we extract and return the expressions for <tt>clk</tt>, <tt>lhs</tt>, and
<tt>rhs</tt>.</p>"

  (defund vl-pattern-match-flop (x)
    "Returns (mv successp clk-expr lhs-expr rhs-expr)"
    (declare (xargs :guard (vl-always-p x)))

    (b* ((stmt (vl-always->stmt x))

         ((unless (and (eq (tag stmt) :vl-compoundstmt)
                       (eq (vl-compoundstmt->type stmt) :vl-timingstmt)))
          (mv nil nil nil nil))

         (ctrl (vl-timingstmt->ctrl stmt))
         (body (vl-timingstmt->body stmt))

         ;; Try to match ctrl with (posedge clk)
         ((unless (and (eq (tag ctrl) :vl-eventcontrol)
                       (not (vl-eventcontrol->starp ctrl))))
          (mv nil nil nil nil))
         (evatoms (vl-eventcontrol->atoms ctrl))
         ((unless (and (= (len evatoms) 1)
                       (eq (vl-evatom->type (car evatoms)) :vl-posedge)))
          (mv nil nil nil nil))
         (clk-expr (vl-evatom->expr (car evatoms)))
         ((unless (vl-idexpr-p clk-expr))
          (mv nil nil nil nil))

         ;; Now that we've extracted the clock, try to match body with lhs [<]= rhs

         ((unless (and (eq (tag body) :vl-assignstmt)
                       ;; Only allow = and <=, i.e., simple blocking/nonblocking assigns
                       (or (eq (vl-assignstmt->type body) :vl-blocking)
                           (eq (vl-assignstmt->type body) :vl-nonblocking))
                       ;; Don't allow event controls, but allow and ignore delays.
                       (or (not (vl-assignstmt->ctrl body))
                           (eq (tag (vl-assignstmt->ctrl body)) :vl-delaycontrol))))
          (mv nil nil nil nil))
         (lhs-expr (vl-assignstmt->lvalue body))
         (rhs-expr (vl-assignstmt->expr body))
         ((unless (vl-idexpr-p lhs-expr))
          (mv nil nil nil nil)))
        (mv t clk-expr lhs-expr rhs-expr)))

  (local (in-theory (enable vl-pattern-match-flop)))

  (defthm type-of-vl-pattern-match-flop
    (booleanp (mv-nth 0 (vl-pattern-match-flop x)))
    :rule-classes :type-prescription)

  (defthm vl-pattern-match-flop-basics
    (implies (force (vl-always-p x))
             (and (equal (vl-expr-p (mv-nth 1 (vl-pattern-match-flop x)))
                         (if (mv-nth 0 (vl-pattern-match-flop x)) t nil))
                  (equal (vl-idexpr-p (mv-nth 1 (vl-pattern-match-flop x)))
                         (if (mv-nth 0 (vl-pattern-match-flop x)) t nil))
                  (equal (vl-expr-p (mv-nth 2 (vl-pattern-match-flop x)))
                         (if (mv-nth 0 (vl-pattern-match-flop x)) t nil))
                  (equal (vl-idexpr-p (mv-nth 2 (vl-pattern-match-flop x)))
                         (if (mv-nth 0 (vl-pattern-match-flop x)) t nil))
                  (equal (vl-expr-p (mv-nth 3 (vl-pattern-match-flop x)))
                         (if (mv-nth 0 (vl-pattern-match-flop x)) t nil))))))




; We now switch to latch inference.  We put latch inference into this file
; along with flop inference, because the two are quite similar and can share
; some code at the end of this file.

(defsection *vl-1-bit-latch-verilog*
  :parents (latch-inference)
  :short "One-bit latch primitive, representated as a @(see vl-module-p)."

  :long "<p>Our @(see latch-inference) transform converts certain
<tt>always</tt> statements into instances of <tt>VL_1_BIT_LATCH</tt>, a special
primitive module.  The constant @(srclink *vl-1-bit-latch-verilog*) contains
our internal (i.e., @(see vl-module-p)) representation of this module.  In
Verilog, the module might be written as follows:</p>

<code>
module VL_1_BIT_LATCH (q, clk, d);

   input  wire clk;
   input  wire d;
   output reg  q;

   always @@(d or clk)
     q &lt;= clk ? d : q;

endmodule
</code>"

  (defconst *vl-1-bit-latch-verilog*

    (b* ((name (hons-copy "VL_1_BIT_LATCH"))
         (atts (acons "VL_HANDS_OFF" nil nil))

         ((mv q-expr q-port q-portdecl &)                 (vl-occform-mkport "q" :vl-output 1))
         ((mv clk-expr clk-port clk-portdecl clk-netdecl) (vl-occform-mkport "clk" :vl-input 1))
         ((mv d-expr d-port d-portdecl d-netdecl)         (vl-occform-mkport "d" :vl-input 1))

         (q-regdecl (make-vl-regdecl :name (hons-copy "q") :loc *vl-fakeloc*))

         ;; always @(d or clk) q <= clk ? d : q;
         (|clk?d:q|     (make-vl-nonatom :op :vl-qmark
                                         :args (list clk-expr d-expr q-expr)
                                         :finalwidth 1
                                         :finaltype :vl-unsigned))
         (|q<=clk?d:q|  (make-vl-assignstmt :type :vl-nonblocking
                                            :lvalue q-expr
                                            :expr |clk?d:q|
                                            :loc *vl-fakeloc*))
         (d-evatom     (make-vl-evatom :type :vl-noedge :expr d-expr))
         (clk-evatom   (make-vl-evatom :type :vl-noedge :expr clk-expr))
         (ctrl         (make-vl-eventcontrol :starp nil :atoms (list d-evatom clk-evatom)))
         (stmt         (make-vl-timingstmt :ctrl ctrl :body |q<=clk?d:q|))
         (always       (make-vl-always :stmt stmt :loc *vl-fakeloc*)))

      (make-vl-module :name      name
                      :origname  name
                      :ports     (list q-port clk-port d-port)
                      :portdecls (list q-portdecl clk-portdecl d-portdecl)
                      :netdecls  (list clk-netdecl d-netdecl)
                      :regdecls  (list q-regdecl)
                      :alwayses  (list always)
                      :minloc    *vl-fakeloc*
                      :maxloc    *vl-fakeloc*
                      :atts      atts))))


(defsection vl-make-1-bit-latch-instances
  :parents (latch-inference)
  :short "Build a list of <tt>VL_1_BIT_LATCH</tt> instances."

  :long "<p><b>Signature:</b> @(call vl-make-1-bit-latch-instances) returns a
list of module instances.</p>

<p>We are given as inputs:</p>

<ul>
<li><tt>q-wires</tt>, a list of expressions, <tt>q[0], ..., q[n-1]</tt>,</li>
<li><tt>clk-wire</tt>, an expression, <tt>clk</tt>, </li>
<li><tt>d-wires</tt>, a list of expressions, <tt>d[0], ..., d[n-1]</tt>, and</li>
<li><tt>n</tt>, which is our current index (for nice name generation)</li>
</ul>

<p>We produce a list of module instances, i.e., </p>

<code>
   VL_1_BIT_LATCH bit_0 (q[0], clk, d[0]) ;
   VL_1_BIT_LATCH bit_1 (q[1], clk, d[1]) ;
   ...
   VL_1_BIT_LATCH bit_{n-1} (q[{n-1}], clk, d[{n-1}]) ;
</code>"

  (defund vl-make-1-bit-latch-instances (q-wires clk-wire d-wires n)
    (declare (xargs :guard (and (vl-exprlist-p q-wires)
                                (vl-expr-p clk-wire)
                                (vl-exprlist-p d-wires)
                                (same-lengthp q-wires d-wires)
                                (natp n))))
    (b* (((when (atom q-wires))
          nil)
         (args (list (make-vl-plainarg :expr (car q-wires) :dir :vl-output :portname (hons-copy "q"))
                     (make-vl-plainarg :expr clk-wire      :dir :vl-input  :portname (hons-copy "clk"))
                     (make-vl-plainarg :expr (car d-wires) :dir :vl-input  :portname (hons-copy "d"))))
         (inst (make-vl-modinst :modname   (vl-module->name *vl-1-bit-latch-verilog*)
                                :instname  (hons-copy (str::cat "bit_" (str::natstr n)))
                                :paramargs (vl-arguments nil nil)
                                :portargs  (vl-arguments nil args)
                                :loc       *vl-fakeloc*)))
      (cons inst
            (vl-make-1-bit-latch-instances (cdr q-wires) clk-wire (cdr d-wires) (+ n 1)))))

  (local (in-theory (enable vl-make-1-bit-latch-instances)))

  (defthm vl-modinstlist-p-of-vl-make-1-bit-latch-instances
    (implies (and (force (vl-exprlist-p q-wires))
                  (force (vl-expr-p clk-wire))
                  (force (vl-exprlist-p d-wires))
                  (force (same-lengthp q-wires d-wires))
                  (force (natp n)))
             (vl-modinstlist-p (vl-make-1-bit-latch-instances q-wires clk-wire d-wires n)))))



(defsection vl-make-n-bit-latch
  :parents (latch-inference)
  :short "Generate <tt>VL_<i>N</i>_BIT_LATCH</tt> for some <i>N</i>."

  :long "<p><b>Signature:</b> @(call vl-make-n-bit-latch) returns a list of
modules.</p>

<p>The first module in the list is the requested module, whose name will be
<tt>VL_<i>N</i>_BIT_LATCH</tt>.  The other modules in the list include any
submodules of <tt>VL_<i>N</i>_BIT_LATCH</tt> (typically
<tt>VL_1_BIT_LATCH</tt>) that need to be added to the module list for
completeness.</p>"

  (defund vl-make-n-bit-latch (n)
    (declare (xargs :guard (posp n)))
    (b* (((when (= n 1))
          (list *vl-1-bit-latch-verilog*))

         (name        (hons-copy (str::cat "VL_" (str::natstr n) "_BIT_LATCH")))

         ((mv q-expr q-port q-portdecl q-netdecl)         (vl-occform-mkport "q" :vl-output n))
         ((mv clk-expr clk-port clk-portdecl clk-netdecl) (vl-occform-mkport "clk" :vl-input 1))
         ((mv d-expr d-port d-portdecl d-netdecl)         (vl-occform-mkport "d" :vl-input n))

         (q-wires     (vl-make-list-of-bitselects q-expr 0 (- n 1)))
         (d-wires     (vl-make-list-of-bitselects d-expr 0 (- n 1)))
         (modinsts    (vl-make-1-bit-latch-instances q-wires clk-expr d-wires 0)))
      (list (make-vl-module :name      name
                            :origname  name
                            :ports     (list q-port clk-port d-port)
                            :portdecls (list q-portdecl clk-portdecl d-portdecl)
                            :netdecls  (list q-netdecl clk-netdecl d-netdecl)
                            :modinsts  modinsts
                            :atts      (acons "VL_HANDS_OFF" nil nil)  ; <-- may not be needed with the new sizing code
                            :minloc    *vl-fakeloc*
                            :maxloc    *vl-fakeloc*)
            *vl-1-bit-latch-verilog*)))

  (local (in-theory (enable vl-make-n-bit-latch)))

  (defthm vl-modulelist-p-of-vl-make-n-bit-latch
    (implies (posp n)
             (vl-modulelist-p (vl-make-n-bit-latch n)))))




(defund vl-evatomlist-all-plain-p (x)
  ;; Recognize a sensitivity list where everything is simple and there are no
  ;; posedge or negedge things.  For instance, @(foo or bar or baz).
  (declare (xargs :guard (vl-evatomlist-p x)))
  (or (atom x)
      (and (eq (vl-evatom->type (car x)) :vl-noedge)
           (vl-idexpr-p (vl-evatom->expr (car x)))
           (vl-evatomlist-all-plain-p (cdr x)))))

(defprojection vl-evatomlist->exprs (x)
  (vl-evatom->expr x)
  :guard (vl-evatomlist-p x)
  :result-type vl-exprlist-p)

(defthm vl-idexprlist-p-of-vl-evatomlist->exprs
  (implies (vl-evatomlist-all-plain-p x)
           (vl-idexprlist-p (vl-evatomlist->exprs x)))
  :hints(("Goal" :in-theory (enable vl-evatomlist-all-plain-p))))




(defun vl-pattern-match-latchbody-form1 (x)
  "Returns (MV SUCCESSP CONDITION LHS RHS)"
  (declare (xargs :guard (vl-stmt-p x)))

; Recognize and decompose an assignment statement of the form:
;     lhs [<]= condition ? rhs : lhs ;

  (b* (((unless (and (eq (tag x) :vl-assignstmt)
                     (member (vl-assignstmt->type x) '(:vl-blocking :vl-nonblocking))))
        (mv nil nil nil nil))

       (lhs (vl-assignstmt->lvalue x))
       (rhs (vl-assignstmt->expr x))

       ((unless (and (eq (tag rhs) :vl-nonatom)
                     (eq (vl-nonatom->op rhs) :vl-qmark)))
        (mv nil nil nil nil))

       (args      (vl-nonatom->args rhs))
       (condition (first args))
       (rhs       (second args))

       ((unless (equal lhs (third args)))
        (mv nil nil nil nil)))

      (mv t condition lhs rhs)))

(defun vl-pattern-match-latchbody-form2 (x)
  "Returns (MV SUCCESSP CONDITION LHS RHS)"
  (declare (xargs :guard (vl-stmt-p x)))

; Recognize and decompose an if-statement of the form:
;     if (condition) lhs <= rhs;

  (b* (((unless (and (eq (tag x) :vl-compoundstmt)
                     (eq (vl-compoundstmt->type x) :vl-ifstmt)))
        (mv nil nil nil nil))

       (condition   (vl-ifstmt->condition x))
       (truebranch  (vl-ifstmt->truebranch x))
       (falsebranch (vl-ifstmt->falsebranch x))

       ((unless (and (eq (tag falsebranch) :vl-nullstmt)
                     (eq (tag truebranch) :vl-assignstmt)
                     (member (vl-assignstmt->type truebranch)
                             '(:vl-blocking :vl-nonblocking))))
        (mv nil nil nil nil))

       (lhs (vl-assignstmt->lvalue truebranch))
       (rhs (vl-assignstmt->expr truebranch)))
      (mv t condition lhs rhs)))

(defun vl-pattern-match-latchbody (x)
  "Returns (MV SUCCESSP CONDITION LHS RHS)"
  (declare (xargs :guard (vl-stmt-p x)))

  (b* (((mv successp condition lhs rhs) (vl-pattern-match-latchbody-form1 x)))
      (if successp
          (mv successp condition lhs rhs)
        (vl-pattern-match-latchbody-form2 x))))



(defsection vl-pattern-match-latch

  (defund vl-pattern-match-latch (x warnings)
    "Returns (mv warnings successp condition-expr lhs-expr rhs-expr)"
    (declare (xargs :guard (and (vl-always-p x)
                                (vl-warninglist-p warnings))))

; We once imagined trying to carry out the following rewrite.
;
;    if (expr)
;       lhs [<]= rhs ;   // i.e., "lhs = rhs" or "lhs <= rhs"
;    else
;       ; // null statement
;
;  ----->
;
;    lhs [<]= expr ? rhs : lhs;
;
; But this seemed fraught with difficulties in general.  For instance,
;
;   1. In the blocking case, the rewritten Verilog may have a different delay
;      in the else case.  In the original Verilog, if expr evalutes to "false"
;      then the whole if statement completes without carrying out any
;      assignments.  In our rewritten Verilog, the else case results in a
;      blocking assignment from lhs to itself, and hence would seem to have a
;      delay of at least one unit.  This might interfere with other statements
;      that are very sensitive to timing.
;
;   2. If a non-blocking assignment is used, the else case results in an
;      assignment being scheduled from lhs to itself.  This could interact
;      badly with other statements.  For instance, consider:
;
;         lhs <= 0;
;         if (expr) lhs <= rhs;
;
;      Then the transformed Verilog would be:
;
;         lhs <= 0;
;         lhs <= expr ? rhs : lhs;
;
; Because of this, we have abandoned this idea for now, and are instead just
; trying to look for simple patterns.  We will recognize either of the
; following patterns as a latch:
;
;    always @( [...] )   // where ... indicates at least rhs and enable
;       if (enable)
;          lhs [<]= rhs;
;
;    always @( [...] )
;       lhs [<]= enable ? rhs : lhs;
;
; This function tries to see whether the bare syntactic criteria are met, and
; if so, return the condition, lhs, and rhs expressions.  If the statement
; looks like a latch but we notice some problem with it, e.g., the sensitivity
; list might be wrong, then we produce some warnings.

    (b* ((stmt (vl-always->stmt x))

         ((unless (and (eq (tag stmt) :vl-compoundstmt)
                       (eq (vl-compoundstmt->type stmt) :vl-timingstmt)))
          (mv warnings nil nil nil nil))

; Make sure the control is ok and decompose it.

         (ctrl (vl-timingstmt->ctrl stmt))
         ((unless (and (eq (tag ctrl) :vl-eventcontrol)
                       (or (vl-eventcontrol->starp ctrl)
                           (vl-evatomlist-all-plain-p (vl-eventcontrol->atoms ctrl)))))
          (mv warnings nil nil nil nil))

         (starp (vl-eventcontrol->starp ctrl))
         (atoms (vl-eventcontrol->atoms ctrl))


; Make sure the body is ok and decompose it.

         (body (vl-timingstmt->body stmt))

         ((mv successp condition lhs rhs)
          (vl-pattern-match-latchbody body))

         ((unless (and successp
                       (vl-idexpr-p lhs)))
          (mv warnings nil nil nil nil))


; Now do some sanity checks on what we've found.

         (lhs-name        (vl-idexpr->name lhs))
         (rhs-wires       (vl-expr-names rhs))
         (condition-wires (vl-expr-names condition))

         ((when (member-equal lhs-name rhs-wires))
          ;; Basic sanity check.
          (mv (cons (make-vl-warning
                     :type :vl-latch-fail
                     :msg "~a0: failing to infer a latch because the register ~
                          being assigned to, ~s1, occurs in the rhs expression, ~
                          ~a2."
                     :args (list x lhs-name rhs))
                    warnings)
              nil nil nil nil))

         ((when (member-equal lhs-name condition-wires))
          ;; Basic sanity check.
          (mv (cons (make-vl-warning
                     :type :vl-latch-fail
                     :msg "~a0: failing to infer a latch because the register ~
                          being assigned to, ~s1, occurs in its own enable ~
                          expression, ~a2."
                     :args (list x lhs-name condition))
                    warnings)
              nil nil nil nil))

; Sanity check the sensitivity list.  We want to make sure all wires used in
; the condition and rhs are found in the sensitivity list.

         (need-wires (if starp
                         nil
                       (append rhs-wires condition-wires)))

         (have-wires (if starp
                         nil
                       (vl-idexprlist->names (vl-evatomlist->exprs atoms))))

         ((unless (subsetp-equal need-wires have-wires))
          (mv (cons (make-vl-warning
                     :type :vl-latch-fail
                     :msg "~a0: failing to infer a latch because the sensitivity ~
                            list omits ~&1, which would seem to be necessary."
                     :args (list x (set-difference-equal need-wires have-wires)))
                    warnings)
              nil nil nil nil))

; As a convenience to the user, we'll warn if the sensitivity list says more
; than we think is needed.  But this won't prevent us from inferring a latch.

         (warnings (if (subsetp-equal have-wires need-wires)
                       warnings
                     (cons (make-vl-warning
                            :type :vl-sensitivity-list
                            :msg "~a0: sensitivity list appears to include ~&1 ~
                                 unnecessarily."
                            :args (list x (set-difference-equal have-wires need-wires)))
                           warnings))))

      (mv warnings t condition lhs rhs)))

  (local (in-theory (enable vl-pattern-match-latch)))

  (defthm vl-warninglist-p-of-vl-pattern-match-latch
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-pattern-match-latch x warnings))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm booleanp-of-vl-pattern-match-latch
    (booleanp (mv-nth 1 (vl-pattern-match-latch x warnings)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-pattern-match-latch-basics
    (implies (force (vl-always-p x))
             (and
              (equal (vl-expr-p (mv-nth 2 (vl-pattern-match-latch x warnings)))
                     (if (mv-nth 1 (vl-pattern-match-latch x warnings)) t nil))
              (equal (vl-expr-p (mv-nth 3 (vl-pattern-match-latch x warnings)))
                     (if (mv-nth 1 (vl-pattern-match-latch x warnings)) t nil))
              (equal (vl-idexpr-p (mv-nth 3 (vl-pattern-match-latch x warnings)))
                     (if (mv-nth 1 (vl-pattern-match-latch x warnings)) t nil))
              (equal (vl-expr-p (mv-nth 4 (vl-pattern-match-latch x warnings)))
                     (if (mv-nth 1 (vl-pattern-match-latch x warnings)) t nil))))))




; Actual inference of flops and latches:

(defsection vl-always-infer-latch/flop
  :parents (flop-inference latch-inference)
  :short "Try to infer a flop or latch from an <tt>always</tt> block."

  :long "<p><b>Signature:</b> @(call vl-always-infer-latch/flop) returns
<tt>(mv successp warnings reg inst addmods decls assigns nf)</tt>.</p>

<h5>Inputs</h5>
<ul>
 <li><tt>x</tt>, an always block we may infer a flop from</li>
 <li><tt>mod</tt>, the module in which <tt>x</tt> resides</li>
 <li><tt>warnings</tt>, a warnings accumulator</li>
 <li><tt>nf</tt>, a @(see vl-namefactory-p) for generating fresh wire names.</li>
</ul>

<p>We may extend <tt>warnings</tt> when <tt>x</tt> looks like it should
be a flop, but it does not appear safe to convert it.</p>

<p><tt>successp</tt> is true only when we wish to convert this always statement
into a flop or latch.  Aside from <tt>successp</tt> and <tt>warnings</tt>, the
other outputs are only useful when <tt>successp</tt> holds.</p>

<h5>Outputs (when successp)</h5>

<ul>

<li><tt>reg</tt> is the @(see vl-regdecl-p) that needs to be converted into an
ordinary wire,</li>

<li><tt>inst</tt> is a new instance of a <tt>VL_<i>N</i>_BIT_FLOP</tt> or
<tt>VL_<i>N</i>_BIT_LATCH</tt> that must be added to the module to replace this
always block,</li>

<li><tt>addmods</tt> are any modules that need to be added to the module list
to ensure that we retain @(see completeness) as we introduce
<tt>inst</tt>,</li>

<li><tt>decls</tt> are any new @(see vl-netdecl-p)s that need to be added
to the module,</li>

<li><tt>assigns</tt> are any new @(see vl-assign-p)s that need to be added to
the module.</li>

<li><tt>nf</tt> is the updated name factory.</li>

</ul>"

  (defund vl-always-infer-latch/flop (x mod warnings nf)
    "Returns (mv successp warnings reg inst addmods decls assigns nf)"
    (declare (xargs :guard (and (vl-always-p x)
                                (vl-module-p mod)
                                (vl-warninglist-p warnings)
                                (vl-namefactory-p nf))))

    (b* (((mv warnings successp type clk-expr lhs-expr rhs-expr)

          ;; Try to match either a flop or latch.
          (b* (((mv successp clk-expr lhs-expr rhs-expr)
                (vl-pattern-match-flop x))
               ((when successp)
                (mv warnings t :flop clk-expr lhs-expr rhs-expr))
               ((mv warnings successp clk-expr lhs-expr rhs-expr)
                (vl-pattern-match-latch x warnings)))
              (mv warnings successp :latch clk-expr lhs-expr rhs-expr)))

         ((unless successp)
          (mv nil warnings nil nil nil nil nil nf))

         (loc        (vl-always->loc x))
         (type-str   (if (eq type :flop) "flop" "latch"))
         (fail-type  (if (eq type :flop) :vl-flop-fail :vl-latch-fail))

         ;; We only try to infer a flop/latch if there is a register
         ;; declaration which seems to be sensible.  In particular, the regdecl
         ;; must not have any array dimensions, and its range needs to be
         ;; resolved.

         (lhs-name (vl-idexpr->name lhs-expr))
         (reg      (vl-find-regdecl lhs-name (vl-module->regdecls mod)))
         ((unless reg)
          (mv nil
              (cons (make-vl-warning
                     :type fail-type
                     :msg "~a0: despite its ~s1-like appearance, we fail to ~
                           infer a ~s1 because ~s2 is not declared to be a reg."
                     :args (list x type-str lhs-name))
                    warnings)
              nil nil nil nil nil nf))

         (lhs-range (vl-regdecl->range reg))
         ((unless (vl-maybe-range-resolved-p lhs-range))
          (mv nil
              (cons (make-vl-warning
                     :type fail-type
                     :msg "~a0: despite its ~s1-like appearance, we fail to ~
                           infer a ~s1 because the size of ~s2 has not been ~
                           determined; its range is ~a3."
                     :args (list x type-str lhs-name lhs-range))
                    warnings)
              nil nil nil nil nil nf))

         ((when (vl-regdecl->arrdims reg))
          (mv nil
              (cons (make-vl-warning
                     :type fail-type
                     :msg "~a0: despite its ~s1-like appearance, we fail to ~
                           infer a ~s1 because ~s2 has array dimensions."
                     :args (list x type-str lhs-name))
                    warnings)
              nil nil nil nil nil nf))

         ;; A severe restriction that (we hope) makes our flop and latch
         ;; inference sound: we fail if any other always-statement ever assigns
         ;; anything to lhs.  (We don't care about initial statements, though.)
         ;; Since we assume that x occurs within mod, and we are assigning to
         ;; lhs within x, we can check for this by ensuring that there is only
         ;; one assignment to lhs.")

         ;; BOZO don't use lvalexprs for semantically important stuff!

         (lvalue-names (vl-exprlist-names (vl-alwayslist-lvalexprs
                                           (vl-module->alwayses mod))))

         ((unless (= 1 (acl2::duplicity lhs-name lvalue-names)))
          (mv nil
              (cons (make-vl-warning
                     :type fail-type
                     :msg "~a0: despite its ~s1-like appearance, we cowardly ~
                           refuse to infer a ~s1 for ~s2 because it is assigned ~
                           to by other always statements."
                     :args (list x type-str lhs-name))
                    warnings)
              nil nil nil nil nil nf))

         ;; At this point, things seem to be working out.  The always statement
         ;; matches the desired pattern, lhs is known to be a register, it's
         ;; not assigned to elsewhere, etc.  We're going to go ahead and infer
         ;; a flop/latch.  The basic idea is to replace the always statement
         ;; with an instance of some VL_N_BIT_FLOP or VL_N_BIT_LATCH.  We can
         ;; determine N by looking at the size of the register.

         (n       (vl-maybe-range-size lhs-range))
         (addmods (if (eq type :flop)
                      (vl-make-n-bit-flop n)
                    (vl-make-n-bit-latch n)))
         (modname (vl-module->name (car addmods)))


         ;; Something tricky is that the rhs expression might be wider than
         ;; the lhs expression.  We want to allow it to be truncated.  But we
         ;; haven't yet computed sizes.  So, our idea is to introduce a new,
         ;; temporary wire that has the size of lhs, and assign rhs to it.
         ;; Later, the assign can be truncated like any other assignment.

         ((mv rhs-temp-name nf)
          (vl-namefactory-plain-name (str::cat lhs-name "_temp_rhs") nf))

         (rhs-temp-expr (make-vl-atom :guts (make-vl-id :name rhs-temp-name)))
         (rhs-temp-decl (make-vl-netdecl :loc loc
                                         :name rhs-temp-name
                                         :type :vl-wire
                                         :range (vl-make-n-bit-range n)))
         (rhs-temp-assign (make-vl-assign :loc loc
                                          :lvalue rhs-temp-expr
                                          :expr rhs-expr))

         (q-arg    (make-vl-plainarg :expr lhs-expr :portname "q" :dir :vl-output))
         (clk-arg  (make-vl-plainarg :expr clk-expr :portname "clk" :dir :vl-input))
         (d-arg    (make-vl-plainarg :expr rhs-temp-expr :portname "d" :dir :vl-input))
         (portargs (vl-arguments nil (list q-arg clk-arg d-arg)))

         ((mv inst-name nf)
          (vl-namefactory-plain-name (str::cat lhs-name "_inst") nf))

         (inst    (make-vl-modinst :instname inst-name
                                   :modname modname
                                   :range nil
                                   :paramargs (vl-arguments nil nil)
                                   :portargs portargs
                                   ;; atts?
                                   :loc loc)))

        (mv t warnings reg inst addmods
            (list rhs-temp-decl)
            (list rhs-temp-assign)
            nf)))

  (defmvtypes vl-always-infer-latch/flop
    (booleanp   ; successp
     nil        ; warnings
     nil        ; reg
     nil        ; inst
     true-listp ; addmods
     true-listp ; decls
     true-listp ; assigns
     nil        ; nf
     ))

  (local (in-theory (enable vl-always-infer-latch/flop)))

  (defthm vl-warninglist-p-of-vl-always-infer-latch/flop
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-always-infer-latch/flop x mod warnings nf)))))

  (defthm vl-always-infer-latch/flop-basics
    (implies (and (force (vl-always-p x))
                  (force (vl-module-p mod))
                  (force (vl-namefactory-p nf)))
             (and
              ;; reg
              (equal
               (vl-regdecl-p (mv-nth 2 (vl-always-infer-latch/flop x mod warnings nf)))
               (if (mv-nth 0 (vl-always-infer-latch/flop x mod warnings nf)) t nil))
              ;; inst
              (equal
               (vl-modinst-p (mv-nth 3 (vl-always-infer-latch/flop x mod warnings nf)))
               (if (mv-nth 0 (vl-always-infer-latch/flop x mod warnings nf)) t nil))
              ;; addmods
              (vl-modulelist-p
               (mv-nth 4 (vl-always-infer-latch/flop x mod warnings nf)))
              ;; decls
              (vl-netdecllist-p
               (mv-nth 5 (vl-always-infer-latch/flop x mod warnings nf)))
              ;; assigns
              (vl-assignlist-p
               (mv-nth 6 (vl-always-infer-latch/flop x mod warnings nf)))
              ;; nf
              (vl-namefactory-p
               (mv-nth 7 (vl-always-infer-latch/flop x mod warnings nf)))))))



(defsection vl-alwayslist-infer-latches/flops
  :parents (flop-inference latch-inference)
  :short "Try to infer latches and flops from a list of <tt>always</tt>
blocks."

  :long "<p><b>Signature:</b> @(call vl-alwayslist-infer-latches/flops) returns
<tt>(mv warnings alwayses regs insts addmods decls assigns nf)</tt>.</p>

<p>We are given <tt>x</tt>, the list of always blocks for the module
<tt>mod</tt>, a name index for <tt>mod</tt>, and the warnings accumulator for
<tt>mod</tt>.  We try to infer flops for each <tt>always</tt> in the list, and
return:</p>

<ul>

<li><tt>alwayses</tt>, a new list of alwayses where we remove any always
 statements that have been successfully converted into flops,</li>

<li><tt>regs</tt>, a list of regdecls that need to be converted into wires,</li>

<li><tt>insts</tt>, a list of module instances that need to be added to the
module (e.g., this list will contain the explicit flop instances that represent
the deleted always blocks),</li>

<li><tt>addmods</tt>, a list of modules that need to be added to the module
list (e.g., this list might include <tt>VL_3_BIT_FLOP</tt> if we've instantiated
it.)</li>

<li><tt>decls</tt> are any new @(see vl-netdecl-p)s that need to be added
to the module,</li>

<li><tt>assigns</tt> are any new @(see vl-assign-p)s that need to be added to
the module.</li>

<li><tt>nf</tt> is the updated name factory.</li>

</ul>"

  (defund vl-alwayslist-infer-latches/flops (x mod warnings nf)
    "Returns (mv warnings alwayses regs insts addmods decls assigns nf)"
    (declare (xargs :guard (and (vl-alwayslist-p x)
                                (vl-module-p mod)
                                (vl-warninglist-p warnings)
                                (vl-namefactory-p nf))))
    (b* (((when (atom x))
          (mv warnings nil nil nil nil nil nil nf))
         ((mv successp1 warnings reg1 inst1 addmods1 decls1 assigns1 nf)
          (vl-always-infer-latch/flop (car x) mod warnings nf))
         ((mv warnings alwayses2 regs2 insts2 addmods2 decls2 assigns2 nf)
          (vl-alwayslist-infer-latches/flops (cdr x) mod warnings nf)))
        (if successp1
            (mv warnings
                alwayses2
                (cons reg1 regs2)
                (cons inst1 insts2)
                (append addmods1 addmods2)
                (append decls1 decls2)
                (append assigns1 assigns2)
                nf)
          (mv warnings
              (cons (car x) alwayses2)
              regs2
              insts2
              addmods2
              decls2
              assigns2
              nf))))

  (defmvtypes vl-alwayslist-infer-latches/flops
    (nil        ; warnings
     true-listp ; alwayses
     true-listp ; regs
     true-listp ; insts
     true-listp ; addmods
     true-listp ; decls
     true-listp ; assigns
     nil        ; nf
     ))

  (local (in-theory (enable vl-alwayslist-infer-latches/flops)))

  (defthm vl-warninglist-p-of-vl-alwayslist-infer-latches/flops
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-alwayslist-infer-latches/flops x mod warnings nf)))))

  (defthm vl-alwayslist-infer-latches/flops-basics
    (implies (and (force (vl-alwayslist-p x))
                  (force (vl-module-p mod))
                  (force (vl-namefactory-p nf)))
             (let ((ret (vl-alwayslist-infer-latches/flops x mod warnings nf)))
               (and (vl-alwayslist-p  (mv-nth 1 ret))
                    (vl-regdecllist-p (mv-nth 2 ret))
                    (vl-modinstlist-p (mv-nth 3 ret))
                    (vl-modulelist-p  (mv-nth 4 ret))
                    (vl-netdecllist-p (mv-nth 5 ret))
                    (vl-assignlist-p  (mv-nth 6 ret))
                    (vl-namefactory-p (mv-nth 7 ret))
                    )))))



(defsection vl-convert-regdecllist-to-netdecllist

; We use this to turn all of the regdecls we've found into ordinary wire
; declarations so that they can be connected to the flop module.

  (defund vl-convert-regdecl-to-netdecl (x)
    (declare (xargs :guard (vl-regdecl-p x)))
    (let* ((name    (vl-regdecl->name x))
           (signedp (vl-regdecl->signedp x))
           (range   (vl-regdecl->range x))
           (arrdims (vl-regdecl->arrdims x))
           ;; (initval (vl-regdecl->initval x))  -- BOZO initval should eventually be removed
           (atts    (vl-regdecl->atts x))
           (loc     (vl-regdecl->loc x)))
      (make-vl-netdecl :name name
                       :type :vl-wire
                       :range range
                       :arrdims arrdims
                       :atts (acons "VL_CONVERTED_REG" nil atts)
                       :signedp signedp
                       :vectoredp nil ;; BOZO sensible?
                       :scalaredp nil ;; BOZO sensible?
                       :signedp signedp
                       :delay nil ;; BOZO probably not ideal
                       :cstrength nil
                       :loc loc)))

  (defthm vl-netdecl-p-of-vl-convert-regdecl-to-netdecl
    (implies (force (vl-regdecl-p x))
             (vl-netdecl-p (vl-convert-regdecl-to-netdecl x)))
    :hints(("Goal" :in-theory (enable vl-convert-regdecl-to-netdecl))))


  (defprojection vl-convert-regdecllist-to-netdecllist (x)
    (vl-convert-regdecl-to-netdecl x)
    :guard (vl-regdecllist-p x)
    :result-type vl-netdecllist-p
    :nil-preservingp nil))





(defsection vl-module-infer-latches/flops

  (defund vl-module-infer-latches/flops (x)
    "Returns (MV X-PRIME ADDMODS)"
    (declare (xargs :guard (vl-module-p x)))
    (b* (((when (vl-module->hands-offp x))
          (mv x nil))
         (alwayses (vl-module->alwayses x))

         ((unless alwayses)
          ;; Optimization.  Skip modules that don't have any always statements.
          (mv x nil))

         (warnings (vl-module->warnings x))
         (regdecls (vl-module->regdecls x))
         (netdecls (vl-module->netdecls x))
         (modinsts (vl-module->modinsts x))
         (assigns  (vl-module->assigns x))

         (nf       (vl-starting-namefactory x))

         ((mv warnings alwayses flop-regs flop-insts addmods new-decls new-assigns nf)
          (vl-alwayslist-infer-latches/flops alwayses x warnings nf))

         (-        (vl-free-namefactory nf))

         (flop-reg-names (vl-regdecllist->names flop-regs))
         (regdecls       (vl-delete-regdecls flop-reg-names regdecls))

         (flop-netdecls  (vl-convert-regdecllist-to-netdecllist flop-regs))
         (netdecls       (append new-decls flop-netdecls netdecls))

         (assigns        (append new-assigns assigns))

         ;; BOZO this might not be optimal for sorting.  Is there any simple
         ;; rule about whether the flops should come first or last?
         (modinsts       (append flop-insts modinsts))

         (x-prime (change-vl-module x
                                    :assigns assigns
                                    :alwayses alwayses
                                    :regdecls regdecls
                                    :netdecls netdecls
                                    :modinsts modinsts
                                    :warnings warnings)))
        (mv x-prime addmods)))

  (defmvtypes vl-module-infer-latches/flops (nil true-listp))

  (local (in-theory (enable vl-module-infer-latches/flops)))

  (defthm vl-module-p-of-vl-module-infer-latches/flops
    (implies (force (vl-module-p x))
             (vl-module-p (mv-nth 0 (vl-module-infer-latches/flops x)))))

  (defthm vl-module->name-of-vl-module-infer-latches/flops
    (equal (vl-module->name (mv-nth 0 (vl-module-infer-latches/flops x)))
           (vl-module->name x)))

  (defthm vl-modulelist-p-of-vl-module-infer-latches/flops
    (implies (force (vl-module-p x))
             (vl-modulelist-p (mv-nth 1 (vl-module-infer-latches/flops x))))))




(defsection vl-modulelist-infer-latches/flops-aux

  (defund vl-modulelist-infer-latches/flops-aux (x)
    "Returns (MV X-PRIME ADDMODS)"
    (declare (xargs :guard (vl-modulelist-p x)))
    (if (atom x)
        (mv nil nil)
      (b* (((mv car-prime car-addmods) (vl-module-infer-latches/flops (car x)))
           ((mv cdr-prime cdr-addmods) (vl-modulelist-infer-latches/flops-aux (cdr x))))
          (mv (cons car-prime cdr-prime)
              (append car-addmods cdr-addmods)))))

  (defmvtypes vl-modulelist-infer-latches/flops-aux
    (true-listp true-listp))

  (local (in-theory (enable vl-modulelist-infer-latches/flops-aux)))

  (defthm vl-modulelist-p-of-vl-modulelist-infer-latches/flops-aux
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 0 (vl-modulelist-infer-latches/flops-aux x)))))

  (defthm vl-modulelist->names-of-vl-modulelist-infer-latches/flops-aux
    (equal (vl-modulelist->names (mv-nth 0 (vl-modulelist-infer-latches/flops-aux x)))
           (vl-modulelist->names x)))

  (defthm vl-modulelist-p-of-vl-modulelist-infer-latches/flops-aux-2
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (mv-nth 1 (vl-modulelist-infer-latches/flops-aux x))))))


(defsection vl-modulelist-infer-latches/flops

  (defund vl-modulelist-infer-latches/flops (x)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (uniquep (vl-modulelist->names x)))))
    (b* (((mv x-prime addmods)
          (vl-modulelist-infer-latches/flops-aux x))
         (merged
          (mergesort (revappend addmods x-prime)))

         (merged-names (vl-modulelist->names merged))

         ((unless (uniquep merged-names))

; I think it's okay to cause an error in this case.  The only way we would
; destroy uniqueness is if the user has introduced a module named VL_N_BIT_FLOP
; and we're now trying to introduce a competing definition for it.  In the
; logic, we just return X, so that flop inference effectively just completely
; fails and changes no modules if any collisions would be introduced.

          (prog2$
           (er hard? 'vl-modulelist-infer-latches/flops
               "Name collision after flop inference.  Duplicate names are: ~&0."
               (duplicated-members merged-names))
           x)))

        merged))

  (local (in-theory (enable vl-modulelist-infer-latches/flops)))

  (defthm vl-modulelist-p-of-vl-modulelist-infer-latches/flops
    (implies (vl-modulelist-p x)
             (vl-modulelist-p (vl-modulelist-infer-latches/flops x))))

  (defthm unique-names-of-vl-modulelist-infer-latches/flops
    (implies (no-duplicatesp-equal (vl-modulelist->names x))
             (no-duplicatesp-equal (vl-modulelist->names (vl-modulelist-infer-latches/flops x))))))

