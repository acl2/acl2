; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "elaborate")
(include-book "../mods/svmods")
(include-book "../mods/lhs")
(include-book "../svex/lattice")
(include-book "centaur/vl/mlib/scopestack" :dir :system)
(include-book "centaur/vl/mlib/reportcard" :dir :system)
(include-book "centaur/vl/mlib/blocks" :dir :System)
(local (include-book "centaur/vl/util/arithmetic" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable cons-equal)))


(defxdoc vl-hierarchy-svex-translation
  :parents (vl-design->svex-design)
  :short "Discussion of the strategy for translating VL modules (and structs,
interfaces, etc.) to SVEX modules."

  :long "<p>This topic covers the general idea of how we translate a simplified
VL design into an SVEX module alist.  The top-level function for this is @(see
vl-design->svex-modalist), not to be confused with @(see
vl-design->svex-design) which additionally runs the series of transforms
necessary to simplify a design once loaded.</p>

<p>The input to this translation is a VL design which has had module parameters
and generate blocks resolved, expressions sized, and always blocks eliminated,
among other requirements.  (@(csee vl-design->svex-design) performs the
necessary transforms before calling @(see vl-design->svex-modalist).)</p>

<p>The crux of this translation is the translation of VL expressions to svex
expressions, which is discussed in @(see vl-expr-svex-translation).  Here we'll
discuss how these expressions are built into an SVEX module hierarchy to
mirror (and sometimes expand on) the VL hierarchy, in such a way that these
modules can then be flattened and compiled into an SVEX-based FSM (see @(see
sv::svex-compilation)).</p>

<h3>Hierarchy and Data Types</h3>

<p>The final goal of the SVEX translation and compilation process is to obtain
a FSM-style flat table of expressions that gives formulas for wire values and
next-states of stateholding elements.  To do this, one of the major challenges
is flattening a module hierarchy so that all the possible ways of referring to
a given wire collapse into one canonical one.  For example, take the following
module hierarchy:</p>
@({
  module c (input [3:0] ci, output [5:3] co);
  endmodule

  module b (input [5:2] bi, output [4:0] bo);
     c cinst (.ci(bi[5:4]+4'b10}), .co(bo[4:2]));
  endmodule

  module a ();
    wire [3:11] w;
    b binst (.bi(w[3:6]), .bo({w[9:11], w[7:8]}));
  endmodule
 })

<p>Here, the following expressions all refer to the same 3-bit chunk:</p>
@({
  w[9:11]
  binst.bo[4:2]
  binst.cinst.co[5:3]
})

<p>To make sense of these modules, if we have expressions within module @('c')
that refer to @('co'), we need to be able to reduce these, once the module
hierarchy is flattened, to refer instead to @('w') -- or vice versa; it's not
so important which direction as long as there's a canonical form.</p>

<p>The svex compilation process (see @(see sv::svex-compilation)) deals with
this by collecting a table of aliases among wires, and then using a
union-find-like algorithm to find a canonical form for each wire (see @(see
sv::alias-normalization)).  The input for this algorithm that we want to
collect for the above module hierarchy is the following list of alias
pairings:</p>

@({
  w[3:6]               <-->    binst.bi[5:2]
  {w[9:11], w[7:8]}    <-->    binst.bo[4:0]
  binst.bo[4:2]        <-->    binst.cinst.co[5:3]
 })

<p>(Note: We have one alias pair for each port connection except for the @('ci')
input of @('cinst') in b.  Because the expression connected to this port is not
simply a concatenation of other wires, we want an assignment instead.)</p>

<p>These names are shown relative to the top-level module, but initially, in
@(see vl-design->svex-modalist), aliases are associated with the module in
which they were generated and the names in those aliases are relative to that
module.  So we generate a module hierarchy something like this:</p>

@({
  module c ();
   wire [3:0] ci;
   wire [5:3] co;
  endmodule

  module b ();
   wire [5:2] bi;
   wire [4:0] bo;
   c cinst ();
   assign cinst.ci[3:0] = bi[5:4]+4'b10;
   alias bo[4:2] = cinst.co[5:3];
 endmodule

 module a ();
   wire [3:11] w;
   b binst ();
   alias w[3:6] = binst.bi[5:2];
   alias {w[9:11], w[7:8]} = binst.bo[4:0];
 endmodule
 })

<p>With this approach, relative-scoped hierarchical identifiers are dealt with
automatically by alias normalization.  This approach to aliasing lends itself
rather naturally to dealing with complex datatypes and interfaces.  We turn
structs, unions, arrays, and interfaces into \"modules\" that each have some
internal aliases to set up the relationships among the local wires.  For
example, suppose we have the following module with a struct-typed variable:</p>

@({
 typedef struct { logic [3:0] a; logic [2:4] b; } mystruct;

 module a ();
  mystruct m;
 endmodule
})

<p>This gets turned into a module hierarchy as follows:</p>

@({
 module struct##mystruct ();
    logic [6:0] __self;   // represents the whole struct
    logic [3:0] a;
    logic [2:4] b;

    alias __self[6:3] = a[3:0];
    alias __self[2:0] = b[2:4];
 endmodule

 module a ();
  // m becomes both a wire and also a module instance:
  logic [6:0] m;
  struct##mystruct m ();

  alias m = m.__self;

 endmodule
 })

<p>It wouldn't be possible in Verilog to have @('m') be the name of both a
variable and a module instance, but this is allowed in svex modules.  This
allows us to view struct indexing as just another form of relative hierarchical
reference.  Arrays become another kind of module, where the wires inside are
the array's indices.  Nested data structures become data-structure modules that
instantiate other data-structure modules.  Interfaces are treated as a
combination of struct variable and module instance.</p>

<p>This approach to array indexing also lets us deal straightforwardly with
instance arrays; see @(see vl-portinfo-instarray-nested-alias) for details.</p>

<h3>Scopes</h3>

<p>Given a module hierarchy like the examples from the previous section, it is
straightforward to flatten the hierarchy into a list of assignments and
aliases.  Then the alias normalization algorithm is able to compute canonical
forms for all aliased wires, and the names used in the assignments can be
normalized.</p>

<p>One complication of this picture is that modules may contain nested scopes,
in which variable names may shadow those in higher scopes.  For example,
generate blocks produce scopes within modules:</p>
@({
  module a ();
    wire wa;
    wire wb = 1;
    if (1) begin : myblock
       wire wb = 0;  // shadows module-global binding
       assign wa = wb;
    end

    wire wc = myblock.wb;

    // test:
    initial begin
      #10;
      $display(\"wa: %b\", wa);
      $display(\"wb: %b\", wb);
      $display(\"wc: %b\", wc);
    end

  endmodule
 })

<p>This shows the 0,1,0 as the values of @('wa, wb, wc') respectively.  In
order to support this, we want to first turn the @('myblock') scope into a
module instance inside module @('a') so that the reference to @('myblock.wb')
will work.  But we also need to resolve the reference to @('wa') inside
@('myblock') to the wire @('wa') in its containing module.  To handle this, we
use a variable naming convention that distinguishes between hierarchical names
relative to the current scope, and those relevant to some higher scope.  We'll
write this for now in pseudo-Verilog as @('$upscope(n, a.b.c)'), where
@('a.b.c') is a path that is relative to the module @('n') scopes above the
current one.  We translate module @('a') as follows:</p>

@({

 module genblock##a.myblock ();
   wire wb;
   assign wb = 0;
   assign $upscope(1, wa) = wb;
 endmodule

 module a ();
   wire wa;
   wire wb;
   wire wc;

   genblock##a.myblock myblock ();

   assign wb = 1;
   assign wc = myblock.wb;
 endmodule
 })")



(defxdoc sv::vl-moddb.lisp :parents (vl-modulelist->svex-modalist))
(local (xdoc::set-default-parents sv::vl-moddb.lisp))

(local (in-theory (disable (tau-system))))


(define svex-svar-from-name ((name stringp))
  :returns (svar sv::svar-p)
  :prepwork ((local (in-theory (enable sv::name-p))))
  (sv::make-svar
   :name (sv::make-address
          :path (sv::make-path-wire :name (string-fix name))))
  ///
  (defret svar-addr-p-of-svex-svar-from-name
    (sv::svar-addr-p svar)
    :hints(("Goal" :in-theory (enable sv::svar-addr-p)))))

(define svex-var-from-name ((name stringp))
  :returns (svex sv::svex-p)
  :prepwork ((local (in-theory (enable sv::name-p))))
  (sv::make-svex-var
   :name (svex-svar-from-name name))
  ///
  (defret svarlist-addr-p-of-svex-var-from-name
    (sv::svarlist-addr-p (sv::svex-vars svex))
    :hints(("Goal" :in-theory (enable sv::svar-addr-p)))))

(define svex-lhs-from-name ((name stringp)
                            &key
                            ((width posp) '1)
                            ((rsh natp) '0))
  :returns (lhs sv::lhs-p)
  :prepwork ((local (in-theory (enable sv::name-p))))
  (list (sv::make-lhrange
         :w width
         :atom (sv::make-lhatom-var
                :name (svex-svar-from-name name)
                :rsh rsh)))
  ///

  (in-theory (disable (:t svex-lhs-from-name)))

  (defret svarlist-addr-p-of-svex-lhs-from-name
    (sv::svarlist-addr-p (sv::lhs-vars lhs))
    :hints(("Goal" :in-theory (enable sv::svar-addr-p sv::lhatom-vars)))))

;; (define vl-cap-lhsexpr ((x vl-expr-p))
;;   :returns (mv errp (xx (implies (and (not errp) (vl-expr-p x))
;;                                  (and (vl-expr-p xx)
;;                                       (vl-expr-welltyped-p xx)))
;;                         :hyp :guard
;;                         :hints(("Goal" :in-theory (enable vl-expr-welltyped-p)))))
;;   (b* (((unless (vl-expr-welltyped-p x))
;;         (mv "Expr not well typed" nil))
;;        ((unless (eq (vl-expr->finaltype x) :vl-unsigned))
;;         (mv "Expr not unsigned" nil))
;;        ((unless (vl-expr->finalwidth x))
;;         (mv "Expr not sized" nil)))
;;     (mv nil (make-vl-nonatom
;;              :op :vl-concat
;;              :args (list |*sized-1'bz*| x)
;;              :finalwidth (+ 1 (vl-expr->finalwidth x))
;;              :finaltype :vl-unsigned))))




;; (define vl-expr->svex-top ((x vl-expr-p))
;;   :returns (mv errmsg
;;                (xsvex (implies (not errmsg)
;;                                (sv::svex-p xsvex))))
;;   (b* (((unless (vl-expr-welltyped-p x))
;;         (mv "Expr not welltyped" nil))
;;        ((unless (vl-expr->finalwidth x))
;;         (mv "Expr not sized" nil))
;;        (svex (vl-expr->svex x)))
;;     (mv nil (sv::svex-call 'sv::concat
;;                              (list (svex-int (vl-expr->finalwidth x))
;;                                    svex (sv::svex-quote (sv::4vec-z)))))))


;; (defthm vl-expr-welltyped-p-of-idexpr
;;   (implies (and (posp finalwidth) finaltype)
;;            (vl-expr-welltyped-p (vl-idexpr name finalwidth finaltype)))
;;   :hints(("Goal" :in-theory (enable vl-idexpr vl-expr-welltyped-p vl-atom-welltyped-p
;;                                     tag-reasoning))))





(define vl-vardecllist-sizes ((x vl-vardecllist-p)
                              (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (sizes (maybe-nat-list-p sizes)))
  :short "Finds the packed size in bits for each variable in the list."
  (b* ((warnings nil)
       ((when (atom x)) (mv (ok) nil))
       ((vl-vardecl x1) (vl-vardecl-fix (car x)))
       ((mv err type) (vl-datatype-usertype-resolve x1.type ss))
       ((mv warnings size)
        (b* (((when err)
              (mv (fatal :type :vl-vardecl-unsizable
                         :msg "~a0: type ~a1 was not resolved: ~@2"
                         :args (list x1 x1.type err))
                  nil))
             ((mv err size) (vl-datatype-size type))
             (warnings (if (or err (not size))
                           (fatal :type :vl-vardecl-unsizable
                                  :msg "~a0: type ~a1 can't be sized: ~@2"
                                  :args (list x1 x1.type
                                              (or err "non-bitvector type")))
                         (ok))))
          (mv warnings size)))
       ((wmv warnings rest) (vl-vardecllist-sizes (cdr x) ss)))
    (mv warnings
        (cons size rest)))
  ///
  (defret true-listp-of-vl-vardecllist-sizes
    (true-listp sizes)
    :rule-classes :type-prescription))

#||
(trace$ #!vl (vl-interface-size-fn
              :entry (list 'vl-interface-size
                           (vl-interface->name x))
              :exit (list 'vl-interface-size
                          (with-local-ps (vl-print-warnings-with-header (car values)))
                          (cadr values))))

||#


(define vl-interface-size ((x vl-interface-p)
                           (ss vl-scopestack-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (size (implies (not err) (natp size)) :rule-classes :type-prescription))
  (b* ((x (vl-interface-fix x))
       ((mv err1 type) (vl-interface-mocktype x ss))
       ((unless (vl-datatype-resolved-p type))
        (mv (vmsg "Mocktype of interface ~a0 not resolved: ~a1"
                  x type)
            nil))
       ((mv err2 size) (vl-datatype-size type)))
    (mv (vmsg-concat err1
                     (or err2
                         (and (not size)
                              (vmsg "Mocktype of interface ~a0 couldn't be sized: ~a1"
                                    x type))))
        size)))
       
      
  

  
(define vlsv-aggregate-subalias ((name sv::name-p)
                                  (width posp))
  :returns (alias sv::lhspairs-p)
  (b* ((var (sv::make-simple-svar name))
       (lhs (sv::make-simple-lhs :width width :var var))
       (selfvar (sv::make-scoped-svar name :self))
       (selflhs (sv::make-simple-lhs :width width :var selfvar)))
    (list (cons lhs selflhs)))
  ///
  (defret vlsv-aggregate-subalias-vars
    (sv::svarlist-addr-p (sv::lhspairs-vars alias))
    :hints(("Goal" :in-theory (enable sv::lhspairs-vars)))))

(define vlsv-aggregate-superalias ((name sv::name-p)
                                   (width posp)
                                   (lsb natp))
  :returns (alias sv::lhspairs-p)
  (b* ((var (sv::make-simple-svar name))
       (lhs (sv::make-simple-lhs :width width :var var))
       (outervar (sv::make-simple-svar :self))
       (outerlhs (sv::make-simple-lhs :width width :var outervar :rsh lsb)))
    (list (cons lhs outerlhs)))
  ///
  (defret vlsv-aggregate-superalias-vars
    (sv::svarlist-addr-p (sv::lhspairs-vars alias))
    :hints(("Goal" :in-theory (enable sv::lhspairs-vars)))))

(define vlsv-aggregate-aliases ((name sv::name-p)
                                (width posp)
                                (lsb maybe-natp))
  :returns (aliases sv::lhspairs-p)
  (append-without-guard (vlsv-aggregate-subalias name width)
                        (and lsb (vlsv-aggregate-superalias name width lsb)))
  ///
  (defret vlsv-aggregate-aliases-vars
    (sv::svarlist-addr-p (sv::lhspairs-vars aliases))))


#||
(trace$ #!vl
        (vl-interfaceinst->svex
         :entry (list 'vl-interfaceinst->svex name ifname context (vl-scopestack->hashkey ss)
                      self-lsb arraywidth)
         :exit (b* (((list warnings wires aliases width single-width) values))
                 (list 'vl-interfaceinst->svex
                       (with-local-ps (vl-print-warnings warnings))
                       wires aliases width single-width))))
||#


(define vl-interfaceinst->svex ((name stringp "name of instance or interface port")
                                (ifname stringp "name of the interface")
                                (context anyp)
                                (ss vl-scopestack-p)
                                (self-lsb maybe-natp
                                          "indicates we're inside an interface
                                           and should make an additional alias
                                           to the outer block starting at
                                           self-lsb")
                                (arraywidth maybe-posp
                                            "indicates an array of instances"))
  :short "Produces the wires and aliases for an interface instantiation."
  :long "<p>This may be used either for an interface port or for an interface
instance.  It looks up the instantiated interface and computes its size,
producing a wire of that size (named after the instance or port name) and
aliases that wire to instname.self.  (An appropriate modinst should be
constructed separately.)</p>"
  :prepwork ((local (defthm name-p-when-stringp
                      (implies (stringp x)
                               (sv::name-p x))
                      :hints(("Goal" :in-theory (enable sv::name-p))))))
  :returns (mv (warnings vl-warninglist-p)
               (wires sv::wirelist-p)
               (aliases sv::lhspairs-p)
               (width natp :rule-classes :type-prescription)
               (single-width natp :rule-classes :type-prescription))
  (b* ((warnings nil)
       (ifname (string-fix ifname))
       (name   (string-fix name))
       (arraywidth (acl2::maybe-posp-fix arraywidth))
       ((mv iface i-ss) (vl-scopestack-find-definition/ss ifname ss))
       ((unless (and iface (eq (tag iface) :vl-interface)))
        (mv (fatal :type :vl-module->svex-fail
                   :msg "~a0: Interface not found: ~s1"
                   :args (list context ifname))
            nil nil 0 0))
       ((mv err size) (vl-interface-size iface i-ss))
       (warnings (vl-err->fatal err
                                :type :vl-interface->svex-fail
                                :msg "Failed to resolve the size of ~a0"
                                :args (list iface)))
       ((unless (posp size))
        (mv warnings nil nil 0 0))
       (arraysize (if arraywidth (* arraywidth size) size))
       (wire (sv::make-wire :name name
                              :width arraysize
                              :low-idx 0))
       (aliases (vlsv-aggregate-aliases name arraysize self-lsb)))
    (mv (ok) (list wire) aliases arraysize size))
  ///
  (local (in-theory (disable sv::lhs-vars-when-consp)))
  (defret vars-of-vl-interfaceinst->svex
    (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
    :hints(("goal" :in-theory (enable sv::lhspairs-vars))
           (and stable-under-simplificationp
                '(:in-theory #!sv (enable lhspairs-vars lhatom-vars))))))


(deftagsum vl-portinfo
  (:bad   ())
  (:blank ())
  ;; (:interface ((portname stringp)
  ;;              (interface vl-interface-p)
  ;;              (argindex natp)
  ;;              (conn-expr vl-expr-p)
  ;;              (port-lhs sv::lhs-p
  ;;                        "Svex expression form of the port.  Not scoped by the
  ;;                         instance name.")
  ;;              (conn-lhs sv::lhs-p)
  ;;              (size natp)))
  (:regular   ((portname stringp)
               (port-dir vl-maybe-direction-p)
               ;; (argindex natp)
               ;; (port-expr vl-expr-p)
               (conn-expr vl-expr-p)
               (port-inner-lhs
                sv::lhs-p
                "Translation of the actual port expression.  Not scoped by the
                 instance name.")
               (port-outer-lhs
                sv::lhs-p
                "If an instance array, then the expression for the port in the
                 intermediate module holding the whole instance array, otherwise
                 same as port-inner-lhs.  Not scoped by the instance name.")
               (conn-svex sv::svex-p)
               (port-size posp)
               ;; (conn-size posp)
               (replicatedp)
               (interfacep booleanp)))
   :layout :tree)

(fty::deflist vl-portinfolist :elt-type vl-portinfo)

(define vl-portinfo-vars ((x vl-portinfo-p))
  :returns (vars sv::svarlist-p)
  (vl-portinfo-case x
    ;; :interface (append (sv::lhs-vars x.port-lhs)
    ;;                    (sv::lhs-vars x.conn-lhs))
    :regular (append (sv::lhs-vars x.port-inner-lhs)
                     (sv::lhs-vars x.port-outer-lhs)
                     (sv::svex-vars x.conn-svex))
    :otherwise nil)
  ///
  (defthm svarlist-addr-p-of-vl-portinfo-vars-implies
    (implies (sv::svarlist-addr-p (vl-portinfo-vars x))
             (and ;; (implies (vl-portinfo-case x :interface)
                  ;;          (b* (((vl-portinfo-interface x)))
                  ;;            (and (sv::svarlist-addr-p (sv::lhs-vars x.port-lhs))
                  ;;                 (sv::svarlist-addr-p (sv::lhs-vars x.conn-lhs)))))
                  (implies (vl-portinfo-case x :regular)
                           (b* (((vl-portinfo-regular x)))
                             (and (sv::svarlist-addr-p (sv::lhs-vars x.port-outer-lhs))
                                  (sv::svarlist-addr-p (sv::lhs-vars x.port-inner-lhs))
                                  (sv::svarlist-addr-p (sv::svex-vars x.conn-svex))))))))
  (defret true-listp-of-vl-portinfo-vars
    (true-listp vars)
    :rule-classes :type-prescription))

(define vl-portinfolist-vars ((x vl-portinfolist-p))
  :returns (vars sv::svarlist-p)
  (if (atom x)
      nil
    (append (vl-portinfo-vars (car x))
            (vl-portinfolist-vars (cdr x)))))


(define vl-portinfo-instarray-nested-alias ((x vl-portinfo-p)
                                            (instindex integerp
                                                       "declared index of this instance")
                                            (instoffset natp
                                                        "number of instances that come after this one"))
  :guard (sv::svarlist-addr-p (vl-portinfo-vars x))
  :returns (aliases sv::lhspairs-p)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable sv::name-p))))
  :short "Produces the alias for the connection between an instance array
module's wire for a given port and some particular instance's port."
  :long "<p>As noted in @(see vl-hierarchy-svex-translation), we replace each
instance array with a single instance of new module representing the array:</p>

@({
  module b (input [3:0] bi, output [2:0] bo);
  endmodule

  module a ();
   wire [3:0] abi;
   wire [11:0] abo;
   b barray [3:0] (.bi(abi+4'b10), .bo(abo));
  endmodule
 })
<p>becomes:</p>
@({
  module b ();
    wire [3:0] bi;
    wire [2:0] bo;
  endmodule

  module arrayinst##a.binst ();
   wire [3:0] bi;
   wire [11:0] bo;

   b <3> ();
   alias <3>.bi = bi;
   alias <3>.bo = bo[11:9];

   b <2> ();
   alias <2>.bi = bi;
   alias <2>.bo = bo[8:6];

   b <1> ();
   alias <1>.bi = bi;
   alias <1>.bo = bo[5:3];

   b <0> ();
   alias <0>.bi = bi;
   alias <0>.bo = bo[2:0];
  endmodule

  module a ();

   wire [3:0] abi;
   wire [11:0] abo;

   arrayinst##a.binst binst ();
   assign binst.bi = abi+4'b10;
   alias  binst.bo = abo;
 endmodule
 })

<p>This function produces one of the aliases inside the @('arrayinst##a.binst')
module.  It always aliases the port expression of the given port with either
the whole local wire for that port (i.e., @('<3>.bi = bi')) or part of that
wire (i.e., @('<3>.bo = bo[11:9]')).  It decides this per the Verilog spec
based on the relative widths of the port expression and port connection
expression: they must either be the same (in which case the whole wire goes to
all copies of the port) or the connection expression must be N times the size
of the port expression, where N is the number of elements in the array; in this
case, the local wire for the port is the size of the whole port connection
expression and a different segment of it is passed to each port copy.</p>

<p>The other major function used to produce this intermediate module is @(see
vl-instarray-port-wiredecls), which produces (in the example) the declarations</p>
@({
   wire [3:0] bi;
   wire [11:0] bo;
 })
<p>from the new arrayinst module.</p>"
  (vl-portinfo-case x
    :regular
    (b* ((instindex (lifix instindex))
         (instoffset (lnfix instoffset))
         (shift (if x.replicatedp
                    0
                  (* x.port-size instoffset)))
         (port-inner-lhs (sv::lhs-add-namespace instindex x.port-inner-lhs))
         (port-outer-lhs (sv::lhs-concat
                          x.port-size
                          (sv::lhs-rsh shift x.port-outer-lhs)
                          nil)))
      (list (cons port-inner-lhs port-outer-lhs)))
    :otherwise nil)
  ///
  (defret vars-of-vl-portinfo-instarray-nested-alias
    (implies (sv::svarlist-addr-p (vl-portinfo-vars x))
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))
    :hints(("Goal" :in-theory (enable sv::lhspairs-vars))))

  (defret true-listp-of-vl-portinfo-instarray-nested-alias
    (true-listp aliases)
    :rule-classes :type-prescription))

(define vl-portinfolist-instarray-nested-aliases
  ((x vl-portinfolist-p)
   (instindex integerp
              "declared index of this instance")
   (instoffset natp
               "number of instances that come after this one"))
  :guard (sv::svarlist-addr-p (vl-portinfolist-vars x))
  :prepwork ((local (in-theory (enable vl-portinfolist-vars))))
  :returns (aliases sv::lhspairs-p)
  (if (atom x)
      nil
    (append (vl-portinfo-instarray-nested-alias (car x) instindex instoffset)
            (vl-portinfolist-instarray-nested-aliases (cdr x) instindex instoffset)))
  ///
  (defret vars-of-vl-portinfolist-instarray-nested-aliases
    (implies (sv::svarlist-addr-p (vl-portinfolist-vars x))
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))
    :hints(("Goal" :in-theory (enable sv::lhspairs-vars)))))




(define vl-instarray-nested-aliases
  ;; BOZO Make this work inside interfaces and with interface arrays
  ((x vl-portinfolist-p)
   (instindex integerp)
   (instoffset natp)
   (inst-incr integerp)
   (inst-modname sv::modname-p)
   (inst-ifacesize maybe-natp "indicates that we're instantiating an interface,
                               so we need :self aliases among them"))
  :guard (sv::svarlist-addr-p (vl-portinfolist-vars x))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable sv::name-p))))
  :returns (mv (aliases sv::lhspairs-p)
               (modinsts sv::modinstlist-p)
               (wires sv::wirelist-p))
  (b* ((instindex (lifix instindex))
       (inst-modname (sv::modname-fix inst-modname))
       (inst-ifacesize (maybe-natp-fix inst-ifacesize))
       ((when (zp instoffset)) (mv nil nil nil))
       (aliases1
        (vl-portinfolist-instarray-nested-aliases x instindex (1- instoffset)))
       (aliases2 (and (posp inst-ifacesize)
                      (vlsv-aggregate-aliases instindex inst-ifacesize (* (1- instoffset) inst-ifacesize))))
       (wires1 (and (posp inst-ifacesize)
                   (list (sv::make-wire :name instindex :width inst-ifacesize :low-idx 0))))
       ((mv aliases3 modinsts2 wires2)
        (vl-instarray-nested-aliases
         x
         (+ (lifix instindex) (lifix inst-incr))
         (1- instoffset)
         inst-incr
         inst-modname inst-ifacesize)))
    (mv (append-without-guard aliases1 aliases2 aliases3)
        (cons (sv::make-modinst :instname instindex
                                  :modname inst-modname)
              modinsts2)
        (append-without-guard wires1 wires2)))
  ///
  (defret vars-of-vl-instarray-nested-instance-alias
    (implies (sv::svarlist-addr-p (vl-portinfolist-vars x))
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))
    :hints(("Goal" :in-theory (enable sv::lhspairs-vars)))))



(define vl-interfaceport->svex ((x vl-interfaceport-p)
                                (ss vl-scopestack-p)
                                (self-lsb maybe-natp)
                                (context-mod sv::modname-p))
  :returns (mv (warnings vl-warninglist-p)
               (wires sv::wirelist-p)
               (insts sv::modinstlist-p)
               (aliases sv::lhspairs-p)
               (modalist sv::modalist-p)
               (width natp :rule-classes :type-prescription))
  :short "Produces svex wires, insts, aliases for an interface port."
  :long "<p>Just adds a modinst to the outputs of @(see vl-interfaceinst->svex).</p>"
  :prepwork ((local (defthm modname-p-when-stringp
                      (implies (stringp x)
                               (sv::modname-p x))
                      :hints(("Goal" :in-theory (enable sv::modname-p)))))
             (local (defthm name-p-when-stringp
                      (implies (stringp x)
                               (sv::name-p x))
                      :hints(("Goal" :in-theory (enable sv::name-p)))))
             (local (defthm modname-p-when-consp
                      (implies (consp x)
                               (sv::modname-p x))
                      :hints(("Goal" :in-theory (enable sv::modname-p))))))
  :guard-debug t
  (b* (((vl-interfaceport x) (vl-interfaceport-fix x))
       (context-mod (sv::modname-fix context-mod))
       (warnings nil)
       ((unless (or (atom x.udims)
                    (and (atom (cdr x.udims))
                         (vl-packeddimension-case (car x.udims) :range)
                         (vl-range-resolved-p (Vl-packeddimension->range (car x.udims))))))
        (mv (fatal :type :vl-bad-interfaceport-array
                   :msg "Unresolved or unsized dimensions on interfaceport array: ~a0"
                   :args (list x))
            nil nil nil nil 0))
       (range (and (consp x.udims)  (vl-packeddimension->range (car x.udims))))
       (arraysize (and range (vl-range-size range)))
       ((wmv warnings wires aliases arrwidth singlewidth)
        (vl-interfaceinst->svex x.name x.ifname x ss self-lsb arraysize))
       ((unless (and arraysize (posp arrwidth)))
        (mv warnings wires (list (sv::make-modinst :instname x.name :modname x.ifname))
            aliases nil arrwidth))
       ((mv arraymod-aliases arraymod-modinsts arraymod-ifacewires)
        (vl-instarray-nested-aliases
         nil (vl-resolved->val (vl-range->msb range))
         arraysize
         (if (vl-range-revp range) 1 -1)
         x.ifname singlewidth))
       (arraymod-selfwire (list (sv::make-wire :name :self :width arrwidth :low-idx 0)))
       (arraymod (sv::make-module :wires (append arraymod-selfwire
                                                 arraymod-ifacewires)
                                  :insts arraymod-modinsts
                                  :aliaspairs arraymod-aliases))
       (array-modname (list :array-ifportmod context-mod x.name))
       (insts (list (sv::make-modinst :instname x.name :modname array-modname))))
    (mv warnings wires insts aliases
        (list (cons array-modname arraymod))
        arrwidth))

  ///
  (defret vars-of-vl-interfaceport->svex
    (and (sv::svarlist-addr-p
          (sv::lhspairs-vars aliases))
         (sv::svarlist-addr-p
          (sv::modalist-vars modalist)))
    :hints(("Goal" :in-theory (enable sv::modalist-vars)))))

(define vl-interfaceports->svex ((x vl-interfaceportlist-p)
                                 (ss vl-scopestack-p)
                                 (self-lsb maybe-natp)
                                 (context-mod sv::modname-p))
  :returns (mv (warnings vl-warninglist-p)
               (wires sv::wirelist-p)
               (insts sv::modinstlist-p)
               (aliases sv::lhspairs-p)
               (modalist sv::modalist-p)
               (width natp :rule-classes :type-prescription))
  :verify-guards nil
  (b* (((when (atom x)) (mv nil nil nil nil nil 0))
       (warnings nil)
       (self-lsb (maybe-natp-fix self-lsb))
       ((wmv warnings wires2 insts2 aliases2 modalist2 width2)
        (vl-interfaceports->svex (cdr x) ss self-lsb context-mod))
       ((wmv warnings wires1 insts1 aliases1 modalist1 width1)
        (vl-interfaceport->svex (car x) ss (and self-lsb (+ width2 self-lsb)) context-mod)))
    (mv warnings
        (append-without-guard wires1 wires2)
        (append-without-guard insts1 insts2)
        (append-without-guard aliases1 aliases2)
        (append-without-guard modalist1 modalist2)
        (+ width1 width2)))
  ///
  (verify-guards vl-interfaceports->svex)
  (defret vars-of-vl-interfaceports->svex
    (and (sv::svarlist-addr-p
          (sv::lhspairs-vars aliases))
         (sv::svarlist-addr-p
          (sv::modalist-vars modalist)))))


(define vl-instarray-plainarg-type-check ((arraysize maybe-posp)
                                          (y-type vl-datatype-p)
                                          (y-expr vl-expr-p)
                                          (x-type vl-datatype-p)
                                          (x-expr vl-expr-p)
                                          (portname stringp))
  :guard (and (vl-datatype-resolved-p y-type)
              (vl-datatype-resolved-p x-type))
  :returns (mv (err (iff (vl-msg-p err) err))
               (multi "nil if all ports are connected to x as a whole, t if they're
                       all connected to separate slices")
               (x-size (implies (not err) (posp x-size)) :rule-classes :type-prescription)
               (y-size (implies (not err) (posp y-size)) :rule-classes :type-prescription))
  (b* (((mv err y-size) (vl-datatype-size y-type))
       ((when (or err (not y-size) (eql 0 y-size)))
        (mv (vmsg "Couldn't size datatype ~a0 for ~s1 port expression ~a2"
                  (vl-datatype-fix y-type) (string-fix portname) (vl-expr-fix y-expr))
            nil nil nil))
       (arraysize (acl2::maybe-posp-fix arraysize))
       ((unless arraysize)
        ;; If we don't have an instarray, then x-type and y-type are the same
        ;; and x has already been extended, if needed.
        (mv nil nil y-size y-size))
       ((mv err x-size) (vl-datatype-size x-type))
       ((when (or err (not x-size) (eql 0 x-size)))
        (mv (vmsg "Couldn't size datatype ~a0 for ~s1 port expression ~a2"
                  (vl-datatype-fix x-type) (string-fix portname) (vl-expr-fix x-expr))
            nil nil nil))
       (y-packed (vl-datatype-packedp y-type))
       (x-packed (vl-datatype-packedp x-type))
       ((when (and x-packed y-packed))
        (b* (((when (eql x-size y-size))
              (mv nil nil x-size y-size))
             ((when (eql x-size (* arraysize y-size)))
              (mv nil t x-size y-size)))
          (mv (vmsg "Bad instancearray port connection size on port ~s0"
                     (string-fix portname))
              nil nil nil)))
       ((when x-packed)
        (mv (vmsg "Bad instancearray port connection: packed expression ~a0 ~
                   passed to unpacked port ~s1"
                  (vl-expr-fix x-expr) (string-fix portname))
            nil nil nil))
       ;; Otherwise we either need the types to be compatible or else we need
       ;; x's type to be an arraysize-element unpacked array of things
       ;; compatible with y's type.
       (compat-err (vl-check-datatype-compatibility y-type x-type :equiv))
       ((unless compat-err)
        (mv nil nil x-size y-size))
       ((mv err ?caveat x-basetype dim)
        (vl-datatype-remove-dim x-type))
       ((when err)
        (mv (vmsg "Incompatible type for connection to instancearray port ~s0"
                  (string-fix portname))
            nil nil nil))
       ((when (vl-packeddimension-case dim :unsized))
        (mv (vmsg "Incompatible type for connection to instancearray port ~s0 ~
                   (unsized dimension)" (string-fix portname))
            nil nil nil))
       (range (vl-packeddimension->range dim))
       ((when (or (not (vl-range-resolved-p range))
                  (not (eql (vl-range-size range) arraysize))))
        (mv (vmsg "Incompatible type for connection to instancearray port ~s0 ~
                   (differing dimension sizes)."
                  (string-fix portname))
            nil nil nil))
       (x-base-packed (vl-datatype-packedp x-basetype))
       ((when (and x-base-packed y-packed
                   (eql x-size (* arraysize y-size))))
        (mv nil t x-size y-size))
       (compat-err2 (vl-check-datatype-compatibility y-type x-basetype :equiv))
       ((when compat-err2)
        ;; (cw "Args: ~x0~%" (list arraysize y-type y-expr x-type x-expr portname))
        (mv (vmsg "Incompatible type for connection to instancearray port ~s0 ~
                   (different slot types)." (string-fix portname))
            nil nil nil)))
    (mv nil t x-size y-size)))








(define vl-gate-plainarg-portinfo ((x vl-plainarg-p)
                                   (portname stringp)
                                   (portdir vl-direction-p)
                                   (argindex natp)
                                   (ss vl-scopestack-p)
                                   (scopes vl-elabscopes-p
                                       "scopestack where the instance occurs")
                                   (arraysize maybe-posp))
  :short "Processes a gate instance argument into a vl-portinfo structure."
  :returns (mv (warnings vl-warninglist-p)
               (res vl-portinfo-p))
  :guard-hints (;; ("goal" :in-theory (enable (force)
                ;;                            vl-plainarg-size-check))
                (and stable-under-simplificationp
                     '(:in-theory (enable sv::name-p)))
                (and stable-under-simplificationp
                     '(:in-theory (enable sv::lhssvex-p
                                          sv::lhssvex-unbounded-p
                                          sv::svex-concat
                                          sv::4vec-index-p))))
  :guard-debug t
  :ignore-ok t
  :irrelevant-formals-ok t
  (b* (((fun (fail warnings)) (mv warnings (make-vl-portinfo-bad)))
       ((vl-plainarg x) (vl-plainarg-fix x))
       (portname (string-fix portname))
       (arraysize (acl2::maybe-posp-fix arraysize))
       ;; (ss (vl-scopestack-fix conf))
       ;; (inst-ss (vl-scopestack-fix inst-ss))
       (warnings nil)
       ((unless x.expr) (mv (ok) (make-vl-portinfo-blank)))

       ;; ((when (not y.name))
       ;;  (cw "Warning! No name for port ~x0, module ~s1~%" y inst-modname)
       ;;  (mv nil nil))
       (portexpr (vl-idexpr portname))
       (port-lhs (svex-lhs-from-name portname))
       (port-type *vl-plain-old-logic-type*)
       ((wmv warnings x-svex x-type ?x-size)
        (vl-expr-to-svex-maybe-typed
         x.expr
         (if arraysize
             nil
           port-type)
         ss scopes :compattype :equiv))

       ((unless x-type) (fail warnings))
       ((mv err multi x-size ?port-size)
        (vl-instarray-plainarg-type-check
         arraysize port-type portexpr
         x-type x.expr portname))

       ((when err)
        (fail (fatal :type :vl-plainarg->svex-fail
                     :msg "~@0"
                     :args (list err))))

       (port-outer-lhs (if (and arraysize multi)
                           (svex-lhs-from-name portname :width (lposfix arraysize))
                         port-lhs))

       (xsvex (sv::svex-concat x-size
                                 (sv::svex-lhsrewrite x-svex x-size)
                                 (sv::svex-z))))
    (mv (ok)
        (make-vl-portinfo-regular
         :portname portname
         :port-dir (vl-direction-fix portdir)
         ;; :argindex argindex
         ;; :port-expr portexpr
         :conn-expr x.expr
         :port-inner-lhs port-lhs
         :port-outer-lhs port-outer-lhs
         :conn-svex xsvex
         :port-size 1
         ;; :conn-size x-size
         :replicatedp (and arraysize (not multi)))))
  ///
  (defret vars-of-vl-gate-plainarg-portinfo
    (sv::svarlist-addr-p (vl-portinfo-vars res))
    :hints(("Goal" :in-theory (enable vl-portinfo-vars sv::lhatom-vars)))))

(define vl-gate-plainarglist-portinfo ((x vl-plainarglist-p)
                                       (portnames string-listp)
                                       (portdirs vl-directionlist-p)
                                       (argindex natp)
                                       (ss vl-scopestack-p)
                                       (scopes vl-elabscopes-p)
                                       (arraysize maybe-posp))
  :guard (and (eql (len x) (len portnames))
              (eql (len x) (len portdirs)))
  :returns (mv (warnings vl-warninglist-p)
               (portinfo vl-portinfolist-p))
  (if (atom x)
      (mv nil nil)
    (b* ((warnings nil)
         ((wmv warnings portinfo1)
          (vl-gate-plainarg-portinfo
           (car x) (car portnames) (car portdirs) argindex ss scopes arraysize))
         ((wmv warnings portinfo2)
          (vl-gate-plainarglist-portinfo
           (cdr x) (cdr portnames) (cdr portdirs)
           (1+ (lnfix argindex)) ss scopes arraysize)))
      (mv warnings
          (cons portinfo1 portinfo2))))
  ///
  (defret vars-of-vl-gate-plainarglist-portinfo
    (sv::svarlist-addr-p (vl-portinfolist-vars portinfo))
    :hints(("Goal" :in-theory (enable vl-portinfolist-vars)))))


(define vl-interfaceref-to-svar ((x vl-expr-p "should be an index expr referencing an interface instance/port")
                                 (ss vl-scopestack-p))
  :returns (mv (err (iff (vl-msg-p err) err))
               (svex (and (sv::svex-p svex)
                          (sv::svarlist-addr-p (sv::svex-vars svex)))))
  (b* ((x (vl-expr-fix x)))
    (vl-expr-case x
      :vl-index
      (b* (((when (or (not (vl-partselect-case x.part :none))
                      (consp x.indices)))
            (mv (vmsg "Don't yet support referencing interface arrays: ~a0" x)
                (svex-x)))
           ((mv err hidtrace context tail)
            (vl-follow-scopeexpr x.scope ss))
           ((when err)
            (mv (vmsg "Couldn't resolve interface reference to ~a0: ~@1" x err) (svex-x)))
           (declname (vl-hidexpr-case tail :end tail.name :otherwise nil))
           ((unless declname)
            (mv (vmsg "Extra indexing on interface reference ~a0: ~a1. Modports
                       should have been removed?" x (make-vl-index
                                                     :scope (make-vl-scopeexpr-end :hid tail)))
                (svex-x)))
           ((unless (vl-hidtrace-resolved-p hidtrace))
            (mv (vmsg "Unresolved hid indices on interface reference: ~a0" x) (svex-x)))
           (path (vl-hidtrace-to-path hidtrace nil))
           ((mv err addr) (vl-scopecontext-to-addr context ss path))
           ((when err)
            (mv (vmsg "Couldn't resolve interface reference to ~a0: context was
                       problematic? ~@1" x err)
                (svex-x))))
        (mv nil (sv::make-svex-var :name (sv::address->svar addr))))
      :otherwise
      (mv (vmsg "Bad expression for interface reference: ~a0" x) (svex-x)))))
           


(define vl-plainarg-portinfo ((x vl-plainarg-p)
                              (y vl-port-p)
                              (argindex natp)
                              (ss vl-scopestack-p)
                              (scopes vl-elabscopes-p
                                  "scopestack where the instance occurs")
                              (inst-modname stringp)
                              (inst-ss vl-scopestack-p
                                       "scopestack inside the instance's module")
                              (inst-scopes vl-elabscopes-p
                                           "elabscopes inside the instance's module")
                              (arraysize maybe-posp))
  :short "Processes a module instance argument into a vl-portinfo structure."
  :returns (mv (warnings vl-warninglist-p)
               (res vl-portinfo-p))
  :guard-hints (;; ("goal" :in-theory (enable (force)
                ;;                            vl-plainarg-size-check))
                (and stable-under-simplificationp
                     '(:in-theory (enable sv::name-p)))
                (and stable-under-simplificationp
                     '(:in-theory (enable sv::lhssvex-p
                                          sv::lhssvex-unbounded-p
                                          sv::svex-concat
                                          sv::4vec-index-p))))
  :guard-debug t
  :prepwork ((local (defthm lhssvex-unbounded-p-of-svex-var-from-name
                      (sv::lhssvex-unbounded-p (svex-var-from-name name))
                      :hints(("Goal" :in-theory (enable svex-var-from-name
                                                        sv::lhssvex-unbounded-p))))))
  (b* (((fun (fail warnings)) (mv warnings (make-vl-portinfo-bad)))
       ((vl-plainarg x) (vl-plainarg-fix x))
       (y (vl-port-fix y))
       (arraysize (acl2::maybe-posp-fix arraysize))
       ;; (ss (vl-scopestack-fix conf))
       ;; (inst-ss (vl-scopestack-fix inst-ss))
       (?inst-modname (string-fix inst-modname))
       (warnings nil)
       ((unless x.expr)
        ;; It wouldn't be OK for an interface port to be blank, but we check
        ;; that in argresolve so we aren't checking it here.
        (mv (ok) (make-vl-portinfo-blank)))

       ((when (eq (tag y) :vl-interfaceport))
        (b* (((vl-interfaceport y))
             ((when (and (consp y.udims)
                         (or (consp (cdr y.udims))
                             (b* ((dim (car y.udims)))
                               (vl-packeddimension-case dim
                                 :range
                                 (not (vl-range-resolved-p dim.range))
                                 :otherwise t)))))
              (fail (fatal :type :vl-plainarg->svex-fail
                           :msg "Can't handle dimensions of interface port ~a0"
                           :args (list y))))
             ((mv err y-memb) (vl-interfaceport-mockmember y inst-ss :reclimit 100))
             ((when (or err (not (vl-datatype-resolved-p (vl-structmember->type y-memb)))))
              (fail (fatal :type :Vl-plainarg->svex-fail
                           :msg "Couldn't get mocktype for interfaceport ~a0: ~@1"
                           :args (list y err))))
             (y-type (vl-structmember->type y-memb))

             ((unless (vl-expr-case x.expr :vl-index))
              (fail (fatal :type :vl-plainarg->svex-fail
                           :msg "Interface port ~a0 connected to non-index arg ~a1"
                           :args (list y x))))

             ((wmv warnings x-svex x-type) (vl-index-expr-to-svex x.expr ss scopes))
             ((unless (and x-type (vl-datatype-resolved-p x-type)))
              (fail (fatal :type :Vl-plainarg->svex-fail
                           :msg "Couldn't resolve type for interfaceport argument .~s0(~a1) (type: ~a2)"
                           :args (list y.name x.expr x-type))))
             (y-expr (make-vl-index :scope (vl-idscope y.name)
                                    :part (if (consp y.udims)
                                              (vl-range->partselect
                                               (vl-packeddimension->range (car y.udims)))
                                            (vl-partselect-none))))

             ((mv type-err multi x-size y-size)
              ;; bozo -- this probably isn't all the right checks yet
              (vl-instarray-plainarg-type-check
               arraysize y-type y-expr x-type x.expr y.name))

             (type-err (or type-err
                           (and (not arraysize)
                                (vl-check-datatype-compatibility x-type y-type :equiv))))

             ((when type-err)
              (fail (fatal :type :vl-plainarg->svex-fail
                           :msg "Types mismatch on interfaceport argument .~s0(~a1): ~@2"
                           :args (list y.name x.expr type-err))))

             (y-lhs (svex-lhs-from-name y.name :width y-size))

             (y-outer-lhs (if (and arraysize multi)
                              (svex-lhs-from-name y.name :width (* y-size (lposfix arraysize)))
                            y-lhs))

             (xsvex (sv::svex-concat x-size
                                     (sv::svex-lhsrewrite x-svex x-size)
                                     (sv::svex-z))))
          (mv (ok)
              (make-vl-portinfo-regular
               :portname y.name
               :port-dir nil
               ;; :argindex argindex
               ;; :port-expr y-expr
               :conn-expr x.expr
               :port-inner-lhs y-lhs
               :port-outer-lhs y-outer-lhs
               :conn-svex xsvex
               :port-size y-size
               ;; :conn-size x-size
               :replicatedp (and arraysize (not multi))
               :interfacep t))))


          ;;    (x-lhs

          ;;    (x-udims (vl-datatype->udims x-type))
          ;;    ((when (consp (cdr x-udims)))
          ;;     (fail (fatal :type :vl-plainarg->svex-fail
          ;;                  :msg "Can't handle multidimensional interface port argument ~
          ;;                        .~s0(~a1)"
          ;;                  :args (list y.name x.expr))))
          ;;    (x-array-resolved (or (atom x-udims)
          ;;                          (b* ((dim (car x-udims)))
          ;;                            (vl-packeddimension-case dim
          ;;                              :range
          ;;                              (vl-range-resolved-p dim.range)
          ;;                              :otherwise nil))))
          ;;    ((unless x-array-resolved)
          ;;     (fail (fatal :type :vl-plainarg->svex-fail
          ;;                  :msg "Bad array dimension on interface port argument ~
          ;;                        .~s0(~a1) (type: ~a2)"
          ;;                  :args (list y.name x.expr
          ;;                              (make-vl-structmember
          ;;                               :name "xx"
          ;;                               :type x-type)))))

          ;;    (x-range-size (and (consp x-udims)
          ;;                       (vl-range->size (vl-packeddimension->range (car x-udims)))))

          ;;    ;; At this point we have:
          ;;    ;;   arraysize -- number of modinsts
          ;;    ;;   x-range-size -- 

          ;;    ((when (and arraysize
          ;;                (atom (vl-datatype->udims x-type))))
          ;;     (fail (fatal :type :vl-plainarg->svex-fail
          ;;                  :msg ""
          ;;                  :args (list y.name x.expr)))
             

          ;;    ((mv interface if-ss) (vl-scopestack-find-definition/ss y.ifname ss))
          ;;    ((unless (and interface (vl-scopedef-interface-p interface)))
          ;;     (fail (fatal :type :vl-plainarg->svex-fail
          ;;               :msg "Interface ~s0 for interface port ~s1 not found"
          ;;               :args (list y.ifname y.name))))
             


          ;;    ((mv err xvar) (vl-interfaceref-to-svar x.expr ss))
          ;;    ((when err)
          ;;     (fail (fatal :type :vl-plainarg->svex-fail
          ;;                  :msg "Failed to resolve argument to interface port ~a0: ~@1"
          ;;                  :args (list y err))))
          ;;    (yvar (svex-var-from-name y.name))
          ;;    ;; ((mv ok yvar) (svex-add-namespace instname yvar))
          ;;    ;; (- (or ok (raise "Programming error: malformed variable in expression ~x0"
          ;;    ;;                  yvar)))
          ;;    ((wmv warnings ifwidth) (vl-interface-size interface if-ss))
          ;;    (warnings (append-without-guard warnings (ok)))
          ;;    (xsvex (sv::svex-concat ifwidth xvar (sv::svex-z)))
          ;;    (ysvex (sv::Svex-concat ifwidth yvar (sv::svex-z)))
          ;;    (xlhs (sv::svex->lhs xsvex))
          ;;    (ylhs (sv::svex->lhs ysvex)))
          ;; (mv (ok)
          ;;     (make-vl-portinfo-interface
          ;;      :portname y.name
          ;;      :interface interface
          ;;      :argindex argindex
          ;;      :conn-expr x.expr
          ;;      :port-lhs ylhs
          ;;      :conn-lhs xlhs
          ;;      :size ifwidth))))

       ;; ((when (not y.name))
       ;;  (cw "Warning! No name for port ~x0, module ~s1~%" y inst-modname)
       ;;  (mv nil nil))
       ((vl-regularport y))
       (y.name (or y.name (cat "unnamed_port_" (natstr argindex))))
       ((unless y.expr)
        (mv (ok) (make-vl-portinfo-blank)))
       ((wmv warnings y-lhs y-type)
        (vl-expr-to-svex-lhs y.expr inst-ss inst-scopes))
       ((unless y-type)
        ;; already warned
        (fail warnings))
       ((wmv warnings x-svex x-type ?x-size)
        (vl-expr-to-svex-maybe-typed
         x.expr (if arraysize nil y-type) ss scopes :compattype :assign))

       ((unless x-type) (fail warnings))
       ((mv err ?multi ?x-size ?y-size)
        (vl-instarray-plainarg-type-check
         arraysize y-type y.expr
         x-type x.expr y.name))

       ((when err)
        (fail (fatal :type :vl-plainarg->svex-fail
                     :msg "~@0"
                     :args (list err))))

       (y-outer-lhs (if arraysize
                        (svex-lhs-from-name y.name :width (if multi (* y-size (lposfix arraysize)) y-size))
                      y-lhs))

       ;; This seems wrong, what is supposed to happen if the port connection
       ;; is narrower than the port expression?
       ;; ;; truncate y to the width of x if necessary
       ;; (y-lhs (if (and (not arraysize)
       ;;                 (< xwidth ywidth))
       ;;            (sv::lhs-concat xwidth y-lhs nil)
       ;;          y-lhs))
       (xsvex (sv::svex-concat x-size
                                 (sv::svex-lhsrewrite x-svex x-size)
                                 (sv::svex-z))))
    (mv (ok)
        (make-vl-portinfo-regular
         :portname y.name
         :port-dir x.dir
         ;; :argindex argindex
         ;; :port-expr y.expr
         :conn-expr x.expr
         :port-inner-lhs y-lhs
         :port-outer-lhs y-outer-lhs
         :conn-svex xsvex
         :port-size y-size
         ;; :conn-size x-size
         :replicatedp (and arraysize (not multi)))))
  ///
  (defret vars-of-vl-plainarg-portinfo
    (sv::svarlist-addr-p (vl-portinfo-vars res))
    :hints(("Goal" :in-theory (enable vl-portinfo-vars sv::lhatom-vars)))))

(define vl-plainarglist-portinfo ((x vl-plainarglist-p)
                                  (y vl-portlist-p)
                                  (argindex natp)
                                  (ss vl-scopestack-p)
                                  (scopes vl-elabscopes-p)
                                  (inst-modname stringp)
                                  (inst-ss vl-scopestack-p)
                                  (inst-scopes vl-elabscopes-p)
                                  (arraysize maybe-posp))
  :guard (eql (len x) (len y))
  :returns (mv (warnings vl-warninglist-p)
               (portinfo vl-portinfolist-p))
  (if (atom x)
      (mv nil nil)
    (b* ((warnings nil)
         ((wmv warnings portinfo1)
          (vl-plainarg-portinfo
           (car x) (car y) argindex ss scopes inst-modname inst-ss inst-scopes arraysize))
         ((wmv warnings portinfo2)
          (vl-plainarglist-portinfo
           (cdr x) (cdr y) (1+ (lnfix argindex)) ss scopes inst-modname inst-ss inst-scopes arraysize)))
      (mv warnings
          (cons portinfo1 portinfo2))))
  ///
  (defret vars-of-vl-plainarglist-portinfo
    (sv::svarlist-addr-p (vl-portinfolist-vars portinfo))
    :hints(("Goal" :in-theory (enable vl-portinfolist-vars)))))



(define vl-portinfo-to-svex-assign-or-alias ((x vl-portinfo-p)
                                             (instname stringp))

  :returns (mv (warnings vl-warninglist-p)
               (assigns sv::assigns-p)
               (aliases sv::lhspairs-p))
  :guard (sv::svarlist-addr-p (vl-portinfo-vars x))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable sv::name-p))))
  (b* ((instname (string-fix instname))
       (warnings nil))
    (vl-portinfo-case x
      :bad (mv (ok) nil nil)
      :blank (mv (ok) nil nil )
      ;; :interface
      ;; (b* ((port-lhs-scoped (sv::lhs-add-namespace instname x.port-lhs)))
      ;;   (mv (ok) nil (list (cons port-lhs-scoped x.conn-lhs))))
      :regular
      (b* ((port-lhs-scoped (sv::lhs-add-namespace instname x.port-outer-lhs))
           ((when (sv::lhssvex-p x.conn-svex))
            (mv (ok)
                nil
                (list (cons port-lhs-scoped (sv::svex->lhs x.conn-svex)))))
           ((when x.interfacep)
            (mv (fatal :type :vl-interfaceport-bad-connection
                       :msg "Non-LHS connection on interfaceport: .~s0(~a1)"
                       :args (list x.portname x.conn-expr))
                nil nil)))

        (mv (if (eq x.port-dir :vl-output)
                (warn :type :vl-port-direction-mismatch
                      :msg  "Non-LHS expression ~a1 on output port ~s0"
                      :args (list x.portname x.conn-expr))
              (ok))
            (list (cons port-lhs-scoped (sv::make-driver :value x.conn-svex)))
            nil))))
  ///
  (defret var-of-vl-portinfo-to-svex-assign-or-alias
    (implies (sv::svarlist-addr-p (vl-portinfo-vars x))
             (and (sv::svarlist-addr-p (sv::assigns-vars assigns))
                  (sv::svarlist-addr-p (sv::lhspairs-vars aliases))))
    :hints(("Goal" :in-theory (enable sv::assigns-vars sv::lhspairs-vars))))
  (defmvtypes vl-portinfo-to-svex-assign-or-alias (nil true-listp true-listp)))

(define vl-portinfolist-to-svex-assigns/aliases ((x vl-portinfolist-p)
                                                  (instname stringp))
  :guard (sv::svarlist-addr-p (vl-portinfolist-vars x))
  :guard-hints (("goal" :in-theory (enable vl-portinfolist-vars)))
  :returns (mv (warnings vl-warninglist-p)
               (assigns sv::assigns-p)
               (aliases sv::lhspairs-p))
  (b* ((warnings nil)
       ((when (atom x)) (mv (ok) nil nil))
       ((wmv warnings assigns1 aliases1)
        (vl-portinfo-to-svex-assign-or-alias (car x) instname))
       ((wmv warnings assigns2 aliases2)
        (vl-portinfolist-to-svex-assigns/aliases (cdr x) instname)))
    (mv warnings
        (append assigns1 assigns2)
        (append aliases1 aliases2)))
  ///
  (defret var-of-vl-portinfolist-to-svex-assigns/aliases
    (implies (sv::svarlist-addr-p (vl-portinfolist-vars x))
             (and (sv::svarlist-addr-p (sv::assigns-vars assigns))
                  (sv::svarlist-addr-p (sv::lhspairs-vars aliases))))
    :hints(("Goal" :in-theory (enable sv::assigns-vars sv::lhspairs-vars
                                      vl-portinfolist-vars))))
  (defmvtypes vl-portinfolist-to-svex-assigns/aliases (nil true-listp true-listp)))




       ;;   (connection-svex
       ;;    (sv::svex-concat
       ;;     port-size
       ;;     (sv::svex-rsh shift
       ;;                     (sv::make-svex-var :name (sv::address->svar
       ;;                                                 (sv::make-address
       ;;                                                  :path (sv::make-path-wire :name y.name)))))
       ;;     (sv::svex-z)))
       ;; (connection-lhsp (sv::lhssvex-p connection-svex))
       ;; ((unless connection-lhsp)
       ;;  (mv (warn :type :vl-plainarg->svex-fail
       ;;            :msg "non-LHS port connection for port ~s0, mod ~s1:~%"
       ;;            :args (list y.name inst-modname))
       ;;      nil))
       ;; (connection-lhs (sv::svex->lhs connection-svex))


(define vl-instarray-port-wiredecls ((x vl-portinfo-p)
                                     (arraysize posp))
  :prepwork ((local (in-theory (enable sv::name-p))))
  :returns (wires sv::wirelist-p)
  ;; :guard (sv::svarlist-addr-p (vl-portinfo-vars x))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable sv::name-p))))
  :short "Produces the wire declaration for the wire of an instance array module
          that consolidates all occurrences of a particular port."
  :long "<p>See @(see vl-portinfo-instarray-nested-alias) for more
details on dealing with modinst arrays.</p>"
  (vl-portinfo-case x
    :regular
    (b* ((xwidth (if x.replicatedp x.port-size (* x.port-size (acl2::lposfix arraysize))))
         (portwire (sv::make-wire :name x.portname
                                    :width xwidth
                                    :low-idx 0)))
      (list portwire))
    :otherwise nil)
  ///
  (defret true-listp-of-vl-instarray-port-wiredecls
    (true-listp wires)
    :rule-classes :type-prescription))

(define vl-instarray-portlist-wiredecls ((x vl-portinfolist-p)
                                         (arraysize posp))
  :returns (wires sv::wirelist-p)
  (if (atom x)
      nil
    (append (vl-instarray-port-wiredecls (car x) arraysize)
            (vl-instarray-portlist-wiredecls (cdr x) arraysize))))




(define vl-modinst->svex-assigns/aliases ((x vl-modinst-p)
                                          (ss vl-scopestack-p)
                                          (scopes vl-elabscopes-p)
                                          (wires   sv::wirelist-p)
                                          (assigns sv::assigns-p)
                                          (aliases sv::lhspairs-p)
                                          (context-mod sv::modname-p)
                                          (self-lsb maybe-natp))
  :returns (mv (warnings vl-warninglist-p)
               (wires   sv::wirelist-p "Wires representing instantiated interfaces")
               (assigns1 sv::assigns-p  "Assignments for nontrivial port expressions")
               (aliases1 sv::lhspairs-p "Aliases for trivial port expressions")
               (width    natp :rule-classes :type-prescription "Width if this is an interface instance")
               (modinsts sv::modinstlist-p "The instance created")
               (modalist sv::modalist-p    "Possibly a new module implementing an instance array."))
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (or (vl-module-p x)
                                   (vl-interface-p x))
                               (vl-scope-p x))))
             (local (in-theory (enable sv::modname-p sv::name-p))))
  :short "Produces all the new svex module components associated with a VL module
          instance or instance array."
  :long "<p>See @(see vl-hierarchy-svex-translation) for more information on
how VL module instances are translated.</p>"

  (b* (((vl-modinst x) (vl-modinst-fix x))
       (wires (sv::wirelist-fix wires))
       (assigns (sv::assigns-fix assigns))
       (aliases (sv::lhspairs-fix aliases))
       (context-mod (sv::modname-fix context-mod))
       (warnings nil)

       ((when (eq (vl-arguments-kind x.portargs) :vl-arguments-named))
        (mv (fatal :type :vl-modinst->svex-fail
                   :msg "~a0: Unexpectedly had named arglist"
                   :args (list x))
            wires assigns aliases 0
            nil nil))
       (x.plainargs (vl-arguments->args x.portargs))
       ((mv inst-mod inst-ss) (vl-scopestack-find-definition/ss x.modname ss))
       ((unless (and inst-mod
                     (or (eq (tag inst-mod) :vl-module)
                         (eq (tag inst-mod) :vl-interface))))
        (mv (fatal :type :vl-modinst->svex-fail
                  :msg "~a0: Unknown module ~s1"
                  :args (list x x.modname))
            wires assigns aliases 0
            nil nil))
       (inst-ss (vl-scopestack-push inst-mod inst-ss))
       (inst-scopes (vl-elabscopes-push-scope inst-mod 
                                              (vl-elabscopes-root scopes)))
       (i.ports (if (eq (tag inst-mod) :vl-module)
                    (vl-module->ports inst-mod)
                  (vl-interface->ports inst-mod)))
       (inst-modname (if (eq (tag inst-mod) :vl-module)
                         (vl-module->name inst-mod)
                       (vl-interface->name inst-mod)))
       ((unless (eql (len i.ports) (len x.plainargs)))
        (mv (fatal :type :vl-modinst->svex-fail
                  :msg "~a0: Mismatched portlist length"
                  :args (list x))
            wires assigns aliases 0
            nil nil))
       ((unless (vl-maybe-range-resolved-p x.range))
        (mv (fatal :type :vl-modinst->svex-fail
                  :msg "~a0: Unresolved instance array range"
                  :args (list x))
            wires assigns aliases 0 nil nil))
       (arraywidth (and x.range (vl-range-size x.range)))

       ((unless x.instname)
        (mv (fatal :type :Vl-modinst->svex-fail
                   :msg "~a0: Unnamed module/interface instance not allowed"
                   :args (list x))
            wires assigns aliases 0 nil nil))

       ((wmv warnings portinfo :ctx x)
        (vl-plainarglist-portinfo
         x.plainargs i.ports 0 ss scopes inst-modname inst-ss inst-scopes arraywidth))

       ((wmv warnings portassigns portaliases :ctx x)
        (vl-portinfolist-to-svex-assigns/aliases portinfo x.instname))
       (assigns (append-without-guard portassigns assigns))
       (aliases (append-without-guard portaliases aliases))

       ((wmv warnings ifwires ifaliases arrwidth iface-width :ctx x)
        (if (eq (tag inst-mod) :vl-interface)
            (vl-interfaceinst->svex x.instname x.modname x ss self-lsb arraywidth)
          (mv nil nil nil 0 nil)))
       (wires   (append-without-guard ifwires wires))
       (aliases (append-without-guard ifaliases aliases))

       ((unless arraywidth)
        ;; no instance array -> we're done.
        (mv (vl-warninglist-add-ctx warnings x) wires assigns aliases arrwidth
            (list (sv::make-modinst :instname x.instname :modname x.modname))
            nil))

       (array-modname (list :arraymod context-mod x.instname))

       (modinst (sv::make-modinst :instname x.instname
                                    :modname array-modname))

       (arraymod-wiredecls (vl-instarray-portlist-wiredecls portinfo arraywidth))
       ((mv arraymod-aliases arraymod-modinsts arraymod-ifacewires)
        (vl-instarray-nested-aliases
         portinfo
         (vl-range-msbidx x.range)
         arraywidth
         (if (vl-range-revp x.range) 1 -1)
         inst-modname iface-width))

       (arraymod-selfwire (and (eq (tag inst-mod) :vl-interface)
                               (posp arrwidth)
                               (list (sv::make-wire :name :self :width arrwidth :low-idx 0))))

       (arraymod (sv::make-module :wires (append arraymod-selfwire
                                                 arraymod-wiredecls
                                                 arraymod-ifacewires)
                                    :insts arraymod-modinsts
                                    :aliaspairs arraymod-aliases)))

    (mv warnings wires assigns aliases arrwidth
        (list modinst)
        (list (cons array-modname arraymod))))
  ///
  (defret vars-of-vl-modinst->svex-assigns/aliases-assigns
    (implies (sv::svarlist-addr-p (sv::assigns-vars assigns))
             (sv::svarlist-addr-p (sv::assigns-vars assigns1))))
  (defret vars-of-vl-modinst->svex-assigns/aliases-aliases
    (implies (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases1))))
  (defret vars-of-vl-modinst->svex-assigns/aliases-modalist
    (sv::svarlist-addr-p (sv::modalist-vars modalist))
    :hints(("Goal" :in-theory (enable sv::modalist-vars
                                      sv::module-vars)))))





(define vl-modinstlist->svex-assigns/aliases ((x vl-modinstlist-p)
                                              (ss vl-scopestack-p)
                                              (scopes vl-elabscopes-p)
                                              (wires   sv::wirelist-p)
                                              (assigns sv::assigns-p)
                                              (aliases sv::lhspairs-p)
                                              (context-mod sv::modname-p)
                                              (self-lsb maybe-natp))
  :short "Collects svex module components for a list of module/interface instances,
          by collecting results from @(see vl-modinst->svex-assigns/aliases)."
  :returns (mv (warnings vl-warninglist-p)
               (wires1   sv::wirelist-p)
               (assigns1 sv::assigns-p)
               (aliases1 sv::lhspairs-p)
               (width    natp :rule-classes :type-prescription)
               (modinsts sv::modinstlist-p)
               (modalist sv::modalist-p))
  :verify-guards nil
  (b* ((warnings nil)
       ((when (atom x))
        (mv nil
            (sv::wirelist-fix wires)
            (sv::assigns-fix assigns)
            (sv::lhspairs-fix aliases) 0
            nil nil))
       (self-lsb (maybe-natp-fix self-lsb))
       ((wmv warnings wires assigns aliases width2 insts2 modalist2)
        (vl-modinstlist->svex-assigns/aliases (cdr x) ss scopes wires assigns aliases context-mod self-lsb))
       ((wmv warnings wires assigns aliases width1 insts1 modalist1)
        (vl-modinst->svex-assigns/aliases (car x) ss scopes wires assigns aliases context-mod (and self-lsb (+ self-lsb width2)))))
    (mv warnings
        wires assigns aliases
        (+ width1 width2)
        (append-without-guard insts1 insts2)
        (append-without-guard modalist1 modalist2)))
  ///
  (verify-guards vl-modinstlist->svex-assigns/aliases)
  (defret vars-of-vl-modinstlist->svex-assigns/aliases-assigns
    (implies (sv::svarlist-addr-p (sv::assigns-vars assigns))
             (sv::svarlist-addr-p (sv::assigns-vars assigns1))))
  (defret vars-of-vl-modinstlist->svex-assigns/aliases-aliases
    (implies (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases1))))
  (defret vars-of-vl-modinstlist->svex-assigns/aliases-modalist
    (sv::svarlist-addr-p (sv::modalist-vars modalist))))


(define vl-gatetypenames-count-up ((n natp)
                                   (idx natp)
                                   (basename stringp))
  :returns (names (and (string-listp names)
                       (eql (len names) (nfix n))))
  (if (zp n)
      nil
    (cons (cat basename (natstr idx))
          (vl-gatetypenames-count-up (1- n) (1+ (lnfix idx)) basename)))
  ///
  (defret vl-gatetypenames-count-up-under-iff
    (iff (vl-gatetypenames-count-up n idx basename)
         (posp n))))

(define svex-vars-from-names ((x string-listp))
  :returns (svexes sv::svexlist-p)
  (if (atom x)
      nil
    (cons (svex-var-from-name (car x))
          (svex-vars-from-names (cdr x))))
  ///
  (defret len-of-svex-vars-from-names
    (equal (len svexes) (len x)))
  (defret svex-vars-from-names-under-iff
    (iff svexes (consp x)))

  (defret svarlist-addr-p-of-svex-vars-from-names
    (sv::svarlist-addr-p (sv::svexlist-vars svexes))))

(define svex-lhses-from-names ((x string-listp))
  :returns (lhses sv::lhslist-p)
  (if (atom x)
      nil
    (cons (svex-lhs-from-name (car x))
          (svex-lhses-from-names (cdr x))))
  ///
  (defret len-of-svex-lhses-from-names
    (equal (len lhses) (len x)))

  (defret svarlist-addr-p-of-svex-lhses-from-names
    (sv::svarlist-addr-p (sv::lhslist-vars lhses))
    :hints(("Goal" :in-theory (enable sv::lhslist-vars)))))

(define svcall-join (operator
                     (args sv::svexlist-p))
  :guard (and (assoc operator sv::*svex-op-table*)
              (consp args))
  :verify-guards nil
  :returns (svex sv::svex-p)
  (if (atom (cdr args))
      (sv::svex-fix (car args))
    (sv::svex-call operator (list (car args)
                                    (svcall-join operator (cdr args)))))
  ///
  (verify-guards svcall-join)

  (defret vars-of-svcall-join
    (implies (not (member v (sv::svexlist-vars args)))
             (not (member v (sv::svex-vars svex))))))


(define vl-fixup-wide-gate-input ((in sv::svex-p))
  :returns (fixed-in sv::svex-p)
  :short "Wrap an input to a gate instance in a truncation expression."
  :long "<p>Consider an AND gate with wide inputs like this:</p>

         @({
              wire out;
              wire [1:0] in1, in2;
              and(out, in1, in2);
         })

         <p>NCV and VCS complain if the output is more than a single bit, but
         they accept wide inputs.  They also behave in different ways in this
         case: NCV does a reduction or on the input, while VCS truncates it and
         just operates on the bottom bit.</p>

         <p>Here we mimic VCS's behavior, wrapping each input expression
         @('in') into a @('(zerox 1 in)') expression.  (We warn about this
         situation elsewhere.)</p>"

  (sv::svcall sv::zerox
              (sv::make-svex-quote :val 1)
              in)
  ///
  (defret vars-of-vl-fixup-wide-gate-input
    (implies (not (member v (sv::svex-vars in)))
             (not (member v (sv::svex-vars fixed-in))))))

(defprojection vl-fixup-wide-gate-inputs ((x sv::svexlist-p))
  :returns (fixed-inputs sv::svexlist-p)
  (vl-fixup-wide-gate-input x)
  ///
  (defret vars-of-vl-fixup-wide-gate-inputs
    (implies (not (member v (sv::svexlist-vars x)))
             (not (member v (sv::svexlist-vars fixed-inputs))))))


(define vl-gatetype-names/dirs/assigns ((type vl-gatetype-p)
                                        (nargs natp))
  :returns (mv (err (iff (vl-msg-p err) err))
               (unimplemented)
               (assigns   sv::assigns-p)
               (portnames (and (string-listp portnames)
                               (implies (not err)
                                        (eql (len portnames) (nfix nargs)))))
               (portdirs (and (vl-directionlist-p portdirs)
                              (implies (not err)
                                       (eql (len portdirs) (nfix nargs))))))
  :prepwork ((local
              #!sv (defthm assigns-p-of-pairlis
                       (implies (and (lhslist-p x)
                                     (driverlist-p y)
                                     (equal (len x) (len y)))
                                (assigns-p (pairlis$ x y)))
                       :hints(("Goal" :in-theory (enable pairlis$ assigns-p))))))
  (b* ((nargs (lnfix nargs))
       (type (vl-gatetype-fix type)))
    (case type
      ((:vl-cmos :vl-rcmos)
       (mv (if (eql nargs 4) nil (vmsg "Need 4 arguments for ~x0" type))
           t nil
           '("out" "in" "ncontrol" "pcontrol")
           '(:vl-output :vl-input :vl-input :vl-input)))
      ((:vl-bufif0 :vl-bufif1 :vl-notif0 :vl-notif1
        :vl-nmos :vl-rnmos :vl-pmos :vl-rpmos)
       (mv (if (eql nargs 3) nil (vmsg "Need 3 arguments for ~x0" type))
           t nil
           '("out" "in" "control")
           '(:vl-output :vl-input :vl-input)))
      ((:vl-and :vl-nand :vl-or :vl-nor :vl-xor :vl-xnor)
       (if (< nargs 2)
           (mv (vmsg "Need 2 or more arguments for ~x0" type) nil nil nil nil)
         (b* ((ins (vl-gatetypenames-count-up (1- nargs) 1 "in"))
              (svex-ins (vl-fixup-wide-gate-inputs (svex-vars-from-names ins)))
              (assigns  (list (cons (svex-lhs-from-name "out")
                                    (if (eql (len svex-ins) 1)
                                        (sv::make-driver
                                         :value
                                         (case type
                                           ((:vl-and :vl-or :vl-xor)
                                            (sv::svcall sv::unfloat (car svex-ins)))
                                           ((:vl-nand :vl-nor :vl-xnor)
                                            (sv::svcall sv::bitnot (car svex-ins)))))
                                      (sv::make-driver
                                       :value
                                       (case type
                                         (:vl-and  (svcall-join 'sv::bitand svex-ins))
                                         (:vl-nand (sv::svcall sv::bitnot (svcall-join 'sv::bitand svex-ins)))
                                         (:vl-or   (svcall-join 'sv::bitor svex-ins))
                                         (:vl-nor  (sv::svcall sv::bitnot (svcall-join 'sv::bitor svex-ins)))
                                         (:vl-xor  (svcall-join 'sv::bitxor svex-ins))
                                         (:vl-xnor (sv::svcall sv::bitnot (svcall-join 'sv::bitxor svex-ins)))))))))
              (portnames (cons "out" ins))
              (portdirs (cons :vl-output (repeat (1- nargs) :vl-input))))
         (mv nil nil assigns portnames portdirs))))
      ((:vl-buf :vl-not)
       (if (< nargs 2)
           (mv (vmsg "Need 2 or more arguments for ~x0" type) nil nil nil nil)
         (b* ((outs (vl-gatetypenames-count-up (1- nargs) 1 "out"))
              (out-lhses (svex-lhses-from-names outs))
              (in-var (svex-var-from-name "in"))
              (assigns (pairlis$ out-lhses
                                 (repeat (1- nargs)
                                         (sv::make-driver
                                          :value
                                          (case type
                                            (:vl-buf (sv::svcall sv::unfloat in-var))
                                            (:vl-not (sv::svcall sv::bitnot in-var)))))))
              (portnames (append outs '("in")))
              (portdirs (append (repeat (1- nargs) :vl-output) '(:vl-input))))
           (mv nil nil assigns portnames portdirs))))
      ((:vl-tranif0 :vl-tranif1 :vl-rtranif0 :vl-rtranif1)
       (mv (if (eql nargs 3) nil (vmsg "Need 3 arguments for ~x0" type))
           t nil
           '("inout1" "inout2" "control")
           '(:vl-inout :vl-inout :vl-input)))
      ((:vl-tran :vl-rtran)
       (mv (if (eql nargs 2) nil (vmsg "Need 2 arguments for ~x0" type))
           t nil
           '("inout1" "inout2")
           '(:vl-inout :vl-inout)))
      ((:vl-pullup :vl-pulldown)
       (mv (if (eql nargs 1) nil (vmsg "Need 1 argument for ~x0" type))
           t nil
           '("net")
           '(:vl-inout)))
      (otherwise
       (prog2$ (impossible)
               (mv (vmsg "Impossible") nil nil nil nil)))))
  ///
  (local #!sv (defthm assigns-vars-of-pairlis$
                  (implies (and (not (member v (lhslist-vars x)))
                                (not (member v (driverlist-vars y))))
                           (not (member v (assigns-vars (pairlis$ x y)))))
                  :hints(("Goal" :in-theory (enable pairlis$
                                                    assigns-vars
                                                    driverlist-vars
                                                    lhslist-vars)))))

  (local #!sv (defthm driverlist-vars-of-repeat
                  (implies (not (member v (svex-vars (driver->value x))))
                           (not (member v (driverlist-vars (repeat n x)))))
                  :hints(("Goal" :in-theory (enable repeat driverlist-vars)))))

  (defret svarlist-addr-p-of-vl-gatetype-names/dirs/assigns
    (sv::svarlist-addr-p (sv::assigns-vars assigns))
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable sv::assigns-vars
                                      vl-fixup-wide-gate-inputs))))))

(define svex-gateinst-wirelist ((names string-listp))
  :returns (wires sv::wirelist-p)
  :prepwork ((local (in-theory (enable sv::name-p))))
  (if (atom names)
      nil
    (cons (sv::make-wire :name (string-fix (car names))
                           :width 1
                           :low-idx 0
                           :revp nil)
          (svex-gateinst-wirelist (cdr names)))))


(define vl-gate-make-svex-module ((type vl-gatetype-p)
                                  (nargs natp))
  :returns (mv (err (iff (vl-msg-p err) err))
               (portnames (and (string-listp portnames)
                               (implies (not err)
                                        (eql (len portnames) (nfix nargs)))))
               (portdirs (and (vl-directionlist-p portdirs)
                              (implies (not err)
                                       (eql (len portdirs) (nfix nargs)))))
               (svmod (implies (not err) (sv::module-p svmod))))
  (b* (((mv err unimpl assigns portnames portdirs)
        (vl-gatetype-names/dirs/assigns type nargs))
       ((when err) (mv err nil nil nil))
       (wires (svex-gateinst-wirelist portnames))
       ((when unimpl) (mv (vmsg "Unimplemented gate: ~x0" (vl-gatetype-fix type))
                          nil nil nil)))
    (mv nil portnames portdirs
        (sv::make-module :wires wires
                           :assigns assigns)))
  ///
  (defret svarlist-addr-p-of-vl-gate-make-svex-module
    (sv::svarlist-addr-p (sv::module-vars svmod))
    :hints(("Goal" :in-theory (enable sv::module-vars)))))






(define vl-gateinst->svex-assigns/aliases ((x vl-gateinst-p)
                                          (ss vl-scopestack-p)
                                          (scopes vl-elabscopes-p)
                                          (wires   sv::wirelist-p)
                                          (assigns sv::assigns-p)
                                          (aliases sv::lhspairs-p)
                                          (context-mod sv::modname-p))
  ;; BOZO deal with gatedelays and transistors someday
  :returns (mv (warnings vl-warninglist-p)
               (wires   sv::wirelist-p "Wires representing instantiated interfaces")
               (assigns1 sv::assigns-p  "Assignments for nontrivial port expressions")
               (aliases1 sv::lhspairs-p "Aliases for trivial port expressions")
               (modinsts sv::modinstlist-p "The instance created")
               (modalist sv::modalist-p    "Possibly a new module implementing an instance array."))
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (or (vl-module-p x)
                                   (vl-interface-p x))
                               (vl-scope-p x))))
             (local (in-theory (enable sv::modname-p sv::name-p))))
  :short "Produces all the new svex module components associated with a VL module
          instance or instance array."
  :long "<p>See @(see vl-hierarchy-svex-translation) for more information on
how VL module instances are translated.</p>"

  (b* (((vl-gateinst x) (vl-gateinst-fix x))
       (wires (sv::wirelist-fix wires))
       (assigns (sv::assigns-fix assigns))
       (aliases (sv::lhspairs-fix aliases))
       (context-mod (sv::modname-fix context-mod))
       (warnings nil)

       (nargs (len x.args))
       ((mv err portnames portdirs svex-mod)
        (vl-gate-make-svex-module x.type nargs))
       ((when err)
        (mv (fatal :type :vl-gateinst->svex-fail
                   :msg "~a0: bad gate instance: ~@1"
                  :args (list x err))
            wires assigns aliases
            nil nil))

       ((unless (vl-maybe-range-resolved-p x.range))
        (mv (fatal :type :vl-gateinst->svex-fail
                  :msg "~a0: Unresolved gate instance array range"
                  :args (list x))
            wires assigns aliases nil nil))
       (arraywidth (and x.range (vl-range-size x.range)))

       ((unless x.name)
        ;; This is taken care of in vl-design-addinstnames.
        (mv (fatal :type :Vl-gateinst->svex-fail
                   :msg "~a0: Unnamed gate instance not allowed"
                   :args (list x))
            wires assigns aliases nil nil))

       ((wmv warnings portinfo)
        (vl-gate-plainarglist-portinfo
         x.args portnames portdirs 0 ss scopes arraywidth))

       ((wmv warnings portassigns portaliases :ctx x)
        (vl-portinfolist-to-svex-assigns/aliases portinfo x.name))
       (assigns (append-without-guard portassigns assigns))
       (aliases (append-without-guard portaliases aliases))

       (gate-modname (hons-copy `(:gate ,x.type ,nargs)))
       (modalist (list (cons gate-modname svex-mod)))

       ((unless arraywidth)
        ;; no instance array -> we're done.
        (mv (vl-warninglist-add-ctx warnings x)
            wires assigns aliases
            (list (sv::make-modinst :instname x.name :modname gate-modname))
            modalist))

       (array-modname (list :arraymod context-mod x.name))

       (modinst (sv::make-modinst :instname x.name
                                    :modname array-modname))

       (arraymod-wiredecls (vl-instarray-portlist-wiredecls portinfo arraywidth))
       ((mv arraymod-aliases arraymod-modinsts arraymod-ifacewires)
        (vl-instarray-nested-aliases
         portinfo
         (vl-range-msbidx x.range)
         arraywidth
         (if (vl-range-revp x.range) 1 -1)
         gate-modname
         nil)) ;; not an interface

       (arraymod (sv::make-module :wires (append-without-guard arraymod-ifacewires arraymod-wiredecls)
                                    :insts arraymod-modinsts
                                    :aliaspairs arraymod-aliases)))

    (mv warnings wires assigns aliases
        (list modinst)
        (cons (cons array-modname arraymod) modalist)))
  ///
  (defret vars-of-vl-gateinst->svex-assigns/aliases-assigns
    (implies (sv::svarlist-addr-p (sv::assigns-vars assigns))
             (sv::svarlist-addr-p (sv::assigns-vars assigns1))))
  (defret vars-of-vl-gateinst->svex-assigns/aliases-aliases
    (implies (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases1))))
  (defret vars-of-vl-gateinst->svex-assigns/aliases-modalist
    (sv::svarlist-addr-p (sv::modalist-vars modalist))
    :hints(("Goal" :in-theory (enable sv::modalist-vars)))))


(define vl-gateinstlist->svex-assigns/aliases ((x vl-gateinstlist-p)
                                              (ss vl-scopestack-p)
                                              (scopes vl-elabscopes-p)
                                              (wires   sv::wirelist-p)
                                              (assigns sv::assigns-p)
                                              (aliases sv::lhspairs-p)
                                              (context-mod sv::modname-p))
  :short "Collects svex module components for a list of module/interface instances,
          by collecting results from @(see vl-gateinst->svex-assigns/aliases)."
  :returns (mv (warnings vl-warninglist-p)
               (wires1   sv::wirelist-p)
               (assigns1 sv::assigns-p)
               (aliases1 sv::lhspairs-p)
               (gateinsts sv::modinstlist-p)
               (modalist sv::modalist-p))
  (b* ((warnings nil)
       ((when (atom x))
        (mv nil
            (sv::wirelist-fix wires)
            (sv::assigns-fix assigns)
            (sv::lhspairs-fix aliases)
            nil nil))
       ((wmv warnings wires assigns aliases insts1 modalist1)
        (vl-gateinst->svex-assigns/aliases (car x) ss scopes wires assigns aliases context-mod))
       ((wmv warnings wires assigns aliases insts2 modalist2)
        (vl-gateinstlist->svex-assigns/aliases (cdr x) ss scopes wires assigns aliases context-mod)))
    (mv warnings
        wires assigns aliases
        (append-without-guard insts1 insts2)
        (append-without-guard modalist1 modalist2)))
  ///
  (defret vars-of-vl-gateinstlist->svex-assigns/aliases-assigns
    (implies (sv::svarlist-addr-p (sv::assigns-vars assigns))
             (sv::svarlist-addr-p (sv::assigns-vars assigns1))))
  (defret vars-of-vl-gateinstlist->svex-assigns/aliases-aliases
    (implies (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases1))))
  (defret vars-of-vl-gateinstlist->svex-assigns/aliases-modalist
    (sv::svarlist-addr-p (sv::modalist-vars modalist))))








(define vl-maybe-gatedelay->delay ((x vl-maybe-gatedelay-p))
  :returns (mv (warnings vl-warninglist-p)
               (del maybe-natp :rule-classes :type-prescription
                    "A natural or NIL, meaning no delay."))
  :short "Extracts a delay amount from a vl-maybe-gatedelay."
  (b* ((x (vl-maybe-gatedelay-fix x))
       ((unless (mbe :logic (vl-gatedelay-p x)
                     :exec (and x t)))
        (mv nil nil))
       ((vl-gatedelay x) x)
       (warnings nil)
       ((unless (and (vl-expr-resolved-p x.rise)
                     (vl-expr-resolved-p x.fall)
                     (or (not x.high) (vl-expr-resolved-p x.high))))
        (mv (warn :type :vl-gatedelay->svex-fail
                  :msg "gatedelay not resolved: ~x0"
                  :args (list x))
            nil))
       (val (vl-resolved->val x.rise))
       ((unless (and (eql val (vl-resolved->val x.fall))
                     (or (not x.high)
                         (eql val (vl-resolved->val x.high)))))
        (mv (warn :type :vl-gatedelay->svex-fail
                  :msg "Complex gatedelay ~x0"
                  :args (list x))
            nil)))
    (mv nil val)))

(defines vl-streaming-unpack-to-svex-assign
  :verify-guards nil
  :prepwork ((local (in-theory (disable acl2::consp-under-iff-when-true-listp
                                        sv::svarlist-addr-p-when-subsetp-equal
                                        rationalp-implies-acl2-numberp
                                        acl2::list-fix-when-len-zero
                                        acl2::true-listp-member-equal
                                        sv::svarlist-addr-p-by-badguy
                                        sv::svarlist-addr-p-when-not-consp
                                        vl-warninglist-p-when-not-consp
                                        vl-warninglist-p-when-subsetp-equal
                                        sv::assigns-p-when-not-consp))))
  (define vl-streaming-unpack-to-svex-assign
    ((lhs vl-expr-p)
     (rhs sv::svex-p)
     (rhs-size natp "remaining number of least-significant bits in the RHS that
                     haven't been used yet")
     (ss vl-scopestack-p)
     (scopes vl-elabscopes-p))
    :returns (mv (warnings vl-warninglist-p)
                 (assigns (implies (sv::svarlist-addr-p (sv::svex-vars rhs))
                                   (and (sv::assigns-p assigns)
                                        (sv::svarlist-addr-p (sv::assigns-vars assigns)))))
                 (size (equal size (mv-nth 3 (vl-expr-to-svex-untyped lhs ss scopes)))
                       :hints ((and stable-under-simplificationp
                                    '(:expand ((vl-expr-to-svex-untyped lhs ss scopes)
                                               (:free (a b) (sv::assigns-vars (cons a b)))))))))
    :measure (vl-expr-count lhs)
    :guard (b* (((mv & & & lhs-size) (vl-expr-to-svex-untyped lhs ss scopes)))
             (and (natp lhs-size)
                  (>= rhs-size lhs-size)))
;; Illustration: suppose LHS is {<< 5 {{<< 3 {a}}, b}}, rhs is c, a is 9 bits,
;; b is 7 bits, c is 24 bits.  Steps:
;;  Recur on the list {{<< 3 {a}}, b}  with rhs {<< 5 {c}}.
;;   Recur on the first element {<< 3 {a}}; size is 9 and size of RHS is 24
;;          so RHS becomes {<< 5 {c}} >> 15, size 9.
;;    Recur on the list {a} with rhs {<< 3 {{<< 5 {c}} >> 14}}.
;;     Recur on a: base case -- convert a and produce:
;;      a = {<< 3 {{<< 5 {c}} >> 14}}
;;   Recur on the second element b; since a used 9 bits, b is 7 bits, and rhs is 24 bits,
;;          so RHS becomes {<< 5 {c}} >> 8, size 6    (because 24-9-7=8).
;;         base case -- convert b and produce b = {<< 5 {c}} >> 8.

  (b* ((lhs (vl-expr-fix lhs))
       (warnings nil)
       (rhs-size (lnfix rhs-size))
       ((wmv warnings ?svex ?type lhs-size)
        (vl-expr-to-svex-untyped lhs ss scopes))
       ;; We know lhs-size exists by the guard.
       ;; Adjust the shift and size of the RHS to recur
       (shift (- rhs-size lhs-size))
       (shifted-rhs (sv::svcall sv::rsh (svex-int shift) rhs)))

    (vl-expr-case lhs
      :vl-stream
      (b* (((mv err slicesize)
            (if (eq lhs.dir :left)
                (vl-slicesize-resolve lhs.size ss scopes)
              ;; irrelevant
              (mv nil 1)))
           ((when err)
            (mv (fatal :type :vl-expr-to-svex-fail
                       :msg "Failed to resolve slice size of streaming ~
                               concat expression ~a0: ~@1"
                       :args (list lhs err))
                nil lhs-size))
           (new-rhs (if (eq lhs.dir :left)
                        (sv::svcall sv::blkrev
                                    (svex-int lhs-size)
                                    (svex-int slicesize)
                                    shifted-rhs)
                      shifted-rhs))
           ((mv warnings assigns)
            (vl-streamexprlist-unpack-to-svex-assign 
             lhs.parts new-rhs lhs-size ss scopes)))
        (mv warnings assigns lhs-size))
      :otherwise
      (b* (((wmv warnings svex-lhs ?lhs-type)
            (vl-expr-to-svex-lhs lhs ss scopes)))
        (mv warnings (list (cons svex-lhs (sv::make-driver :value shifted-rhs))) lhs-size)))))

  (define vl-streamexpr-unpack-to-svex-assign
    ((lhspart vl-streamexpr-p)
     (rhs sv::svex-p)
     (rhs-size natp)
     (ss vl-scopestack-p)
     (scopes vl-elabscopes-p))
    :returns (mv (warnings vl-warninglist-p)
                 (assigns (implies (sv::svarlist-addr-p (sv::svex-vars rhs))
                                   (and (sv::assigns-p assigns)
                                        (sv::svarlist-addr-p (sv::assigns-vars assigns)))))
                 (lhspart-size (implies (mv-nth 2 (vl-streamexpr-to-svex lhspart ss scopes))
                                        (equal lhspart-size
                                               (mv-nth 2 (vl-streamexpr-to-svex lhspart ss scopes))))
                               :hints ((and stable-under-simplificationp
                                            '(:expand ((vl-streamexpr-to-svex lhspart ss scopes)))))))
    :guard (b* (((mv & & size) (vl-streamexpr-to-svex lhspart ss scopes)))
             (and size (>= rhs-size size)))
    :measure (vl-streamexpr-count lhspart)
    (b* (((vl-streamexpr lhspart) (vl-streamexpr-fix lhspart))
         (rhs-size (lnfix rhs-size)))
      ;; We know there's no 'with' because vl-streamexpr-to-svex wouldn't have produced a size.

      (vl-streaming-unpack-to-svex-assign lhspart.expr rhs rhs-size ss scopes)))
      
         

  (define vl-streamexprlist-unpack-to-svex-assign
    ((lhsparts vl-streamexprlist-p)
     (rhs sv::svex-p)
     (rhs-size natp)
     (ss vl-scopestack-p)
     (scopes vl-elabscopes-p))
    :returns (mv (warnings vl-warninglist-p)
                 (assigns (implies (sv::svarlist-addr-p (sv::svex-vars rhs))
                                   (and (sv::assigns-p assigns)
                                        (sv::svarlist-addr-p (sv::assigns-vars assigns))))))
    :measure (vl-streamexprlist-count lhsparts)
    :guard (b* (((mv & & size) (vl-streamexprlist-to-svex lhsparts ss scopes)))
             (and size (>= rhs-size size)))
    (b* ((lhsparts (vl-streamexprlist-fix lhsparts))
         (rhs-size (lnfix rhs-size))
         ((when (atom lhsparts)) (mv nil nil))
         (warnings nil)
         ((wmv warnings assigns1 size1)
          (vl-streamexpr-unpack-to-svex-assign (car lhsparts) rhs rhs-size ss scopes))
         ((wmv warnings assigns2)
          (vl-streamexprlist-unpack-to-svex-assign (cdr lhsparts) rhs (- rhs-size size1) ss scopes)))
      (mv warnings (append-without-guard assigns1 assigns2))))
  ///
  (verify-guards vl-streaming-unpack-to-svex-assign
    :hints (("goal" :do-not-induct t)
            (and stable-under-simplificationp
                 '(:expand ((vl-expr-to-svex-untyped lhs ss scopes)
                            (vl-streaming-concat-to-svex lhs ss scopes)
                            (vl-streamexprlist-to-svex lhsparts ss scopes)
                            (vl-streamexpr-to-svex lhspart ss scopes)))))
    :otf-flg t)

  (deffixequiv-mutual vl-streaming-unpack-to-svex-assign))


(define vl-streaming-unpack-to-svex-assign-top
  ((lhs vl-expr-p)
   (rhs sv::svex-p)
   (orig-x vl-assign-p)
   (rhs-size natp "remaining number of least-significant bits in the RHS that
                     haven't been used yet")
   (ss vl-scopestack-p)
   (scopes vl-elabscopes-p))
  :short "Resolve an assignment where the LHS is a streaming concatenation, after
          converting the RHS expression to svex (untyped)."

  :returns (mv (warnings vl-warninglist-p)
               (assigns (implies (sv::svarlist-addr-p (sv::svex-vars rhs))
                                 (and (sv::assigns-p assigns)
                                      (sv::svarlist-addr-p (sv::assigns-vars assigns))))))
  :guard (vl-expr-case lhs :vl-stream)
  :guard-hints ((and stable-under-simplificationp
                     '(:expand ((vl-expr-to-svex-untyped lhs ss scopes)
                                (vl-streaming-concat-to-svex lhs ss scopes)))))
  (b* (((vl-stream lhs) (vl-expr-fix lhs))
       (rhs-size (lnfix rhs-size))
       (orig-x (vl-assign-fix orig-x))
       (warnings nil)
       ((wmv warnings ?lhs-svex ?lhs-type lhs-size)
        (vl-expr-to-svex-untyped lhs ss scopes))
       ((unless lhs-size)
        (mv (fatal :type :vl-bad-stream-assignment
                   :msg "~a0: couldn't size LHS streaming concatenation"
                   :args (list orig-x))
            nil))
       ((mv err slicesize)
        (if (eq lhs.dir :left)
            (vl-slicesize-resolve lhs.size ss scopes)
          ;; irrelevant
          (mv nil 1)))
       ((when err)
        (mv (fatal :type :vl-expr-to-svex-fail
                   :msg "Failed to resolve slice size of streaming ~
                               concat expression ~a0: ~@1"
                   :args (list lhs err))
            nil))
       ((mv warnings rhs rhs-size)
        (cond ((< rhs-size lhs-size)
               ;; Concat onto the RHS enough zeros so that it matches.
               (mv (fatal :type :vl-bad-stream-assignment
                          :msg "~a0: SystemVerilog prohibits streaming assignments
                                   where a streaming concatenation expression (either
                                   LHS or RHS) is larger than the other."
                          :args (list orig-x))
                   (sv::svcall sv::concat (svex-int (- lhs-size rhs-size))
                               (svex-int 0)
                               rhs)
                   lhs-size))
              (t (mv warnings rhs rhs-size))))
       (rhs-bitstream (if (eq lhs.dir :left)
                          (sv::svcall sv::blkrev
                                      (svex-int rhs-size)
                                      (svex-int slicesize)
                                      rhs)
                        rhs))
       (rhs-shift (if (< lhs-size rhs-size)
                      (sv::svcall sv::rsh (svex-int (- rhs-size lhs-size)) rhs-bitstream)
                    rhs-bitstream))
       ((wmv warnings assigns)
        (vl-streamexprlist-unpack-to-svex-assign lhs.parts rhs-shift lhs-size ss scopes)))
    (mv warnings assigns))

  :long "<p>To see how simulators treat streaming concatenations on the LHS, it
is most instructive to look at some examples.</p>

<p>First, consider the example in \"sv/cosims/stream3/test.sv\":</p>

@({
  logic [3:0] in;
  logic [3:0] out;
  assign {<< 3 {out}} = in;
 })

<p>When @('{<< 3 {a}}') occurs on the RHS of an assignment (and @('a') is 4
bits wide), it basically means the same thing as @('{ a[2:0], a[3] }').  So we
might think that we'd get the same results for @('guess1') if we assign it
as:</p>

@({
 logic [3:0] guess1;
 assign { guess1[2:0], guess1[3] } = in;
})

<p>But this isn't the case, at least in the major commercial simulators, VCS
and NCVerilog. Instead, when we run it on the following inputs:</p>

@({
 0001
 0010
 0100
 1000
 })

<p>we get the following outputs:</p>

@({
 out: 0010, guess1: 1000
 out: 0100, guess1: 0001
 out: 1000, guess1: 0010
 out: 0001, guess1: 0100
 })

<p>Actually, what this corresponds to is:</p>

@({
 assign out = { in[2:0], in[3] };
 })
<p>or:</p>
@({
 assign out = {<< 3 {in}};
 })

<p>This doesn't make a lot of sense, but the pattern holds generally: if you
see a streaming concatenation on the LHS, it means the same as if you put it on
the RHS.  (A complication in testing this rule is that the LHS and RHS need to
be the same size for both to be allowed.)</p>

<p>This rule is complicated by the fact that streaming concatenations can be
nested, and can have more than one expression concatenated together.  It is
also not clear how to treat cases where the RHS has more bits than the LHS.  We
reverse engineered the behavior of VCS using the example in
\"sv/cosims/stream4/test.sv\". (NCVerilog doesn't fully support multiple
streaming expressions inside a concatenation on the LHS.)</p>

@({
  logic [31:0] in;
  logic [8:0] out1;
  logic [6:0] out2;
  assign {<< 5 {{<< 3 {out1}}, out2}} = in[31:0];
 })

<p>When run on the input pattern</p>
@({
 00000000000000000000000000000001
 00000000000000000000000000000010
 00000000000000000000000000000100
 ...
})
<p>this produces the results:</p>

@({
 out1 000010000, out2 0000000
 out1 000100000, out2 0000000
 out1 000000001, out2 0000000
 out1 000000010, out2 0000000
 out1 000000100, out2 0000000
 out1 000000000, out2 1000000
 out1 001000000, out2 0000000
 out1 010000000, out2 0000000
 out1 100000000, out2 0000000
 out1 000001000, out2 0000000
 out1 000000000, out2 0000010
 out1 000000000, out2 0000100
 out1 000000000, out2 0001000
 out1 000000000, out2 0010000
 out1 000000000, out2 0100000
 out1 000000000, out2 0000000
 out1 000000000, out2 0000000
 out1 000000000, out2 0000000
 out1 000000000, out2 0000000
 out1 000000000, out2 0000001
})

<p>This turns out to be equivalent to the following:

@({
 logic [31:0] temp1;
 logic [15:0] temp2;
 logic [8:0] temp3;
 logic [6:0] temp4;
 assign temp1 = {<< 5 {in[31:0]}};
 assign temp2 = temp1 >> 16;
 assign {temp3, temp4} = temp2;
 assign out2 = temp4;
 assign out1 = {<< 3 {temp3}};
 })

<p>It's not clear why we should think this is the correct behavior, but we at
least can derive an algorithm from it:</p>

<ol> <li>Move the outermost streaming concatenation operator to the
RHS (obtaining temp1, in the example).</li>

<li>Compute the bit widths of LHS and RHS and right-shift the RHS by
@('rhswidth - lhswidth') (obtaining temp2, in thie example).</p>

<li>Chop up the RHS into chunks matching the sizes of the concatenated
subexpressions of the LHS (obtaining temp3, temp4).</li>

<li>Make a new assignment of each chunk to its corresponding LHS subexpression,
and for each assignment created that has a LHS streaming concatenation, repeat
this process.  (Thus we assign out2 to temp4 and end up assigning out1 to
@('{<< 3 {temp3}}').</li>

</ol>

<p>Note that when repeating the process for the last step, we can skip step 2,
because the sizes match by construction.</p>")



#||

(trace$
 #!vl
 (vl-assign->svex-assign
  :entry (list 'vl-assign->svex-assign
               (with-local-ps (vl-pp-assign x)))
  :exit (list 'vl-assign->svex-assign
              (cadr values))))
||#




(define vl-assign->svex-assign ((x vl-assign-p)
                                (ss vl-scopestack-p)
                                (scopes vl-elabscopes-p))
  :returns (mv (warnings vl-warninglist-p)
               (assigns sv::assigns-p "The assignment"))
  :short "Turn a VL assignment into an SVEX assignment or delayed assignment."
  :long "<p>This just straightforwardly converts the LHS and RHS to svex
expressions, then converts the LHS into a @(see sv::lhs-p).</p>

<p>At the moment we only support a single-tick delay, just because for a
multi-tick we'd have to generate new names for the intermediate states.</p>"
  :prepwork ((local (in-theory (enable (force)))))
  (b* (((vl-assign x) (vl-assign-fix x))
       (warnings nil)
       ((when (vl-expr-case x.lvalue :vl-stream))
        (b* (((wmv warnings rhs ?rhs-type rhs-size)
              (vl-expr-to-svex-untyped x.expr ss scopes))
             ((unless rhs-size)
              (mv warnings nil))
             ((wmv warnings delay :ctx x) (vl-maybe-gatedelay->delay x.delay))
             (rhs (if delay (sv::svex-add-delay rhs delay) rhs))
             
             ((wmv warnings assigns)
              (vl-streaming-unpack-to-svex-assign-top x.lvalue rhs x rhs-size ss scopes)))
          (mv warnings assigns)))

       ((wmv warnings lhs lhs-type :ctx x)
        (vl-expr-to-svex-lhs x.lvalue ss scopes))
       ((unless lhs-type) (mv warnings nil))
       ((wmv warnings delay :ctx x) (vl-maybe-gatedelay->delay x.delay))
       ((wmv warnings svex-rhs :ctx x)
        (vl-expr-to-svex-datatyped x.expr x.lvalue lhs-type ss scopes :compattype :assign))
       ;; BOZO deal with drive strengths
       ((when (not delay))
        (mv warnings (list (cons lhs (sv::make-driver :value svex-rhs)))))
       (svex-rhs (sv::svex-add-delay svex-rhs delay)))
    (mv nil (list (cons lhs (sv::make-driver :value svex-rhs)))))

  ///

  (defret vars-of-vl-assign->svex-assign-assigns
    (sv::svarlist-addr-p (sv::assigns-vars assigns))
    :hints(("Goal" :in-theory (enable sv::assigns-vars)))))

(define vl-assigns->svex-assigns ((x vl-assignlist-p)
                                  (ss vl-scopestack-p)
                                  (scopes vl-elabscopes-p)
                                  (assigns sv::assigns-p))
  :short "Collects svex module components for a list of assignments, by collecting
          results from @(see vl-assign->svex-assign)."
  :returns (mv (warnings vl-warninglist-p)
               (assigns1 sv::assigns-p))
  (if (atom x)
      (mv nil
          (sv::assigns-fix assigns))
    (b* ((warnings nil)
         ((wmv warnings assigns1) (vl-assign->svex-assign (car x) ss scopes))
         ((wmv warnings assigns)
          (vl-assigns->svex-assigns (cdr x) ss scopes
                                    (append-without-guard assigns1 assigns))))
      (mv warnings assigns)))
  ///

  (more-returns
   (assigns1 :name vars-of-vl-assigns->svex-assigns-assigns
             (implies (sv::svarlist-addr-p (sv::assigns-vars assigns))
                      (sv::svarlist-addr-p (sv::assigns-vars assigns1))))))


(define vl-alias->svex-alias ((x vl-alias-p)
                                (ss vl-scopestack-p)
                                (scopes vl-elabscopes-p))
  :returns (mv (warnings vl-warninglist-p)
               (aliases sv::lhspairs-p))
  :short "Turn a VL alias into an SVEX alias."
  :long "<p>This just straightforwardly converts the LHS and RHS to svex
expressions, then @(see sv::lhs-p) objects.</p>"
  :prepwork ((local (in-theory (enable (force)))))
  (b* (((vl-alias x) (vl-alias-fix x))
       (warnings nil)
       ((wmv warnings lhs lhs-type :ctx x)
        (vl-expr-to-svex-lhs x.lhs ss scopes))
       ((wmv warnings rhs rhs-type :ctx x)
        (vl-expr-to-svex-lhs x.rhs ss scopes))
       ((unless (and lhs-type rhs-type))
        (mv warnings nil))
       (err (vl-check-datatype-compatibility lhs-type rhs-type :equiv))
       ((when err)
        (mv (fatal :type :vl-bad-alias
                   :msg "~a0: Incompatible LHS/RHS types: ~@1."
                   :args (list x err))
            nil)))
    (mv nil (list (cons lhs rhs))))

  ///
  (defmvtypes vl-alias->svex-alias (nil true-listp))

  (defret vars-of-vl-alias->svex-alias
    (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
    :hints(("Goal" :in-theory (enable sv::lhspairs-vars)))))


(define vl-aliases->svex-aliases ((x vl-aliaslist-p)
                                  (ss vl-scopestack-p)
                                  (scopes vl-elabscopes-p)
                                  (aliases sv::lhspairs-p))
  :short "Collects svex module components for a list of aliases by collecting
          results from @(see vl-alias->svex-alias)."
  :returns (mv (warnings vl-warninglist-p)
               (aliases1 sv::lhspairs-p))
  (if (atom x)
      (mv nil
          (sv::lhspairs-fix aliases))
    (b* ((warnings nil)
         ((wmv warnings aliases1) (vl-alias->svex-alias (car x) ss scopes))
         ((wmv warnings aliases)
          (vl-aliases->svex-aliases (cdr x) ss scopes
                                    (append aliases1 aliases))))
      (mv warnings aliases)))
  ///

  (more-returns
   (aliases1 :name vars-of-vl-aliases->svex-aliases-aliases
             (implies (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
                      (sv::svarlist-addr-p (sv::lhspairs-vars aliases1))))))









#||
(defmacro index (x y)
  `(make-vl-nonatom :op :vl-index
                    :args (list ,x
                                (vl-make-index ,y))))

(defmacro dot (x y)
  `(make-vl-nonatom :op :vl-hid-dot
                    :args (list ,x ,y)))

(let ((a (vl-idexpr "a" nil nil))
      (b (vl-idexpr "b" nil nil))
      (c (vl-idexpr "c" nil nil)))
  (vl-index->svex-path
   (index (index (dot (index (index a 1) 2)
                      (dot (index (index b 5) 6) c))
                 7)
          8)))


||#







;; ;; BOZO vl-datatype->svex-modname (and generally all the things that generate
;; ;; svex module names) are totally unverified and could be producing name
;; ;; conflicts, with unpredictable results.
;; (define vl-scopestack-namespace ((x vl-scopestack-p) acc)
;;   :returns (name-nest)
;;   :measure (vl-scopestack-count x)
;;   (vl-scopestack-case x
;;     :null acc
;;     :global (cons ':top acc)
;;     :local (vl-scopestack-namespace
;;             x.super
;;             (cons (let ((name (vl-scope->name x.top)))
;;                     (list (tag x.top) (or name "anonymous")))
;;                   acc))))

(define vl-datatype->svex-modname ((x vl-datatype-p))
  :returns (name sv::modname-p
                 :hints(("Goal" :in-theory (enable sv::modname-p))))
  :guard-hints (("Goal" :in-theory (enable sv::modname-p)))
  (hons-copy
   (sv::modname-fix (vl-datatype-fix x))))
  ;; (b* (((when (or (consp (vl-datatype->udims x))
  ;;                 (consp (vl-datatype->pdims x))
  ;;                 (not (vl-datatype-case x :vl-usertype))))
  ;;       (sv::modname-fix (vl-scopestack-namespace conf (list (vl-datatype-fix x))))))
  ;;   (hons-copy
  ;;    (sv::modname-fix
  ;;     `(:datatype . ,(vl-scopestack-namespace conf `(,(vl-usertype->name x))))))))





(define vl-datatype-elem->mod-components
  ((name sv::name-p "The name of the new wire")
   (subwire sv::wire-p "A dummy wire with dimensions appropriate for the new wire")
   (self-lsb maybe-natp "Where to line up the wire with the self instance, for
                         nontrivial data-structures")
   (submod (or (sv::modname-p submod)
               (not submod))
           "For nontrivial data-structures, the name of the module representing
            the data structure"))
  :long "<p>To create a wire of a given datatype, we first make the required
modules and instances for the datatype, then connect up a new wire to the
instance's :self wire.  So if we have, e.g.,</p>
@({
  logic [3:0] foo;
  struct { logic [2:0] bar; logic [1:4] baz; } fa;
 })

<p>then we first run @(see vl-datatype->mods) on each of the datatypes.  For
the @('logic [3:0]') type, it doesn't produce a module since that fits in a
simple vector.  For the struct type, it produces a module containing something
like this:</p>

@({
 logic [6:0] self;       // representing the whole struct
 logic [2:0] bar;
 logic [1:4] baz;
 alias bar = self[6:4];  // aliases describe which fields correspond to which parts of self
 alias baz = self[3:0];
 })

<p>@(csee vl-datatype->mods) produces this module and returns its name (which is
just the VL datatype -- call it \"ourstruct\" for our purposes) and its self
wire.</p>

<p>So now, to make the wire foo, we look at the values returned by @(see
vl-datatype->mods): it still produces a self wire, even though it doesn't
create a submodule, and we just modify that self wire to set the name to foo.
For fa, we do the same thing, but we also create an instance of the struct
module -- also named fa -- and alias the wire fa to that instance's self wire:</p>
@({
  logic [6:0] fa;
  ourstruct fa ();
  alias fa = fa.self;
 })
<p>When the aliases are all composed together, this induces the right aliases
for the struct:</p>
@({
  alias fa[3:0] = fa.baz;
  alias fa[6:4] = fa.bar;
 })

<p>Sometimes we need to do this same thing for members of a struct/union or
interface.  In this case, there is an additional alias that we need to
generate, mapping each vector to the (outer) self wire.  This is determined by
the @('self-lsb') input; if given, then we create an additional alias to the
self wire, where the lsb of the new wire lines up with the given index of the
self wire.  (This creates the aliases between bar/baz and the self wire of
ourstruct, above.)</p>"

  :returns (mv (wire1 sv::wire-p  "The resulting wire declaration")
               (insts1 sv::modinstlist-p "Instance of the data structure module
                                            if necessary")
               (aliases1 sv::lhspairs-p
                         "Aliases: between the new wire and the self of the instanced
                          data structure module, if necessary, and between the
                          new wire and the outer data structure/interface
                          module."))
  (b* (((sv::wire subwire))
       (wire (sv::make-wire :name name
                              :width subwire.width
                              :low-idx subwire.low-idx))
       ((unless (or submod self-lsb))
        ;; Simple vector datatype and not within a data structure where we need
        ;; to alias this to the self.  Just return the wire with no insts/aliases.
        (mv wire nil nil))
       ((mv insts aliases1)
        (if submod
            (b* ((modinst (sv::make-modinst :instname name :modname submod)))
              (mv (list modinst)
                  (vlsv-aggregate-subalias name subwire.width)))
          (mv nil nil)))
       (aliases2
        (if self-lsb
            (vlsv-aggregate-superalias name subwire.width self-lsb)
          nil)))
    (mv wire insts (append aliases2 aliases1)))
  ///
  (more-returns
   (aliases1 :name vars-of-vl-datatype-elem->mod-components
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases1))
             :hints(("Goal" :in-theory (enable sv::lhspairs-vars sv::lhatom-vars))))))


(define vl-datatype-dimension->mod-components ((count natp)
                                               (msi integerp)
                                               (incr integerp)
                                               (subwire sv::wire-p)
                                               (submod (or (sv::modname-p submod)
                                                           (not submod))))
  :short "Iterates over the indices of an array, creating svex module components
          for each index using @(see vl-datatype-elem->mod-components)"
  :guard-hints (("goal" :in-theory (enable sv::name-p)))
  :returns (mv (wires sv::wirelist-p)
               (insts sv::modinstlist-p)
               (aliases sv::lhspairs-p))
  (b* (((when (zp count)) (mv nil nil nil))
       (next-count (1- count))
       ((mv wire1 insts1 aliases1)
        (vl-datatype-elem->mod-components
         (lifix msi) subwire (* (sv::wire->width subwire) next-count) submod))
       ((mv wires insts aliases)
        (vl-datatype-dimension->mod-components
         next-count (+ (lifix incr) (lifix msi)) incr subwire submod)))
    (mv (cons wire1 wires)
        (append-without-guard insts1 insts)
        (append-without-guard aliases1 aliases)))
  ///
  (more-returns
   (aliases :name vars-of-vl-datatype-dimension->mod-components
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
             :hints(("Goal" :in-theory (enable sv::lhspairs-vars sv::lhatom-vars))))))



(define sv::maybe-modnamelist-p (x)
  (if (atom x)
      t
    (and (or (sv::modname-p (car x)) (not (car x)))
         (sv::maybe-modnamelist-p (cdr x))))
  ///
  (defthm sv::maybe-modnamelist-p-of-cons
    (equal (sv::maybe-modnamelist-p (cons a b))
           (and (or (not a) (sv::modname-p a))
                (sv::maybe-modnamelist-p b)))))




(define vl-struct-fields->mod-components ((members vl-structmemberlist-p)
                                          (subwires sv::wirelist-p)
                                          (submodnames sv::maybe-modnamelist-p))
  :short "Iterates over the fields of a struct, creating svex module components
          for each field using @(see vl-datatype-elem->mod-components)"
  :prepwork ((local (in-theory (disable cons-equal
                                        acl2::append-when-not-consp))))
  :guard (and (equal (len subwires) (len members))
              (equal (len submodnames) (len members)))
  :verify-guards nil
  :guard-hints (("goal" :in-theory (enable sv::name-p sv::maybe-modnamelist-p)))
  :returns (mv (wires sv::wirelist-p)
               (insts sv::modinstlist-p)
               (aliases sv::lhspairs-p)
               (width natp :rule-classes :type-prescription))
  (b* (((when (atom members)) (mv nil nil nil 0))
       ((vl-structmember x) (car members))
       ((mv wires insts aliases width)
        (vl-struct-fields->mod-components (cdr members) (cdr subwires) (cdr submodnames)))
       ((mv wire1 insts1 aliases1)
        (vl-datatype-elem->mod-components
         x.name (car subwires) width (car submodnames))))
    (mv (cons wire1 wires)
        (append-without-guard insts1 insts)
        (append-without-guard aliases1 aliases)
        (+ (sv::wire->width wire1) width)))
  ///
  (verify-guards vl-struct-fields->mod-components
    :hints (("goal" :in-theory (enable sv::name-p sv::maybe-modnamelist-p))))
  (more-returns
   (width (implies (consp members) (posp width))
          :name posp-width-of-vl-struct-fields->mod-components
          :rule-classes :type-prescription))
  (more-returns
   (aliases :name vars-of-vl-struct-fields->mod-components
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))))


(define vl-union-fields->mod-components ((members vl-structmemberlist-p)
                                          (subwires sv::wirelist-p)
                                          (submodnames sv::maybe-modnamelist-p))
  :short "Iterates over the fields of a union, creating svex module components
          for each field using @(see vl-datatype-elem->mod-components)"
  :prepwork ((local (defthm max-linear-1
                      (<= a (max a b))
                      :rule-classes :linear))
             (local (defthm max-linear-2
                      (<= b (max a b))
                      :rule-classes :linear))
             (local (in-theory (disable cons-equal max
                                        acl2::append-when-not-consp))))
  :guard (and (equal (len subwires) (len members))
              (equal (len submodnames) (len members)))
  :verify-guards nil
  :guard-hints (("goal" :in-theory (enable sv::name-p sv::maybe-modnamelist-p)))
  :returns (mv (wires sv::wirelist-p)
               (insts sv::modinstlist-p)
               (aliases sv::lhspairs-p)
               (width natp :rule-classes :type-prescription))
  (b* (((when (atom members)) (mv nil nil nil 0))
       ((vl-structmember x) (car members))
       ((mv wires insts aliases width)
        (vl-union-fields->mod-components (cdr members) (cdr subwires) (cdr submodnames)))
       ((mv wire1 insts1 aliases1)
        (vl-datatype-elem->mod-components
         x.name (car subwires) 0 (car submodnames))))
    (mv (cons wire1 wires)
        (append-without-guard insts1 insts)
        (append-without-guard aliases1 aliases)
        (max (sv::wire->width wire1) width)))
  ///
  (verify-guards vl-union-fields->mod-components
    :hints (("goal" :in-theory (enable sv::name-p sv::maybe-modnamelist-p))))
  (more-returns
   (width (implies (consp members) (posp width))
          :name posp-width-of-vl-union-fields->mod-components
          :rule-classes :type-prescription))
  (more-returns
   (aliases :name vars-of-vl-union-fields->mod-components
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))))



(define vl-datatype->all-dims ((x vl-datatype-p))
  :returns (dims vl-packeddimensionlist-p)
  (append-without-guard (vl-datatype->udims x)
                        (vl-datatype->pdims x)))


(defines vl-datatype->mods
  :verify-guards nil
  :prepwork (;; (local (defthm vl-datatype-count-of-vl-datatype-update-dims
             ;;          (equal (vl-datatype-count (vl-datatype-update-dims pdims udims x))
             ;;                 (vl-datatype-count x))
             ;;          :hints(("Goal" :in-theory (enable vl-datatype-update-dims
             ;;                                            vl-datatype-count)))))
             ;; (local (defthm vl-range-resolved-p-when-car-of-rangelist
             ;;          (implies (and (vl-resolved-rangelist-p x)
             ;;                        (consp x))
             ;;                   (and (vl-range-p (car x))
             ;;                        (vl-range-resolved-p (car x))))
             ;;          :hints(("Goal" :in-theory (enable
             ;;          vl-resolved-rangelist-p)))))
             (local (Defthm append-nil
                      (equal (append nil x) x)))
             (local (in-theory (disable (tau-system)
                                        acl2::member-of-cons
                                        acl2::car-of-append
                                        acl2::consp-of-append
                                        acl2::append-when-not-consp
                                        acl2::cancel_times-equal-correct
                                        default-car;;  default-cdr
                                        not
                                        acl2::consp-when-member-equal-of-cons-listp
                                        sv::lhspairs-p-when-subsetp-equal
                                        sv::modalist-p-when-not-consp)))
             (local (in-theory (enable vl-datatype->all-dims)))
             #!sv
             (local (defthm modalist-vars-of-cons
                      (equal (modalist-vars (cons (cons a b) c))
                             (append (and (modname-p a)
                                          (module-vars b))
                                     (modalist-vars c)))
                      :hints(("Goal" :in-theory (enable modalist-vars
                                                        modalist-fix)))))

             (local (defthm vl-datatype-count-of-update-dims
                      (equal (vl-datatype-count
                              (vl-datatype-update-dims pdims udims x))
                             (+ (vl-datatype-count x)
                                (vl-packeddimensionlist-count pdims)
                                (vl-packeddimensionlist-count udims)
                                (- (vl-packeddimensionlist-count
                                    (vl-datatype->pdims x)))
                                (- (vl-packeddimensionlist-count
                                    (vl-datatype->udims x)))))
                      :hints(("Goal" :expand ((vl-datatype-count x)
                                              (vl-datatype-count
                                               (vl-datatype-update-dims
                                                pdims udims x))))
                             (and stable-under-simplificationp
                                  '(:in-theory (enable
                                                vl-datatype-update-dims))))))

             (local (defthm vl-packeddimensionlist-count-of-append
                      (equal (vl-packeddimensionlist-count (append a b))
                             (+ -1 (vl-packeddimensionlist-count a)
                                (vl-packeddimensionlist-count b)))
                      :hints(("Goal" :in-theory (enable
                                                 vl-packeddimensionlist-count
                                                 append)
                              :induct (append a b)))))

             (local (defthm o<-when-atoms
                      (implies (and (atom x) (atom y))
                               (equal (o< x y)
                                      (< x y)))
                      :hints(("Goal" :in-theory (enable o<)))))

             (local (defthm vl-packeddimensionlist-count-of-cdr1
                      (equal (vl-packeddimensionlist-count (cdr a))
                             (if (consp a)
                                 (+ -1 (- (vl-packeddimension-count (car a)))
                                    (vl-packeddimensionlist-count a))
                               (vl-packeddimensionlist-count a)))
                      :hints(("Goal" :expand ((vl-packeddimensionlist-count
                                               a))))))

             (local (in-theory (disable vl-datatype-udims-when-vl-coretype
                                        vl-datatype-udims-when-vl-struct
                                        vl-datatype-udims-when-vl-union
                                        vl-datatype-udims-when-vl-enum
                                        vl-datatype-udims-when-vl-usertype
                                        vl-datatype-pdims-when-vl-coretype
                                        vl-datatype-pdims-when-vl-struct
                                        vl-datatype-pdims-when-vl-union
                                        vl-datatype-pdims-when-vl-enum
                                        vl-datatype-pdims-when-vl-usertype)))


             ;; (local (defthm vl-maybe-usertype-resolve-when-dims
             ;;          (implies (consp (vl-datatype->all-dims x))
             ;;                   (equal (vl-maybe-usertype-resolve x)
             ;;                          (vl-datatype-fix x)))
             ;;          :hints(("Goal" :in-theory (enable vl-datatype->all-dims
             ;;                                            vl-maybe-usertype-resolve)))))

             ;; (local (defthm posp-rec-limit-when-usertypes-ok
             ;;          (implies (and (zp rec-limit)
             ;;                        (vl-datatype-case x :vl-usertype))
             ;;                   (vl-datatype-check-usertypes x ss :rec-limit rec-limit))
             ;;          :hints (("goal" :expand ((:free (rec-limit)
             ;;                                    (vl-datatype-check-usertypes x ss :rec-limit rec-limit)))))))
             ;; #!sv
             ;; (local (defthm module-vars-of-module
             ;;          (equal (module-vars (module wires insts assigns delays aliases))
             ;;                 (append (assigns-vars assigns)
             ;;                         (svar-map-vars delays)
             ;;                         (lhspairs-vars aliases)))
             ;;          :hints(("Goal" :in-theory (enable module-vars)))))
             (fty::set-deffixequiv-mutual-default-hints
              ((acl2::just-expand-mrec-default-hint 'fty::fnname id nil world)))
             (std::set-returnspec-mrec-default-hints
              ((acl2::just-expand-mrec-default-hint 'std::fnname id nil world)))
             (local (in-theory (disable member-equal-when-member-equal-of-cdr-under-iff
                                        double-containment
                                        acl2::car-when-all-equalp
                                        acl2::mv-nth-cons-meta))))

  (define vl-datatype->mods ((x vl-datatype-p)
                             ;; (conf vl-svexconf-p)
                             (modalist sv::modalist-p))
    :guard (vl-datatype-resolved-p x)
    :returns
    (mv (err   (iff (vl-msg-p err) err))
        (wire1 (implies (not err) (sv::wire-p wire1))
               "The :self wire of the data structure, from its own scope.  For
                reference, not for use within the outer context.  This has the
                right width and, if a simple 1D vector type, range.")
        (modname (iff (sv::modname-p modname) modname)
                 "If we needed to create a module for this, return the module
                  name.  Otherwise, i.e. for simple vector types, nil.")
        (modalist1 (and (sv::modalist-p modalist1)
                        (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                 (sv::svarlist-addr-p (sv::modalist-vars modalist1))))))
    :measure (Vl-datatype-count x)
    :hints (("goal" :cases ((consp (vl-datatype->all-dims x)))))
    :short "Create an svex module representing a datatype.  This module
declares the wire names that exist inside the datatype, contains module
instances representing nested datatypes, and arranges aliases among the various
pieces of different wires."
    :long "<p>An example of how this works.  Suppose we have the following
rather horrible variable declaration:</p>

@({
 struct { union { logic [3:0] a; logic [5:4] b [2:0] ; } c;
          logic [2:4] d; } [3:0] myvar [2:3];
 })

<p>Modulo the choice of names for the generated modules, this will be reflected
in svex as the following module declarations and, finally, a wire and instance
declaration for the variable itself:</p>

@({
 // Modules implementing the data structure:
 module b_array ();
   wire [5:0] __self;  // size 6 = 3*2
   wire [5:4] <2>;
   wire [5:4] <1>;
   wire [5:4] <0>;
   alias <2> = __self[5:4];
   alias <2> = __self[3:2];
   alias <2> = __self[1:0];
 endmodule

 module c_union ();
   wire [5:0] __self;  // size 6 = max(6,4)
   wire [3:0] a;
   wire [5:0] b;
   b_array b ();
   alias b = b.__self;
   alias a = __self[3:0];
   alias b = __self[5:0];
 endmodule

 module myvar_struct ();
   wire [8:0] __self; // size 9 = 6+3
   wire [5:0] c;
   wire [2:4] d;
   c_union c ();
   alias c = c.__self;
   alias c = __self[8:3];
   alias d = __self[2:0];
 endmodule

 module myvar_struct_array ();
   wire [17:0] __self; // size 18 = 9*2
   wire [8:0] <2>;
   wire [8:0] <3>;
   myvar_struct <2> ();
   myvar_struct <3> ();
   alias <2> = <2>.__self;
   alias <3> = <3>.__self;
   alias <2> = __self[17:9];
   alias <3> = __self[8:0];
 endmodule

 // Declaration/instance/alias for the variable:
 wire [17:0] myvar;
 myvar_struct_array myvar ();
 alias myvar = myvar.__self;
 })

<p>@('Vl-datatype->mods') is responsible for producing these modules.  It mainly
returns a @(see sv::modalist) of the newly generated modules, but also
returns the name of the module corresponding to the given datatype (if any) and
a wire whose range is appropriate for a variable declared to be of the given
type (this is used by @(see vl-datatype-elem->mod-components)).</p>"
    (b* ((type-modname (vl-datatype->svex-modname x))
         (modalist (sv::modalist-fix modalist))
         (look (sv::modalist-lookup type-modname modalist))
         (x (vl-maybe-usertype-resolve x))
         (look (or look
                   (sv::modalist-lookup (vl-datatype->svex-modname x) modalist)))
         ((when look)
          (b* (((sv::module look))
               (modalist (sv::modalist-fix modalist))
               (wire (sv::wirelist-find :self look.wires))
               ((unless wire)
                (mv (vmsg "Programming error: no wire named :self in data ~
                           structure module ~x0" look)
                    (sv::make-wire :name "ERROR" :width 1 :low-idx 0) nil modalist)))
            (mv nil wire type-modname modalist)))
         (dims (vl-datatype->all-dims x))
         (simple-vector-type-p
          ;; BOZO Check what happens to an unpacked array of single-bit coretypes?
          (and (eq (vl-datatype-kind x) :vl-coretype)
               (member (vl-coretype->name x)
                       '(:vl-logic :vl-reg :vl-bit))
               (or (atom dims)
                   (atom (cdr dims)))))
         ((when (and (consp dims)
                     (b* ((dim (car dims)))
                       (or (vl-packeddimension-case dim :unsized)
                           (not (vl-range-resolved-p (vl-packeddimension->range dim)))))))
          (mv (vmsg "Bad dimension on datatype ~a0" x) nil nil modalist))
         ((unless (or (atom dims)
                      simple-vector-type-p))
          (b* ((new-type (vl-datatype-update-dims
                          ;; we don't distinguish between udims/pdims here
                          (cdr dims) nil x))
               (range (vl-packeddimension->range (car dims)))
               ((mv err subwire submod-name modalist)
                (vl-datatype->mods new-type modalist))
               ((when err) (mv err nil nil modalist))
               ((sv::wire subwire))
               (msi (vl-range-msbidx range))
               (revp (vl-range-revp range))
               (size (vl-range-size range))
               (selfwire (sv::make-wire :name :self
                                          :width (* size subwire.width)
                                          :low-idx 0))
               ;; for each index in the range, we need:
               ;; - a wire declaration
               ;; - an instance of submodule
               ;; - an alias between the wire and self
               ;; - an alias between the wire and the instance's self.
               ((mv wires insts aliases)
                (vl-datatype-dimension->mod-components
                 (vl-range-size range) ;; counter
                 msi ;; current index
                 (if revp 1 -1) ;; incr/decr of current index
                 subwire
                 submod-name))
               (new-mod (sv::make-module :wires (cons selfwire wires)
                                           :insts insts
                                           :aliaspairs aliases))
               (modalist (hons-acons type-modname new-mod modalist)))
            (mv nil selfwire type-modname modalist))))
      (vl-datatype-case x
        :vl-coretype
        (b* (((vl-coredatatype-info xinfo) (vl-coretypename->info x.name))
             ((unless xinfo.size)
              (mv (vmsg "Unsizable coretype: ~a0" x)
                  nil nil modalist))
             ((mv width low-bit revp)
              (b* (((when (eql xinfo.size 1))
                    (if (consp dims)
                        (b* ((range (vl-packeddimension->range (car dims))))
                          (mv (vl-range-size range)
                              (vl-range-low-idx range)
                              (vl-range-revp range)))
                      (mv 1 0 nil))))
                (mv xinfo.size 0 nil))))
          (mv nil
              (sv::make-wire :name :self :width width :low-idx low-bit :revp revp)
              nil (sv::modalist-fix modalist)))
        :vl-struct
        (b* (((mv err subwires submodnames modalist)
              (vl-structmemberlist->submods x.members modalist))
             ((when err) (mv err nil nil modalist))
             ((when (atom x.members))
              (mv (vmsg "empty struct") nil nil modalist))
             ((mv wires insts aliases totalwidth)
              (vl-struct-fields->mod-components x.members subwires submodnames))
             (selfwire (sv::make-wire :name :self :width totalwidth :low-idx 0))
             (new-mod (sv::make-module :wires (cons selfwire wires)
                                         :insts insts
                                         :aliaspairs aliases))
             (modalist (hons-acons type-modname new-mod modalist)))
          (mv nil selfwire type-modname modalist))
        :vl-union
        (b* (((mv err subwires submodnames modalist)
              (vl-structmemberlist->submods x.members modalist))
             ((when err) (mv err nil nil modalist))
             ((when (atom x.members))
              (mv (vmsg "empty union") nil nil modalist))
             ((mv wires insts aliases totalwidth)
              (vl-union-fields->mod-components x.members subwires submodnames))
             (selfwire (sv::make-wire :name :self :width totalwidth :low-idx 0))
             (new-mod (sv::make-module :wires (cons selfwire wires)
                                         :insts insts
                                         :aliaspairs aliases))
             (modalist (hons-acons type-modname new-mod modalist)))
          (mv err selfwire type-modname modalist))

        :vl-enum
        (vl-datatype->mods x.basetype modalist)

        :otherwise (mv (vmsg "Can't handle type ~a0" x)
                       nil nil (sv::modalist-fix modalist)))))


  (define vl-structmemberlist->submods ((x vl-structmemberlist-p)
                                        (modalist sv::modalist-p))
    :guard (vl-structmemberlist-resolved-p x)
    :measure (vl-structmemberlist-count x)
    :returns
    (mv (err (iff (vl-msg-p err) err))
        (wires (and (sv::wirelist-p wires)
                    (implies (not err)
                             (equal (len wires) (len x)))))
        (modnames (and (sv::maybe-modnamelist-p modnames)
                       (implies (not err)
                                (equal (len modnames) (len x)))))
        (modalist1 (and (sv::modalist-p modalist1)
                        (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                 (sv::svarlist-addr-p (sv::modalist-vars modalist1))))))
    (b* (((when (atom x)) (mv nil nil nil (sv::modalist-fix modalist)))
         ((vl-structmember xf) (car x))
         ((mv err wire1 modname1 modalist)
          (vl-datatype->mods xf.type modalist))
         ((when err) (mv err nil nil modalist))
         ((mv err rest-wires rest-modnames modalist)
          (vl-structmemberlist->submods (cdr x) modalist))
         ((when err) (mv err nil nil modalist)))
      (mv nil
          (cons wire1 rest-wires)
          (cons modname1 rest-modnames)
          modalist)))
  ///
  (local (in-theory (disable vl-datatype->mods)))
  ;; (local (defthm usertypes-ok-of-usertype-resolve
  ;;          (implies (not (vl-datatype-check-usertypes x ss))
  ;;                   (not (vl-datatype-check-usertypes
  ;;                         (mv-nth 0 (vl-maybe-usertype-resolve x ss))
  ;;                         (mv-nth 1 (vl-maybe-usertype-resolve x ss)))))
  ;;          :rule-classes
  ;;          ((:forward-chaining :trigger-terms
  ;;            ((vl-maybe-usertype-resolve x ss))))))

  ;; (local (defthm usertypes-ok-of-struct-members
  ;;          (implies (and (not (vl-datatype-check-usertypes x ss))
  ;;                        (equal (vl-datatype-kind x) :vl-struct))
  ;;                   (not (vl-structmemberlist-check-usertypes
  ;;                         (vl-struct->members x) ss :rec-limit 1000)))
  ;;          :hints (("goal" :expand ((vl-datatype-check-usertypes x ss))))))

  ;; (local (defthm usertypes-ok-of-union-members
  ;;          (implies (and (not (vl-datatype-check-usertypes x ss))
  ;;                        (equal (vl-datatype-kind x) :vl-union))
  ;;                   (not (vl-structmemberlist-check-usertypes
  ;;                         (vl-union->members x) ss :rec-limit 1000)))
  ;;          :hints (("goal" :expand ((vl-datatype-check-usertypes x ss))))))

  (verify-guards vl-datatype->mods
    ;; :hints ((and stable-under-simplificationp
    ;;              '(:expand ((vl-structmemberlist-check-usertypes x ss :rec-limit 1000)))))
    :guard-debug t)

  (deffixequiv-mutual vl-datatype->mods))




(define vl-vardecl->svex ((x vl-vardecl-p)
                          (modalist sv::modalist-p)
                          (self-lsb maybe-natp))
  :short "Produce the svex wire declaration and any aliases, modinsts, and modules
          necessary for a given vardecl."
  :returns (mv (warnings vl-warninglist-p)
               (width natp :rule-classes :type-prescription)
               (wires sv::wirelist-p)
               (aliases sv::lhspairs-p)
               (modinsts sv::modinstlist-p)
               (modalist1 sv::modalist-p))
  :prepwork ((local (in-theory (enable sv::svar-p sv::name-p))))
  (b* (((vl-vardecl x) (vl-vardecl-fix x))
       (modalist (sv::modalist-fix modalist))
       (warnings nil)
       ((unless (vl-datatype-resolved-p x.type))
        (mv (fatal :type :vl-vardecl->svex-fail
                   :msg "~a0: Failed to resolve usertypes"
                   :args (list x))
            0 nil nil nil modalist))
       ((mv err size) (vl-datatype-size x.type))
       ((when (or err (not size)))
        (mv (fatal :type :vl-vardecl->svex-fail
                   :msg "~a0: Failed to size datatype ~a1: ~@2"
                   :args (list x x.type
                               (if err err "exact error unknown")))
            0 nil nil nil modalist))
       ((mv err subwire datamod modalist)
        (vl-datatype->mods x.type modalist))
       ((when err)
        (mv (fatal :type :vl-vardecl->svex-fail
                   :msg "~a0: Failed to process datatype ~a1: ~@2"
                   :args (list x x.type err))
            0 nil nil nil modalist))
       ((mv wire insts aliases)
        (vl-datatype-elem->mod-components x.name subwire self-lsb datamod)))
    (mv nil size
        (list wire) aliases insts modalist))
  ///
  (more-returns
   (modalist1 :name vars-of-vl-vardecl->svex-modalist
              (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                       (sv::svarlist-addr-p (sv::modalist-vars modalist1))))
   (aliases :name vars-of-vl-vardecl->svex-aliases
            (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))))



(define vl-vardecllist->svex ((x vl-vardecllist-p)
                              (modalist sv::modalist-p)
                              (interfacep
                               "controls whether we create aliases between the
                                local :self wire and the vars, as we must for the
                                vardecls within an interface"))
  :short "Collects svex module components for a list of vardecls, by collecting
          results from @(see vl-vardecl->svex)."
  :prepwork ((local (in-theory (disable cons-equal))))
  :returns (mv (warnings vl-warninglist-p)
               (width natp :rule-classes :type-prescription)
               (wires sv::wirelist-p)
               (aliases sv::lhspairs-p)
               (modinsts sv::modinstlist-p)
               (modalist1 sv::modalist-p))
  (b* (((when (atom x)) (mv nil 0 nil nil nil (sv::modalist-fix modalist)))
       (warnings nil)
       ((wmv warnings width2 wires2 aliases2 modinsts2 modalist)
        (vl-vardecllist->svex (cdr x) modalist interfacep))
       ((wmv warnings width1 wire1 aliases1 modinsts1 modalist)
        (vl-vardecl->svex (car x) modalist (and interfacep width2))))
    (mv warnings
        (+ width1 width2)
        (append-without-guard wire1 wires2)
        (append-without-guard aliases1 aliases2)
        (append-without-guard modinsts1 modinsts2)
        modalist))
  ///

  (more-returns
   (modalist1 :name vars-of-vl-vardecllist->svex-modalist
              (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                       (sv::svarlist-addr-p (sv::modalist-vars modalist1))))
   (aliases :name vars-of-vl-vardecllist->svex-aliases
            (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))))


;; (define vl-delay-primitive->svex-module ((x vl-atts-p) (modname stringp))
;;   :returns (s sv::module-p)
;;   (b* ((width-expr (cdr (hons-assoc-equal "VL_SVEX_PRIMITIVE_WIDTH" x)))
;;        ((unless (and width-expr
;;                      (vl-expr-resolved-p width-expr)
;;                      (< 0 (vl-resolved->val width-expr))))
;;         (cw "Warning: bad width expr for delay primitive ~s0: ~x1~%" modname width-expr)
;;         (sv::make-module))
;;        (width (vl-resolved->val width-expr)))
;;     ;; Keep in sync with vl-make-n-bit-delay-1!
;;     (sv::make-module :wires (list (sv::make-wire :name "in" :width width :lsb 0)
;;                                     (sv::make-wire :name "out" :width width :lsb 0))
;;                        :delays (list (cons (list (sv::make-lhrange :w width
;;                                                                      :atom (sv::make-lhatom-var
;;                                                                             :name "out" :rsh 0)))
;;                                            "in")))))


;; (define vl-primitive->svex-module ((x vl-atts-p) (modname stringp))
;;   :returns (s sv::module-p)
;;   (b* ((primitive-type-expr (cdr (hons-assoc-equal "VL_SVEX_PRIMITIVE" x)))
;;        ((unless (and primitive-type-expr
;;                      (vl-fast-atom-p primitive-type-expr)
;;                      (vl-fast-string-p (vl-atom->guts primitive-type-expr))))
;;         (cw "Warning: bad primitive type on module ~s0: ~x1~%" modname primitive-type-expr)
;;         (sv::make-module))
;;        (type (vl-string->value (vl-atom->guts primitive-type-expr)))
;;        ((when (equal type "delay"))
;;         (vl-delay-primitive->svex-module x modname)))
;;     (cw "Warning: unknown svex primitive type: ~s0~%" type)
;;     (sv::make-module)))

;; (local
;;  #!sv
;;  (defthm fast-alist-fork-when-modalist-fix-atom
;;    (implies (not (consp (modalist-fix x)))
;;             (modalist-equiv (fast-alist-fork x y) y))
;;    :hints(("Goal" :in-theory (enable modalist-fix fast-alist-fork)))))

(local
 #!sv
 (defthm member-modalist-vars-of-fast-alist-fork
   (implies (and (not (member v (modalist-vars x)))
                 (not (member v (modalist-vars y)))
                 (modalist-p x))
            (not (member v (modalist-vars (fast-alist-fork x y)))))
   :hints(("Goal" :in-theory (enable fast-alist-fork)
           :induct (fast-alist-fork x y)
           :expand ((modalist-vars x)
                    (modalist-p x)
                    (modalist-fix x)
                    (:free (x) (modalist-vars (cons x y))))))))

(define maybe-nat ((flag) (num natp))
  :returns (res maybe-natp :rule-classes :type-prescription)
  (and flag (lnfix num)))


(defines vl-genblob->svex-modules
  :prepwork ((local (defthm modname-p-when-consp
                      (implies (consp x)
                               (sv::modname-p x))
                      :hints(("Goal" :in-theory (enable sv::modname-p)))))
             (local (defthm name-p-when-stringp
                      (implies (stringp x)
                               (sv::name-p x))
                      :hints(("Goal" :in-theory (enable sv::name-p)))))
             (local (defthm name-p-when-integerp
                      (implies (integerp x)
                               (sv::name-p x))
                      :hints(("Goal" :in-theory (enable sv::name-p)))))
             (local (defthm name-p-when-anonymo
                      (sv::name-p (cons :anonymous x))
                      :hints(("Goal" :in-theory (enable sv::name-p)))))
             (local (defthm name-p-when-vl-scopeid-p
                      (implies (vl-scopeid-p x)
                               (sv::name-p x))
                      :hints(("Goal" :in-theory (enable sv::name-p)))))
             (local (in-theory (disable double-containment
                                        vl-warninglist-p-when-not-consp
                                        sv::modalist-p-when-not-consp)))
             (fty::set-deffixequiv-mutual-default-hints
              ((acl2::just-expand-mrec-default-hint 'fty::fnname id nil world)))
             (std::set-returnspec-mrec-default-hints
              ((acl2::just-expand-mrec-default-hint 'std::fnname id nil world)
               (and stable-under-simplificationp
                    `(:in-theory (e/d (sv::svarlist-addr-p-by-badguy)
                                      ,(acl2::recursivep 'std::fnname world))))))
             (local (in-theory (disable sv::svarlist-addr-p-when-subsetp-equal
                                        acl2::subsetp-member
                                        acl2::consp-under-iff-when-true-listp
                                        acl2::append-under-iff
                                        acl2::append-atom-under-list-equiv
                                        acl2::member-when-atom
                                        acl2::subsetp-append1
                                        acl2::subsetp-when-atom-right
                                        acl2::subsetp-when-atom-left
                                        acl2::consp-append
                                        member-equal-when-member-equal-of-cdr-under-iff
                                        default-cdr default-car
                                        acl2::maybe-natp-when-natp
                                        sv::svarlist-addr-p-by-badguy
                                        hons-shrink-alist-when-not-consp
                                        sv::svarlist-addr-p-when-not-consp
                                        acl2::append-when-not-consp
                                        consp-when-member-equal-of-vl-elabscopes-p)))
             (local (in-theory (enable sv::modalist-vars))))
  :verify-guards nil

  (define vl-genblock->svex-modules
    ((x vl-genblock-p)
     (elabindex  "outside of the scope")
     (modname sv::modname-p)
     (modalist sv::modalist-p)
     (self-lsb maybe-natp "indicates whether we are in an interface; if so, gives
                           the lsb of the outer block's wire at which to alias
                           the inner block's wire"))
    :returns (mv (warnings vl-warninglist-p)
                 (modalist1
                  (and (sv::modalist-p modalist1)
                       (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p (sv::modalist-vars modalist1)))))
                 (insts     sv::modinstlist-p)
                 (wires     sv::wirelist-p "containing, for interfaces, the block's wire")
                 (aliases   (and (sv::lhspairs-p aliases)
                                 (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))
                            "when interface, aliases between the new wire and the
                             self of the block, and between the new wire and the
                             self of the outer block")
                 (width natp "total width of all wires inside the genblock")
                 (new-elabindex))
    :measure (vl-genblob-genblock-count x)
    (b* ((modname (sv::modname-fix modname))
         (modalist (sv::modalist-fix modalist))
         (self-lsb (maybe-natp-fix self-lsb))
         ((vl-genblock x) (vl-genblock-fix x))
         (warnings nil)
         ((unless x.name)
          (mv (fatal :type :vl-programming-error
                     :msg "Expected block to be named: ~a0"
                     :args (list x))
              modalist
              nil nil nil 0
              elabindex))
         (modname (if (atom modname)
                      (list modname :genblock x.name)
                    (append-without-guard modname (list :genblock x.name))))
         (genblob (vl-sort-genelements x.elems :scopetype :vl-genblock :id x.name))
         ((wmv warnings mod modalist width elabindex)
          (vl-genblob->svex-modules genblob elabindex modname modalist self-lsb))
         (modalist (hons-acons modname mod modalist))
         (modinst (sv::make-modinst :modname modname
                                    :instname x.name))
         ((unless (and self-lsb (not (eql width 0))))
          (mv warnings modalist
              (list modinst) nil nil 0 elabindex))

         (wire (sv::make-wire :name x.name :width width :low-idx 0))
         (aliases (vlsv-aggregate-aliases x.name width self-lsb)))

      (mv warnings modalist (list modinst)
          (list wire) aliases width elabindex)))

  (define vl-genblob->svex-modules ((x vl-genblob-p)
                                    (elabindex "outside of the genblob scope")
                                    (modname sv::modname-p)
                                    (modalist sv::modalist-p)
                                    (interfacep "determines whether we create :self
                                                 wires aliased to the concatenation
                                                 of all the variables"))
    :short "Given a @(see vl-genblob), translate its contents into an svex @(see
            sv::module)."
    :long "<p>Mostly, this function delegates its work to other functions:</p>
<ul>
<li>@(see vl-vardecllist->svex) to process variable declarations</li>
<li>@(see vl-assigns->svex-assigns) to process assignments</li>
<li>@(see vl-modinstlist->svex-assigns/aliases) to process module instances.</li>
</ul>
<p>It also creates new modules for any generate blocks/arrays present.</p>"
    :returns (mv (warnings vl-warninglist-p)
                 (mod (and (sv::module-p mod)
                           (sv::svarlist-addr-p
                            (sv::module-vars mod))))
                 (modalist1
                  (and (sv::modalist-p modalist1)
                       (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p (sv::modalist-vars modalist1)))))
                 (width natp :rule-classes :type-prescription)
                 (new-elabindex))
    :measure (vl-genblob-count x)

    (b* ((warnings nil)
         (elabindex (vl-elabindex-push (vl-genblob-fix x)))
         ((vl-genblob x))
         ((wmv ?ok warnings ?new-x elabindex)
          ;; new-x isn't really relevant since we've already run
          ;; unparameterization before; we're just doing this to generate the
          ;; tables.
          (vl-genblob-elaborate x elabindex))
         (elabindex (vl-elabindex-sync-scopes))
         (ss (vl-elabindex->ss))
         (scopes (vl-elabindex->scopes))

         ((wmv warnings vars-width wires aliases datainsts modalist)
          (vl-vardecllist->svex x.vardecls (sv::modalist-fix modalist)
                                interfacep))
         ((wmv warnings assigns) (vl-assigns->svex-assigns x.assigns ss scopes nil))
         ((wmv warnings aliases) (vl-aliases->svex-aliases x.aliases ss scopes aliases))
         ((wmv warnings wires assigns aliases insts-width insts arraymod-alist)
          (vl-modinstlist->svex-assigns/aliases x.modinsts ss scopes wires assigns aliases modname (maybe-nat interfacep vars-width)))
         
         ((wmv warnings wires assigns aliases ginsts gatemod-alist)
          (vl-gateinstlist->svex-assigns/aliases x.gateinsts ss scopes wires assigns aliases modname))
         
         ((wmv warnings ifportwires ifportinsts ifportaliases ifportmod-alist ifports-width)
          (vl-interfaceports->svex x.ifports (vl-elabindex->ss) 
                                   (maybe-nat interfacep (+ vars-width insts-width))
                                   modname))
         
         (modalist (hons-shrink-alist ifportmod-alist (hons-shrink-alist gatemod-alist (hons-shrink-alist arraymod-alist modalist))))

         ((wmv warnings always-assigns)
          (vl-alwayslist->svex x.alwayses ss scopes))
         ((wmv warnings) (vl-initiallist-size-warnings x.initials ss scopes))
         ((wmv warnings) (vl-finallist-size-warnings x.finals ss scopes))

         ;; (delays (sv::delay-svarlist->delays (append-without-guard delayvars always-delayvars)))

         ((wmv warnings modalist gen-insts gen-wires gen-aliases gen-width elabindex)
          (vl-generates->svex-modules
           x.generates elabindex modname modalist
           (maybe-nat interfacep (+ vars-width insts-width ifports-width))))

         (totalwidth (+ vars-width insts-width ifports-width gen-width))

         (self-wire (and interfacep
                         (not (eql totalwidth 0))
                         (list (sv::make-wire :name :self :width totalwidth :low-idx 0))))

         (module (sv::make-module :wires (append-without-guard self-wire ifportwires wires gen-wires)
                                  :insts (append-without-guard ifportinsts datainsts ginsts insts gen-insts)
                                  :assigns (append-without-guard always-assigns assigns)
                                  :aliaspairs (append-without-guard ifportaliases aliases gen-aliases)))
         (modalist (hons-shrink-alist arraymod-alist modalist))
         (elabindex (vl-elabindex-undo)))
      (mv warnings module modalist totalwidth elabindex)))

  (define vl-generates->svex-modules
    ((x vl-genelementlist-p)
     (elabindex)
     (modname sv::modname-p)
     (modalist sv::modalist-p)
     (self-lsb maybe-natp "indicates whether we are in an interface; if so, gives
                           the lsb of the outer block's wire at which to alias
                           the inner block's wire"))

    :returns (mv (warnings vl-warninglist-p)
                 (modalist1
                  (and (sv::modalist-p modalist1)
                       (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p (sv::modalist-vars modalist1)))))
                 (insts     sv::modinstlist-p)
                 (wires     sv::wirelist-p)
                 (aliases   (and (sv::lhspairs-p aliases)
                                 (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))
                            "when interface, aliases between the new wire and the
                             self of the block, and between the new wire and the
                             self of the outer block")
                 (width     natp :rule-classes :type-prescription)
                 (new-elabindex))
    :measure (vl-genblob-generates-count x)
    (b* ((warnings nil)
         (self-lsb (maybe-natp-fix self-lsb))
         ((when (atom x)) (mv (ok) (sv::modalist-fix modalist) nil nil nil 0 elabindex))
         ((wmv warnings modalist insts2 wires2 aliases2 width2 elabindex)
          (vl-generates->svex-modules
           (cdr x) elabindex modname modalist self-lsb))
         ((wmv warnings modalist insts1 wires1 aliases1 width1 elabindex)
          (vl-generate->svex-modules
           (car x) elabindex modname modalist (and self-lsb (+ self-lsb width2)))))
      (mv warnings modalist
          (append-without-guard insts1 insts2)
          (append-without-guard wires1 wires2)
          (append-without-guard aliases1 aliases2)
          (+ width1 width2)
          elabindex)))


  (define vl-generate->svex-modules
    ((x vl-genelement-p)
     (elabindex)
     (modname sv::modname-p)
     (modalist sv::modalist-p)
     (self-lsb maybe-natp "indicates whether we are in an interface; if so, gives
                           the lsb of the outer block's wire at which to alias
                           the inner block's wire"))
    :returns (mv (warnings vl-warninglist-p)
                 (modalist1
                  (and (sv::modalist-p modalist1)
                       (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p (sv::modalist-vars modalist1)))))
                 (insts      sv::modinstlist-p)
                 (wires     sv::wirelist-p)
                 (aliases   (and (sv::lhspairs-p aliases)
                                 (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))
                            "when interface, aliases between the new wire and the
                             self of the block, and between the new wire and the
                             self of the outer block")
                 (width     natp :rule-classes :type-prescription)
                 (new-elabindex))
    :measure (vl-genblob-generate-count x)
    (b* ((warnings nil)
         (modalist (sv::modalist-fix modalist))
         (x (vl-genelement-fix x)))
      (vl-genelement-case x
        :vl-genbegin
        (vl-genblock->svex-modules x.block elabindex modname modalist self-lsb)

        :vl-genarray
        (b* ((modname (sv::modname-fix modname))
             ((unless x.name)
              (mv (fatal :type :vl-programming-error
                         :msg "Expected generate array to be named: ~a0"
                         :args (list x))
                  modalist nil nil nil 0 elabindex))
             (modname (if (atom modname)
                          (list modname :genarray x.name)
                        (append-without-guard modname (list :genarray x.name))))
             ;; This is a weird thing to do, but at the moment we need it to
             ;; make our scopes work out.  See the discussion under
             ;; vl-scopecontext-to-addr.
             (elabindex (vl-elabindex-push (make-vl-genblob :scopetype :vl-genarray
                                                            :id x.name)))
             ((wmv warnings modalist block-insts block-wires block-aliases block-width elabindex)
              (vl-genblocks->svex-modules x.blocks elabindex modname modalist self-lsb))
             (arraymod (sv::make-module :insts block-insts
                                        :wires block-wires
                                        :aliaspairs block-aliases))
             (modalist (hons-acons modname arraymod modalist))
             (elabindex (vl-elabindex-undo))
             ((unless (and self-lsb (not (eql block-width 0))))
              (mv warnings modalist
                  (list (sv::make-modinst :modname modname
                                          :instname x.name))
                  nil nil block-width elabindex))

             (array-wire (sv::make-wire :name x.name :width block-width :low-idx 0))
             (aliases (vlsv-aggregate-aliases x.name block-width self-lsb)))
          (mv warnings modalist
              (list (sv::make-modinst :modname modname
                                      :instname x.name))
              (list array-wire)
              aliases
              block-width
              elabindex))

        :otherwise
        (mv (fatal :type :vl-module->svex-fail
                   :msg "Unresolved generate block: ~a0"
                   :args (list (vl-genelement-fix x)))
            (sv::modalist-fix modalist) nil nil nil 0
            elabindex))))

  (define vl-genblocks->svex-modules
    ((x vl-genblocklist-p)
     (elabindex)
     (modname sv::modname-p)
     (modalist sv::modalist-p)
     (self-lsb maybe-natp "indicates whether we are in an interface; if so, gives
                           the lsb of the outer block's wire at which to alias
                           the inner block's wire"))
    :returns (mv (warnings vl-warninglist-p)
                 (modalist1
                  (and (sv::modalist-p modalist1)
                       (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p (sv::modalist-vars modalist1)))))
                 (insts sv::modinstlist-p)
                 (wires sv::wirelist-p)
                 (aliases   (and (sv::lhspairs-p aliases)
                                 (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))
                            "when interface, aliases between the new wire and the
                             self of the block, and between the new wire and the
                             self of the outer block")
                 (width natp :rule-classes :type-prescription)
                 (new-elabindex))
    :measure (vl-genblob-genblocklist-count x)
    (b* ((warnings nil)
         (self-lsb (maybe-natp-fix self-lsb))
         ((when (atom x)) (mv (ok) (sv::modalist-fix modalist) nil nil nil 0 elabindex))
         ((wmv warnings modalist insts2 wires2 aliases2 width2 elabindex)
          (vl-genblocks->svex-modules (cdr x) elabindex modname modalist self-lsb))
         ((wmv warnings modalist insts1 wires1 aliases1 width1 elabindex)
          (vl-genblock->svex-modules (car x) elabindex modname modalist
                                     (and self-lsb (+ self-lsb width2)))))
      (mv warnings modalist
          (append-without-guard insts1 insts2)
          (append-without-guard wires1 wires2)
          (append-without-guard aliases1 aliases2)
          (+ width1 width2)
          elabindex)))
  ///
  (verify-guards vl-genblob->svex-modules)

  (local (in-theory (disable cons-equal
                             vl-genblob->svex-modules
                             vl-generates->svex-modules
                             vl-generate->svex-modules
                             vl-genblocks->svex-modules
                             vl-genblock->svex-modules)))

  (deffixequiv-mutual vl-genblob->svex-modules))





(define vl-module->svex-module ((name stringp)
                                (elabindex "global scope")
                                (modalist sv::modalist-p))
  :short "Translate a VL module into an svex module, adding any auxiliary modules
          necessary."
  :long "<p>Mostly this function just calls @(see vl-genblob->svex-modules) to
do its work.  However, it also needs to take care of the module's interface
ports, by calling @(see vl-interfaceports->svex).</p>"
  :returns (mv (warnings vl-warninglist-p)
               (modalist1 (and (sv::modalist-p modalist1)
                               (implies
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist1))))
                          :hints(("Goal" :in-theory (enable sv::modalist-vars))))
               (new-elabindex))
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x))))
             (local (in-theory (enable sv::modname-p))))
  (b* ((modalist (sv::modalist-fix modalist))
       (name (string-fix name))
       (x (vl-scopestack-find-definition name (vl-elabindex->ss)))
       (warnings nil)
       ((unless (and x (eq (tag x) :vl-module)))
        (mv (warn :type :vl-module->svex-fail
                  :msg "Module not found: ~s0"
                  :args (list name))
            (sv::modalist-fix modalist)
            elabindex))
       ((vl-module x) x)
       (genblob (vl-module->genblob x))
       ((wmv warnings mod modalist ?width elabindex)
        (vl-genblob->svex-modules genblob elabindex x.name modalist nil)))
    (mv warnings (hons-acons x.name mod modalist) elabindex)))


(define vl-modulelist->svex-modalist
  ((x vl-modulelist-p)
   (elabindex "global scope")
   (modalist sv::modalist-p))
  :returns (mv (warnings vl-reportcard-p)
               (modalist1 (and (sv::modalist-p modalist1)
                               (implies
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist1)))))
               (new-elabindex))
  (b* (((when (atom x)) (mv nil (sv::modalist-fix modalist) elabindex))
       (name (vl-module->name (car x)))
       ((mv warnings modalist elabindex)
        (vl-module->svex-module name elabindex modalist))
       
       ((mv reportcard modalist elabindex)
        (vl-modulelist->svex-modalist (cdr x) elabindex modalist)))
    (mv (if warnings
            (cons (cons name warnings) reportcard)
          reportcard)
        modalist
        elabindex)))


(define vl-interface->svex-module ((name stringp)
                                   (elabindex "global scope")
                                   (modalist sv::modalist-p))
  :returns (mv (warnings vl-warninglist-p)
               (modalist1 (and (sv::modalist-p modalist1)
                               (implies
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist1))))
                          :hints(("Goal" :in-theory (enable sv::modalist-vars))))
               elabindex)
  :prepwork ((local (defthm vl-scope-p-when-vl-interface-p-strong
                      (implies (vl-interface-p x)
                               (vl-scope-p x))))
             (local (in-theory (enable sv::modname-p))))
  :short "Translate a VL interface definition into an svex module."
  :long "<p>We expect an interface to basically only contain variable
declarations.  We ignore modports.  The module generated for an interface is
much like that generated for a struct; it has a :self wire that is aliased to
the concatenation of all its other declared wires.</p>"
  (b* ((modalist (sv::modalist-fix modalist))
       (name (string-fix name))
       (x (vl-scopestack-find-definition name (vl-elabindex->ss)))
       (warnings nil)
       ((unless (and x (eq (tag x) :vl-interface)))
        (mv (warn :type :vl-interface->svex-fail
                  :msg "Interface not found: ~s0"
                  :args (list name))
            (sv::modalist-fix modalist)
            elabindex))
       ((vl-interface x) x)
       (genblob (vl-interface->genblob x))
       ((wmv warnings mod modalist ?width elabindex)
        (vl-genblob->svex-modules genblob elabindex x.name modalist t)))
    (mv warnings
        (hons-acons (sv::modname-fix name) mod modalist)
        elabindex)))

(define vl-interfacelist->svex-modalist
  ((x vl-interfacelist-p)
   (elabindex "global scope")
   (modalist sv::modalist-p))
  :returns (mv (warnings vl-reportcard-p)
               (modalist1 (and (sv::modalist-p modalist1)
                               (implies
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist1))))
                          :hints(("Goal" :in-theory (enable sv::modalist-vars))))
               (new-elabindex))
  (b* (((when (atom x)) (mv nil (sv::modalist-fix modalist) elabindex))
       (name (vl-interface->name (car x)))
       ((mv warnings modalist elabindex) (vl-interface->svex-module name elabindex modalist))

       ((mv reportcard modalist elabindex) (vl-interfacelist->svex-modalist (cdr x) elabindex modalist)))
    (mv (if warnings
            (cons (cons name warnings) reportcard)
          reportcard)
        modalist
        elabindex)))


(define vl-design->svex-modalist ((x vl-design-p))
  :parents (vl-design->svex-design)
  :short "Translate a simplified VL design into an SVEX modalist."
  :long "<p>This expects the input to be a VL modulelist that is
unparametrized, with resolved selects/ranges, always blocks processed into
flop/latch primitives, and all expressions sized.  A suitable series of
transforms is implemented in @(see vl-simplify-svex).</p>

<p>See @(see vl-hierarchy-svex-translation) for discussion of our approach to
this translation.</p>"
  :returns (mv (reportcard vl-reportcard-p)
               (svexmods (and (sv::modalist-p svexmods)
                              (sv::svarlist-addr-p
                               (sv::modalist-vars svexmods)))))
  (b* (((vl-design x) (vl-design-fix x))
       ((local-stobjs elabindex) (mv reportcard modalist elabindex))
       (elabindex (vl-elabindex-init x))
       ((mv reportcard1 modalist elabindex) (vl-modulelist->svex-modalist x.mods elabindex nil))
       ((mv reportcard2 modalist elabindex) (vl-interfacelist->svex-modalist x.interfaces elabindex modalist))
       (reportcard (vl-clean-reportcard (append-without-guard reportcard1 reportcard2))))
    (vl-scopestacks-free)
    (mv reportcard modalist elabindex)))
