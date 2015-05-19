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
(local (include-book "centaur/misc/arith-equivs" :dir :system))
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
instance arrays; see @(see vl-instarray-plainarg-nested-instance-alias) for details.</p>

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



(define vl-interface-size ((x vl-interface-p)
                           (ss vl-scopestack-p))
  :prepwork ((local (defthm nat-listp-remove-nil
                      (implies (maybe-nat-list-p x)
                               (nat-listp (remove nil x)))
                      :hints(("Goal" :in-theory (enable maybe-nat-list-p))))))
  :short "Computes the number of bits in all the variables in an interface."
  :returns (mv (warnings vl-warninglist-p)
               (size natp :rule-classes :type-prescription))
  (b* (((vl-interface x) (vl-interface-fix x))
       (ss (vl-scopestack-push x ss))
       ((mv warnings sizes) (vl-vardecllist-sizes x.vardecls ss)))
    (mv warnings (sum-nats (remove nil sizes)))))

(define vl-interfaceinst->svex ((name stringp "name of instance or interface port")
                                (ifname stringp "name of the interface")
                                (context anyp)
                                (ss vl-scopestack-p))
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
               (aliases sv::lhspairs-p))
  (b* ((warnings nil)
       (ifname (string-fix ifname))
       (name   (string-fix name))
       ((mv iface i-ss) (vl-scopestack-find-definition/ss ifname ss))
       ((unless (and iface (eq (tag iface) :vl-interface)))
        (mv (warn :type :vl-module->svex-fail
                  :msg "~a0: Interface not found: ~s1"
                  :args (list context ifname))
            nil nil))
       ((wmv warnings size) (vl-interface-size iface i-ss))
       ((unless (posp size))
        (mv warnings nil nil))
       (wire (sv::make-wire :name name
                              :width size
                              :low-idx 0))
       (wire-lhs (svex-lhs-from-name name :width size))
       (subself-var (sv::address->svar
                     (sv::make-address
                      :path (sv::make-path-scope :namespace name :subpath :self))))
       (subself-lhs (list (sv::make-lhrange :w size
                                              :atom (sv::make-lhatom-var
                                                     :name subself-var :rsh 0)))))
    (mv (ok) (list wire) (list (cons wire-lhs subself-lhs))))
  ///
  (local (in-theory (disable sv::lhs-vars-when-consp)))
  (defthm vars-of-vl-interfaceinst->svex
    (sv::svarlist-addr-p
     (sv::lhspairs-vars
      (mv-nth 2 (vl-interfaceinst->svex name ifname context ss))))
    :hints(("goal" :in-theory (enable sv::lhspairs-vars))
           (and stable-under-simplificationp
                '(:in-theory #!sv (enable lhspairs-vars lhatom-vars))))))


(define vl-interfaceport->svex ((x vl-interfaceport-p)
                                (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (wires sv::wirelist-p)
               (insts sv::modinstlist-p)
               (aliases sv::lhspairs-p))
  :short "Produces svex wires, insts, aliases for an interface port."
  :long "<p>Just adds a modinst to the outputs of @(see vl-interfaceinst->svex).</p>"
  :prepwork ((local (defthm modname-p-when-stringp
                      (implies (stringp x)
                               (sv::modname-p x))
                      :hints(("Goal" :in-theory (enable sv::modname-p)))))
             (local (defthm name-p-when-stringp
                      (implies (stringp x)
                               (sv::name-p x))
                      :hints(("Goal" :in-theory (enable sv::name-p))))))
  (b* (((vl-interfaceport x) (vl-interfaceport-fix x))
       (insts (list (sv::make-modinst :instname x.name :modname x.ifname)))
       ((mv warnings wires aliases)
        (vl-interfaceinst->svex x.name x.ifname x ss)))
    (mv warnings wires insts aliases))
  ///
  (defthm vars-of-vl-interfaceport->svex
    (sv::svarlist-addr-p
     (sv::lhspairs-vars
      (mv-nth 3 (vl-interfaceport->svex x ss))))))

(define vl-interfaceports->svex ((x vl-interfaceportlist-p)
                                 (ss vl-scopestack-p))
  :returns (mv (warnings vl-warninglist-p)
               (wires sv::wirelist-p)
               (insts sv::modinstlist-p)
               (aliases sv::lhspairs-p))
  (b* (((when (atom x)) (mv nil nil nil nil))
       (warnings nil)
       ((wmv warnings wires1 insts1 aliases1)
        (vl-interfaceport->svex (car x) ss))
       ((wmv warnings wires2 insts2 aliases2)
        (vl-interfaceports->svex (cdr x) ss)))
    (mv warnings
        (append-without-guard wires1 wires2)
        (append-without-guard insts1 insts2)
        (append-without-guard aliases1 aliases2)))
  ///

  (defthm vars-of-vl-interfaceports->svex
    (sv::svarlist-addr-p
     (sv::lhspairs-vars
      (mv-nth 3 (vl-interfaceports->svex x ss))))))



;; ;; (fty::deflist boolean-list :pred boolean-listp :elt-type booleanp
;; ;;   :elementp-of-nil t)

;; (define vl-plainarg-size-check ((x vl-plainarg-p)
;;                                 (y vl-port-p)
;;                                 (argindex natp)
;;                                 (inst-modname stringp)
;;                                 (instname stringp)
;;                                 (arraysize maybe-posp))
;;   :returns (warnings vl-warninglist-p)
;;   :prepwork ((local (in-theory (disable acl2::zp-open not
;;                                         integerp-when-natp))))
;;   :short "Creates warnings, if necessary, for arguments to a module instance or
;;           instance array."
;;   :long "<p>We check that the port connections are appropriately sized and that
;; interface ports are connected to interfaces.  If we warn about anything here,
;; we'll consider the whole module instance to be bad and skip it.</p>"
;;   (b* (((vl-plainarg x) (vl-plainarg-fix x))
;;        (instname (string-fix instname))
;;        (inst-modname (string-fix inst-modname))
;;        (warnings nil)
;;        (y (vl-port-fix y))
;;        ((when (eq (tag y) :vl-interfaceport))
;;         (b* (((when arraysize)
;;               (warn :type :vl-plainarg->svex-fail
;;                   :msg "~s0: interface ports in instance arrays not supported: ~s1"
;;                   :args (list instname (vl-interfaceport->name y))))
;;              ((unless (or (not x.expr)
;;                           (vl-idexpr-p x.expr)))
;;               (warn :type :vl-plainarg->svex-fail
;;                     :msg "Non-ID expression on interface port ~s0"
;;                     :args (list (vl-interfaceport->name y)))))
;;           (ok)))
;;        ((vl-regularport y))
;;        (y.name (or y.name (cat "unnamed_port_" (natstr argindex))))
;;        ((unless (and y.expr x.expr))
;;         ;; Blank port or port connection -- anything goes.
;;         (ok))
;;        (ywidth (vl-expr->finalwidth y.expr))
;;        (ytype (vl-expr->finaltype y.expr))
;;        ((unless (and (posp ywidth) ytype
;;                      (vl-expr-welltyped-p y.expr)))
;;         (warn :type :vl-plainarg->svex-fail
;;               :msg "Port expression unsized: ~s0, module ~s1"
;;               :args (list y.name inst-modname)))
;;        (xwidth (vl-expr->finalwidth x.expr))
;;        ((unless (and (vl-expr-welltyped-p x.expr)
;;                      (posp xwidth)))
;;         (warn :type :vl-plainarg->svex-fail
;;               :msg "Port connection not well-typed: ~s0, inst ~s1~%"
;;               :args (list y.name instname)))
;;        ((when (and arraysize
;;                    (not (or (eql ywidth xwidth)
;;                             (eql (* ywidth arraysize) xwidth)))))
;;         (warn :type :vl-plainarg->svex-fail
;;               :msg "Port connection has incompatible width for port ~
;;                         expression: ~s0, inst ~s1"
;;               :args (list y.name instname))))
;;     (ok))
;;   ///
;;   (more-returns
;;    (warnings :name true-listp-of-vl-plainarg-size-check
;;              true-listp :rule-classes :type-prescription))
;;   (defthm vl-plainarg-size-check-normalize-under-iff
;;     (implies (syntaxp (not (and (or (equal inst-modname ''"")
;;                                     (equal inst-modname ''nil))
;;                                 (or (equal instname ''"")
;;                                     (equal instname ''nil)))))
;;              (iff (vl-plainarg-size-check x y argidx inst-modname instname arraysize)
;;                   (vl-plainarg-size-check x y argidx nil "" arraysize)))))


;; (define vl-plainarglist-size-check ((x vl-plainarglist-p)
;;                                     (y vl-portlist-p)
;;                                     (argindex natp)
;;                                     (inst-modname stringp)
;;                                     (instname stringp)
;;                                     (arraysize maybe-posp))
;;   :verbosep t
;;   :guard (eql (len x) (len y))
;;   :returns (warnings vl-warninglist-p)
;;   (b* (((when (atom x)) nil)
;;        (warnings (vl-plainarg-size-check
;;                    (car x) (car y) argindex inst-modname instname arraysize))
;;        (warnings
;;         (vl-plainarglist-size-check (cdr x) (cdr y) (1+ (lnfix argindex))
;;                                     inst-modname instname arraysize)))
;;     (append-without-guard warnings warnings))
;;   ///
;;   (more-returns
;;    (warnings :name true-listp-of-vl-plainarglist-size-check
;;              true-listp :rule-classes :type-prescription))

;;   (defthm vl-plainarglist-size-check-normalize-under-iff
;;     (implies (syntaxp (not (and (or (equal inst-modname ''"")
;;                                     (equal inst-modname ''nil))
;;                                 (or (equal instname ''"")
;;                                     (equal instname ''nil)))))
;;              (iff (vl-plainarglist-size-check x y argidx inst-modname instname arraysize)
;;                   (vl-plainarglist-size-check x y argidx nil "" arraysize)))))





;; (define vl-plainarg->svex-assign-or-alias ((x vl-plainarg-p)
;;                                            (y vl-port-p)
;;                                            (argindex natp)
;;                                            (ss vl-scopestack-p)
;;                                            (fns sv::svex-alist-p)
;;                                            (inst-modname stringp)
;;                                            (inst-ss vl-scopestack-p)
;;                                            (instname stringp)
;;                                            (arraysize maybe-posp)
;;                                            (ctx acl2::any-p))
;;   :prepwork ((local (in-theory (disable vl-warninglist-p-when-not-consp
;;                                         acl2::append-when-not-consp
;;                                         rationalp-implies-acl2-numberp
;;                                         double-containment
;;                                         stringp-when-true-listp
;;                                         acl2::true-listp-when-atom
;;                                         acl2::list-fix-when-len-zero
;;                                         (tau-system)
;;                                         not)))
;;              (local (in-theory (enable sv::lhatom-vars))))
;;   :short "Creates an assignment or alias, as appropriate, for a port connection."
;;   :long "<p>Given a module instance such as</p>
;; @({ foo fooinst (.fa({a, c[1:0]}), .fb(b+1)) })
;; <p>this function produces aliases and assignments reflecting the port
;; connections.  In this case, @('fa') is connected to an lvalue expression but
;; @('fb') is not, which means we will create an alias for the @('fa') connection
;; but an assignment for the @('fb') connection.  We disregard the directionality
;; of the ports except to create a warning if we make an assignment to an output
;; port (i.e. if, in this example, @('fb') is an output).</p>"
;;   ;; :guard (not (vl-plainarg-size-check x y argindex inst-modname instname arraysize))
;;   :returns (mv (warnings vl-warninglist-p)
;;                (assigns sv::assigns-p "list of lhs/svex pairs (at most one)")
;;                (aliases sv::lhspairs-p "list of lhs/lhs pairs (at most one)")
;;                (replicatedp "For instance array, is the connection replicated (T)
;;                              or distributed (NIL)"))
;;   :guard-hints (;; ("goal" :in-theory (enable (force)
;;                 ;;                            vl-plainarg-size-check))
;;                 (and stable-under-simplificationp
;;                      '(:in-theory (enable sv::name-p)))
;;                 ;; (and stable-under-simplificationp
;;                 ;;      '(:in-theory (enable sv::lhssvex-p
;;                 ;;                           sv::lhssvex-unbounded-p
;;                 ;;                           sv::svex-concat
;;                 ;;                           sv::4vec-index-p)))
;;                 )
;;   (b* (((vl-plainarg x) (vl-plainarg-fix x))
;;        (y (vl-port-fix y))
;;        ;; (ss (vl-scopestack-fix ss))
;;        ;; (inst-ss (vl-scopestack-fix inst-ss))
;;        (?inst-modname (string-fix inst-modname))
;;        (instname     (string-fix instname))
;;        (warnings nil)

;;        ((when (eq (tag y) :vl-interfaceport))
;;         (b* (((vl-interfaceport y))
;;              ((when arraysize)
;;               (mv (fatal :type :vl-plainarg->svex-fal
;;                          :msg "~a0: Interface arrays aren't yet suported: ~a1"
;;                          :args (list ctx y))
;;                   nil nil nil))
;;              ((when (not x.expr)) (mv (ok) nil nil nil))
;;              ((mv interface if-ss) (vl-scopestack-find-definition/ss y.ifname ss))
;;              ((unless (and interface (eq (tag interface) :vl-interface)))
;;               (mv (fatal :type :vl-plainarg->svex-fail
;;                         :msg "~a2: Interface ~s0 for interface port ~s1 not found"
;;                         :args (list y.ifname y.name ctx))
;;                   nil nil nil))
;;              ((unless (vl-idexpr-p x.expr))
;;               (mv (fatal :type :vl-plainarg->svex-fail
;;                          :msg "~a0: Connection to interfaceport ~a1 must be a ~
;;                                simple ID, for the moment: ~a2"
;;                          :args (list ctx y.name x.expr))
;;                   nil nil nil))
;;              (xvar (sv::make-svex-var :name (sv::address->svar
;;                                                (sv::make-address
;;                                                 :path (sv::make-path-wire :name (vl-idexpr->name x.expr))))))
;;              (yvar (sv::make-svex-var :name (sv::address->svar
;;                                                (sv::make-address
;;                                                 :path
;;                                                 (sv::make-path-scope
;;                                                  :namespace instname
;;                                                  :subpath (sv::make-path-wire :name (vl-idexpr->name x.expr)))))))
;;              ;; ((mv ok yvar) (svex-add-namespace instname yvar))
;;              ;; (- (or ok (raise "Programming error: malformed variable in expression ~x0"
;;              ;;                  yvar)))
;;              ((wmv warnings ifwidth) (vl-interface-size interface if-ss))
;;              (warnings (append-without-guard warnings (ok)))
;;              (xsvex (sv::svex-concat ifwidth xvar (sv::svex-z)))
;;              (ysvex (sv::Svex-concat ifwidth yvar (sv::svex-z)))
;;              (xlhs (sv::svex->lhs xsvex))
;;              (ylhs (sv::svex->lhs ysvex)))
;;           (mv (ok) nil (list (cons xlhs ylhs)) nil)))


;;        ;; ((when (not y.name))
;;        ;;  (cw "Warning! No name for port ~x0, module ~s1~%" y inst-modname)
;;        ;;  (mv nil nil))
;;        ((vl-regularport y))
;;        (y.name (or y.name (cat "unnamed_port_" (natstr argindex))))
;;        ((unless (and y.expr x.expr))
;;         ;; Blank port or connection. Don't create an assign or alias.
;;         (mv (ok) nil nil nil))
;;        ((wmv warnings y-lhs y-type y-type-ss)
;;         (vl-expr-to-svex-lhs y.expr inst-ss ctx warnings))
;;        ((unless y-type)
;;         (mv warnings nil nil nil))
;;        ((wmv warnings x-svex x-type x-type-ss)
;;         (if arraysize
;;             ;; Can't just assume the datatype of y, b/c it might be that or it
;;             ;; might be arraysize * that.
;;             (vl-expr-to-svex-typed x.expr ss fns ctx warnings)
;;           (b* (((wmv warnings x-svex)
;;                 (vl-expr-to-svex-datatyped
;;                  x.expr y-type y-type-ss ss fns ctx warnings)))
;;             (mv warnings x-svex y-type y-type-ss))))

;;        ((unless x-type) (mv warnings nil nil nil))
;;        ((wmv ok warnings ?multi ?x-size ?y-size)
;;         (vl-instarray-plainarg-type-check
;;          arraysize y-type y-type-ss y.expr
;;          x-type x-type-ss x.expr ctx y.name warnings))

;;        ((unless ok) (mv warnings nil nil nil))

;;        (y-lhs (if arraysize
;;                   (list (sv::make-lhrange
;;                          :w y-size
;;                          :atom (sv::make-lhatom-var
;;                                 :name (sv::address->svar
;;                                        (sv::make-address
;;                                         :path (sv::make-path-wire :name y.name)))
;;                                 :rsh 0)))
;;                 y-lhs))

;;        ;; This seems wrong, what is supposed to happen if the port connection
;;        ;; is narrower than the port expression?
;;        ;; ;; truncate y to the width of x if necessary
;;        ;; (y-lhs (if (and (not arraysize)
;;        ;;                 (< xwidth ywidth))
;;        ;;            (sv::lhs-concat xwidth y-lhs nil)
;;        ;;          y-lhs))
;;        (xsvex (sv::svex-concat y-size
;;                                  (sv::svex-lhsrewrite x-svex 0 y-size)
;;                                  (sv::svex-z)))
;;        (x-lhsp (sv::lhssvex-p xsvex))
;;        ((unless x-lhsp)
;;         (mv (if (eq x.dir :vl-output)
;;                 (warn :type :vl-port-direction-mismatch
;;                       :msg  "Non-LHS expression on output ~
;;                                                port: inst ~s0, port ~x1, expr ~
;;                                                ~x2~%"
;;                       :args (list instname y.name x.expr))
;;               warnings)
;;             (list (cons y-lhs (sv::make-driver :value xsvex)))
;;             nil (not multi)))
;;        (x-lhs (sv::svex->lhs xsvex)))
;;     (mv warnings nil (list (cons y-lhs x-lhs))
;;         (not multi)))
;;   ///
;;   (defmvtypes vl-plainarg->svex-assign-or-alias (nil true-listp true-listp))

;;   (defret vl-plainarg->svex-assign-or-alias-vars
;;     (and (sv::svarlist-addr-p (sv::assigns-vars assigns))
;;          (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))
;;     :hints(("Goal" :in-theory (enable sv::lhspairs-vars sv::assigns-vars)))))





;; (define vl-plainarglist->svex-assigns/aliases ((x vl-plainarglist-p)
;;                                                (y vl-portlist-p)
;;                                                (argidx natp)
;;                                                (ss vl-scopestack-p)
;;                                                (fns sv::svex-alist-p)
;;                                                (inst-modname stringp)
;;                                                (inst-ss vl-scopestack-p)
;;                                                (instname stringp)
;;                                                (assigns sv::assigns-p)
;;                                                (aliases sv::lhspairs-p)
;;                                                (arraywidth maybe-posp)
;;                                                (ctx))
;;   :guard (eql (len x) (len y))
;;   :returns (mv (warnings vl-warninglist-p)
;;                (assigns1 sv::assigns-p)
;;                (aliases1 sv::lhspairs-p)
;;                (replicateds true-listp))
;;   (b* (((when (atom x))
;;         (mv nil
;;             (sv::assigns-fix assigns)
;;             (sv::lhspairs-fix aliases)
;;             nil))
;;        ((wmv warnings assigns1 aliases1 replic1)
;;         (vl-plainarg->svex-assign-or-alias (car x) (car y) argidx ss fns inst-modname inst-ss instname arraywidth ctx))
;;        ((wmv warnings assigns2 aliases2 replic2)
;;         (vl-plainarglist->svex-assigns/aliases
;;          (cdr x) (cdr y) (1+ (lnfix argidx))
;;          ss fns inst-modname inst-ss instname
;;          (append assigns1 assigns)
;;          (append aliases1 aliases)
;;          arraywidth ctx)))
;;     (mv (append-without-guard warnings warnings) assigns2 aliases2
;;         (cons replic1 replic2)))
;;   ///
;;   (defret vl-plainarglist->svex-assign-or-alias-vars
;;     (and (implies (sv::svarlist-addr-p (sv::assigns-vars assigns))
;;                   (sv::svarlist-addr-p (sv::assigns-vars assigns1)))
;;          (implies (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
;;                   (sv::svarlist-addr-p (sv::lhspairs-vars aliases1)))))
;;   (defret len-of-vl-plainarglist->svex-assign-or-alias-replicateds
;;     (equal (len replicateds)
;;            (len x))))


;; (define vl-instarray-plainarglist-nested-instance-alias
;;   ((y vl-portlist-p)
;;    (replicateds (eql (len replicateds) (len y)))
;;    (argindex natp)
;;    (instindex integerp)
;;    (instoffset natp)
;;    (inst-modname stringp)
;;    (inst-ss vl-scopestack-p)
;;    (instname stringp)
;;    (arraysize posp)
;;    (ctx))
;;   :returns (mv (warnings vl-warninglist-p)
;;                (aliases sv::lhspairs-p))
;;   (b* (((when (atom y)) (mv nil nil))
;;        ((wmv warnings aliases1)
;;         (vl-instarray-plainarg-nested-instance-alias
;;          (car y) (car replicateds)
;;          argindex instindex instoffset inst-modname inst-ss instname arraysize ctx))
;;        ((wmv warnings aliases2)
;;         (vl-instarray-plainarglist-nested-instance-alias
;;          (cdr y) (cdr replicateds)
;;          (1+ (lnfix argindex)) instindex instoffset inst-modname inst-ss instname arraysize ctx)))
;;     (mv (append-without-guard warnings warnings)
;;         (append-without-guard aliases1 aliases2)))
;;   ///
;;   (more-returns
;;    (aliases :name vars-of-vl-instarray-plainarglist-nested-instance-alias
;;             (sv::svarlist-addr-p (sv::lhspairs-vars aliases))
;;             :hints(("Goal" :in-theory (enable sv::lhspairs-vars))))))


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
        (mv (vmsg "Couldn't size datatype ~a0 for ~s1 port ~
                         expression ~a2"
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
       (compat-err (vl-compare-datatypes y-type x-type))
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
       (compat-err2 (vl-compare-datatypes y-type x-basetype))
       ((when compat-err2)
        ;; (cw "Args: ~x0~%" (list arraysize y-type y-expr x-type x-expr portname))
        (mv (vmsg "Incompatible type for connection to instancearray port ~s0 ~
                   (different slot types)." (string-fix portname))
            nil nil nil)))
    (mv nil t x-size y-size)))

(deftagsum vl-portinfo
  (:bad   ())
  (:blank ())
  (:interface ((portname stringp)
               (interface vl-interface-p)
               (argindex natp)
               (conn-name stringp)
               (port-lhs sv::lhs-p
                         "Svex expression form of the port.  Not scoped by the
                          instance name.")
               (conn-lhs sv::lhs-p)
               (size natp)))
  (:regular   ((portname stringp)
               (port-dir vl-maybe-direction-p)
               (argindex natp)
               (port-expr vl-expr-p)
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
               (conn-size posp)
               (replicatedp))
   :layout :alist))

(fty::deflist vl-portinfolist :elt-type vl-portinfo)







(define vl-portinfo-vars ((x vl-portinfo-p))
  :returns (vars sv::svarlist-p)
  (vl-portinfo-case x
    :interface (append (sv::lhs-vars x.port-lhs)
                       (sv::lhs-vars x.conn-lhs))
    :regular (append (sv::lhs-vars x.port-inner-lhs)
                     (sv::lhs-vars x.port-outer-lhs)
                     (sv::svex-vars x.conn-svex))
    :otherwise nil)
  ///
  (defthm svarlist-addr-p-of-vl-portinfo-vars-implies
    (implies (sv::svarlist-addr-p (vl-portinfo-vars x))
             (and (implies (vl-portinfo-case x :interface)
                           (b* (((vl-portinfo-interface x)))
                             (and (sv::svarlist-addr-p (sv::lhs-vars x.port-lhs))
                                  (sv::svarlist-addr-p (sv::lhs-vars x.conn-lhs)))))
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

(define vl-gate-plainarg-portinfo ((x vl-plainarg-p)
                                   (portname stringp)
                                   (portdir vl-direction-p)
                                   (argindex natp)
                                   (conf vl-svexconf-p
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
       (port-type (make-vl-coretype :name :vl-logic))
       ((wmv warnings x-svex x-type ?x-size)
        (vl-expr-to-svex-maybe-typed
         x.expr
         (if arraysize
             nil
           port-type)
         conf))

       ((unless x-type) (fail warnings))
       ((mv err ?multi x-size ?port-size)
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
                                 (sv::svex-lhsrewrite x-svex 0 x-size)
                                 (sv::svex-z))))
    (mv (ok)
        (make-vl-portinfo-regular
         :portname portname
         :port-dir (vl-direction-fix portdir)
         :argindex argindex
         :port-expr portexpr
         :conn-expr x.expr
         :port-inner-lhs port-lhs
         :port-outer-lhs port-outer-lhs
         :conn-svex xsvex
         :port-size 1
         :conn-size x-size
         :replicatedp (not multi))))
  ///
  (defret vars-of-vl-gate-plainarg-portinfo
    (sv::svarlist-addr-p (vl-portinfo-vars res))
    :hints(("Goal" :in-theory (enable vl-portinfo-vars sv::lhatom-vars)))))

(fty::deflist vl-directionlist :elt-type vl-direction-p
  :elementp-of-nil nil)

(define vl-gate-plainarglist-portinfo ((x vl-plainarglist-p)
                                       (portnames string-listp)
                                       (portdirs vl-directionlist-p)
                                       (argindex natp)
                                       (conf vl-svexconf-p)
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
           (car x) (car portnames) (car portdirs) argindex conf arraysize))
         ((wmv warnings portinfo2)
          (vl-gate-plainarglist-portinfo
           (cdr x) (cdr portnames) (cdr portdirs)
           (1+ (lnfix argindex)) conf arraysize)))
      (mv warnings
          (cons portinfo1 portinfo2))))
  ///
  (defret vars-of-vl-gate-plainarglist-portinfo
    (sv::svarlist-addr-p (vl-portinfolist-vars portinfo))
    :hints(("Goal" :in-theory (enable vl-portinfolist-vars)))))


(define vl-plainarg-portinfo ((x vl-plainarg-p)
                              (y vl-port-p)
                              (argindex natp)
                              (conf vl-svexconf-p
                                  "scopestack where the instance occurs")
                              (inst-modname stringp)
                              (inst-ss vl-scopestack-p
                                       "scopestack inside the instance's module")
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
       ((vl-svexconf conf))
       (y (vl-port-fix y))
       (arraysize (acl2::maybe-posp-fix arraysize))
       ;; (ss (vl-scopestack-fix conf))
       ;; (inst-ss (vl-scopestack-fix inst-ss))
       (?inst-modname (string-fix inst-modname))
       (warnings nil)
       ((unless x.expr) (mv (ok) (make-vl-portinfo-blank)))
       ((when (eq (tag y) :vl-interfaceport))
        (b* (((vl-interfaceport y))
             ((when arraysize)
              (fail (fatal :type :vl-plainarg->svex-fal
                           :msg "Interface arrays aren't yet suported: ~a0"
                           :args (list y))))
             ((mv interface if-ss) (vl-scopestack-find-definition/ss y.ifname conf.ss))
             ((unless (and interface (eq (tag interface) :vl-interface)))
              (fail (fatal :type :vl-plainarg->svex-fail
                        :msg "Interface ~s0 for interface port ~s1 not found"
                        :args (list y.ifname y.name))))
             ((unless (vl-idexpr-p x.expr))
              (fail (fatal :type :vl-plainarg->svex-fail
                         :msg "Connection to interfaceport ~a0 must be a ~
                               simple ID, for the moment: ~a1"
                         :args (list y.name x.expr))))
             (xvar (svex-var-from-name (vl-idexpr->name x.expr)))
             (yvar (svex-var-from-name y.name))
             ;; ((mv ok yvar) (svex-add-namespace instname yvar))
             ;; (- (or ok (raise "Programming error: malformed variable in expression ~x0"
             ;;                  yvar)))
             ((wmv warnings ifwidth) (vl-interface-size interface if-ss))
             (warnings (append-without-guard warnings (ok)))
             (xsvex (sv::svex-concat ifwidth xvar (sv::svex-z)))
             (ysvex (sv::Svex-concat ifwidth yvar (sv::svex-z)))
             (xlhs (sv::svex->lhs xsvex))
             (ylhs (sv::svex->lhs ysvex)))
          (mv (ok)
              (make-vl-portinfo-interface
               :portname y.name
               :interface interface
               :argindex argindex
               :conn-name (vl-idexpr->name x.expr)
               :port-lhs ylhs
               :conn-lhs xlhs
               :size ifwidth))))

       ;; ((when (not y.name))
       ;;  (cw "Warning! No name for port ~x0, module ~s1~%" y inst-modname)
       ;;  (mv nil nil))
       ((vl-regularport y))
       (y.name (or y.name (cat "unnamed_port_" (natstr argindex))))
       ((unless y.expr)
        (mv (ok) (make-vl-portinfo-blank)))
       ((wmv warnings y-lhs y-type)
        (vl-expr-to-svex-lhs y.expr (make-vl-svexconf :ss inst-ss)))
       ((unless y-type)
        ;; already warned
        (fail warnings))
       ((wmv warnings x-svex x-type ?x-size)
        (vl-expr-to-svex-maybe-typed
         x.expr (if arraysize nil y-type) conf))

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
                                 (sv::svex-lhsrewrite x-svex 0 x-size)
                                 (sv::svex-z))))
    (mv (ok)
        (make-vl-portinfo-regular
         :portname y.name
         :port-dir x.dir
         :argindex argindex
         :port-expr y.expr
         :conn-expr x.expr
         :port-inner-lhs y-lhs
         :port-outer-lhs y-outer-lhs
         :conn-svex xsvex
         :port-size y-size
         :conn-size x-size
         :replicatedp (not multi))))
  ///
  (defret vars-of-vl-plainarg-portinfo
    (sv::svarlist-addr-p (vl-portinfo-vars res))
    :hints(("Goal" :in-theory (enable vl-portinfo-vars sv::lhatom-vars)))))

(define vl-plainarglist-portinfo ((x vl-plainarglist-p)
                                  (y vl-portlist-p)
                                  (argindex natp)
                                  (conf vl-svexconf-p)
                                  (inst-modname stringp)
                                  (inst-ss vl-scopestack-p)
                                  (arraysize maybe-posp))
  :guard (eql (len x) (len y))
  :returns (mv (warnings vl-warninglist-p)
               (portinfo vl-portinfolist-p))
  (if (atom x)
      (mv nil nil)
    (b* ((warnings nil)
         ((wmv warnings portinfo1)
          (vl-plainarg-portinfo
           (car x) (car y) argindex conf inst-modname inst-ss arraysize))
         ((wmv warnings portinfo2)
          (vl-plainarglist-portinfo
           (cdr x) (cdr y) (1+ (lnfix argindex)) conf inst-modname inst-ss arraysize)))
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
      :interface
      (b* ((port-lhs-scoped (sv::lhs-add-namespace instname x.port-lhs)))
        (mv (ok) nil (list (cons port-lhs-scoped x.conn-lhs))))
      :regular
      (b* ((port-lhs-scoped (sv::lhs-add-namespace instname x.port-outer-lhs))
           ((when (sv::lhssvex-p x.conn-svex))
            (mv (ok)
                nil
                (list (cons port-lhs-scoped (sv::svex->lhs x.conn-svex))))))
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
  ((x vl-portinfolist-p)
   (instindex integerp)
   (instoffset natp)
   (inst-incr integerp)
   (inst-modname sv::modname-p))
  :guard (sv::svarlist-addr-p (vl-portinfolist-vars x))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable sv::name-p))))
  :returns (mv (aliases sv::lhspairs-p)
               (modinsts sv::modinstlist-p))
  (b* ((instindex (lifix instindex))
       (inst-modname (sv::modname-fix inst-modname))

       ((when (zp instoffset)) (mv nil nil))
       (aliases1
        (vl-portinfolist-instarray-nested-aliases x instindex (1- instoffset)))
       ((mv aliases2 modinsts2)
        (vl-instarray-nested-aliases
         x
         (+ (lifix instindex) (lifix inst-incr))
         (1- instoffset)
         inst-incr
         inst-modname)))
    (mv (append-without-guard aliases1 aliases2)
        (cons (sv::make-modinst :instname instindex
                                  :modname inst-modname)
              modinsts2)))
  ///
  (defret vars-of-vl-instarray-nested-instance-alias
    (implies (sv::svarlist-addr-p (vl-portinfolist-vars x))
             (sv::svarlist-addr-p (sv::lhspairs-vars aliases)))
    :hints(("Goal" :in-theory (enable sv::lhspairs-vars)))))



(define vl-instarray-port-wiredecls ((x vl-portinfo-p)
                                     (arraysize posp))
  :prepwork ((local (in-theory (enable sv::name-p))))
  :returns (wires sv::wirelist-p)
  ;; :guard (sv::svarlist-addr-p (vl-portinfo-vars x))
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable sv::name-p))))
  :short "Produces the wire declaration for the wire of an instance array module
          that consolidates all occurrences of a particular port."
  :long "<p>See @(see vl-instarray-plainarg-nested-instance-alias) for more
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
                                          (conf vl-svexconf-p)
                                          (wires   sv::wirelist-p)
                                          (assigns sv::assigns-p)
                                          (aliases sv::lhspairs-p)
                                          (context-mod sv::modname-p))
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

  (b* (((vl-modinst x) (vl-modinst-fix x))
       (wires (sv::wirelist-fix wires))
       (assigns (sv::assigns-fix assigns))
       (aliases (sv::lhspairs-fix aliases))
       (context-mod (sv::modname-fix context-mod))
       ((vl-svexconf conf))
       (warnings nil)

       ((when (eq (vl-arguments-kind x.portargs) :vl-arguments-named))
        (mv (fatal :type :vl-modinst->svex-fail
                   :msg "~a0: Unexpectedly had named arglist"
                   :args (list x))
            wires assigns aliases
            nil nil))
       (x.plainargs (vl-arguments->args x.portargs))
       ((mv inst-mod inst-ss) (vl-scopestack-find-definition/ss x.modname conf.ss))
       ((unless (and inst-mod
                     (or (eq (tag inst-mod) :vl-module)
                         (eq (tag inst-mod) :vl-interface))))
        (mv (fatal :type :vl-modinst->svex-fail
                  :msg "~a0: Unknown module ~s1"
                  :args (list x x.modname))
            wires assigns aliases
            nil nil))
       (inst-ss (vl-scopestack-push inst-mod inst-ss))
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
            wires assigns aliases
            nil nil))
       ((unless (vl-maybe-range-resolved-p x.range))
        (mv (fatal :type :vl-modinst->svex-fail
                  :msg "~a0: Unresolved instance array range"
                  :args (list x))
            wires assigns aliases nil nil))
       (arraywidth (and x.range (vl-range-size x.range)))

       ((unless x.instname)
        (mv (fatal :type :Vl-modinst->svex-fail
                   :msg "~a0: Unnamed module/interface instance not allowed"
                   :args (list x))
            wires assigns aliases nil nil))

       ((wmv warnings portinfo :ctx x)
        (vl-plainarglist-portinfo
         x.plainargs i.ports 0 conf inst-modname inst-ss arraywidth))

       ((wmv warnings portassigns portaliases :ctx x)
        (vl-portinfolist-to-svex-assigns/aliases portinfo x.instname))
       (assigns (append-without-guard portassigns assigns))
       (aliases (append-without-guard portaliases aliases))

       ((wmv warnings ifwires ifaliases :ctx x)
        (if (eq (tag inst-mod) :vl-interface)
            (vl-interfaceinst->svex x.instname x.modname x conf.ss)
          (mv nil nil nil)))
       (wires   (append-without-guard ifwires wires))
       (aliases (append-without-guard ifaliases aliases))

       ((unless arraywidth)
        ;; no instance array -> we're done.
        (mv (vl-warninglist-add-ctx warnings x) wires assigns aliases
            (list (sv::make-modinst :instname x.instname :modname x.modname))
            nil))

       (array-modname (list :arraymod context-mod x.instname))

       (modinst (sv::make-modinst :instname x.instname
                                    :modname array-modname))

       (arraymod-wiredecls (vl-instarray-portlist-wiredecls portinfo arraywidth))
       ((mv arraymod-aliases arraymod-modinsts)
        (vl-instarray-nested-aliases
         portinfo
         (vl-range-msbidx x.range)
         arraywidth
         (if (vl-range-revp x.range) 1 -1)
         inst-modname))

       (arraymod (sv::make-module :wires arraymod-wiredecls
                                    :insts arraymod-modinsts
                                    :aliaspairs arraymod-aliases)))

    (mv warnings wires assigns aliases
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
                                              (conf vl-svexconf-p)
                                              (wires   sv::wirelist-p)
                                              (assigns sv::assigns-p)
                                              (aliases sv::lhspairs-p)
                                              (context-mod sv::modname-p))
  :short "Collects svex module components for a list of module/interface instances,
          by collecting results from @(see vl-modinst->svex-assigns/aliases)."
  :returns (mv (warnings vl-warninglist-p)
               (wires1   sv::wirelist-p)
               (assigns1 sv::assigns-p)
               (aliases1 sv::lhspairs-p)
               (modinsts sv::modinstlist-p)
               (modalist sv::modalist-p))
  (b* ((warnings nil)
       ((when (atom x))
        (mv nil
            (sv::wirelist-fix wires)
            (sv::assigns-fix assigns)
            (sv::lhspairs-fix aliases)
            nil nil))
       ((wmv warnings wires assigns aliases insts1 modalist1)
        (vl-modinst->svex-assigns/aliases (car x) conf wires assigns aliases context-mod))
       ((wmv warnings wires assigns aliases insts2 modalist2)
        (vl-modinstlist->svex-assigns/aliases (cdr x) conf wires assigns aliases context-mod)))
    (mv warnings
        wires assigns aliases
        (append-without-guard insts1 insts2)
        (append-without-guard modalist1 modalist2)))
  ///
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
              (svex-ins (svex-vars-from-names ins))
              (assigns  (list (cons (svex-lhs-from-name "out")
                                    (sv::make-driver
                                     :value
                                     (case type
                                       (:vl-and  (svcall-join 'sv::bitand svex-ins))
                                       (:vl-nand (sv::svcall sv::bitnot (svcall-join 'sv::bitand svex-ins)))
                                       (:vl-or   (svcall-join 'sv::bitor svex-ins))
                                       (:vl-nor  (sv::svcall sv::bitnot (svcall-join 'sv::bitor svex-ins)))
                                       (:vl-xor  (svcall-join 'sv::bitxor svex-ins))
                                       (:vl-xnor (sv::svcall sv::bitnot (svcall-join 'sv::bitxor svex-ins))))))))
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
                 '(:in-theory (enable sv::assigns-vars))))))

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
                                          (conf vl-svexconf-p)
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
       ((vl-svexconf conf))
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
         x.args portnames portdirs 0 conf arraywidth))

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
            nil))

       (array-modname (list :arraymod context-mod x.name))

       (modinst (sv::make-modinst :instname x.name
                                    :modname array-modname))

       (arraymod-wiredecls (vl-instarray-portlist-wiredecls portinfo arraywidth))
       ((mv arraymod-aliases arraymod-modinsts)
        (vl-instarray-nested-aliases
         portinfo
         (vl-range-msbidx x.range)
         arraywidth
         (if (vl-range-revp x.range) 1 -1)
         gate-modname))

       (arraymod (sv::make-module :wires arraymod-wiredecls
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
                                              (conf vl-svexconf-p)
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
        (vl-gateinst->svex-assigns/aliases (car x) conf wires assigns aliases context-mod))
       ((wmv warnings wires assigns aliases insts2 modalist2)
        (vl-gateinstlist->svex-assigns/aliases (cdr x) conf wires assigns aliases context-mod)))
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


(define vl-assign->svex-assign ((x vl-assign-p)
                                (conf vl-svexconf-p))
  :returns (mv (warnings vl-warninglist-p)
               (assigns sv::assigns-p "The assignment"))
  :short "Turn a VL assignment into an SVEX assignment or delayed assignment."
  :long "<p>This just straightforwardly converts the LHS and RHS to svex
expressions, then converts the LHS into a @(see sv::lhs-p).</p>

<p>At the moment we only support a single-tick delay, just because for a
multi-tick we'd have to generate new names for the intermediate states.</p>"
  :prepwork ((local (in-theory (enable (force)))))
  (b* (((vl-assign x) (vl-assign-fix x))
       ((vl-svexconf conf))
       (warnings nil)
       ((wmv warnings lhs lhs-type :ctx x)
        (vl-expr-to-svex-lhs x.lvalue conf))
       ((unless lhs-type) (mv warnings nil))
       ((wmv warnings delay :ctx x) (vl-maybe-gatedelay->delay x.delay))
       ((wmv warnings svex-rhs :ctx x)
        (vl-expr-to-svex-datatyped x.expr lhs-type conf))
       ;; BOZO deal with drive strengths
       ((when (not delay))
        (mv warnings (list (cons lhs (sv::make-driver :value svex-rhs)))))
       (svex-rhs (sv::svex-add-delay svex-rhs delay)))
    (mv nil (list (cons lhs (sv::make-driver :value svex-rhs)))))

  ///
  (defmvtypes vl-assign->svex-assign (nil true-listp))

  (defret vars-of-vl-assign->svex-assign-assigns
    (sv::svarlist-addr-p (sv::assigns-vars assigns))
    :hints(("Goal" :in-theory (enable sv::assigns-vars)))))

(define vl-assigns->svex-assigns ((x vl-assignlist-p)
                                  (conf vl-svexconf-p)
                                  (assigns sv::assigns-p))
  :short "Collects svex module components for a list of assignments, by collecting
          results from @(see vl-assign->svex-assign)."
  :returns (mv (warnings vl-warninglist-p)
               (assigns1 sv::assigns-p))
  (if (atom x)
      (mv nil
          (sv::assigns-fix assigns))
    (b* ((warnings nil)
         ((wmv warnings assigns1) (vl-assign->svex-assign (car x) conf))
         ((wmv warnings assigns)
          (vl-assigns->svex-assigns (cdr x) conf
                                    (append assigns1 assigns))))
      (mv warnings assigns)))
  ///

  (more-returns
   (assigns1 :name vars-of-vl-assigns->svex-assigns-assigns
             (implies (sv::svarlist-addr-p (sv::assigns-vars assigns))
                      (sv::svarlist-addr-p (sv::assigns-vars assigns1))))))









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
       (var (sv::address->svar (sv::make-address
                                  :path (sv::make-path-wire :name name))))
       (wire-lhs (list (sv::make-lhrange :w subwire.width
                                           :atom (sv::make-lhatom-var :name var :rsh 0))))
       ((mv insts aliases1)
        (if submod
            (b* ((modinst (sv::make-modinst :instname name :modname submod))
                 (subself-var (sv::address->svar
                               (sv::make-address
                                :path (sv::make-path-scope :namespace name :subpath :self))))
                 (subself-lhs (list (sv::make-lhrange :w subwire.width
                                                        :atom (sv::make-lhatom-var
                                                               :name subself-var :rsh 0)))))
              (mv (list modinst) (list (cons wire-lhs subself-lhs))))
          (mv nil nil)))
       (aliases2
        (if self-lsb
            (b* ((self-lhs (list (sv::make-lhrange
                                  :w subwire.width
                                  :atom (sv::make-lhatom-var :name :self :rsh self-lsb)))))
              (list (cons wire-lhs self-lhs)))
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
                   :args (list x x.type err))
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
             (local (in-theory (disable double-containment
                                        vl-warninglist-p-when-not-consp
                                        sv::modalist-p-when-not-consp)))
             (fty::set-deffixequiv-mutual-default-hints
              ((acl2::just-expand-mrec-default-hint 'fty::fnname id nil world)))
             (std::set-returnspec-mrec-default-hints
              ((acl2::just-expand-mrec-default-hint 'std::fnname id nil world)))
             (local (in-theory (disable sv::svarlist-addr-p-when-subsetp-equal
                                        acl2::subsetp-member
                                        acl2::consp-under-iff-when-true-listp
                                        acl2::append-under-iff
                                        acl2::append-atom-under-list-equiv
                                        acl2::member-when-atom
                                        member-equal-when-member-equal-of-cdr-under-iff
                                        default-cdr default-car)))
             (local (in-theory (enable sv::modalist-vars))))
  :verify-guards nil

  (define vl-genblob->svex-modules ((x vl-genblob-p)
                                    (ss vl-scopestack-p)
                                    (modname sv::modname-p)
                                    (modalist sv::modalist-p))
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
                              (sv::svarlist-addr-p (sv::modalist-vars modalist1))))))
  :measure (vl-genblob-count x)

  (b* ((warnings nil)
       (ss (vl-scopestack-push (vl-genblob-fix x) ss))
       (blobconf (make-vl-svexconf :ss ss))
       ((vl-genblob x))
       ((wmv ?ok warnings ?new-x blobconf)
        ;; new-x isn't really relevant since we've already run
        ;; unparameterization before; we're just doing this to generate the
        ;; tables.
        (vl-genblob-elaborate x blobconf))

       ((wmv warnings ?width wires aliases datainsts modalist)
        (vl-vardecllist->svex x.vardecls (sv::modalist-fix modalist)
                              nil)) ;; no :self aliases
       ((wmv warnings assigns) (vl-assigns->svex-assigns x.assigns blobconf nil))
       ((wmv warnings wires assigns aliases insts arraymod-alist)
        (vl-modinstlist->svex-assigns/aliases x.modinsts blobconf wires assigns aliases modname))
       ((wmv warnings wires assigns aliases ginsts gatemod-alist)
        (vl-gateinstlist->svex-assigns/aliases x.gateinsts blobconf wires assigns aliases modname))
       (modalist (hons-shrink-alist gatemod-alist (hons-shrink-alist arraymod-alist modalist)))

       ((wmv warnings always-assigns)
        (vl-alwayslist->svex x.alwayses blobconf))

       ;; (delays (sv::delay-svarlist->delays (append-without-guard delayvars always-delayvars)))

       (- (vl-svexconf-free blobconf))

       ((wmv warnings modalist gen-insts)
        (vl-generates->svex-modules
         x.generates 0 ss modname modalist))

       (module (sv::make-module :wires wires
                                  :insts (append-without-guard gen-insts datainsts ginsts insts)
                                  :assigns (append-without-guard always-assigns assigns)
                                  :aliaspairs aliases))
       (modalist (hons-shrink-alist arraymod-alist modalist)))
    (mv warnings module modalist)))

  (define vl-generates->svex-modules ((x vl-genelementlist-p)
                                      (index natp)
                                      (ss vl-scopestack-p)
                                      (modname sv::modname-p)
                                      (modalist sv::modalist-p))

    :returns (mv (warnings vl-warninglist-p)
                 (modalist1
                  (and (sv::modalist-p modalist1)
                       (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p (sv::modalist-vars modalist1)))))
                 (insts     sv::modinstlist-p))
    :measure (vl-genblob-generates-count x)
    (b* ((warnings nil)
         ((when (atom x)) (mv (ok) (sv::modalist-fix modalist) nil))
         ((wmv warnings modalist insts1)
          (vl-generate->svex-modules
           (car x) (lnfix index) ss modname modalist))
         ((wmv warnings modalist insts2)
          (vl-generates->svex-modules
           (cdr x) (1+ (lnfix index)) ss modname modalist)))
      (mv warnings modalist (append-without-guard insts1 insts2))))

    (define vl-generate->svex-modules ((x vl-genelement-p)
                                       (index natp)
                                       (ss vl-scopestack-p)
                                       (modname sv::modname-p)
                                       (modalist sv::modalist-p))
      :returns (mv (warnings vl-warninglist-p)
                   (modalist1
                    (and (sv::modalist-p modalist1)
                         (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                  (sv::svarlist-addr-p (sv::modalist-vars modalist1)))))
                   (insts      sv::modinstlist-p))
      :measure (vl-genblob-generate-count x)
      (b* ((warnings nil))
        (vl-genelement-case x
          :vl-genblock
          (b* ((modname (sv::modname-fix modname))
               (index (lnfix index))
               (modname (if (atom modname)
                            (list modname :genblock (or x.name index))
                          (append-without-guard modname (list :genblock (or x.name index)))))
               (genblob (vl-sort-genelements x.elems :scopetype :vl-genblock))
               ((wmv warnings mod modalist)
                (vl-genblob->svex-modules genblob ss modname modalist)))
            (mv warnings (hons-acons modname mod modalist)
                (list (sv::make-modinst :modname modname
                                          :instname (or x.name (list :anonymous index))))))

          :vl-genarray
          (b* ((modname (sv::modname-fix modname))
               (index (lnfix index))
               (modname (if (atom modname)
                            (list modname :genarray (or x.name index))
                          (append-without-guard modname (list :genarray (or x.name index)))))
               ;; BOZO This is a weird thing to do, but at the moment we need it
               ;; to make our scopes work out.  To fix this, see the discussion
               ;; under vl-path-scope->svex-addr and fix that first.
               (ss (vl-scopestack-push (make-vl-genblob) ss))
               ((wmv warnings modalist block-insts)
                (vl-genarrayblocks->svex-modules x.blocks ss modname modalist))
               (arraymod (sv::make-module :insts block-insts))
               (modalist (hons-acons modname arraymod modalist)))
            (mv warnings modalist
                (list (sv::make-modinst :modname modname
                                          :instname (or x.name (list :anonymous index))))))
          :otherwise
          (mv (warn :type :vl-module->svex-fail
                    :msg "Unresolved generate block: ~a0"
                    :args (list (vl-genelement-fix x)))
              (sv::modalist-fix modalist) nil))))

    (define vl-genarrayblocks->svex-modules ((x vl-genarrayblocklist-p)
                                             (ss vl-scopestack-p)
                                             (modname sv::modname-p)
                                             (modalist sv::modalist-p))
      :returns (mv (warnings vl-warninglist-p)
                   (modalist1
                    (and (sv::modalist-p modalist1)
                         (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                  (sv::svarlist-addr-p (sv::modalist-vars modalist1)))))
                   (insts sv::modinstlist-p))
      :measure (vl-genblob-genarrayblocklist-count x)
      (b* ((warnings nil)
           ((when (atom x)) (mv (ok) (sv::modalist-fix modalist) nil))
           ((wmv warnings modalist insts1)
            (vl-genarrayblock->svex-modules (car x) ss modname modalist))
           ((wmv warnings modalist insts2)
            (vl-genarrayblocks->svex-modules (cdr x) ss modname modalist)))
        (mv warnings modalist (append-without-guard insts1 insts2))))

    (define vl-genarrayblock->svex-modules ((x vl-genarrayblock-p)
                                            (ss vl-scopestack-p)
                                            (modname sv::modname-p)
                                            (modalist sv::modalist-p))
      :returns (mv (warnings vl-warninglist-p)
                   (modalist1
                    (and (sv::modalist-p modalist1)
                         (implies (sv::svarlist-addr-p (sv::modalist-vars modalist))
                                  (sv::svarlist-addr-p (sv::modalist-vars modalist1)))))
                   (insts sv::modinstlist-p))
      :measure (vl-genblob-genarrayblock-count x)
      (b* ((warnings nil)
           ((vl-genarrayblock x))
           (modname (sv::modname-fix modname))
           (modname (append-without-guard modname (list x.index)))
           (genblob (vl-sort-genelements x.elems :scopetype :vl-genarrayblock))
           ((wmv warnings mod modalist)
            (vl-genblob->svex-modules genblob ss modname modalist)))
        (mv warnings (hons-acons modname mod modalist)
            (list (sv::make-modinst :modname modname :instname x.index)))))
    ///
    (verify-guards vl-genblob->svex-modules)

    (local (in-theory (disable cons-equal
                               vl-genblob->svex-modules
                               vl-generates->svex-modules
                               vl-generate->svex-modules
                               vl-genarrayblocks->svex-modules
                               vl-genarrayblock->svex-modules)))

    (deffixequiv-mutual vl-genblob->svex-modules))





(define vl-module->svex-module ((name stringp)
                                (ss vl-scopestack-p)
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
                          :hints(("Goal" :in-theory (enable sv::modalist-vars)))))
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x))))
             (local (in-theory (enable sv::modname-p))))
  (b* ((modalist (sv::modalist-fix modalist))
       (name (string-fix name))
       (x (vl-scopestack-find-definition name ss))
       (warnings nil)
       ((unless (and x (eq (tag x) :vl-module)))
        (mv (warn :type :vl-module->svex-fail
                  :msg "Module not found: ~s0"
                  :args (list name))
            (sv::modalist-fix modalist)))
       ((vl-module x) x)
       (genblob (vl-module->genblob x))
       ((wmv warnings mod modalist)
        (vl-genblob->svex-modules genblob ss x.name modalist))
       ((sv::module mod))
       ((wmv warnings ifwires ifinsts ifaliases)
        (vl-interfaceports->svex x.ifports ss))
       (mod (sv::change-module
             mod
             :wires (append-without-guard ifwires mod.wires)
             :insts (append-without-guard ifinsts mod.insts)
             :aliaspairs (append-without-guard ifaliases mod.aliaspairs))))
    (mv warnings (hons-acons x.name mod modalist))))


(define vl-modulelist->svex-modalist
  ((x vl-modulelist-p)
   (ss vl-scopestack-p)
   (modalist sv::modalist-p))
  :returns (mv (warnings vl-reportcard-p)
               (modalist1 (and (sv::modalist-p modalist1)
                               (implies
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist1))))))
  (b* (((when (atom x)) (mv nil (sv::modalist-fix modalist)))
       (name (vl-module->name (car x)))
       ((mv warnings modalist) (vl-module->svex-module name ss modalist))

       ((mv reportcard modalist) (vl-modulelist->svex-modalist (cdr x) ss modalist)))
    (mv (if warnings
            (cons (cons name warnings) reportcard)
          reportcard)
        modalist)))


(define vl-interface->svex-module ((name stringp)
                                   (ss vl-scopestack-p)
                                   (modalist sv::modalist-p))
  :returns (mv (warnings vl-warninglist-p)
               (modalist1 (and (sv::modalist-p modalist1)
                               (implies
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist1))))
                          :hints(("Goal" :in-theory (enable sv::modalist-vars)))))
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
       (x (vl-scopestack-find-definition name ss))
       (warnings nil)
       ((unless (and x (eq (tag x) :vl-interface)))
        (mv (warn :type :vl-interface->svex-fail
                  :msg "Interface not found: ~s0"
                  :args (list name))
            (sv::modalist-fix modalist)))
       ((vl-interface x) x)
       (?ss (vl-scopestack-push x ss))
       ;; CONVENTION: This returns only the vardecls whose types were
       ;; successfully resolved.  In interfaces, we consider only these
       ;; variables.  Any other variables won't have aliases set up so they'll
       ;; just be floating.
       ((wmv warnings totalwidth wires aliases datainsts modalist)
        (vl-vardecllist->svex x.vardecls (sv::modalist-fix modalist) t))
       (selfwire (and (not (eql totalwidth 0))
                      (sv::make-wire :name :self :width totalwidth :low-idx 0)))
       (mod (sv::make-module :wires (if selfwire (cons selfwire wires) wires)
                               :insts datainsts
                               :aliaspairs aliases)))
    (mv warnings
        (hons-acons (sv::modname-fix name) mod modalist))))

(define vl-interfacelist->svex-modalist
  ((x vl-interfacelist-p)
   (ss vl-scopestack-p)
   (modalist sv::modalist-p))
  :parents (sv::svex)
  :returns (mv (warnings vl-reportcard-p)
               (modalist1 (and (sv::modalist-p modalist1)
                               (implies
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist))
                                (sv::svarlist-addr-p
                                 (sv::modalist-vars modalist1))))
                          :hints(("Goal" :in-theory (enable sv::modalist-vars)))))
  (b* (((when (atom x)) (mv nil (sv::modalist-fix modalist)))
       (name (vl-interface->name (car x)))
       ((mv warnings modalist) (vl-interface->svex-module name ss modalist))

       ((mv reportcard modalist) (vl-interfacelist->svex-modalist (cdr x) ss modalist)))
    (mv (if warnings
            (cons (cons name warnings) reportcard)
          reportcard)
        modalist)))


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
       (ss (vl-scopestack-init x))
       ((mv reportcard1 modalist) (vl-modulelist->svex-modalist x.mods ss nil))
       ((mv reportcard2 modalist) (vl-interfacelist->svex-modalist x.interfaces ss modalist))
       (reportcard (vl-clean-reportcard (append-without-guard reportcard1 reportcard2))))
    (vl-scopestacks-free)
    (mv reportcard modalist)))
