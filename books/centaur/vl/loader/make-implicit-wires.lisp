; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "../mlib/allexprs")
(include-book "../mlib/context")
(include-book "../mlib/modnamespace")
(include-book "../mlib/stmt-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))


; We might consider unlocalizing some of these and finding them homes, but
; they're not necessarily that widely useful and, for instance, the modelement
; rules here might be kind of slow in general.

(local (defthm vl-modelement-p-when-vl-blockitem-p
         (implies (vl-blockitem-p x)
                  (vl-modelement-p x))
         :hints(("Goal" :in-theory (enable vl-blockitem-p vl-modelement-p)))))

(local (defthm vl-modelementlist-p-when-vl-blockitemlist-p
         (implies (vl-blockitemlist-p x)
                  (vl-modelementlist-p x))
         :hints(("Goal" :induct (len x)))))

;; (local (defthm acl2-count-of-vl-fundecl->decls
;;          (and (<= (acl2-count (vl-fundecl->decls x))
;;                   (acl2-count x))
;;               (implies (consp x)
;;                        (< (acl2-count (vl-fundecl->decls x))
;;                           (acl2-count x))))
;;          :hints(("Goal" :in-theory (enable vl-fundecl->decls)))
;;          :rule-classes ((:rewrite) (:linear))))

;; (local (defthm acl2-count-of-vl-compoundstmt->decls
;;          (and (<= (acl2-count (vl-compoundstmt->decls x))
;;                   (acl2-count x))
;;               (implies (consp x)
;;                        (< (acl2-count (vl-compoundstmt->decls x))
;;                           (acl2-count x))))
;;          :hints(("Goal" :in-theory (enable vl-compoundstmt->decls)))
;;          :rule-classes ((:rewrite) (:linear))))

;; (local (defthm vl-compoundstmt->type-forward-to-consp
;;          (implies (vl-compoundstmt->type x)
;;                   (consp x))
;;          :rule-classes :forward-chaining
;;          :hints(("Goal" :in-theory (enable vl-compoundstmt->type)))))



(defxdoc make-implicit-wires
  :parents (loader)
  :short "Add declarations for implicit wires."

  :long "<p>As part of the parsing process, even before a proper @(see
vl-module-p) structures are generated, we add explicit declarations for any
wires that are only implicitly declared.  This allows subsequent transforms to
expect that every wire should have a declaration.</p>


<h3>Implicit Wires in the Verilog-2005 Standard</h3>

<p>Verilog allows wires to be implicitly declared in certain cases.</p>

<p>When a wire is implicitly declared, its type is controlled by the
@('`default_nettype') compiler directive (Section 19.2).  But VL's @(see
preprocessor) does not yet support this directive and will cause an error if it
is used, so for now we can safely assume any implicit wires should just have
type @('wire').  (We can probably add support @('default_nettype') without too
much work, since our new approach of going through the module elements
sequentially means that we have easy access to location information.)</p>

<p>We think wires need to be declared, explicitly or implicitly, before being
used.  The Verilog-2005 standard seems not to explicitly say whether or not
this is the case, and the language at the start of Section 4.5 is somewhat
vague: we are supposed to assume implicit nets <i>in the absence of an explicit
declaration</i> in certain situations.  But later in 4.5 we find some language
that pretty strongly suggests we are only to consider whether or not there is
an explicit declaration <i>before</i> the use of the net: \"<i>and that
identifier has not been <b>declared previously</b> in the scope...</i>.\"</p>

<p>Section 4.5 outlines the conditions under which an implicit wire declaration
is supposed to be made.  In each case, the implicit declaration is to be added
to the nearest scope, but it seems like this only matters in the case of
@('generate') blocks, which we don't currently support.  (You might think that
it would matter for functions, tasks, and named blocks as well, but it doesn't
seem possible to use implicit wires in these contexts, see bullet #4 below for
details).</p>

<p>Note: I think that throughout Section 4.5, the words <i>port expression
declaration</i> are a typo that should be <i>port declaration</i>; nowhere else
in the Verilog-2005 standard do the words <i>port expression declaration</i>
occur, at least according to Acrobat's find function.)</p>

<h4>Case 1</h4>

<p>If there is a port declaration like @('input [3:0] i;') that has no
corresponding wire declaration, then we are supposed to infer an implicit net
with the vector width of the \"port expression declaration,\" which I think
means the @('[3:0]') part.  This seems basically reasonable when you just read
it, but there are a lot of subtle issues that arise; see #7 below for some
experiments.</p>

<p>Note that per 12.3.3, a port declaration like @('input wire [3:0] i;') is
treated as both an input declaration and an explicit wire declaration.  We
don't have to do anything special to handle this, because the parser
automatically builds both a @(see vl-portdecl-p) and a @(see vl-netdecl-p) for
such declarations; see @(srclink vl-parse-port-declaration-noatts).</p>

<h4>Case 2</h4>

<p>If there is an undeclared identifier in the terminal list of a primitive or
module instance, or in the left-hand side of a continuous assignment statement,
then we are supposed to infer an implicit, scalar net.</p>

<p>I think a \"primitive instance\" is supposed to mean either a gate instance
or a user-defined primitive instance.  See for instance Section 7.1.6, which
talks about \"primitive instance connection lists\" in reference to gates, and
11.6.6 where primitive terminals are distinguished from module ports.  So, this
means we should infer implicit wires in the ports/terminals of any instance,
regardless of whether it's a gate/udp/module.</p>


<h3>Implicit Wires in Verilog Implementations</h3>

<p>We developed some tests (see @('test/test-implicit.v')) to see how
Verilog-XL and NCVerilog handle implicit wires.  Here are our findings.</p>

<p><b>#1</b>.  As expected, both allow implicit wires to be inferred from the
arguments of gate and module instances.  This seems to be the intent of Case
2.</p>

<p><b>#2</b>.  As expected, both complain about undeclared wires on the
right-hand side of an @('assign') statement.  This seems to agree with Case
2.</p>

<p><b>#3</b>.  As expected, NCVerilog allows us to infer implicit nets from the
left-hand sides of @('assign') elements.  Unfortunately, Verilog-XL complains
about such wires, which seems to contradict the Verilog-2005 standard.  As a
compromise, our approach is to mimick NCVerilog and infer the implicit net, but
warn that some other tools like Verilog-XL may not allow the construct.</p>

<p>A subtle case is, what if #2 and #3 overlap, i.e., an undeclared wire occurs
on both the left-hand and right-hand sides?  NCVerilog seems to process the
left-hand side first, and hence it allows us to infer an implicit wire for
@('w') when we give it an assignment like @('assign w = w').  This isn't
entirely contrived; someone might occasionally write things like @('assign {a,
abar} = {foo, ~a}').</p>

<p><b>#4</b>.  Mostly as expected, neither tool allows undeclared wires on
either side of an assignment in an always block.  The tools even reject
implicit wires in procedural continuous assignments, e.g., @('always @(b)
assign w = a;').  But this seems arguably incorrect: is not a procedural
continuous assignment also a continuous assignment, whose LHS should therefore
be able to contain implicit wires?</p>

<p>We mimick these tools and disallow the implicit net, even thought the spec
might perhaps be interpreted as allowing it, because it allows us to avoid
certain scoping issues.</p>

<p>In particular, suppose we see a procedural continuous assignment statement,
@('assign w = ...'), where @('w') is not declared.  If this statement occurs in
a task or a named block within an initial/always statement, should the
declaration for @('w') be added to the module or to this more local scope?  I'm
not sure.  So, the good thing about not inferring implicit nets for these
assignments is that I don't have to be able to answer the question, because I'm
not going to infer a net anyway.</p>

<p><b>#5</b>.  As expected, neither implementation tolerates undeclared wires
on either side of assignments in function bodies.  This seems perfectly
reasonable since functions aren't allowed to have procedural continuous
assignments (10.4.4 E).</p>

<p><b>#6</b> As expected, both Verilog-XL and NCVerilog require that all wires
be declared (either explicitly or implicitly) before they are used.  For
instance, they if @('a') is declared but @('w') is not, then they reject code
fragments such as:</p>

@({
assign a = w;   // error here, saying w is undeclared
wire w;
})

<p>And also for code like this:</p>

@({
not(a, w);
wire w;         // error here, saying w is implicitly declared above
})


<p><b>#7</b> The whole declare-before-use thing is pretty strange for ports.
Suppose @('c') is a port of the module.  Then, both NCVerilog and Verilog-XL
will complain if you try to write:</p>

@({
wire c2 = c;    // error here, saying c is not declared.
input c;
})

<p>Verilog-XL seems to require the port declaration to come before the wire
declaration, if any.  That is, it considers the following an error, whereas
NCVerilog allows it:</p>

@({
wire c;
input c;
})

<p>This seems to hold for implicit declarations, too.  For instance, Verilog-XL
rejects the following, but NCVerilog allows it:</p>

@({
buf(c, c2);     // implicit declaration of wire c here
input c;
})

<p>But both Verilog-XL and NCVerilog allow the following, even though you might
think the buf gate would introduce an implicit declaration of @('c') that would
conflict with the explicit declaration.</p>

@({
input c;
buf(c, c2);
wire c;
})

<p>We try to be permissive and mimick NCVerilog, but add a (non-fatal) warning
if a wire's net declaration comes before its port declaration to explain that
some other tools do not permit this.</p>


<h3>Other Notes</h3>

<p>In previous versions of VL, we allowed declarations to come in any order,
and inferred an implicit wire whenever a wire was used in a context that
permitted it.  We now try to be more faithful to other Verilog systems and
require that wires be declared before their first uses, since this seems like
the right way to interpret the Verilog-2005 standard.</p>

<p>We add declarations for implicit wires before we even construct a proper
@(see vl-module-p).  This makes it easy for us to consider the order of module
elements, without having to rely on some technique such as the @(see
vl-location-p)s associated with module elements, which could be unreliable if a
module spans multiple files, e.g., because of includes.</p>

<p>With regard to Case 1, we add a net declaration for each port declaration
that is missing a corresponding wire declaration.  In the process, we make sure
that at least some declaration (be it a wire or port declaration) of each port
occurs before every use of the port.  If only a wire declaration occurs before
some use of the port wire, we issue a non-fatal warning saying that Verilog-XL
does not tolerate this ordering.</p>

<p>When we add implicit wires for ports, we use the range of the port
declaration, which seems to be correct with respect to the \"vector width of
the port declaration expression,\" described above.  We also keep the
signedness of the port, which isn't discussed above, but appears to be the
correct thing to do; see @(see portdecl-sign) for details.  We place the
implicit wire declaration at the same location as the corresponding port
declaration, which seems like the easiest place to put it.  We also mark each
implicit wire declaration with the @('VL_PORT_IMPLICIT') attribute, though we
have no particular use for this.</p>

<p>With regard to Case 2, we add one-bit wire declarations for any undeclared
wires that occur within the port arguments of gate and module instances, and
which occur in the left-hand sides of continuous assignments.  For assignments,
we always issue a non-fatal warning that says Verilog-XL doesn't add implicit
nets here, and we always process the left-hand side first (like NCVerilog).  We
add the wire declarations at the locations in which they are implicitly
declared, and mark them with the @('VL_IMPLICIT') attribute, which is useful in
@(see typo-detection).</p>")



; FEATURE-CREEP WARNING.  It is tempting to try to do a lot here, e.g., we
; might want to check for any illegally redefined wires, compatibility between
; port and net declarations, etc.  But after some false starts down this road,
; I think this is a mistake.
;
; We only need to care about the order of elements to (1) properly handle
; adding implicit wires, and (2) make sure things are defined before being
; used.  The well-formedness checks that, e.g., make sure nothing is multiply
; defined, that the ports/netdecls agree, etc., really don't need to consider
; module element order, so keep them separate!

(define vl-make-ordinary-implicit-wires
  :parents (make-implicit-wires)
  :short "Generate net declarations for one-bit implicit wires."
  ((loc   vl-location-p)
   (names string-listp))
  :returns (nets vl-netdecllist-p)
  :long "<p>We are given @('x'), a string list that should initially contain
the names of some implicit wires that we are supposed to introduce, and
@('loc'), a @(see vl-location-p) that should be the @('minloc') for the module.
We produce a list of one-bit @(see vl-netdecl-p)s, one for each name in
@('x').</p>"

  (if (consp names)
      (cons (make-vl-netdecl :name (car names)
                             :type :vl-wire
                             :loc loc
                             :atts (list (cons "VL_IMPLICIT" nil)))
            (vl-make-ordinary-implicit-wires loc (cdr names)))
    nil)
  ///
  (defthm vl-netdecllist->names-of-vl-make-ordinary-implicit-wires
    (equal (vl-netdecllist->names (vl-make-ordinary-implicit-wires loc names))
           (string-list-fix names))))


(define vl-modinst-exprs-for-implicit-wires
  :parents (make-implicit-wires)
  :short "Get the expressions from a module instance, for making implicit wires."
  ((x vl-modinst-p))
  :returns
  (mv (main vl-exprlist-p
            "The expressions from the modinst's port list, where implicit wires
             are allowed.")
      (other vl-exprlist-p
             "The other expressions in the module instance (its range,
              parameter list, etc.) where implicit wires aren't allowed."))
  (b* (((vl-modinst x) x))
    (mv (vl-arguments-allexprs x.portargs)
        (append (vl-maybe-range-allexprs x.range)
                (vl-arguments-allexprs x.paramargs)
                (vl-maybe-gatedelay-allexprs x.delay))))
  ///
  (defmvtypes vl-modinst-exprs-for-implicit-wires (true-listp true-listp))

  (defthm vl-modinst-exprs-for-implicit-wires-complete
    ;; Just to make sure we keep ths up to date if we ever change
    ;; vl-modinst-allexprs
    (let ((ret (vl-modinst-exprs-for-implicit-wires x)))
      (set-equiv (append (mv-nth 0 ret)
                         (mv-nth 1 ret))
                 (vl-modinst-allexprs x)))
    :hints(("Goal" :in-theory (enable set-equiv vl-modinst-allexprs)))))



(define vl-gateinst-exprs-for-implicit-wires
  :parents (make-implicit-wires)
  :short "Gets the expressions from a gate instance, for making implicit wires."
  ((x vl-gateinst-p))
  :returns
  (mv (main vl-exprlist-p
            "The expressions from the gateinst's port list, where implicit
             wires are allowed.")
      (other vl-exprlist-p
             "The other expressions in the gate instance (its range, delay)
             where implicit wires aren't allowed."))
  (b* (((vl-gateinst x) x))
    (mv (vl-plainarglist-allexprs x.args)
        (append (vl-maybe-range-allexprs x.range)
                (vl-maybe-gatedelay-allexprs x.delay))))
  ///
  (defmvtypes vl-gateinst-exprs-for-implicit-wires (true-listp true-listp))
  (defthm vl-gateinst-exprs-for-implicit-wires-complete
    ;; Just to make sure we keep ths up to date if we ever change
    ;; vl-gateinst-allexprs
    (let ((ret (vl-gateinst-exprs-for-implicit-wires x)))
      (set-equiv (append (mv-nth 0 ret)
                             (mv-nth 1 ret))
                     (vl-gateinst-allexprs x)))
    :hints(("Goal" :in-theory (enable set-equiv vl-gateinst-allexprs)))))



(define vl-remove-declared-wires
  :parents (vl-make-implicit-wires)
  :short "Filter names to remove wires that we've already seen declarations
for, whether they're port declarations or ordinary declarations."

  ((names string-listp)
   (portdecls "Fast alist binding names of declared (port) wires to anything.")
   (decls     "Fast alist binding names of declared (regular) wires to anything."))
  :returns
  (implicit string-listp "Subset of @('names') that don't have declarations.")
  (b* (((when (atom names))
        nil)
       (name1 (string-fix (car names)))
       ((when (or (hons-get name1 decls)
                  (hons-get name1 portdecls)))
        (vl-remove-declared-wires (cdr names) portdecls decls)))
    (cons name1 (vl-remove-declared-wires (cdr names) portdecls decls))))


(define vl-warn-about-undeclared-wires
  :parents (vl-make-implicit-wires)
  :short "Add fatal warnings about names that are used but not declared."

  ((ctx       vl-modelement-p "Where we saw these names.")
   (names     string-listp    "The names we saw.")
   (portdecls "Fast alist binding names of declared (port) wires to anything.")
   (decls     "Fast alist binding names of declared (regular) wires to anything.")
   (warnings  vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((ctx        (vl-modelement-fix ctx))
       (undeclared (mergesort (vl-remove-declared-wires names portdecls decls)))
       ((when (atom undeclared))
        (ok)))
    (fatal :type :vl-warn-undeclared
           :msg (if (atom (cdr undeclared))
                    "~a0: identifier ~w1 is used but not yet declared."
                  "~a0: identifiers ~&2 are used but not yet declared.")
           :args (list ctx (car undeclared) undeclared))))


(define vl-blockitem-check-undeclared
  :parents (vl-make-implicit-wires)
  :short "Check for undeclared wires in an arbitrary @(see vl-blockitem-p), and
extends @('decls') with the newly declared name."

  ((x         vl-blockitem-p "Arbitrary block item to process.")
   (portdecls "Fast alist binding names of declared (port) wires to anything.")
   (decls     "Fast alist binding names of declared (regular) wires to anything.")
   (warnings  vl-warninglist-p))
  :returns
  (mv (new-warnings vl-warninglist-p)
      (new-decls    "Extended @('decls') alist."))
  (b* ((x (vl-blockitem-fix x))
       ((mv name exprs)
        (case (tag x)
          (:vl-vardecl   (mv (vl-vardecl->name x)   (vl-vardecl-allexprs x)))
          (otherwise     (mv (vl-paramdecl->name x) (vl-paramdecl-allexprs x)))))

       ;; First, make sure all the names used in expressions like ranges and
       ;; array dimensions have been declared.  Then, add a binding for the
       ;; declaration.  Doing it in this order lets us catch garbage like
       ;; reg [r:0] r.
       (used-names (vl-exprlist-names exprs))
       (warnings   (vl-warn-about-undeclared-wires x used-names portdecls decls warnings))
       (decls      (hons-acons name nil decls)))
    (mv warnings decls)))


(define vl-blockitemlist-check-undeclared
  :parents (vl-make-implicit-wires)
  :short "Extends @(see vl-blockitem-check-undeclared) across a @(see
vl-blockitemlist-p)."
  ((x vl-blockitemlist-p)
   (portdecls "Fast alist binding names of declared (port) wires to anything.")
   (decls     "Fast alist binding names of declared (regular) wires to anything.")
   (warnings  vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (decls))
  (b* (((when (atom x))
        (mv (ok) decls))
       ((mv warnings decls)
        (vl-blockitem-check-undeclared (car x) portdecls decls warnings)))
    (vl-blockitemlist-check-undeclared (cdr x) portdecls decls warnings)))


(defines vl-stmt-check-undeclared
  :parents (vl-make-implicit-wires)
  :short "Check an arbitrary @(see vl-stmt-p) for uses of undeclared names."

  :long "<p>Most statements are totally straightforward; we just need to make
sure that all identifiers used anywhere within them have been declared.</p>

<p>Named blocks are the only complication.  They have their own scope and can
have their own declarations, which come before their sub-statements.  So, if we
see a named block, we basically fork the decls to create a local namespace, add
all of the local declarations to it, and then check all the sub-statements in
this extended namespace.</p>"

  (define vl-stmt-check-undeclared
    ((ctx       vl-modelement-p "Where this statement occurs.")
     (x         vl-stmt-p       "The statement to process.")
     (portdecls "Fast alist binding names of declared (port) wires to anything.")
     (decls     "Fast alist binding names of declared (regular) wires to anything.")
     (warnings vl-warninglist-p))
    :returns (new-warnings vl-warninglist-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* ((x (vl-stmt-fix x))

         ((when (vl-atomicstmt-p x))
          (b* ((used-names (vl-exprlist-names (vl-stmt-allexprs x)))
               (warnings   (vl-warn-about-undeclared-wires ctx used-names portdecls decls warnings)))
            warnings))

         ((when (eq (vl-stmt-kind x) :vl-blockstmt))
          (b* (((vl-blockstmt x) x)
               ;; Initially the local-decls will just be the current decls
               ;; we've seen, since things in the module's scope can still be
               ;; referenced from within the named block.
               (local-decls (hons-shrink-alist decls nil))
               ;; Add in all local declarations.
               ((mv warnings local-decls)
                (vl-blockitemlist-check-undeclared x.decls portdecls local-decls warnings))
               ;; Check all the sub-statements in the extended scope.
               (warnings (vl-stmtlist-check-undeclared ctx x.stmts portdecls local-decls warnings)))
            ;; Note that a named block doesn't have any other kinds of
            ;; expressions (i.e., x.ctrl and x.exprs are necessarily empty).
            ;; So, there's nothing to check other than the statements, and
            ;; hence we're already done and can now throw away the local scope.
            (fast-alist-free local-decls)
            warnings))

         ;; No other statement has its own scope, but some kinds of statements
         ;; (e.g., case statements, for loops, timing statements) have their
         ;; own expressions, so we need to check those.

         ;; We don't use vl-stmt-allexprs here because it also grabs the exprs
         ;; for sub-statements, which could be incorrect because a sub-block
         ;; statement of course needs to be checked w.r.t. its local scope.
         ;; So, we instead use this ugly sort of way to grab only the local
         ;; expressions.  We don't have to collect from x.decls since this
         ;; isn't a block statement.
         (local-exprs (append (vl-maybe-delayoreventcontrol-allexprs
                               (vl-compoundstmt->ctrl x))
                              (vl-compoundstmt->exprs x)))
         (local-names (vl-exprlist-names local-exprs))
         (warnings    (vl-warn-about-undeclared-wires ctx local-names portdecls decls warnings)))

      ;; Finally check the substatements.
      (vl-stmtlist-check-undeclared ctx (vl-compoundstmt->stmts x) portdecls decls warnings)))

    (define vl-stmtlist-check-undeclared
      ((ctx vl-modelement-p)
       (x   vl-stmtlist-p)
       (portdecls)
       (decls)
       (warnings vl-warninglist-p))
      :returns (new-warnings vl-warninglist-p)
      :measure (vl-stmtlist-count x)
      (b* (((when (atom x))
            (ok))
           (warnings (vl-stmt-check-undeclared ctx (car x) portdecls decls warnings)))
        (vl-stmtlist-check-undeclared ctx (cdr x) portdecls decls warnings)))

    ///
    (verify-guards vl-stmt-check-undeclared)
    (deffixequiv-mutual vl-stmt-check-undeclared))



(define vl-fundecl-check-undeclared
  :parents (vl-make-implicit-wires)
  :short "Check an arbitrary @(see vl-fundecl-p) for uses of undeclared names."

  :long "<p>Function declarations are tricky because they can have their own
declarations and hence we need to treat them basically like a named block
statement.</p>

<p>BOZO a problem with our approach is that paramterized function inputs won't
exactly work, e.g., for</p>

@({
function foo ;
  parameter p = 4;
  input [p-1:0] in;
  ...
endfunction
})

<p>We will think that @('p') is undeclared when we see @('in'), because we
aren't maintaining the mixed order of inputs and parameters.</p>

<p>Well, this is a pretty obscure, so I don't want to fix it until it becomes a
problem.</p>"

  ((x         vl-fundecl-p)
   (portdecls "Fast alist binding names of declared (port) wires to anything.")
   (decls     "Fast alist binding names of declared (regular) wires to anything.")
   (warnings  vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((x (vl-fundecl-fix x))
       ((vl-fundecl x) x)

       ;; Check for undeclared names in the non-local parts (the inputs and
       ;; return value range.)  It's not quite right to do the inputs here, as
       ;; described above, but in practice it shouldn't be much of a problem.
       (other-names (vl-exprlist-names (append (vl-taskportlist-allexprs x.inputs)
                                               (vl-maybe-range-allexprs x.rrange))))
       (warnings    (vl-warn-about-undeclared-wires x other-names portdecls decls warnings))

       ;; Now make a local scope and add the local declarations, as in named
       ;; block statements.
       (local-decls (hons-shrink-alist decls nil))

       ;; Now check/add the block items.  As we do this, we're acting like the
       ;; inputs haven't been declared yet.  That's not quite right, but it
       ;; should be practically pretty reasonable since it's not valid to refer
       ;; to an input in the other declarations.
       ((mv warnings local-decls)
        (vl-blockitemlist-check-undeclared x.decls portdecls local-decls warnings))

       ;; Okay, now add the inputs to the local scope, since it's valid to
       ;; refer to them in the body.  Also add in the function's name since it
       ;; can be a valid return value.
       (local-decls  (make-fal (pairlis$ (vl-taskportlist->names x.inputs) nil) local-decls))
       (local-decls  (hons-acons x.name nil local-decls))

       ;; The local scope is constructed, check the function's body.
       (warnings (vl-stmt-check-undeclared x x.body portdecls local-decls warnings)))
    ;; That's it, all done with the local scope.
    (fast-alist-free local-decls)
    warnings))


(define vl-taskdecl-check-undeclared
  :parents (vl-make-implicit-wires)
  :short "Check an arbitrary @(see vl-taskdecl-p) for uses of undeclared
names."
  :long "<p>This is nearly identical to @(see vl-fundecl-check-undeclared) and
it has the same problems with parameters.</p>"

  ((x         vl-taskdecl-p)
   (portdecls "Fast alist binding names of declared (port) wires to anything.")
   (decls     "Fast alist binding names of declared (regular) wires to anything.")
   (warnings  vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((x (vl-taskdecl-fix x))
       ((vl-taskdecl x) x)

       ;; Check for undeclared names in the task's visible ports.  It's not
       ;; quite right to do the ports here if they have parameters, as
       ;; described above, but in practice it shouldn't be much of a problem.
       (other-names (vl-exprlist-names (vl-taskportlist-allexprs x.ports)))
       (warnings    (vl-warn-about-undeclared-wires x other-names portdecls decls warnings))

       ;; Now make a local scope and add the local declarations, as in named
       ;; block statements.
       (local-decls (hons-shrink-alist decls nil))

       ;; Now check/add the block items.  As we do this, we're acting like the
       ;; ports haven't been declared yet.  That's not quite right, but it
       ;; should be practically pretty reasonable since it's not valid to refer
       ;; to a port in the other declarations.
       ((mv warnings local-decls)
        (vl-blockitemlist-check-undeclared x.decls portdecls local-decls warnings))

       ;; Okay, now add the ports to the local scope, since it's valid to
       ;; refer to them in the body.
       (local-decls (make-fal (pairlis$ (vl-taskportlist->names x.ports) nil) local-decls))

       ;; The local scope is constructed, check the task's body.
       (warnings (vl-stmt-check-undeclared x x.body portdecls local-decls warnings)))

    ;; That's it, all done with the local scope.
    (fast-alist-free local-decls)
    warnings))


(define vl-make-implicit-wires-aux
  :parents (make-implicit-wires)
  :short "Main function for adding implicit wires."

  ((x vl-modelementlist-p
      "Module elements to process, should be in the same order in which they
       were parsed.")
   (portdecls
    "A fast alist that binds the names (strings) of port declarations we've
     seen to their associated declarations.")
   (decls
    "A fast alist that binds the names (strings) of all other kinds of
     declarations to @('nil').  We include bindings here for any wires we've
     added implicit declarations for.")
   (acc
    "An accumulator for module elements which starts out as @('nil') and
     essentially becomes a copy of @('x'), along with any implicit wire
     declarations that we've added.  Items are accumulated in reverse order."
    vl-modelementlist-p)
   (warnings vl-warninglist-p
             "An ordinary @(see warnings) accumulator, which we may extend with
              fatal warnings (e.g., for undeclared identifiers) or non-fatal warnings
              (e.g., for compatibility warnings like <i>Verilog-XL doesn't
              infer an implicit wire here.</i>)."))

  :returns (mv (new-warnings vl-warninglist-p)
               (portdecls    "Extended fast alist.")
               (decls        "Extended fast alist.")
               (acc          vl-modelementlist-p))

  :long "<p>Note that to keep this code simple, we don't try to defend against
multiply declared names here.</p>

<p>We don't try to add any port declarations here, because we have to sort of
get through the whole module to make sure there isn't an explicit declaration
later on.  We handle that in @(see vl-make-implicit-wires).</p>"

  :verbosep t
  :measure (len x)
  :hooks ((:fix
           :hints (("Goal"
                    :expand ((:free (portdecls decls acc warnings)
                              (VL-MAKE-IMPLICIT-WIRES-AUX (VL-MODELEMENTLIST-FIX X) PORTDECLS DECLS ACC WARNINGS))
                             (:free (portdecls decls acc warnings)
                              (VL-MAKE-IMPLICIT-WIRES-AUX X PORTDECLS DECLS ACC WARNINGS)))))))

  (b* ((x        (vl-modelementlist-fix x))
       (warnings (vl-warninglist-fix warnings))
       (acc      (vl-modelementlist-fix acc))

       ((when (atom x))
        (mv warnings portdecls decls acc))

       (elem (vl-modelement-fix (car x)))
       (tag  (tag elem))

       ((when (eq tag :vl-port))
        ;; We shouldn't see any ports.
        (raise "We shouldn't see ports here.")
        (vl-make-implicit-wires-aux (cdr x) portdecls decls acc warnings))

       ((when (eq tag :vl-portdecl))
        ;; We have to first make sure that there aren't undeclared
        ;; identifiers being used in the range, then record that a
        ;; declaration was made.  Doing it in this order lets us catch
        ;; garbage like input [in:0] in;
        (b* ((names     (vl-exprlist-names (vl-portdecl-allexprs elem)))
             (warnings  (vl-warn-about-undeclared-wires elem names portdecls decls warnings))
             (portdecls (hons-acons (vl-portdecl->name elem) elem portdecls))
             (acc       (cons elem acc)))
          (vl-make-implicit-wires-aux (cdr x) portdecls decls acc warnings)))

       ((when (or (eq tag :vl-vardecl)
                  (eq tag :vl-paramdecl)))
        (b* (((mv warnings decls)
              (vl-blockitem-check-undeclared elem portdecls decls warnings))
             (acc (cons elem acc)))
          (vl-make-implicit-wires-aux (cdr x) portdecls decls acc warnings)))

       ((when (eq tag :vl-netdecl))
        ;; Same as block items, really.
        (b* ((names     (vl-exprlist-names (vl-netdecl-allexprs elem)))
             (warnings  (vl-warn-about-undeclared-wires elem names portdecls decls warnings))
             (decls     (hons-acons (vl-netdecl->name elem) nil decls))
             (acc       (cons elem acc)))
          (vl-make-implicit-wires-aux (cdr x) portdecls decls acc warnings)))

       ;; Module and gate instances are relatively simple.  First, make sure
       ;; all the identifiers in their non-port expressions (like ranges and
       ;; parameter arguments) are declared.  Then, gather all identifiers
       ;; in their port arguments, and add declarations for any of them that
       ;; are not declared.

       ((mv inst-p loc main-exprs other-exprs)
        (case tag
          (:vl-modinst
           (b* ((loc  (vl-modinst->loc elem))
                ((mv main other) (vl-modinst-exprs-for-implicit-wires elem)))
             (mv t loc main other)))
          (:vl-gateinst
           (b* ((loc  (vl-gateinst->loc elem))
                ((mv main other) (vl-gateinst-exprs-for-implicit-wires elem)))
             (mv t loc main other)))
          (otherwise
           (mv nil nil nil nil))))

       ((when inst-p)
        (b* ((other-names (vl-exprlist-names other-exprs))
             (main-names  (vl-exprlist-names main-exprs))
             (warnings    (vl-warn-about-undeclared-wires elem other-names portdecls decls warnings))
             (imp-names   (mergesort (vl-remove-declared-wires main-names portdecls decls)))
             (imp-nets    (vl-make-ordinary-implicit-wires loc imp-names))
             (decls       (make-fal (pairlis$ imp-names nil) decls))
             (acc         (revappend imp-nets acc)) ;; revappend keeps them in mergesorted-name order
             (acc         (cons elem acc)))
          (vl-make-implicit-wires-aux (cdr x) portdecls decls acc warnings)))

       ;; Assignments are a little complicated to add compatibility
       ;; warnings, but it still isn't too bad.

       ((when (eq tag :vl-assign))
        (b* (((vl-assign elem) elem)
             (lhs-names        (vl-expr-names elem.lvalue))
             (imp-lhs          (mergesort (vl-remove-declared-wires lhs-names portdecls decls)))
             (warnings
              (if (not imp-lhs)
                  warnings
                (cons (make-vl-warning
                       :type :vl-tricky-implicit
                       :msg "~a0: wire~s1 ~&2 ~s3 implicitly declared by ~
                                the left-hand side of this assignment.  This ~
                                is perfectly valid according to the Verilog-2005 ~
                                standard, but some Verilog tools tools (like ~
                                Verilog-XL) do not support it, so for better ~
                                compatibility you may wish to add ~s4."
                       :args (list elem
                                   (if (vl-plural-p imp-lhs) "s" "")
                                   imp-lhs
                                   (if (vl-plural-p imp-lhs) "are" "is")
                                   (if (vl-plural-p imp-lhs)
                                       "explicit declarations for these wires"
                                     "an explicit declaration of this wire"))
                       :fatalp nil
                       :fn 'vl-make-implicit-wires-aux)
                      warnings)))
             (imp-nets   (vl-make-ordinary-implicit-wires elem.loc imp-lhs))
             (decls      (make-fal (pairlis$ imp-lhs nil) decls))
             (acc        (revappend imp-nets acc))

             ;; Okay, all done adding implicit nets for the LHS.  Now make sure
             ;; all the other expressions are using declared ids.
             (other-names (vl-exprlist-names (cons elem.expr (vl-maybe-gatedelay-allexprs elem.delay))))
             (warnings    (vl-warn-about-undeclared-wires elem other-names portdecls decls warnings))
             (acc         (cons elem acc)))
          (vl-make-implicit-wires-aux (cdr x) portdecls decls acc warnings)))



       ((when (or (eq tag :vl-initial)
                  (eq tag :vl-always)))
        ;; Statements are tricky because of named blocks, but we've already
        ;; dealt with how to handle them, and they can't introduce any
        ;; implicit wires, so this is easy.
        (b* ((stmt     (if (eq tag :vl-initial)
                           (vl-initial->stmt elem)
                         (vl-always->stmt elem)))
             (warnings (vl-stmt-check-undeclared elem stmt portdecls decls warnings))
             (acc      (cons elem acc)))
          (vl-make-implicit-wires-aux (cdr x) portdecls decls acc warnings)))

       ((when (eq tag :vl-fundecl))
        ;; Functions are tricky because they have their own scope, but we've
        ;; already dealt with how to handle them, and they can't introduce
        ;; any implicit wires, so this is easy.
        (b* ((warnings (vl-fundecl-check-undeclared elem portdecls decls warnings))
             (decls    (hons-acons (vl-fundecl->name elem) nil decls))
             (acc      (cons elem acc)))
          (vl-make-implicit-wires-aux (cdr x) portdecls decls acc warnings)))

       ((when (eq tag :vl-taskdecl))
        ;; Tasks are tricky because they have their own scope, but we've
        ;; already dealt with how to handle them, and they can't introduce
        ;; any implicit wires, so this is easy.
        (b* ((warnings (vl-taskdecl-check-undeclared elem portdecls decls warnings))
             (decls    (hons-acons (vl-taskdecl->name elem) nil decls))
             (acc      (cons elem acc)))
          (vl-make-implicit-wires-aux (cdr x) portdecls decls acc warnings)))

       )

    (impossible)
    (mv warnings portdecls decls acc))
  ///
  (defthm vl-portdecllist-p-of-alist-vals-of-vl-make-implicit-wires-aux
    (implies (force (vl-portdecllist-p (alist-vals portdecls)))
             (vl-portdecllist-p
              (alist-vals (mv-nth 1 (vl-make-implicit-wires-aux x portdecls decls acc warnings)))))))


(define vl-make-port-implicit-wires
  :parents (make-implicit-wires)
  :short "@(call vl-make-port-implicit-wires) generates net declarations for
ports that don't have corresponding net declarations."

  ((portdecls "Alist binding names to port declarations."
              (vl-portdecllist-p (alist-vals portdecls)))
   (decls     "Alist binding names declared in the module to @('nil')."))

  :hooks nil ;; bozo wtf kind of crazy thing is this trying to prove?
  :verbosep t

  :returns
  (implicit vl-netdecllist-p
            "A list of new net declarations, one for each port declaration
             without a corresponding ordinary declaration.")

  :long "<p>BOZO what about scalaredp, vectoredp, cstrength, delay?  I think we
don't care, but it might be good to look into this again.</p>"

  (b* (((when (atom portdecls))
        nil)

       ((when (atom (car portdecls)))
        ;; Bad alist convention
        (vl-make-port-implicit-wires (cdr portdecls) decls))

       ((vl-portdecl portdecl) (cdar portdecls))
       ((when (hons-get portdecl.name decls))
        ;; Already declared, nothing to add.
        (vl-make-port-implicit-wires (cdr portdecls) decls))

       (new-decl (make-vl-netdecl :name    portdecl.name
                                  :type    :vl-wire
                                  :range   portdecl.range
                                  :atts    (cons (cons "VL_PORT_IMPLICIT" nil) portdecl.atts)
                                  :signedp portdecl.signedp
                                  :loc     portdecl.loc)))
    (cons new-decl
          (vl-make-port-implicit-wires (cdr portdecls) decls))))


(define vl-make-implicit-wires
  :parents (make-implicit-wires)
  :short "Augment a list of module elements with declarations for any implicit
nets, and make sure that every identifier being used has a declaration."

  ((elems vl-modelementlist-p
          "All of the module elements from a single module, in the order they
           were parsed.")
   (warnings vl-warninglist-p
             "An ordinary @(see warnings) accumulator, which may be extended
              with fatal and/or nonfatal warnings."))
  :returns
  (mv (new-elems vl-modelementlist-p
                 "Extended version of @('elems'), perhaps with new declarations
                  for implicit wires.")
      (new-warnings vl-warninglist-p))

  :long "<p>We try to add declarations for any implicit wires.  Unless there is
a fatal warning, the resulting module element list will have declarations for
all of its identifiers.</p>"

    (b* (((mv warnings portdecls decls acc)
          (vl-make-implicit-wires-aux elems nil nil nil warnings))
         (implicit-port-decls
          (vl-make-port-implicit-wires portdecls decls))
         (- (fast-alist-free portdecls))
         (- (fast-alist-free decls))
         (new-elems (revappend-without-guard acc implicit-port-decls)))
      (mv new-elems warnings)))

