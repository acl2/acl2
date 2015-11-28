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
(include-book "shadowcheck")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc make-implicit-wires
  :parents (annotate)
  :short "Create explicit declarations for implicit wires.  This is generally
the first step after parsing a design."

  :long "<p>Verilog allows wires to be implicitly declared in certain cases.
For instance, even if @('w') has not yet been declared, you can write things
like:</p>

@({
    assign w = &in;
})

<p>and we are to assume that @('w') is a one-bit wire.  This is mostly
straightforward but there are some subtleties; see @(see
implicit-wires-minutia) for more discussion.</p>

<p>Our general approach to handling these wires in VL is to add explicit
declarations for them.  Having explicit declarations seems like a generally
good idea.  For instance, it allows us to easily check for conflicting
declarations with the same name, and to generally assume that when we look
something up we should get a real declaration for it.</p>

<p>Historically, VL added explicit declarations for these wires as part of the
@(see loader), even before a proper @(see vl-module-p) structures were
generated, which allowed us to easily consider the order of module elements.
But when we added support for SystemVerilog @('import') statements, we found
this approach to be tricky.  In particular, to decide whether we need to add a
declaration for some particular wire @('foo'), we now need to consider whether
@('foo') is defined by any imported package.  For this to work, we really want
to be able to inspect the whole @(see vl-design) while making implicit wires.
We therefore decided to split making implicit wires out of the parser and into
a separate transform.</p>

<h3>Note: Special Transform!</h3>

<p>This transform is unique and we generally expect to run it as the first step
after parsing.  Normally it is invoked as part of @(see annotate).  It is also
closely related to @(see shadowcheck)&mdash;indeed, it invokes
shadowcheck&mdash; and the two should generally be regarded as a single,
unified transition from just-parsed modules to a more canonical form.</p>

<p>The special thing about @('make-implicit-wires') and @('shadowcheck') is
that these transforms we need to process module elements in parse order, i.e.,
the order that things occur in the source files.  In contrast, throughout the
rest of VL we pay no attention to the parse order and just treat modules as if
they contain various sets of elements (e.g., assignments, gates, etc.).</p>

<p>The elements are available in parse order in the special @('parse-temps')
field of the @(see vl-module).  Other transforms should never look at
@('parse-temps'), but should refer to these typed fields, instead.</p>")

(local (xdoc::set-default-parents make-implicit-wires))

(defxdoc implicit-wires-minutia
  :short "Some details about implicit wires."
  :long "<p>Adding implicit wires turns out to be surprisingly subtle.  Here
are some notes about implicit wires in Verilog-2005.</p>

<p>When a wire is implicitly declared, its type is controlled by the
@('`default_nettype') compiler directive (Section 19.2).  But VL's @(see
preprocessor) does not yet support this directive and will cause an error if it
is used, so for now we can safely assume any implicit wires should just have
type @('wire').  (We can probably add support @('default_nettype') without too
much work, since our new approach of going through the module elements
sequentially means that we have easy access to location information.  On the
other hand, this is a really subtle directive to be using and we hope nobody
tries to use it.)</p>

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
to the nearest scope.  It seems like this mostly only matters in the case of
@('generate') blocks.  You might think that it would matter for functions,
tasks, and named blocks as well, but it doesn't seem possible to use implicit
wires in these contexts, see bullet #4 below for details.</p>

<p>Note: I think that throughout Section 4.5, the words <i>port expression
declaration</i> are a typo that should be <i>port declaration</i>; nowhere else
in the Verilog-2005 standard do the words <i>port expression declaration</i>
occur, at least according to Acrobat's find function.</p>

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
automatically builds both a @(see vl-portdecl-p) and a @(see vl-vardecl-p) for
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


<h3>Implicit Wires in Verilog Tools</h3>

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
about such wires, which seems to contradict the Verilog-2005 standard.  We
choose to mimick NCVerilog and infer the implicit net.  Historically we also
issued warnings that other tools like Verilog-XL may not allow the construct,
but these warnings seemed to be noise and we eventually decided that it would
be better not to issue them.</p>

<p>A subtle case is, what if #2 and #3 overlap, i.e., an undeclared wire occurs
on both the left-hand and right-hand sides?  This isn't entirely contrived;
someone might occasionally write things like @('assign {a, abar} = {foo, ~a}').
NCVerilog seems to process the left-hand side first, and hence it allows us to
infer an implicit wire for @('w') when we give it an assignment like @('assign
w = w').</p>

<p><b>#4</b>.  Mostly as expected, neither tool allows undeclared wires on
either side of an assignment in an always block.  The tools even reject
implicit wires in procedural continuous assignments, e.g., @('always @(b)
assign w = a;').</p>

<p>This seems arguably incorrect: is not a procedural continuous assignment
also a continuous assignment, whose LHS should therefore be able to contain
implicit wires?  But we mimick these tools and disallow the implicit net, even
thought the spec might perhaps be interpreted as allowing it.</p>

<p>A nice consequence of disallowing implicit wires here is that it allows us
to avoid certain scoping questions.  In particular, suppose we see a procedural
continuous assignment statement, @('assign w = ...'), where @('w') is not
already declared.  If this statement occurs in a task or a named block within
an initial/always statement, should the declaration for @('w') be added to the
module or to this more local scope?  I'm not sure.  So, the good thing about
not inferring implicit nets for these assignments is that I don't have to be
able to answer the question, because I'm not going to infer a net anyway.</p>

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
implicit wire declaration with the @('VL_PORT_IMPLICIT') attribute.  This
attribute is used by the @(see printer) to avoid printing any net declarations
that were implicit.</p>

<p>With regard to Case 2, we add one-bit wire declarations for any undeclared
wires that occur within the port arguments of gate and module instances, and
which occur in the left-hand sides of continuous assignments.  For assignments,
we always issue a non-fatal warning that says Verilog-XL doesn't add implicit
nets here, and we always process the left-hand side first (like NCVerilog).  We
add the wire declarations at the locations in which they are implicitly
declared, and mark them with the @('VL_IMPLICIT') attribute, which is useful in
@(see typo-detection).</p>")



; FEATURE-CREEP WARNING.
;
; It is tempting to try to do a lot here, e.g., we might want to check for any
; illegally redefined wires, compatibility between port and net declarations,
; etc.  But after some false starts down this road, I think this is a mistake.
;
; We only need to care about the order of elements to properly handle adding
; implicit wires.  Other kinds of well-formedness checks, e.g., that make sure
; nothing is multiply defined, that the ports/netdecls agree, etc., really
; don't need to consider module element order, so keep them separate!
;
; We used to check, here, that names are defined before being used.  That made
; some amount of sense since that's highly related to parse order.  But we now
; prefer to relegate this to shadowcheck, where we have full scopestacks and
; can generally look things up more reliably.

(defines vl-expr-names-for-implicit-nrev
  :parents (vl-expr-names-for-implicit)
  :flag-local nil

  (define vl-expr-names-for-implicit-nrev ((x vl-expr-p) nrev)
    :measure (vl-expr-count x)
    :flag :expr
    (vl-expr-case x
      (:vl-index
       ;; Want only plain names with no selects/indexing, and don't want to
       ;; descend into any select/indexing subexpressions.
       (if (and (vl-idscope-p x.scope)
                (vl-partselect-case x.part :none)
                (atom x.indices))
           (nrev-push (vl-idscope->name x.scope) nrev)
         (nrev-fix nrev)))
      ;; The pattern case is subtle.  See particularly vl-patternkey and
      ;; vl-patternkey-ambiguity.  Historically we had problems with pattern
      ;; keys like "foo" fooling us into introducing implicit wires.  Now our
      ;; parser makes sure to treat those as structure names, so we can just
      ;; fall through to the default here and it works out correctly.
      (:otherwise
       (vl-exprlist-names-for-implicit-nrev (vl-expr->subexprs x) nrev))))

  (define vl-exprlist-names-for-implicit-nrev ((x vl-exprlist-p) nrev)
    :measure (vl-exprlist-count x)
    :flag :list
    (b* (((when (atom x))
          (nrev-fix nrev))
         (nrev (vl-expr-names-for-implicit-nrev (car x) nrev)))
      (vl-exprlist-names-for-implicit-nrev (cdr x) nrev))))


(defines vl-expr-names-for-implicit
  :short "Collect up wire names that might need to be implicitly declared."

  :long "<p>Experimentation with NCVerilog and VCS reveals that only certain
names within expressions lead to implicit wires being declared.  Here are some
findings:</p>

<ul>

<li>If we have a plain name on the left-hand side, like @('assign foo = 0'), then
we get an implicit wire.</li>

<li>If we instead have something like @('assign foo.bar = 0'), then we're
referencing something elsewhere and we don't want to create implicit wires
named @('foo') or @('bar').</li>

<li>Suppose we explicitly declare @('wire [3:0] vec;').  Then both NCVerilog
and VCS reject @('assign vec[w] = 0') where @('w') is undeclared, instead of
inferring an implicit wire @('w').  So I think we do not want to collect names
from <i>within</i> the indices and part-selects.</li>

<li>When @('foo') is not previously declared, both NCVerilog and VCS reject
@('assign foo[0] = 0').  So I don't think we want to collect names that have
indexing or part-selects applied to them.</li>

<li>On the other hand, NCVerilog rejects but VCS accepts (with warnings) gates
such as @('buf mybuf(o, foo[0])'), and seems to infer a wire for @('foo').  We
will try to mimic NCVerilog's behavior since it is more consistent, and
<i>not</i> infer wires that are being indexed into.</li>

<li>Within gate connections, NCV and VCS allow implicit wires in many
expressions, e.g., @('w1 + w2'), @('myfun(w)'), both sides of @('inside')
expressions, etc.</li>

<li>In submodule connections, NCV allows implicit wires to be inferred inside
of assignment patterns like @('triple_t'{a:implicit_w1,b:implicit_w2,...}').
Our version of VCS says this isn't yet implemented.</li>

</ul>"

  (define vl-expr-names-for-implicit ((x vl-expr-p))
    :returns (names string-listp)
    :measure (vl-expr-count x)
    :verify-guards nil
    (mbe :logic
         (vl-expr-case x
           (:vl-index
            ;; Want only plain names with no selects/indexing, and don't want to
            ;; descend into any select/indexing subexpressions.
            (if (and (vl-idscope-p x.scope)
                     (vl-partselect-case x.part :none)
                     (atom x.indices))
                (list (vl-idscope->name x.scope))
              nil))
           ;; The pattern case is subtle.  See particularly vl-patternkey and
           ;; vl-patternkey-ambiguity.  Historically we had problems with pattern
           ;; keys like "foo" fooling us into introducing implicit wires.  Now our
           ;; parser makes sure to treat those as structure names, so we can just
           ;; fall through to the default here and it works out correctly.
           (:otherwise
            (vl-exprlist-names-for-implicit (vl-expr->subexprs x))))
         :exec
         (with-local-nrev
           (vl-expr-names-for-implicit-nrev x nrev))))

  (define vl-exprlist-names-for-implicit ((x vl-exprlist-p))
    :returns (names string-listp)
    :measure (vl-exprlist-count x)
    (mbe :logic
         (if (atom x)
             nil
           (append (vl-expr-names-for-implicit (car x))
                   (vl-exprlist-names-for-implicit (cdr x))))
         :exec
         (with-local-nrev
           (vl-exprlist-names-for-implicit-nrev x nrev))))
  ///

  (defthm true-listp-of-vl-expr-names-for-implicit
    (true-listp (vl-expr-names-for-implicit x))
    :rule-classes :type-prescription)

  (defthm true-listp-of-vl-exprlist-names-for-implicit
    (true-listp (vl-exprlist-names-for-implicit x))
    :rule-classes :type-prescription)

  (deffixequiv-mutual vl-expr-names-for-implicit)

  (defthm-vl-expr-names-for-implicit-nrev-flag
    (defthm vl-expr-names-for-implicit-nrev-removal
      (equal (vl-expr-names-for-implicit-nrev x nrev)
             (append nrev (vl-expr-names-for-implicit x)))
      :flag :expr)
    (defthm vl-exprlist-names-for-implicit-nrev-removal
      (equal (vl-exprlist-names-for-implicit-nrev x nrev)
             (append nrev (vl-exprlist-names-for-implicit x)))
      :flag :list)
    :hints(("Goal"
            :in-theory (enable acl2::rcons)
            :expand ((vl-expr-names-for-implicit x)
                     (vl-exprlist-names-for-implicit x)
                     (vl-expr-names-for-implicit-nrev x nrev)
                     (vl-exprlist-names-for-implicit-nrev x nrev)))))
  (verify-guards vl-expr-names-for-implicit))


(define vl-make-ordinary-implicit-wires
  :short "Generate net declarations for one-bit implicit wires."
  ((loc   vl-location-p "Location to use for the new declarations.")
   (names string-listp  "Names of wires to make declarations for."))
  :returns (nets vl-vardecllist-p "One-bit wire declarations for these names.")
  (if (consp names)
      (cons (make-vl-vardecl :name (car names)
                             :type *vl-plain-old-wire-type*
                             :nettype :vl-wire
                             :loc loc
                             :atts (list (cons "VL_IMPLICIT" nil)))
            (vl-make-ordinary-implicit-wires loc (cdr names)))
    nil)
  ///
  (defthm vl-vardecllist->names-of-vl-make-ordinary-implicit-wires
    (equal (vl-vardecllist->names (vl-make-ordinary-implicit-wires loc names))
           (string-list-fix names))))


(define vl-collect-exprs-for-implicit-wires-from-namedarg ((x vl-namedarg-p))
  :returns (exprs vl-exprlist-p "Expressions where implicit wires are allowed.")
  (b* (((vl-namedarg x))
       ((when x.nameonly-p)
        ;; SystemVerilog name-only style arguments like .foo are not allowed to
        ;; introduce implicit wires.
        nil))
    (vl-maybe-expr-allexprs x.expr))
  ///
  (more-returns (exprs true-listp :rule-classes :type-prescription)))

(define vl-collect-exprs-for-implicit-wires-from-namedargs ((x vl-namedarglist-p))
  :returns (exprs vl-exprlist-p "Expressions where implicit wires are allowed.")
  (if (atom x)
      nil
    (append (vl-collect-exprs-for-implicit-wires-from-namedarg (car x))
            (vl-collect-exprs-for-implicit-wires-from-namedargs (cdr x))))
  ///
  (more-returns (exprs true-listp :rule-classes :type-prescription)))

(define vl-collect-exprs-for-implicit-wires-from-portargs ((x vl-arguments-p))
  :returns (exprs vl-exprlist-p "Expressions where implicit wires are allowed.")
  (vl-arguments-case x
    (:vl-arguments-named
     (vl-collect-exprs-for-implicit-wires-from-namedargs x.args))
    (:vl-arguments-plain
     ;; If using plain arguments, there are no .name style arguments, so
     ;; everything is allowed to have implicit wires.
     (vl-plainarglist-allexprs x.args)))
  ///
  (more-returns (exprs true-listp :rule-classes :type-prescription)))

(define vl-modinst-exprs-for-implicit-wires ((x vl-modinst-p))
  :returns (exprs vl-exprlist-p "Expressions where implicit wires are allowed.")
  (b* (((vl-modinst x) x))
    (vl-collect-exprs-for-implicit-wires-from-portargs x.portargs))
  ///
  (more-returns (exprs true-listp :rule-classes :type-prescription)))

(define vl-gateinst-exprs-for-implicit-wires ((x vl-gateinst-p))
  :short "Gets the expressions from a gate instance, for making implicit wires."
  :returns (exprs vl-exprlist-p "Expressions where implicit wires are allowed.")
  (b* (((vl-gateinst x) x))
    (vl-plainarglist-allexprs x.args))
  ///
  (more-returns (exprs true-listp :rule-classes :type-prescription)))



(defprod vl-implicitst
  :short "State for the @(see make-implicit-wires) transform."
  :tag nil
  :layout :tree
  ((portdecls "Fast alist binding names of declared port names to their
               declarations."
              vl-portdecl-alist-p)
   (decls     "Fast alist binding names of declared non-port names to anything.
               These names can be the names of wires, instances, functions, etc.,
               that are in the local scope, for instance."
              acl2::any-p)
   (imports   "Fast alist binding imported names to anything."
              acl2::any-p)
   (ss        vl-scopestack-p
              "Scopestack for lookup of global names.  Note that this scopestack
               doesn't typically contain the current module we're looking at,
               because it isn't really a complete module until we add the implicit
               wires to it.")))

(define vl-remove-declared-wires
  :short "Filter names to remove wires that are already declared.  We remove
          the names of any port declarations, ordinary declarations, global
          names, and imported names."
  ((names string-listp)
   (st    vl-implicitst-p))
  :returns
  (implicit string-listp
            "Subset of @('names') that don't have declarations already,
             e.g., names that we want to add implicit declarations for.")
  :hooks ((:fix :hints (("goal" :induct (vl-remove-declared-wires names st)
                         :in-theory (disable (:d vl-remove-declared-wires)))
                        (and stable-under-simplificationp
                             (flag::expand-calls-computed-hint
                              clause '(vl-remove-declared-wires))))))
  (b* (((when (atom names))
        nil)
       ((vl-implicitst st))
       (name1 (string-fix (car names)))
       ((when (or (hons-get name1 st.decls)
                  (hons-get name1 st.portdecls)
                  (hons-get name1 st.imports)
                  (vl-scopestack-find-item name1 st.ss)))
        ;; This name has been declared locally or in some superior scope.
        ;; Because of that, we do not want to add an implicit wire for
        ;; this name.
        (vl-remove-declared-wires (cdr names) st)))
    (cons name1 (vl-remove-declared-wires (cdr names) st))))

(define vl-import-update-implicit ((x        vl-import-p)
                                   (st       vl-implicitst-p)
                                   (warnings vl-warninglist-p))
  :returns (mv (new-warnings vl-warninglist-p)
               (new-st vl-implicitst-p))
  (b* (((vl-import x) (vl-import-fix x))
       ((vl-implicitst st))
       (package  (vl-scopestack-find-package x.pkg st.ss))
       (warnings (if package
                     (ok)
                   (fatal :type :vl-bad-import
                          :msg "~a0: trying to import from undefined package ~s1."
                          :args (list x x.pkg))))
       (imports  st.imports)
       (imports  (if (eq x.part :vl-import*)
                     ;; Add all the names from the package onto imports.
                     (hons-shrink-alist
                      ;; If the package wasn't found and we tried to
                      ;; import foo::* from it, we've already caused a
                      ;; fatal warning, so it's okay to fudge here.
                      (and package
                           (vl-package-scope-item-alist-top package))
                      imports)
                   ;; Import of a single name.
                   (hons-acons (the string x.part) nil imports)))
       (st   (change-vl-implicitst st :imports imports)))
    (mv warnings st)))

(define vl-blockitem-update-implicit ((x        vl-blockitem-p)
                                      (st       vl-implicitst-p)
                                      (warnings vl-warninglist-p))
  :returns (mv (new-warnings vl-warninglist-p)
               (new-st       vl-implicitst-p))
  (b* ((x (vl-blockitem-fix x))
       ((when (eq (tag x) :vl-import))
        (vl-import-update-implicit x st warnings))
       (name (case (tag x)
               (:vl-vardecl   (vl-vardecl->name x))
               (:vl-paramdecl (vl-paramdecl->name x))
               (otherwise     (vl-typedef->name x))))
       (decls (hons-acons name nil (vl-implicitst->decls st)))
       (st    (change-vl-implicitst st :decls decls)))
    (mv (ok) st)))

(define vl-blockitemlist-update-implicit ((x        vl-blockitemlist-p)
                                          (st       vl-implicitst-p)
                                          (warnings vl-warninglist-p))
  :returns (mv (new-warnings vl-warninglist-p)
               (new-st       vl-implicitst-p))
  (b* (((when (atom x))
        (mv (ok) (vl-implicitst-fix st)))
       ((mv warnings st) (vl-blockitem-update-implicit (car x) st warnings))
       ((mv warnings st) (vl-blockitemlist-update-implicit (cdr x) st warnings)))
    (mv warnings st)))

(define vl-genelement-make-implicit-wires
  :short "Make implicit wires for a single modelement."
  ((x        vl-genelement-p
             "Base genelement to process.")
   (st       vl-implicitst-p)
   (newitems vl-genelementlist-p
             "Accumulator for rewriting X and inserting implicit variable
              declarations right where they occur.")
   (warnings vl-warninglist-p))
  :guard (vl-genelement-case x :vl-genbase)
  :returns (mv (warnings vl-warninglist-p)
               (st       vl-implicitst-p)
               (newitems vl-genelementlist-p))

  :prepwork ((local (defthm vl-blockitem-p-when-vl-vardecl-p-no-limit
                      (implies (vl-vardecl-p x)
                               (vl-blockitem-p x))))
             (local (defthm vl-blockitem-p-when-vl-paramdecl-p-no-limit
                      (implies (vl-paramdecl-p x)
                               (vl-blockitem-p x))))
             (local (defthm vl-blockitem-p-when-vl-import-p-no-limit
                      (implies (vl-import-p x)
                               (vl-blockitem-p x))))
             (local (in-theory (disable vl-blockitem-p-when-vl-vardecl-p
                                        vl-blockitem-p-when-vl-paramdecl-p
                                        vl-blockitem-p-when-vl-import-p
                                        acl2::consp-under-iff-when-true-listp))))

  :guard-hints ((and stable-under-simplificationp
                     '(:use ((:instance vl-modelement-p-when-invalid-tag (x (vl-genbase->item x))))
                       :in-theory (disable vl-modelement-p-when-invalid-tag))))

  (b* ((x        (vl-genelement-fix x))
       (st       (vl-implicitst-fix st))
       (newitems (vl-genelementlist-fix newitems))

       (item (vl-genbase->item x))
       (tag  (tag item))

       ;; Note: recall the FEATURE-CREEP WARNING above.  We are too dumb to do
       ;; anything yet except track what is declared and add implicit wires as
       ;; needed.  Do not try to notice uses of undeclared wires, warn about
       ;; multiply declared things, etc., because it's too hard until more has
       ;; been resolved.

       ((when (or (eq tag :vl-interfaceport)
                  (eq tag :vl-regularport)
                  (eq tag :vl-modport)))
        (b* ((warnings (fatal :type :vl-programming-error
                              :msg "~a0: unexpected kind of module item."
                              :args (list item)))
             (st       (change-vl-implicitst st))
             (newitems (cons x newitems)))
          (mv warnings st newitems)))

       ((when (eq tag :vl-portdecl))
        (b* ((declname  (vl-portdecl->name item))
             (portdecls (hons-acons declname item (vl-implicitst->portdecls st)))
             (st        (change-vl-implicitst st :portdecls portdecls))
             (newitems  (cons x newitems)))
          (mv (ok) st newitems)))

       ((when (or (eq tag :vl-vardecl)
                  (eq tag :vl-paramdecl)
                  (eq tag :vl-import)))
        (b* (((mv warnings st) (vl-blockitem-update-implicit item st warnings))
             (newitems (cons x newitems)))
          (mv warnings st newitems)))

       ((when (or (eq tag :vl-modinst)
                  (eq tag :vl-gateinst)))
        (b* (((mv loc port-exprs maybe-name)
              (if (eq tag :vl-modinst)
                  (mv (vl-modinst->loc item)
                      (vl-modinst-exprs-for-implicit-wires item)
                      (vl-modinst->instname item))
                (mv (vl-gateinst->loc item)
                    (vl-gateinst-exprs-for-implicit-wires item)
                    (vl-gateinst->name item))))
             (port-names  (vl-exprlist-names-for-implicit port-exprs))
             (imp-names   (mergesort (vl-remove-declared-wires port-names st)))
             (imp-nets    (vl-make-ordinary-implicit-wires loc imp-names))
             (decls       (vl-implicitst->decls st))
             (decls       (make-fal (pairlis$ imp-names nil) decls))
             (decls       (if maybe-name (hons-acons maybe-name nil decls) decls))
             (st          (change-vl-implicitst st :decls decls))
             (newitems    (append (vl-modelementlist->genelements imp-nets) newitems))
             (newitems    (cons x newitems)))
          (mv (ok) st newitems)))

       ((when (eq tag :vl-assign))
        (b* (((vl-assign item))
             (lhs-names  (vl-expr-names-for-implicit item.lvalue))
             (imp-names  (mergesort (vl-remove-declared-wires lhs-names st)))
             (imp-nets   (vl-make-ordinary-implicit-wires item.loc imp-names))
             (decls      (vl-implicitst->decls st))
             (decls      (make-fal (pairlis$ imp-names nil) decls))
             (st         (change-vl-implicitst st :decls decls))
             (newitems   (append (vl-modelementlist->genelements imp-nets) newitems))
             (newitems   (cons x newitems)))
          (mv (ok) st newitems)))

       ((when (eq tag :vl-alias))
        (b* (((vl-alias item) item)
             (lhs-names (vl-expr-names-for-implicit item.lhs))
             (rhs-names (vl-expr-names-for-implicit item.rhs))
             (imp-names (mergesort (vl-remove-declared-wires (append lhs-names rhs-names) st)))
             (imp-nets  (vl-make-ordinary-implicit-wires item.loc imp-names))
             ;; BOZO should we bother warning about this?
             (warnings  (if (not imp-names)
                            (ok)
                          (warn :type :vl-tricky-implicit
                                :msg "~a0: wire~s1 ~&2 ~s3 implicitly ~
                                      declared by this alias declaration."
                                :args (list item
                                            (if (vl-plural-p imp-names) "s" "")
                                            imp-names
                                            (if (vl-plural-p imp-names) "are" "is")))))
             (decls     (vl-implicitst->decls st))
             (decls     (make-fal (pairlis$ imp-names nil) decls))
             (st        (change-vl-implicitst st :decls decls))
             (newitems  (append (vl-modelementlist->genelements imp-nets) newitems))
             (newitems  (cons x newitems)))
          (mv warnings st newitems)))

       ((when (or (eq tag :vl-initial)
                  (eq tag :vl-final)
                  (eq tag :vl-always)
                  (eq tag :vl-dpiexport)))
        ;; These don't declare any names, nothing to do.
        (b* ((newitems (cons x newitems)))
          (mv (ok) st newitems)))

       ((when (or (eq tag :vl-fundecl)
                  (eq tag :vl-taskdecl)
                  (eq tag :vl-dpiimport)
                  (eq tag :vl-assertion)
                  (eq tag :vl-cassertion)
                  (eq tag :vl-property)
                  (eq tag :vl-sequence)
                  (eq tag :vl-typedef)
                  (eq tag :vl-fwdtypedef)
                  (eq tag :vl-genvar)))
        ;; These have their own names but there's no additional implicit wires to
        ;; be introduced by them, so just extend decls.
        (b* ((name     (case tag
                         (:vl-fundecl    (vl-fundecl->name item))
                         (:vl-taskdecl   (vl-taskdecl->name item))
                         (:vl-dpiimport  (vl-dpiimport->name item))
                         (:vl-assertion  (vl-assertion->name item))
                         (:vl-cassertion (vl-cassertion->name item))
                         (:vl-property   (vl-property->name item))
                         (:vl-sequence   (vl-sequence->name item))
                         (:vl-typedef    (vl-typedef->name item))
                         (:vl-fwdtypedef (vl-fwdtypedef->name item))
                         (:vl-genvar     (vl-genvar->name item))))
             (decls    (hons-acons name nil (vl-implicitst->decls st)))
             (st       (change-vl-implicitst st :decls decls))
             (newitems (cons x newitems)))
          (mv (ok) st newitems))))

    (impossible)
    (mv (ok) st newitems)))



(define vl-implicitsts-restore-fast-alists ((st     vl-implicitst-p)
                                            (new-st vl-implicitst-p))
  :short "Assuming new-st is a modified version of st, restores any changed
          fast alists in st and frees them in new-st.  Side effects only."
  (b* (((vl-implicitst st))
       ((vl-implicitst new-st)))
    ;; I once wanted to use fast-alist-len here, but that doesn't work: if the
    ;; st has had its fast alists stolen, then we (of course) can't call
    ;; fast-alist-len on them.
    (or (same-lengthp st.portdecls new-st.portdecls)
        (progn$ (fast-alist-free new-st.portdecls)
                (make-fast-alist st.portdecls)))
    (or (same-lengthp st.decls new-st.decls)
        (progn$ (fast-alist-free new-st.decls)
                (make-fast-alist st.decls)))
    (or (same-lengthp st.imports new-st.imports)
        (progn$ (fast-alist-free new-st.imports)
                (make-fast-alist st.imports)))))


; We might consider unlocalizing some of these and finding them homes, but
; they're not necessarily that widely useful and, for instance, the modelement
; rules here might be kind of slow in general.

;; (local (in-theory (disable (tau-system))))

;; (local (defthm vl-modelement-p-when-vl-blockitem-p
;;          (implies (vl-blockitem-p x)
;;                   (vl-modelement-p x))
;;          :hints(("Goal" :in-theory (enable vl-blockitem-p vl-modelement-p
;;                                            tag-reasoning)))))

;; (local (defthm vl-modelementlist-p-when-vl-blockitemlist-p
;;          (implies (vl-blockitemlist-p x)
;;                   (vl-modelementlist-p x))
;;          :hints(("Goal" :induct (len x)))))


(defines vl-make-implicit-wires-aux
  :verify-guards nil

  (define vl-make-implicit-wires-generate
    :short "Make implicit wires for a generate statement."
    ((x        vl-genelement-p)
     (st       vl-implicitst-p)
     (warnings vl-warninglist-p))
    :returns (mv (new-warnings vl-warninglist-p)
                 (new-x        vl-genelement-p "Extended with implicit declarations."))
    :long "<p>Per SystemVerilog-2012 Section 6.10: wires that are implicitly
           declared within a generate block are local to that generate block.
           So we collect the implicit declarations for each particular generate
           block without leaking them into the outer context.</p>

           <p>This function should be called from outside (including
           vl-make-implicit-wires-aux) on non-genbase elements.  However,
           recursive calls may be on genbases, which are then assumed to be
           stand-alone elements that are in a generate construct by
           themselves.</p>"
    :measure (vl-genelement-count x)
    (vl-genelement-case x

      :vl-genloop
      (b* (((vl-implicitst st))
           ;; Bind the loop index var in the state first.
           (new-decls              (hons-acons x.var nil st.decls))
           (local-st               (change-vl-implicitst st :decls new-decls))
           ((mv warnings new-body) (vl-make-implicit-wires-generate x.body local-st warnings))
           (-                      (vl-implicitsts-restore-fast-alists st local-st))
           (new-x                  (change-vl-genloop x :body new-body)))
        (mv warnings new-x))

      :vl-genif
      (b* (((mv warnings new-then) (vl-make-implicit-wires-generate x.then st warnings))
           ((mv warnings new-else) (vl-make-implicit-wires-generate x.else st warnings))
           (new-x                  (change-vl-genif x :then new-then :else new-else)))
        (mv warnings new-x))

      :vl-gencase
      (b* (((mv warnings new-cases)   (vl-make-implicit-wires-gencaselist x.cases st warnings))
           ((mv warnings new-default) (vl-make-implicit-wires-generate x.default st warnings))
           (new-x                     (change-vl-gencase x :cases new-cases :default new-default)))
        (mv warnings new-x))

      :vl-genblock
      (b* (((mv warnings new-st new-elems) (vl-make-implicit-wires-aux x.elems st nil warnings))
           (- (vl-implicitsts-restore-fast-alists st new-st))
           (new-x (change-vl-genblock x :elems new-elems)))
        (mv warnings new-x))

      :vl-genbase
      (b* (((mv warnings new-st new-elems) (vl-genelement-make-implicit-wires x st nil warnings))
           (- (vl-implicitsts-restore-fast-alists st new-st))
           (new-x (make-vl-genblock :elems new-elems :loc (vl-modelement->loc x.item))))
        (mv warnings new-x))

      :otherwise
      (mv (warn :type :vl-programming-error
                :msg "~a0: Didn't expect to see this kind of generate element yet."
                :args (list (vl-genelement-fix x)))
          (vl-genelement-fix x))))

  (define vl-make-implicit-wires-gencaselist ((x        vl-gencaselist-p)
                                              (st       vl-implicitst-p)
                                              (warnings vl-warninglist-p))
    :returns (mv (new-warnings vl-warninglist-p)
                 (new-x        vl-gencaselist-p "Extended with implicit declarations."))
    :measure (vl-gencaselist-count x)
    (b* ((x (vl-gencaselist-fix x))
         ((when (atom x)) (mv (vl-warninglist-fix warnings) nil))
         ((mv warnings new-elem) (vl-make-implicit-wires-generate (cdar x) st warnings))
         ((mv warnings new-rest) (vl-make-implicit-wires-gencaselist (cdr x) st warnings))
         (new-x (cons (cons (caar x) new-elem) new-rest)))
      (mv warnings new-x)))

  (define vl-make-implicit-wires-aux
    :short "Main function for adding implicit wires."
    ((x        vl-genelementlist-p "Elements to process in parse order.")
     (st       vl-implicitst-p)
     (newitems vl-genelementlist-p
               "Accumulator for rewriting X and inserting implicit variable
                declarations right where they occur.")
     (warnings vl-warninglist-p))
    :returns (mv (new-warnings vl-warninglist-p)
                 (new-st       vl-implicitst-p)
                 (newitems     vl-genelementlist-p))
    :measure (vl-genelementlist-count x)

    :long "<p>Note that to keep this code simple, we don't try to defend
           against multiply declared names here.</p>

           <p>We don't try to add any port declarations here, because we have
           to sort of get through the whole module to make sure there isn't an
           explicit declaration later on.  We handle that in @(see
           vl-make-implicit-wires-main).</p>"

    (b* ((x        (vl-genelementlist-fix x))
         (st       (vl-implicitst-fix st))
         (warnings (vl-warninglist-fix warnings))
         (newitems (vl-genelementlist-fix newitems))

         ((when (atom x))
          (mv warnings st newitems))

         (elem (car x))

         ((unless (vl-genelement-case elem :vl-genbase))
          (b* (((mv warnings new-elem)
                (vl-make-implicit-wires-generate elem st warnings))
               (newitems (cons new-elem newitems)))
            (vl-make-implicit-wires-aux (cdr x) st newitems warnings)))

         ((mv warnings st newitems)
          (vl-genelement-make-implicit-wires elem st newitems warnings)))
      (vl-make-implicit-wires-aux (cdr x) st newitems warnings)))
  ///
  (verify-guards vl-make-implicit-wires-aux)
  (deffixequiv-mutual vl-make-implicit-wires-aux))


(define vl-make-port-implicit-wires
  :short "Generate variable declarations for ports that don't have
          corresponding variable declarations."
  ((items vl-genelementlist-p
          "Items to process in <b>reverse</b> parse order, with implicit
           wire declarations already added in.")
   (decls "Alist binding all the non-port names that are (ever) declared
           in the module to anything.  This lets us tell, when we get to
           a port declaration, whether we need to add a corresponding
           net declaration for it.")
   (newitems vl-genelementlist-p
             "Accumulator for our new items (reverse of items order, i.e.,
              back into parse order.)"))
  :returns (newitems vl-genelementlist-p
                     "Parse order, with port-implicit decls added.")
  (b* (((when (atom items))
        (vl-genelementlist-fix newitems))

       (item (vl-genelement-fix (car items)))

       ((unless (and (vl-genelement-case item :vl-genbase)
                     (eq (tag (vl-genbase->item item)) :vl-portdecl)))
        ;; Don't care about anything except portdecls.
        (vl-make-port-implicit-wires (cdr items) decls (cons item newitems)))

       ((vl-portdecl portdecl) (vl-genbase->item item))
       ((when (hons-get portdecl.name decls))
        ;; There's a corresponding declaration for this port declaration
        ;; somewhere else in the module, so there's nothing we need to add.
        (vl-make-port-implicit-wires (cdr items) decls (cons item newitems)))

       ;; Else, we do want to create a corresponding net declaration.  BOZO
       ;; what about scalaredp, vectoredp, cstrength, delay?  I think we don't
       ;; care, but it might be good to double check this.
       (new-decl (make-vl-genbase
                  :item (make-vl-vardecl :name    portdecl.name
                                         :type    portdecl.type
                                         :atts    (cons '("VL_PORT_IMPLICIT") portdecl.atts)
                                         :loc     portdecl.loc))))
    (vl-make-port-implicit-wires (cdr items) decls (list* item new-decl newitems))))

(define vl-make-implicit-wires-main
  :short "Top level routine for adding implicit wires to a module's load items."
  ((loaditems vl-genelementlist-p    "Module elements in parse order.")
   (ifports   vl-interfaceportlist-p "Interface ports for the module (we implicitly declare them first).")
   (ss        vl-scopestack-p        "Partial scopestack with info for superior scopes.")
   (warnings  vl-warninglist-p       "Ordinary @(see warnings) accumulator."))
  :returns
  (mv (newitems  vl-genelementlist-p "Extended @('loaditems') with implicit wires added.")
      (warnings  vl-warninglist-p    "Possibly extended @(see warnings)."))
  (b* ((ifports (vl-interfaceportlist-fix ifports))
       (decls   (make-fast-alist (pairlis$ (vl-portlist->names ifports) (list-fix ifports))))
       (st      (make-vl-implicitst :decls     decls
                                    :portdecls nil
                                    :imports   nil
                                    :ss        ss))
       (newitems nil)
       ;; Add regular implicit wires.  This reverses the items.
       ((mv warnings st newitems) (vl-make-implicit-wires-aux loaditems st newitems warnings))
       ;; Add port implicit wires.  This reverses them again so they're back in parse order.
       ((vl-implicitst st))
       (newitems (vl-make-port-implicit-wires newitems st.decls nil))
       (- (fast-alist-free st.portdecls))
       (- (fast-alist-free st.decls))
       (- (fast-alist-free st.imports)))
    (mv newitems warnings)))

;; (trace$ #!vl (vl-make-implicit-wires-main
;;               :entry (list 'vl-module-make-implicit-wires-main
;;                            (with-local-ps
;;                              (vl-ps-seq
;;                               (vl-println "loaditems:")
;;                               (vl-pp-genelementlist loaditems)
;;                               (vl-println "ifports:")
;;                               (vl-pp-interfaceportlist ifports))))
;;               :exit (list 'vl-module-make-implicit-wires-main
;;                           (b* (((list implicit newitems warnings-out) values))
;;                             (with-local-ps
;;                               (vl-ps-seq
;;                                (vl-println "implicit:")
;;                                (vl-pp-vardecllist implicit)
;;                                (vl-println "newitems:")
;;                                (vl-pp-genelementlist newitems)
;;                                (vl-println "warnings:")
;;                                (vl-print-warnings (butlast warnings-out
;;                                                            (len warnings)))))))))


(define vl-module-make-implicit-wires ((x  vl-module-p)
                                       (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x))
       (x.loaditems (and x.parse-temps
                         (append (vl-modelementlist->genelements
                                  (vl-parse-temps->paramports x.parse-temps))
                                 (vl-parse-temps->loaditems x.parse-temps))))
       ((mv newitems warnings)
        (vl-make-implicit-wires-main x.loaditems x.ifports ss x.warnings))
       ((vl-genblob c) (vl-sort-genelements newitems))
       (parse-temps (and x.parse-temps
                         (change-vl-parse-temps x.parse-temps
                                                :paramports nil
                                                :loaditems newitems))))
    (change-vl-module x
                      :portdecls   c.portdecls
                      :assigns     c.assigns
                      :aliases     c.aliases
                      :vardecls    c.vardecls
                      :paramdecls  c.paramdecls
                      :fundecls    c.fundecls
                      :taskdecls   c.taskdecls
                      :modinsts    c.modinsts
                      :gateinsts   c.gateinsts
                      :alwayses    c.alwayses
                      :initials    c.initials
                      :generates   c.generates
                      :genvars     c.genvars
                      :imports     c.imports
                      :typedefs    c.typedefs
                      :assertions  c.assertions
                      :cassertions c.cassertions
                      :dpiimports  c.dpiimports
                      :dpiexports  c.dpiexports
                      :warnings    warnings
                      :parse-temps parse-temps)))


(defprojection vl-modulelist-make-implicit-wires ((x  vl-modulelist-p)
                                                  (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-make-implicit-wires x ss))

(define vl-design-make-implicit-wires ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))

       ;; Part 1 -- Introduce implicit wires
       (ss    (vl-scopestack-init x))
       (mods  (vl-modulelist-make-implicit-wires x.mods ss))
       (new-x (change-vl-design x :mods mods))
       (-     (vl-scopestacks-free)))

    ;; Part 2 -- Check for tricky shadowing, sane imports, etc.
    (vl-shadowcheck-design new-x)))







;; (defines vl-stmt-check-undeclared
;;   :short "Check an arbitrary @(see vl-stmt-p) for uses of undeclared names."

;;   :long "<p>Most statements are totally straightforward; we just need to make
;; sure that all identifiers used anywhere within them have been declared.</p>

;; <p>Named blocks are the only complication.  They have their own scope and can
;; have their own declarations and imports, which come before their
;; sub-statements.  So, if we see a named block, we basically fork the decls and
;; imports to create a local namespace, add all of the local declarations to it,
;; and then check all the sub-statements in this extended namespace.</p>"

;;   (define vl-stmt-check-undeclared
;;     ((ctx       vl-modelement-p "Where this statement occurs.")
;;      (x         vl-stmt-p       "The statement to process.")
;;      (st        vl-implicitst-p)
;;      (warnings  vl-warninglist-p))
;;     :returns (new-warnings vl-warninglist-p)
;;     :measure (vl-stmt-count x)
;;     :verify-guards nil
;;     (b* ((x (vl-stmt-fix x))

;;          ((when (vl-atomicstmt-p x))
;;           (b* ((used-names (vl-exprlist-varnames (vl-stmt-allexprs x)))
;;                (warnings   (vl-warn-about-undeclared-wires ctx used-names st warnings)))
;;             warnings))

;;          ((when (vl-stmt-case x :vl-blockstmt))
;;           (b* (((vl-blockstmt x) x)
;;                ((vl-implicitst st) st)
;;                ;; Initially the local-decls will just be the current decls
;;                ;; we've seen, since things in the module's scope can still be
;;                ;; referenced from within the named block.
;;                (local-decls   (hons-shrink-alist st.decls nil))
;;                (local-imports (hons-shrink-alist st.imports nil))
;;                (local-st      (change-vl-implicitst st :decls local-decls :imports local-imports))
;;                ;; Add in all local declarations.
;;                ((mv warnings local-st) (vl-blockitemlist-check-undeclared x.loaditems local-st warnings))
;;                ;; Check all the sub-statements in the extended scope.
;;                (warnings (vl-stmtlist-check-undeclared ctx x.stmts local-st warnings)))
;;             ;; Note that a named block doesn't have any other kinds of
;;             ;; expressions (i.e., x.ctrl and x.exprs are necessarily empty).
;;             ;; So, there's nothing to check other than the statements, and
;;             ;; hence we're already done and can now throw away the local scope.
;;             (fast-alist-free (vl-implicitst->decls local-st))
;;             (fast-alist-free (vl-implicitst->imports local-st))
;;             warnings))

;;          ((when (vl-stmt-case x :vl-forstmt))
;;           (b* (((vl-forstmt x))
;;                ((vl-implicitst st) st)
;;                ;; Basically similar to the blockstmt case: create a new scope...
;;                (local-decls   (hons-shrink-alist st.decls nil))
;;                (local-imports (hons-shrink-alist st.imports nil))
;;                (local-st      (change-vl-implicitst st :decls local-decls :imports local-imports))
;;                ;; Add in local declarations for things like for(int i = 0; ...).
;;                ;; We abuse the fact that vardecls are blockitems to just reuse our
;;                ;; blockitem handler.
;;                ((mv warnings local-st) (vl-blockitemlist-check-undeclared x.initdecls local-st warnings))
;;                ;; Now check the rest of the for statement components in the extended
;;                ;; scope.
;;                (warnings (vl-stmtlist-check-undeclared ctx x.initassigns local-st warnings))
;;                (warnings (vl-warn-about-undeclared-wires ctx (vl-expr-varnames x.test) local-st warnings))
;;                (warnings (vl-stmtlist-check-undeclared ctx x.stepforms local-st warnings))
;;                (warnings (vl-stmt-check-undeclared ctx x.body local-st warnings)))
;;             ;; All done with the local scope.
;;             (fast-alist-free (vl-implicitst->decls local-st))
;;             (fast-alist-free (vl-implicitst->imports local-st))
;;             warnings))

;;          ;; No other statement has its own scope, but some kinds of statements
;;          ;; (e.g., case statements, assignments, timing statements) have their
;;          ;; own expressions, so we need to check those.

;;          ;; We don't use vl-stmt-allexprs here because it also grabs the exprs
;;          ;; for sub-statements, which could be incorrect because a sub-block
;;          ;; statement of course needs to be checked w.r.t. its local scope.
;;          ;; So, we instead use this ugly sort of way to grab only the local
;;          ;; expressions.  We don't have to collect from x.decls since this
;;          ;; isn't a block statement.
;;          (local-exprs (append (vl-maybe-delayoreventcontrol-allexprs
;;                                (vl-compoundstmt->ctrl x))
;;                               (vl-compoundstmt->exprs x)))
;;          (local-names (vl-exprlist-varnames local-exprs))
;;          (warnings    (vl-warn-about-undeclared-wires ctx local-names st warnings)))

;;       ;; Finally check the substatements.
;;       (vl-stmtlist-check-undeclared ctx (vl-compoundstmt->stmts x) st warnings)))

;;     (define vl-stmtlist-check-undeclared ((ctx      vl-modelement-p)
;;                                           (x        vl-stmtlist-p)
;;                                           (st       vl-implicitst-p)
;;                                           (warnings vl-warninglist-p))
;;       :returns (new-warnings vl-warninglist-p)
;;       :measure (vl-stmtlist-count x)
;;       (b* (((when (atom x))
;;             (ok))
;;            (warnings (vl-stmt-check-undeclared ctx (car x) st warnings)))
;;         (vl-stmtlist-check-undeclared ctx (cdr x) st warnings)))

;;     ///
;;     (verify-guards vl-stmt-check-undeclared)
;;     (deffixequiv-mutual vl-stmt-check-undeclared))



;; (define vl-fundecl-check-undeclared
;;   :short "Check an arbitrary @(see vl-fundecl-p) for uses of undeclared names."

;;   :long "<p>Function declarations are tricky because they can have their own
;; declarations and hence we need to treat them basically like a named block
;; statement.</p>

;; <p>BOZO a problem with our approach is that paramterized function inputs won't
;; exactly work, e.g., for</p>

;; @({
;; function foo ;
;;   parameter p = 4;
;;   input [p-1:0] in;
;;   ...
;; endfunction
;; })

;; <p>We will think that @('p') is undeclared when we see @('in'), because we
;; aren't maintaining the mixed order of inputs and parameters.</p>

;; <p>Well, this is a pretty obscure, so I don't want to fix it until it becomes a
;; problem.</p>"

;;   ((x         vl-fundecl-p)
;;    (st        vl-implicitst-p)
;;    (warnings  vl-warninglist-p))
;;   :returns (new-warnings vl-warninglist-p)
;;   (b* ((x (vl-fundecl-fix x))
;;        ((vl-fundecl x) x)

;;        ;; Check for undeclared names in the non-local parts (the inputs and
;;        ;; return value range.)  It's not quite right to do the inputs here, as
;;        ;; described above, but in practice it shouldn't be much of a problem.
;;        (other-names (vl-exprlist-varnames (append (vl-portdecllist-allexprs x.portdecls)
;;                                                   (vl-datatype-allexprs x.rettype))))
;;        (warnings    (vl-warn-about-undeclared-wires x other-names st warnings))

;;        ;; Now make a local scope and add the local declarations, as in named
;;        ;; block statements.
;;        (local-decls (hons-shrink-alist (vl-implicitst->decls st) nil))
;;        (local-imports (hons-shrink-alist (vl-implicitst->imports st) nil))
;;        (local-st    (change-vl-implicitst st :decls local-decls :imports local-imports))

;;        ;; Now check/add the block items.  As we do this, we're acting like the
;;        ;; inputs haven't been declared yet.  That's not quite right, but it
;;        ;; should be practically pretty reasonable since it's not valid to refer
;;        ;; to an input in the other declarations.
;;        ((mv warnings local-st)
;;         (vl-blockitemlist-check-undeclared x.parsed-blockitems local-st warnings))

;;        ;; Okay, now add the inputs to the local scope, since it's valid to
;;        ;; refer to them in the body.  Also add in the function's name since it
;;        ;; can be a valid return value.
;;        (local-decls  (vl-implicitst->decls local-st))
;;        (local-decls  (make-fal (pairlis$ (vl-portdecllist->names x.portdecls) nil) local-decls))
;;        (local-decls  (hons-acons x.name nil local-decls))
;;        (local-st     (change-vl-implicitst local-st :decls local-decls))

;;        ;; The local scope is constructed, check the function's body.
;;        (warnings (vl-stmt-check-undeclared x x.body local-st warnings)))
;;     ;; That's it, all done with the local scope.
;;     (fast-alist-free local-decls)
;;     warnings))


;; (define vl-dpiimport-check-undeclared
;;   :short "Check an arbitrary @(see vl-dpiimport) for uses of undeclared names."
;;   ((x         vl-dpiimport-p)
;;    (st        vl-implicitst-p)
;;    (warnings  vl-warninglist-p))
;;   :returns (new-warnings vl-warninglist-p)
;;   (b* (((vl-dpiimport x) (vl-dpiimport-fix x))
;;        ;; Analogous to functions -- check names in return type and parameters
;;        (other-names (vl-exprlist-varnames (append (vl-portdecllist-allexprs x.portdecls)
;;                                                   (vl-maybe-datatype-allexprs x.rettype))))
;;        (warnings    (vl-warn-about-undeclared-wires x other-names st warnings)))
;;     ;; There's not anything else here we can check since the import's
;;     ;; definition is in some C file somewhere.
;;     warnings))


;; (define vl-taskdecl-check-undeclared
;;   :short "Check an arbitrary @(see vl-taskdecl-p) for uses of undeclared
;; names."
;;   :long "<p>This is nearly identical to @(see vl-fundecl-check-undeclared) and
;; it has the same problems with parameters.</p>"

;;   ((x         vl-taskdecl-p)
;;    (st        vl-implicitst-p)
;;    (warnings  vl-warninglist-p))
;;   :returns (new-warnings vl-warninglist-p)
;;   (b* ((x (vl-taskdecl-fix x))
;;        ((vl-taskdecl x) x)

;;        ;; Check for undeclared names in the task's visible ports.  It's not
;;        ;; quite right to do the ports here if they have parameters, as
;;        ;; described above, but in practice it shouldn't be much of a problem.
;;        (other-names (vl-exprlist-varnames (vl-portdecllist-allexprs x.portdecls)))
;;        (warnings    (vl-warn-about-undeclared-wires x other-names st warnings))

;;        ;; Now make a local scope and add the local declarations, as in named
;;        ;; block statements.
;;        (local-decls (hons-shrink-alist (vl-implicitst->decls st) nil))
;;        (local-imports (hons-shrink-alist (vl-implicitst->imports st) nil))
;;        (local-st    (change-vl-implicitst st :decls local-decls :imports local-imports))

;;        ;; Now check/add the block items.  As we do this, we're acting like the
;;        ;; ports haven't been declared yet.  That's not quite right, but it
;;        ;; should be practically pretty reasonable since it's not valid to refer
;;        ;; to a port in the other declarations.
;;        ((mv warnings local-st)
;;         (vl-blockitemlist-check-undeclared x.parsed-blockitems local-st warnings))

;;        ;; Okay, now add the ports to the local scope, since it's valid to
;;        ;; refer to them in the body.
;;        (local-decls (vl-implicitst->decls local-st))
;;        (local-decls (make-fal (pairlis$ (vl-portdecllist->names x.portdecls) nil) local-decls))
;;        (local-st    (change-vl-implicitst local-st :decls local-decls))

;;        ;; The local scope is constructed, check the task's body.
;;        (warnings (vl-stmt-check-undeclared x x.body local-st warnings)))

;;     ;; That's it, all done with the local scope.
;;     (fast-alist-free local-decls)
;;     warnings))

