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

<p>This transform is unique and we generally expect to run it as a very early
step after parsing.  Normally it is invoked as part of @(see annotate).  It is
also closely related to @(see shadowcheck)&mdash;indeed, it invokes
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
declared, and mark them with the @('VL_IMPLICIT') attribute.  Historically this
attribute was used in a ``typo detection'' @(see vl-lint) check, which has
become defunct but can probably be easily revived.</p>")

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
    ;; Don't try to understand this.  It's just an nrev-optimized version of
    ;; vl-expr-names-for-implicit, which is very tricky.  See its docs below.
    (vl-expr-case x
      (:vl-index
       (if (and (vl-idscope-p x.scope)
                (vl-partselect-case x.part :none)
                (atom x.indices))
           (nrev-push (vl-idscope->name x.scope) nrev)
         (nrev-fix nrev)))
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
names within expressions lead to implicit wires being declared.  See especially
the @('vl/linttest/implicit') tests for a test suite of sorts.  Here are some
findings:</p>

<ul>

<li>If we have a plain name on the left-hand side, like @('assign foo = 0'), then
we get an implicit wire.</li>

<li>If we instead have something like @('assign foo.bar = 0'), then we're
referencing something elsewhere and we don't want to create implicit wires
named @('foo') or @('bar').</li>

<li>When @('foo') is not previously declared, both NCVerilog and VCS reject
@('assign foo[0] = 0').  So I don't think we want to collect names that have
indexing or part-selects applied to them.  On the other hand, NCVerilog rejects
but VCS accepts (with warnings) gates such as @('buf mybuf(o, foo[0])'), and
seems to infer a wire for @('foo').  We will try to mimic NCVerilog's behavior
since it is more consistent, and <i>not</i> infer wires that are being indexed
into.</li>

<li>Suppose we explicitly declare @('wire [3:0] vec;').  Then both NCVerilog
and VCS reject @('assign vec[w] = 0') where @('w') is undeclared, instead of
inferring an implicit wire @('w').  So I think we do not want to collect names
from <i>within</i> the indices and part-selects.  However, distressingly, NCV
and VCS both accept @('buf myand2(o, vec[w]);'), so what is the rule?  I think
it seems most sensible to not infer implicit wires within the index
expressions.</li>

<li>Within gate connections, NCV and VCS allow implicit wires in many
expressions, e.g., @('w1 + w2'), @('myfun(w)'), both sides of @('inside')
expressions, etc.  (These kinds of expressions aren't allowed in the LHS of
assignments, so we don't worry about them there.)</li>

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
         (if (atom x)
             nil
           (with-local-nrev
             (vl-exprlist-names-for-implicit-nrev x nrev)))))
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
                             :type *vl-plain-old-logic-type*
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
               (new-st       vl-implicitst-p))
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


(define vl-genbase-make-implicit-wires
  :short "Make implicit wires for a single modelement."
  ((x        vl-genelement-p  "Base genelement to process.")
   (st       vl-implicitst-p  "Current state, so we can tell what is declared.")
   (impitems vl-vardecllist-p "Accumulator for implicit variable declarations.")
   (warnings vl-warninglist-p))
  :guard (vl-genelement-case x :vl-genbase)
  :returns (mv (warnings vl-warninglist-p)
               (st       vl-implicitst-p)
               (impitems vl-vardecllist-p))

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
       (impitems (vl-vardecllist-fix impitems))
       (item     (vl-genbase->item x))
       (tag      (tag item))

       ;; Note: recall the FEATURE-CREEP WARNING above.  We are too dumb to do
       ;; anything yet except track what is declared and add implicit wires as
       ;; needed.  Do not try to notice uses of undeclared wires, warn about
       ;; multiply declared things, etc., because it's too hard until more has
       ;; been resolved.

       ((when (or (eq tag :vl-interfaceport)
                  (eq tag :vl-regularport)))
        (mv (fatal :type :vl-programming-error
                   :msg "~a0: unexpected kind of module item."
                   :args (list item))
            st impitems))

       ((when (eq tag :vl-portdecl))
        (b* ((declname  (vl-portdecl->name item))
             (portdecls (hons-acons declname item (vl-implicitst->portdecls st)))
             (st        (change-vl-implicitst st :portdecls portdecls)))
          (mv (ok) st impitems)))

       ((when (or (eq tag :vl-vardecl)
                  (eq tag :vl-paramdecl)
                  (eq tag :vl-import)))
        (b* (((mv warnings st) (vl-blockitem-update-implicit item st warnings)))
          (mv warnings st impitems)))

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
             (impitems    (append imp-nets impitems)))
          (mv (ok) st impitems)))

       ((when (eq tag :vl-assign))
        (b* (((vl-assign item))
             (lhs-names  (vl-expr-names-for-implicit item.lvalue))
             (imp-names  (mergesort (vl-remove-declared-wires lhs-names st)))
             (imp-nets   (vl-make-ordinary-implicit-wires item.loc imp-names))
             (decls      (vl-implicitst->decls st))
             (decls      (make-fal (pairlis$ imp-names nil) decls))
             (st         (change-vl-implicitst st :decls decls))
             (impitems   (append imp-nets impitems)))
          (mv (ok) st impitems)))

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
             (impitems  (append imp-nets impitems)))
          (mv warnings st impitems)))

       ((when (or (eq tag :vl-initial)
                  (eq tag :vl-final)
                  (eq tag :vl-always)
                  (eq tag :vl-dpiexport)

                  ;; BOZO not sure how these are scoped yet.
                  (eq tag :vl-clkdecl)
                  (eq tag :vl-gclkdecl)
                  (eq tag :vl-defaultdisable)
                  (eq tag :vl-bind)
                  (eq tag :vl-class)
                  (eq tag :vl-covergroup)
                  (eq tag :vl-elabtask)
                  ))
        ;; These don't declare any names, nothing to do.
        (mv (ok) st impitems))

       ((when (or (eq tag :vl-fundecl)
                  (eq tag :vl-taskdecl)
                  (eq tag :vl-dpiimport)
                  (eq tag :vl-assertion)
                  (eq tag :vl-cassertion)
                  (eq tag :vl-property)
                  (eq tag :vl-sequence)
                  (eq tag :vl-typedef)
                  (eq tag :vl-fwdtypedef)
                  (eq tag :vl-genvar)
                  ;; SystemVerilog-2012 Section 25.5 (page 718): "modport
                  ;; declarations shall not implicitly declare new ports"
                  (eq tag :vl-modport)
                  ))
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
                         (:vl-genvar     (vl-genvar->name item))
                         (:vl-modport    (vl-modport->name item))))
             (decls    (hons-acons name nil (vl-implicitst->decls st)))
             (st       (change-vl-implicitst st :decls decls)))
          (mv (ok) st impitems))))

    (impossible)
    (mv (ok) st impitems)))


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


(defines vl-genelementlist-make-implicit-wires
  :verify-guards nil

  :prepwork
  ((local (defthm count-help
            (< (vl-genelement-count (first (vl-genblock->elems x)))
               (vl-genblock-count x))
            :rule-classes :linear
            :hints(("Goal" :expand ((vl-genblock-count x)
                                    (vl-genelementlist-count (vl-genblock->elems x))))))))


  (define vl-genelementlist-make-implicit-wires
    :short "Main loop for introducing implicit wires."
    ((x        vl-genelementlist-p "List of items to process, in parse order.")
     (st       vl-implicitst-p     "Evolving state, keeps track of what's declared.")
     (newitems vl-genelementlist-p "Accumulator for rewritten versions of the items in @('x'), reverse parse order.")
     (impitems vl-vardecllist-p    "Accumulator for implicit wire declarations to add to this scope.")
     (warnings vl-warninglist-p    "Accumulator for warnings."))
    :returns
    (mv (warnings vl-warninglist-p)
        (st       vl-implicitst-p)
        (newitems vl-genelementlist-p)
        (impitems vl-vardecllist-p))
    :measure (two-nats-measure (vl-genelementlist-count x) 0)
    (b* ((st       (vl-implicitst-fix st))
         (warnings (vl-warninglist-fix warnings))
         (newitems (vl-genelementlist-fix newitems))
         (impitems (vl-vardecllist-fix impitems))
         ((when (atom x))
          (mv (ok) st newitems impitems))
         ((mv warnings st new-car impitems)
          (vl-genelement-make-implicit-wires (car x) st impitems warnings))
         (newitems (cons new-car newitems)))
      (vl-genelementlist-make-implicit-wires (cdr x) st newitems impitems warnings)))

  (define vl-genblock-make-implicit-wires
    :short "Only for genblocks that definitely introduce their own scope, e.g.,
            named begin/end blocks or generate loops.  (Not for conditional
            generate blocks because scoping is trickier there.)"
    ((x        vl-genblock-p)
     (st       vl-implicitst-p)
     (warnings vl-warninglist-p))
    :returns
    (mv (warnings vl-warninglist-p)
        (st       vl-implicitst-p)
        (new-x    vl-genblock-p "Updated version of the block, extended with declarations
                                 for any implicit wires as necessary."))
    :measure (two-nats-measure (vl-genblock-count x) 0)
    :long "<p>SystemVerilog-2012 Section 6.10: wires that are implicitly
           declared within a generate block are local to that generate block.
           So we attach the implicit declarations for everything within this
           block to this scope, without leaking them into the outer
           context.</p>"
    (b* (((vl-genblock x) (vl-genblock-fix x))
         (st              (vl-implicitst-fix st))
         (warnings        (vl-warninglist-fix warnings))
         ((mv warnings new-st new-elems new-implicit)
          (vl-genelementlist-make-implicit-wires x.elems st nil nil warnings))
         ;; Sticking the implicit declarations first is important so that
         ;; shadowcheck will see them first, before seeing any of the items
         ;; that might depend on them.
         (new-x (change-vl-genblock x :elems (append (vl-modelementlist->genelements new-implicit)
                                                     (rev new-elems))))
         (- (vl-implicitsts-restore-fast-alists st new-st))
         ;; Done with the inside of the block; all that's left is to extend the
         ;; current scope with a declaration of the block name, if any.  NOTE:
         ;; if you're tempted to not add the name here, to clean up the
         ;; ugliness in loops in vl-genelement-make-implicit-wires, please note
         ;; that IF/CASE statement handling is also relying on the name being
         ;; added here, so this really is the lesser evil!
         (new-st (if x.name
                     (change-vl-implicitst st :decls (hons-acons x.name x (vl-implicitst->decls st)))
                   st)))
      (mv warnings new-st new-x)))

  (define vl-genblock-under-cond-make-implicit-wires
    :short "Only for genblocks that are found in conditional contexts, i.e.,
            the then/else branches of if statements, or the bodies of case
            statements.  (Scoping is tricky here)."
    ((x        vl-genblock-p)
     (st       vl-implicitst-p)
     (warnings vl-warninglist-p))
    :returns
    (mv (warnings vl-warninglist-p)
        (st       vl-implicitst-p)
        (new-x    vl-genblock-p "Updated version of the block, extended with
                                 declarations for any implicit wires as necessary."))
    :measure (two-nats-measure (vl-genblock-count x) 1)
    :long "<p>This is slightly tricky because of the condnest case.  For
           background see SystemVerilog-2012 Section 27.5 and see @(see
           vl-genblock).</p>

           <p>We are careful here not to introduce new scopes when we go into
           condnest ifs.  Note though that the only places we could introduce
           implicit wires are always in the leaves of the IF structure, and the
           leaves always have a block.</p>"
    (b* (((vl-genblock x) (vl-genblock-fix x))
         (st       (vl-implicitst-fix st))
         (warnings (vl-warninglist-fix warnings))

         ((unless x.condnestp)
          ;; Not the special nested cond case; handle it as a regular genblock
          ;; that creates its own scope, etc.  We don't need to add any
          ;; implicit items in this case.
          (b* (((mv warnings st new-x) (vl-genblock-make-implicit-wires x st warnings)))
            (mv warnings st new-x)))

         ;; Check that the element in the block is as expected for a condnest.
         ((unless (and (tuplep 1 x.elems)
                       (or (vl-genelement-case (car x.elems) :vl-genif)
                           (vl-genelement-case (car x.elems) :vl-gencase))))
          (mv (fatal :type :vl-programming-error
                     :msg "Block flagged as nested conditional was not: ~a0"
                     :args (list x))
              st x))

         ;; Now, without entering a new scope, rewrite the element.
         ((mv warnings st new-car impitems)
          (vl-genelement-make-implicit-wires (car x.elems) st nil warnings))
         ((when impitems)
          ;; Sanity check.  I think this should never happen because the
          ;; element of X should be an IF/CASE whose leaves should all be
          ;; scopes, and any implicit wires needed for those leaves should
          ;; therefore be added to the leaves themselves.
          (mv (fatal :type :vl-programming-error
                     :msg "Expected all implicit wires from a nested generate
                           if/case to be associated with the sub-block: ~a0"
                     :args (list x))
              st x))
         (new-x (change-vl-genblock x :elems (list new-car))))
      (mv (ok) st new-x)))

  (define vl-genelement-make-implicit-wires
    ((x        vl-genelement-p)
     (st       vl-implicitst-p)
     (impitems vl-vardecllist-p "Accumulator for implicit wire declarations.")
     (warnings vl-warninglist-p))
    :measure (two-nats-measure (vl-genelement-count x) 0)
    :returns (mv (new-warnings vl-warninglist-p)
                 (st           vl-implicitst-p)
                 (new-x        vl-genelement-p)
                 (impitems     vl-vardecllist-p))
    (b* ((x        (vl-genelement-fix x))
         (st       (vl-implicitst-fix st))
         (warnings (vl-warninglist-fix warnings))
         (impitems (vl-vardecllist-fix impitems)))

      (vl-genelement-case x
        :vl-genbase
        ;; X itself doesn't change, but it may require implicit wires to be
        ;; declared on its behalf.
        (b* (((mv warnings st impitems)
              (vl-genbase-make-implicit-wires x st impitems warnings)))
          (mv warnings st x impitems))

        :vl-genbegin
        ;; We expect to have already flattened out unnamed blocks, so make sure
        ;; that we have a name (and hence that this block indeed is supposed to
        ;; introduce a scope.)
        (b* (((unless (stringp (vl-genblock->name x.block)))
              (mv (fatal :type :vl-programming-error
                         :msg "Unnamed block still present during make-implicit-wires: ~a0."
                         :args (list x))
                  st x impitems))
             ((mv warnings st new-block) (vl-genblock-make-implicit-wires x.block st warnings))
             (new-x                      (change-vl-genbegin x :block new-block)))
          (mv warnings st new-x impitems))

        :vl-genloop
        ;; Any implicit items get added to the loop body.
        (b* ((fake-paramdecl
              ;; See SystemVerilog-2012 Section 27.4.  The genvar for the loop
              ;; is supposed to be a localparam for the loop body.  So create a
              ;; fake paramdecl, basically only for use in error messages.
              (make-vl-paramdecl :name x.var
                                 :localp t
                                 :type (make-vl-explicitvalueparam
                                        :type *vl-plain-old-integer-type*)
                                 :loc x.loc))
             ;; Now process the loop body in a new scope where the loop
             ;; variable is already declared.
             (new-decls                       (hons-acons x.var fake-paramdecl (vl-implicitst->decls st)))
             (local-st                        (change-vl-implicitst st :decls new-decls))
             ((mv warnings local-st new-body) (vl-genblock-make-implicit-wires x.body local-st warnings))
             (new-x                           (change-vl-genloop x :body new-body))
             ;; Gross hack.  After we're done with the loop body, we want to
             ;; keep the body's name (if any).  But we definitely don't want to
             ;; keep the loop variable, because it's no longer in scope.  This
             ;; is a problem: above we added the loop variable (explicitly) and
             ;; the loop body's name (via vl-genblock-make-implicit-wires) to
             ;; the local-st.  So if we throw away the local-st to get rid of
             ;; the loop variable, we also throw away the loop body's name.
             ;; Well, fine: we'll throw it away and then add it back in, here.
             (- (vl-implicitsts-restore-fast-alists st local-st))
             (name (vl-genblock->name x.body))
             (st   (if name
                       (b* ((new-decls (hons-acons name x (vl-implicitst->decls st))))
                         (change-vl-implicitst st :decls new-decls))
                     st)))
          (mv warnings st new-x impitems))

        :vl-genif
        ;; Note that if the then/else blocks are named, then they have their
        ;; own scopes and we'll automatically add their names to ST as we
        ;; process their blocks.
        ;;
        ;; Subtle: Note that on NCV and VCS, names seem to be regarded as
        ;; declared even when the block doesn't end up existing
        ;; post-elaboration; see failtest/gen1l.v.  So, we're doing it right
        ;; and don't have to be any smarter about it.
        ;;
        ;; Subtle: The then/else blocks might (legally) reuse names.  We don't
        ;; care about this here because we only care about whether names are
        ;; declared, not how many times they have been declared.  So even if
        ;; they both have the same name, it's fine for us to have added them
        ;; both.
        (b* (((mv warnings st new-then)
              (vl-genblock-under-cond-make-implicit-wires x.then st warnings))
             ((mv warnings st new-else)
              (vl-genblock-under-cond-make-implicit-wires x.else st warnings))
             (new-x (change-vl-genif x :then new-then :else new-else)))
          (mv warnings st new-x impitems))

        :vl-gencase
        ;; Essentially similar to genif.
        (b* (((mv warnings st new-cases)
              (vl-gencaselist-make-implicit-wires x.cases st warnings))
             ((mv warnings st new-default)
              (vl-genblock-under-cond-make-implicit-wires x.default st warnings))
             (new-x (change-vl-gencase x :cases new-cases :default new-default)))
          (mv warnings st new-x impitems))

        :otherwise
        ;; This should be fine, don't really need to support genarray things
        ;; here, because this is part of annotate.
        (mv (fatal :type :vl-programming-error
                   :msg "~a0: Didn't expect to see this kind of generate element yet."
                   :args (list (vl-genelement-fix x)))
            st x impitems))))

  (define vl-gencaselist-make-implicit-wires
    ((x        vl-gencaselist-p)
     (st       vl-implicitst-p)
     (warnings vl-warninglist-p))
    :returns
    (mv (warnings vl-warninglist-p)
        (st       vl-implicitst-p)
        (new-x    vl-gencaselist-p))
    :measure (two-nats-measure (vl-gencaselist-count x) 0)
    (b* ((x        (vl-gencaselist-fix x))
         (st       (vl-implicitst-fix st))
         ((when (atom x))
          (mv (ok) st nil))
         ((cons exprs1 block1) (car x))
         ((mv warnings st new-block1)
          (vl-genblock-under-cond-make-implicit-wires block1 st warnings))
         ((mv warnings st new-rest)
          (vl-gencaselist-make-implicit-wires (cdr x) st warnings))
         (new-x (cons (cons exprs1 new-block1)
                      new-rest)))
      (mv warnings st new-x)))

  ///
  (verify-guards vl-genelementlist-make-implicit-wires)
  (deffixequiv-mutual vl-genelementlist-make-implicit-wires))


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

       ;; Note: It's OK that this doesn't go into sub-generate constructs:
       ;; port declarations aren't allowed in generates.

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
                                         :nettype portdecl.nettype
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
       (impitems nil)
       ;; Add regular implicit wires.  This reverses the items.
       ((mv warnings st newitems impitems)
        (vl-genelementlist-make-implicit-wires loaditems st newitems impitems warnings))
       ;; Ugly append to make the implicit items come "first" (preserving reverse order)
       (newitems (append newitems (vl-modelementlist->genelements impitems)))
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

(defsection implicit-wires-generate-scoping
  :short "Some details about generate block scoping quirks which affect
implicit wire handling and other aspects of scoping."

  :long "<p>AFAICT none of the following is discussed in the SystemVerilog-2012
standard.</p>

<p>Unlike any other kind of @('generate') statement, it seems that plain old
@('begin ... end') style generate blocks with no names are treated by
commercial simulators in a special way.  In particular, they don't (at least at
the top level; see below) introduce new scopes.</p>

<p>This has implications for correctly introducing implicit wires and also for
scoping in general.  We want to be smart enough to prohibit things like:</p>

@({
     module m;
       not(v, w);       // implicit declaration of w
       begin
         wire w = 1;    // illegal (redefinition of w)
       end
     endmodule
})

<p>while at the same time allowing legal things like:</p>

@({
     module m;
       not(v, w);       // implicit declaration of w
       begin : myblock
         wire w = 1;    // fine (this is a new scope)
       end
     endmodule
})


<h5>Top-level begin/end: no name = no scope</h5>

<p>On both NCV and VCS, at least at the top level of a module, an unnamed block
does NOT appear to introduce a new scope.  Instead, wires declared inside it
become visible to the rest of the module after the generate, just as if they
were declared before the begin/end block.</p>

<p>Moreover, the following seem to be roughly(*) equivalent,</p>

@({
     module m ;                    module m ;
       begin
         ...              vs.           ...
       end
     endmodule                     endmodule
})

<p>(*) Exceptions we're aware of: begin/end blocks aren't allowed to have
ports, specify blocks, and specparams (Section 27.3) and parameter declarations
inside of begin/end blocks are supposed to be treated as localparams.  Testing
suggests that these restrictions still hold for unnamed top-level begin/end
blocks.  See especially @(see vl-genelementlist-flatten).</p>


<h5>Interior begin/end: no name = unclear scope</h5>

<p>We find that NCV and VCS <b>disagree</b> about the handling of scopes for
nested begin/end generate blocks.  In particular, consider something like:</p>

@({
    module m ;
    begin
      wire [3:0] w1 = 0;
      begin
        wire [3:0] w2 = 1;
      end
      wire [3:0] w3 = w1;
      wire [3:0] w4 = w2;
    end
    endmodule
})

<p>This code is happily accepted by NCVerilog, suggesting that the inner
begin/end block is not given its own scope.  However, VCS instead produces an
error saying that @('w2') is not declared, which suggests that VCS treats
interior begin/end blocks as new scopes.  Note however that VCS still treats
top-level begin/end blocks as not being new scopes.  Messy.</p>

<p>In VL we choose to follow the behavior of NCVerilog since it is seems more
consistent.  That is, we will universally regard any unnamed begin/end generate
blocks as <b>not</b> introducing a scope.</p>


<h5>Eliminating begin/end blocks</h5>

<p>Since we are going to treat unnamed begin/end blocks as not having their own
scopes, there's really no reason to keep them around.</p>

<p>It also seems like a good idea to get rid of them.  If we keep unnamed
begin/end blocks around, then when building scopes for @(see vl-scopestack)s,
we would need to would need to collect all the items from (say) the module, and
then also dive down into the begin/end blocks and (recursively) collect up the
items within them.  It seems much nicer and simpler to inline the contents of
these generate blocks into their surroundings.  Similarly we would need to do
this sort of thing for packages.</p>

<p>We do this inlining as part of introducing implicit wires.  This seems like
a reasonable place: it certainly needs to happen before or during implicit wire
introduction in order to get implicit wires right.  It also needs to happen
before we create scopestacks for shadowchecking.</p>")

(local (xdoc::set-default-parents implicit-wires-generate-scoping))

(defines vl-genelementlist-flatten
  :short "Special flattening of unnamed @('begin/end') blocks."
  :long "<p>See @(see implicit-wires-generate-scoping).  Here we flatten the
         unnamed begin/end blocks and take care of weird special cases like
         checking that generates have no ports, converting @('parameter')s to
         @('localparam')s within generates, etc.</p>"
  :verify-guards nil
  (define vl-genblock-flatten ((x vl-genblock-p)
                               (warnings vl-warninglist-p))
    ;; Used for IF, CASE, and FOR loop bodies
    :returns (mv (warnings vl-warninglist-p)
                 (new-x    vl-genblock-p))
    :measure (vl-genblock-count x)
    (b* (((vl-genblock x))
         ((mv warnings new-elems) (vl-genelementlist-flatten x.elems t nil warnings)))
      (mv warnings (change-vl-genblock x :elems (rev new-elems)))))

  (define vl-genelementlist-flatten ((x vl-genelementlist-p)
                                     (genp booleanp)
                                     (newitems vl-genelementlist-p)
                                     (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (newitems vl-genelementlist-p))
    :measure (vl-genelementlist-count x)
    (b* (((when (atom x))
          (mv (ok) (vl-genelementlist-fix newitems)))
         ((mv warnings newitems) (vl-genelement-flatten (car x) genp newitems warnings)))
      (vl-genelementlist-flatten (cdr x) genp newitems warnings)))

  (define vl-genelement-flatten ((x        vl-genelement-p     "Single item to process.")
                                 (genp     booleanp            "Are we currently in a generate block?")
                                 (newitems vl-genelementlist-p "Accumulator for replacement items.")
                                 (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (newitems vl-genelementlist-p "Extended with @('x') or its replacement."))
    :measure (vl-genelement-count x)
    (b* ((x        (vl-genelement-fix x))
         (newitems (vl-genelementlist-fix newitems)))
      (vl-genelement-case x
        :vl-genbase
        (b* (((unless genp)
              ;; Not inside a generate, don't do anything.
              (mv (ok) (cons x newitems)))

             ((when (mbe :logic (vl-portdecl-p x.item)
                         :exec (eq (tag x.item) :vl-portdecl)))
              ;; SystemVerilog-2012 27.2, page 749. "A generate may not
              ;; contain port declarations."  See failtest/gen10.v
              (mv (fatal :type :vl-bad-portdecl
                         :msg "~a0: port declarations are not allowed in generates."
                         :args (list x))
                  (cons x newitems)))

             ((when (mbe :logic (vl-paramdecl-p x.item)
                         :exec (eq (tag x.item) :vl-paramdecl)))
              ;; SystemVerilog-2012 27.2, page 749.  "Parameters declared in
              ;; generate blocks shall be treated as localparams."  See also
              ;; failtest/gen11.v
              (b* ((new-item
                    (if (vl-paramdecl->localp x.item)
                        x.item
                      (change-vl-paramdecl
                       x.item
                       :localp t
                       ;; Attribute just for debugging.
                       :atts (cons (cons "VL_LOCALIZED_DUE_TO_GENERATE" nil)
                                   (vl-paramdecl->atts x.item)))))
                   (new-x (change-vl-genbase x :item new-item)))
                (mv (ok) (cons new-x newitems))))

             ;; BOZO if support for specify blocks or specparam declarations
             ;; is ever added, we will need to extend this to prohibit them
             ;; per 27.2.  For now they're not implemented.
             )

          ;; If we get here, this is some other kind of module element.  There
          ;; aren't any nested generates.  Just keep it.
          (mv (ok) (cons x newitems)))

        :vl-genbegin
        (b* (((vl-genblock x.block))
             ((unless x.block.name)
              ;; Unnamed begin/end block gets flattened into the current scope.
              (vl-genelementlist-flatten x.block.elems t newitems warnings))
             ;; Named begin/end block gets its own scope, so we don't want to
             ;; get rid of it; just flatten the elements inside of it
             ;; (independently of the current newitems).
             ((mv warnings newelems) (vl-genelementlist-flatten x.block.elems t nil warnings))
             (new-block              (change-vl-genblock x.block :elems (rev newelems))))
          (mv (ok) (cons (change-vl-genbegin x :block new-block) newitems)))

        :vl-genif
        (b* (((mv warnings new-then) (vl-genblock-flatten x.then warnings))
             ((mv warnings new-else) (vl-genblock-flatten x.else warnings))
             (new-x (change-vl-genif x :then new-then :else new-else)))
          (mv (ok) (cons new-x newitems)))

        :vl-gencase
        (b* (((mv warnings new-cases) (vl-gencaselist-flatten x.cases warnings))
             ((mv warnings new-default) (vl-genblock-flatten x.default warnings))
             (new-x (change-vl-gencase x :default new-default :cases new-cases)))
          (mv (ok) (cons new-x newitems)))

        :vl-genloop
        (b* (((mv warnings new-body) (vl-genblock-flatten x.body warnings))
             (new-x (change-vl-genloop x :body new-body)))
          (mv (ok) (cons new-x newitems)))

        :vl-genarray
        (mv (fatal :type :vl-programming-error
                   :msg "Didn't expect to see genarray before elaboration: ~a0."
                   :args (list x))
            (cons x newitems)))))

  (define vl-gencaselist-flatten ((cases vl-gencaselist-p)
                                  (warnings vl-warninglist-p))
    :returns (mv (warnings vl-warninglist-p)
                 (new-cases vl-gencaselist-p))
    :measure (vl-gencaselist-count cases)
    (b* ((cases (vl-gencaselist-fix cases))
         ((when (atom cases))
          (mv (ok) nil))
         ((cons exprs1 block1) (car cases))
         ((mv warnings new-block1) (vl-genblock-flatten block1 warnings))
         ((mv warnings rest) (vl-gencaselist-flatten (cdr cases) warnings)))
      (mv warnings (cons (cons exprs1 new-block1) rest))))
  ///
  (verify-guards vl-genelementlist-flatten
    :hints ((and stable-under-simplificationp
                 '(:in-theory (enable tag-reasoning))))))


(define vl-module-make-implicit-wires ((x  vl-module-p)
                                       (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x))
       (x.loaditems (and x.parse-temps
                         (append (vl-modelementlist->genelements
                                  (vl-parse-temps->paramports x.parse-temps))
                                 (vl-parse-temps->loaditems x.parse-temps))))
       ((mv warnings rev-flatitems)
        (vl-genelementlist-flatten x.loaditems nil nil x.warnings))
       ((mv newitems warnings)
        (vl-make-implicit-wires-main (rev rev-flatitems) x.ifports ss warnings))
       (parse-temps (and x.parse-temps
                         (change-vl-parse-temps x.parse-temps
                                                :paramports nil
                                                :loaditems newitems))))
    (change-vl-module (vl-genblob->module (vl-sort-genelements newitems) x)
                      :ports x.ports
                      :parse-temps parse-temps
                      :warnings warnings)))

(defprojection vl-modulelist-make-implicit-wires ((x  vl-modulelist-p)
                                                  (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-make-implicit-wires x ss))


(define vl-interface-make-implicit-wires ((x  vl-interface-p)
                                       (ss vl-scopestack-p))
  ;; Just styled after vl-module-make-implicit-wires
  :returns (new-x vl-interface-p)
  (b* (((vl-interface x))
       (x.loaditems (and x.parse-temps
                         (append (vl-modelementlist->genelements
                                  (vl-parse-temps->paramports x.parse-temps))
                                 (vl-parse-temps->loaditems x.parse-temps))))
       (ifports (vl-collect-interface-ports x.ports))
       ((mv warnings rev-flatitems)
        (vl-genelementlist-flatten x.loaditems nil nil x.warnings))
       ((mv newitems warnings)
        (vl-make-implicit-wires-main (rev rev-flatitems) ifports ss warnings))
       (parse-temps (and x.parse-temps
                         (change-vl-parse-temps x.parse-temps
                                                :paramports nil
                                                :loaditems newitems))))
    (change-vl-interface (vl-genblob->interface (vl-sort-genelements newitems) x)
                         :ports x.ports
                         :parse-temps parse-temps
                         :warnings warnings)))

(defprojection vl-interfacelist-make-implicit-wires ((x  vl-interfacelist-p)
                                                     (ss vl-scopestack-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-make-implicit-wires x ss))


(define vl-design-make-implicit-wires ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))

       ;; Part 1 -- Introduce implicit wires
       (ss         (vl-scopestack-init x))
       (mods       (vl-modulelist-make-implicit-wires x.mods ss))
       (interfaces (vl-interfacelist-make-implicit-wires x.interfaces ss))
       (new-x      (change-vl-design x
                                     :mods mods
                                     :interfaces interfaces))
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
