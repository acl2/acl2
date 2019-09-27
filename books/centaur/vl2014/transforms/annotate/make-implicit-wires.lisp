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
(include-book "shadowcheck")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

; We might consider unlocalizing some of these and finding them homes, but
; they're not necessarily that widely useful and, for instance, the modelement
; rules here might be kind of slow in general.

(local (in-theory (disable (tau-system))))

(local (defthm vl-modelement-p-when-vl-blockitem-p
         (implies (vl-blockitem-p x)
                  (vl-modelement-p x))
         :hints(("Goal" :in-theory (enable tag-reasoning
                                           vl-blockitem-p
                                           vl-modelement-p)))))

(local (defthm vl-modelementlist-p-when-vl-blockitemlist-p
         (implies (vl-blockitemlist-p x)
                  (vl-modelementlist-p x))
         :hints(("Goal" :induct (len x)))))

(defxdoc make-implicit-wires
  :parents (annotate)
  :short "Add declarations for implicit wires."

  :long "<p>Verilog allows wires to be implicitly declared in certain
cases.</p>

<p>Historically, VL added explicit declarations for these wires as part of the
@(see loader), even before a proper @(see vl-module-p) structures were
generated.  This allowed all transforms to expect that every wire should have a
declaration.  It also allowed us to consider the order of module elements,
without having to rely on some technique such as the @(see vl-location-p)s
associated with module elements, which could be unreliable if a module spans
multiple files, e.g., because of includes.</p>

<p>When we added support for SystemVerilog @('import') statements, we found
this approach to be tricky.  In particular, to decide whether we need to add a
declaration for some particular wire @('foo'), we now need to consider whether
@('foo') is defined by any imported package.  For this, we really want to be
able to inspect the whole @(see vl-design) while making implicit wires.</p>

<p>We therefore decided to split making implicit wires out of the parser and
into a proper transform.  However, we generally expect to run this transform
very early, perhaps even as the first step after parsing.  Normally this should
be done as part of the @(see annotate) transform.</p>

<p>Note that this transform is somewhat unique.  It is the only transform that
considers the module elements in the order that they occur in the file.  It
reads this information from the @('loaditems') field of the @(see vl-module).
As part of this transform, the @('loaditems') field is <b>cleared</b>.  Other
transforms should never use @('loaditems').</p>


<h3>Implicit Wires in the Verilog-2005 Standard</h3>

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
certain scoping issues.  In particular, suppose we see a procedural continuous
assignment statement, @('assign w = ...'), where @('w') is not declared.  If
this statement occurs in a task or a named block within an initial/always
statement, should the declaration for @('w') be added to the module or to this
more local scope?  I'm not sure.  So, the good thing about not inferring
implicit nets for these assignments is that I don't have to be able to answer
the question, because I'm not going to infer a net anyway.</p>

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

(local (xdoc::set-default-parents make-implicit-wires))

; FEATURE-CREEP WARNING.
;
; It is tempting to try to do a lot here, e.g., we might want to check for any
; illegally redefined wires, compatibility between port and net declarations,
; etc.  But after some false starts down this road, I think this is a mistake.
;
; We only need to care about the order of elements to (1) properly handle
; adding implicit wires, and (2) make sure things are defined before being
; used.  Other kinds of well-formedness checks, e.g., that make sure nothing is
; multiply defined, that the ports/netdecls agree, etc., really don't need to
; consider module element order, so keep them separate!

(define vl-make-ordinary-implicit-wires
  :short "Generate net declarations for one-bit implicit wires."
  ((loc   vl-location-p)
   (names string-listp))
  :returns (nets vl-vardecllist-p)
  :long "<p>We are given @('x'), a string list that should initially contain
the names of some implicit wires that we are supposed to introduce, and
@('loc'), a @(see vl-location-p) that should be the @('minloc') for the module.
We produce a list of one-bit @(see vl-vardecl-p)s, one for each name in
@('x').</p>"

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

(define vl-collect-exprs-for-implicit-wires-from-namedarg
  :parents (vl-modinst-exprs-for-implicit-wires)
  ((x vl-namedarg-p))
  :returns
  (mv (main  vl-exprlist-p "Expressions where implicit wires are allowed.")
      (other vl-exprlist-p "Expressions where implicit wires are not allowed."))
  (b* (((vl-namedarg x))
       ((when x.nameonly-p)
        ;; SystemVerilog name-only style arguments like .foo are not allowed to
        ;; introduce implicit wires, so put them into the "other" wires.
        (mv nil (vl-maybe-expr-allexprs x.expr))))
    (mv (vl-maybe-expr-allexprs x.expr) nil))
  ///
  (defmvtypes vl-collect-exprs-for-implicit-wires-from-namedarg (true-listp true-listp))

  (defthm vl-collect-exprs-for-implicit-wires-from-namedarg-complete
    ;; Just to make sure we keep this up to date if we ever change
    ;; vl-namedarg-allexprs
    (b* (((mv main other)
          (vl-collect-exprs-for-implicit-wires-from-namedarg x)))
      (set-equiv (append main other)
                 (vl-namedarg-allexprs x)))
    :hints(("Goal" :in-theory (enable set-equiv vl-namedarg-allexprs)))))

(define vl-collect-exprs-for-implicit-wires-from-namedargs
  :parents (vl-modinst-exprs-for-implicit-wires)
  ((x vl-namedarglist-p))
  :returns
  (mv (main  vl-exprlist-p "Expressions where implicit wires are allowed.")
      (other vl-exprlist-p "Expressions where implicit wires are not allowed."))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv main1 other1) (vl-collect-exprs-for-implicit-wires-from-namedarg (car x)))
       ((mv main2 other2) (vl-collect-exprs-for-implicit-wires-from-namedargs (cdr x))))
    (mv (append main1 main2)
        (append other1 other2)))
  ///
  (defmvtypes vl-collect-exprs-for-implicit-wires-from-namedargs (true-listp true-listp))

  (local (defthm l1
           (b* (((mv main other)
                 (vl-collect-exprs-for-implicit-wires-from-namedarg x)))
             (set-equiv (vl-namedarg-allexprs x)
                        (append main other)))))

  (local (in-theory (disable vl-collect-exprs-for-implicit-wires-from-namedarg-complete)))

  (defthm vl-collect-exprs-for-implicit-wires-from-namedargs-complete
    ;; Just to make sure we keep this up to date if we ever change
    ;; vl-namedarglist-allexprs
    (b* (((mv main other)
          (vl-collect-exprs-for-implicit-wires-from-namedargs x)))
      (set-equiv (append main other)
                 (vl-namedarglist-allexprs x)))
    :hints(("Goal"
            :induct (len x)
            :in-theory (enable set-equiv vl-namedarglist-allexprs)))))

(define vl-collect-exprs-for-implicit-wires-from-portargs
  :parents (vl-modinst-exprs-for-implicit-wires)
  ((x vl-arguments-p))
  :returns
  (mv (main  vl-exprlist-p "Expressions where implicit wires are allowed.")
      (other vl-exprlist-p "Expressions where implicit wires are not allowed."))
  (vl-arguments-case x
    (:vl-arguments-named
     (vl-collect-exprs-for-implicit-wires-from-namedargs x.args))
    (:vl-arguments-plain
     ;; If using plain arguments, there are no .name style arguments, so
     ;; everything is allowed to have implicit wires.
     (mv (vl-plainarglist-allexprs x.args)
         nil)))
  ///
  (defmvtypes vl-collect-exprs-for-implicit-wires-from-portargs (true-listp true-listp))

  (defthm vl-collect-exprs-for-implicit-wires-from-portargs-complete
    ;; Just to make sure we keep this up to date if we ever change
    ;; vl-arguments-allexprs
    (b* (((mv main other)
          (vl-collect-exprs-for-implicit-wires-from-portargs x)))
      (set-equiv (append main other)
                 (vl-arguments-allexprs x)))
    :hints(("Goal"
            :in-theory (enable set-equiv vl-arguments-allexprs)))))

(define vl-modinst-exprs-for-implicit-wires
  :short "Get the expressions from a module instance, for making implicit wires."
  ((x vl-modinst-p))
  :returns
  (mv (main vl-exprlist-p
            "The expressions from the modinst's port list, where implicit wires
             are allowed.")
      (other vl-exprlist-p
             "The other expressions in the module instance (its range,
              parameter list, etc.) where implicit wires aren't allowed."))
  (b* (((vl-modinst x) x)
       ((mv main other)
        (vl-collect-exprs-for-implicit-wires-from-portargs x.portargs)))
    (mv main (append other
                     (vl-maybe-range-allexprs x.range)
                     (vl-paramargs-allexprs x.paramargs)
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
    :hints(("Goal" :in-theory (e/d (set-equiv vl-modinst-allexprs)
                                   (acl2::subsetp-append1))))))

(define vl-gateinst-exprs-for-implicit-wires
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


(define vl-vardecl-exprs-for-implicit-wires
  :short "Gets the expressions from a variable declaration, for making implicit
wires.  We omit the expressions inside the datatype."
  ((x vl-vardecl-p))
  :returns (exprs vl-exprlist-p)
  (b* (((vl-vardecl x) x))
    (append (vl-maybe-expr-allexprs x.initval)
            (vl-maybe-gatedelay-allexprs x.delay))))


(defprod vl-implicitst
  :short "State for the @(see make-implicit-wires) transform."
  :tag nil
  :layout :tree
  ((portdecls "Fast alist binding names of declared port names to anything."
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
the names of any port declarations, ordinary declarations, global names, and
imported names."
  ((names string-listp)
   (st    vl-implicitst-p))
  :returns
  (implicit string-listp
            "Subset of @('names') that don't have declarations already,
             e.g., names that we don't want to add local declarations for.")
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

(define vl-warn-about-undeclared-wires
  :short "Add fatal warnings about names that are used but not declared."
  ((ctx       vl-modelement-p "Where we saw these names.")
   (names     string-listp    "The names we saw.")
   (st        vl-implicitst-p)
   (warnings  vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((ctx        (vl-modelement-fix ctx))
       (undeclared (mergesort (vl-remove-declared-wires names st)))
       ((when (atom undeclared))
        (ok)))
    (fatal :type :vl-warn-undeclared
           :msg (if (atom (cdr undeclared))
                    "~a0: identifier ~w1 is used but not yet declared."
                  "~a0: identifiers ~&2 are used but not yet declared.")
           :args (list ctx (car undeclared) undeclared))))

(define vl-import-check-undeclared ((x vl-import-p)
                                    (st vl-implicitst-p)
                                    (warnings vl-warninglist-p))
  :returns
  (mv (new-warnings vl-warninglist-p)
      (new-st       vl-implicitst-p))
  (b* (((vl-import x) (vl-import-fix x))
       (package  (vl-scopestack-find-package x.pkg (vl-implicitst->ss st)))
       (warnings (if package
                     (ok)
                   (fatal :type :vl-bad-import
                          :msg "~a0: trying to import from undefined package ~s1."
                          :args (list x x.pkg))))
       (imports  (vl-implicitst->imports st))
       (imports  (if (eq x.part :vl-import*)
                     ;; Add all the names from the package onto imports.
                     (hons-shrink-alist
                      ;; If the package wasn't found and we tried to
                      ;; import foo::* from it, we've already caused a
                      ;; fatal warning, so it's okay to fudge here.
                      (and package
                           (vl-package-scope-item-alist-top package))
                      imports)
                   (hons-acons (the string x.part) t imports)))
       (st       (change-vl-implicitst st :imports imports)))
    (mv warnings st)))

(define vl-blockitem-check-undeclared
  :short "Check for undeclared wires in an arbitrary @(see vl-blockitem-p), and
extends @('decls') with the newly declared name."

  ((x         vl-blockitem-p "Arbitrary block item to process.")
   (st        vl-implicitst-p)
   (warnings  vl-warninglist-p))
  :returns
  (mv (new-warnings vl-warninglist-p)
      (new-st       vl-implicitst-p))
  (b* ((x (vl-blockitem-fix x))
       ((when (eq (tag x) :vl-import))
        (vl-import-check-undeclared x st warnings))
       ((mv name exprs)
        (case (tag x)
          (:vl-vardecl   (mv (vl-vardecl->name x)   (vl-vardecl-exprs-for-implicit-wires x)))
          (otherwise     (mv (vl-paramdecl->name x) (vl-paramdecl-allexprs x)))))

       ;; First, make sure all the names used in expressions like ranges and
       ;; array dimensions have been declared.  Then, add a binding for the
       ;; declaration.  Doing it in this order lets us catch garbage like
       ;; reg [r:0] r.
       (used-names (vl-exprlist-varnames exprs))
       (warnings   (vl-warn-about-undeclared-wires x used-names st warnings))
       (decls      (hons-acons name nil (vl-implicitst->decls st)))
       (st         (change-vl-implicitst st :decls decls)))
    (mv warnings st)))

(define vl-blockitemlist-check-undeclared
  :short "Extends @(see vl-blockitem-check-undeclared) across a @(see
vl-blockitemlist-p)."
  ((x        vl-blockitemlist-p)
   (st       vl-implicitst-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (st       vl-implicitst-p))
  (b* (((when (atom x))
        (mv (ok) (vl-implicitst-fix st)))
       ((mv warnings st)
        (vl-blockitem-check-undeclared (car x) st warnings)))
    (vl-blockitemlist-check-undeclared (cdr x) st warnings)))

(defines vl-stmt-check-undeclared
  :short "Check an arbitrary @(see vl-stmt-p) for uses of undeclared names."

  :long "<p>Most statements are totally straightforward; we just need to make
sure that all identifiers used anywhere within them have been declared.</p>

<p>Named blocks are the only complication.  They have their own scope and can
have their own declarations and imports, which come before their
sub-statements.  So, if we see a named block, we basically fork the decls and
imports to create a local namespace, add all of the local declarations to it,
and then check all the sub-statements in this extended namespace.</p>"

  (define vl-stmt-check-undeclared
    ((ctx       vl-modelement-p "Where this statement occurs.")
     (x         vl-stmt-p       "The statement to process.")
     (st        vl-implicitst-p)
     (warnings  vl-warninglist-p))
    :returns (new-warnings vl-warninglist-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    (b* ((x (vl-stmt-fix x))

         ((when (vl-atomicstmt-p x))
          (b* ((used-names (vl-exprlist-varnames (vl-stmt-allexprs x)))
               (warnings   (vl-warn-about-undeclared-wires ctx used-names st warnings)))
            warnings))

         ((when (eq (vl-stmt-kind x) :vl-blockstmt))
          (b* (((vl-blockstmt x) x)
               ((vl-implicitst st) st)
               ;; Initially the local-decls will just be the current decls
               ;; we've seen, since things in the module's scope can still be
               ;; referenced from within the named block.
               (local-decls (hons-shrink-alist st.decls nil))
               (local-imports (hons-shrink-alist st.imports nil))
               (local-st    (change-vl-implicitst st :decls local-decls :imports local-imports))
               ;; Add in all local declarations.
               ((mv warnings local-st) (vl-blockitemlist-check-undeclared x.loaditems local-st warnings))
               ;; Check all the sub-statements in the extended scope.
               (warnings (vl-stmtlist-check-undeclared ctx x.stmts local-st warnings)))
            ;; Note that a named block doesn't have any other kinds of
            ;; expressions (i.e., x.ctrl and x.exprs are necessarily empty).
            ;; So, there's nothing to check other than the statements, and
            ;; hence we're already done and can now throw away the local scope.
            (fast-alist-free (vl-implicitst->decls local-st))
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
         (local-names (vl-exprlist-varnames local-exprs))
         (warnings    (vl-warn-about-undeclared-wires ctx local-names st warnings)))

      ;; Finally check the substatements.
      (vl-stmtlist-check-undeclared ctx (vl-compoundstmt->stmts x) st warnings)))

    (define vl-stmtlist-check-undeclared ((ctx      vl-modelement-p)
                                          (x        vl-stmtlist-p)
                                          (st       vl-implicitst-p)
                                          (warnings vl-warninglist-p))
      :returns (new-warnings vl-warninglist-p)
      :measure (vl-stmtlist-count x)
      (b* (((when (atom x))
            (ok))
           (warnings (vl-stmt-check-undeclared ctx (car x) st warnings)))
        (vl-stmtlist-check-undeclared ctx (cdr x) st warnings)))

    ///
    (verify-guards vl-stmt-check-undeclared)
    (deffixequiv-mutual vl-stmt-check-undeclared))


(define vl-fundecl-check-undeclared
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
   (st        vl-implicitst-p)
   (warnings  vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((x (vl-fundecl-fix x))
       ((vl-fundecl x) x)

       ;; Check for undeclared names in the non-local parts (the inputs and
       ;; return value range.)  It's not quite right to do the inputs here, as
       ;; described above, but in practice it shouldn't be much of a problem.
       (other-names (vl-exprlist-varnames (append (vl-portdecllist-allexprs x.portdecls)
                                                  (vl-datatype-allexprs x.rettype))))
       (warnings    (vl-warn-about-undeclared-wires x other-names st warnings))

       ;; Now make a local scope and add the local declarations, as in named
       ;; block statements.
       (local-decls (hons-shrink-alist (vl-implicitst->decls st) nil))
       (local-imports (hons-shrink-alist (vl-implicitst->imports st) nil))
       (local-st    (change-vl-implicitst st :decls local-decls :imports local-imports))

       ;; Now check/add the block items.  As we do this, we're acting like the
       ;; inputs haven't been declared yet.  That's not quite right, but it
       ;; should be practically pretty reasonable since it's not valid to refer
       ;; to an input in the other declarations.
       ((mv warnings local-st)
        (vl-blockitemlist-check-undeclared x.blockitems local-st warnings))

       ;; Okay, now add the inputs to the local scope, since it's valid to
       ;; refer to them in the body.  Also add in the function's name since it
       ;; can be a valid return value.
       (local-decls  (vl-implicitst->decls local-st))
       (local-decls  (make-fal (pairlis$ (vl-portdecllist->names x.portdecls) nil) local-decls))
       (local-decls  (hons-acons x.name nil local-decls))
       (local-st     (change-vl-implicitst local-st :decls local-decls))

       ;; The local scope is constructed, check the function's body.
       (warnings (vl-stmt-check-undeclared x x.body local-st warnings)))
    ;; That's it, all done with the local scope.
    (fast-alist-free local-decls)
    warnings))


(define vl-taskdecl-check-undeclared
  :short "Check an arbitrary @(see vl-taskdecl-p) for uses of undeclared
names."
  :long "<p>This is nearly identical to @(see vl-fundecl-check-undeclared) and
it has the same problems with parameters.</p>"

  ((x         vl-taskdecl-p)
   (st        vl-implicitst-p)
   (warnings  vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* ((x (vl-taskdecl-fix x))
       ((vl-taskdecl x) x)

       ;; Check for undeclared names in the task's visible ports.  It's not
       ;; quite right to do the ports here if they have parameters, as
       ;; described above, but in practice it shouldn't be much of a problem.
       (other-names (vl-exprlist-varnames (vl-portdecllist-allexprs x.portdecls)))
       (warnings    (vl-warn-about-undeclared-wires x other-names st warnings))

       ;; Now make a local scope and add the local declarations, as in named
       ;; block statements.
       (local-decls (hons-shrink-alist (vl-implicitst->decls st) nil))
       (local-imports (hons-shrink-alist (vl-implicitst->imports st) nil))
       (local-st    (change-vl-implicitst st :decls local-decls :imports local-imports))

       ;; Now check/add the block items.  As we do this, we're acting like the
       ;; ports haven't been declared yet.  That's not quite right, but it
       ;; should be practically pretty reasonable since it's not valid to refer
       ;; to a port in the other declarations.
       ((mv warnings local-st)
        (vl-blockitemlist-check-undeclared x.blockitems local-st warnings))

       ;; Okay, now add the ports to the local scope, since it's valid to
       ;; refer to them in the body.
       (local-decls (vl-implicitst->decls local-st))
       (local-decls (make-fal (pairlis$ (vl-portdecllist->names x.portdecls) nil) local-decls))
       (local-st    (change-vl-implicitst local-st :decls local-decls))

       ;; The local scope is constructed, check the task's body.
       (warnings (vl-stmt-check-undeclared x x.body local-st warnings)))

    ;; That's it, all done with the local scope.
    (fast-alist-free local-decls)
    warnings))


(local (defthm crock
         (implies (vl-importpart-p x)
                  (equal (stringp x)
                         (not (equal x :vl-import*))))
         :hints(("Goal" :in-theory (enable vl-importpart-p)))))

(define vl-make-implicit-wires-aux
  :short "Main function for adding implicit wires."
  ((x        vl-genelementlist-p
             "Module elements to process, should be in the same order in which they
              were parsed.")
   (st       vl-implicitst-p)
   (implicit vl-vardecllist-p
             "Accumulator for new variable declarations to add.")
   (newitems vl-genelementlist-p
             "Accumulator for rewriting X and inserting implicit variable
              declarations right where they occur.")
   (warnings vl-warninglist-p
             "An ordinary @(see warnings) accumulator, which we may extend with
              fatal warnings (e.g., for undeclared identifiers) or non-fatal warnings
              (e.g., for compatibility warnings like <i>Verilog-XL doesn't
              infer an implicit wire here.</i>)."))

  :returns (mv (new-warnings vl-warninglist-p)
               (st           vl-implicitst-p)
               (implicit     vl-vardecllist-p)
               (newitems     vl-genelementlist-p))

  :long "<p>Note that to keep this code simple, we don't try to defend against
multiply declared names here.</p>

<p>We don't try to add any port declarations here, because we have to sort of
get through the whole module to make sure there isn't an explicit declaration
later on.  We handle that in @(see vl-make-implicit-wires-main).</p>"

  :measure (len x)
  :hooks ((:fix
           :hints (("Goal"
                    :expand ((:free (st implicit warnings newitems)
                              (vl-make-implicit-wires-aux (vl-genelementlist-fix x) st implicit newitems warnings))
                             (:free (st implicit warnings newitems)
                              (vl-make-implicit-wires-aux x st implicit newitems warnings)))))))

  :prepwork ((local (defthm vl-blockitem-p-when-vl-vardecl-p-no-limit
                      (implies (vl-vardecl-p x)
                               (vl-blockitem-p x))))
             (local (in-theory (disable vl-blockitem-p-when-vl-vardecl-p)))
             (local (defthm vl-blockitem-p-when-vl-paramdecl-p-no-limit
                      (implies (vl-paramdecl-p x)
                               (vl-blockitem-p x))))
             (local (in-theory (disable vl-blockitem-p-when-vl-paramdecl-p)))
             (local (in-theory (disable acl2::consp-under-iff-when-true-listp))))

  :guard-hints ((and stable-under-simplificationp
                     '(:use ((:instance vl-modelement-p-when-invalid-tag (x (vl-genbase->item (car x)))))
                       :in-theory (disable vl-modelement-p-when-invalid-tag))))

  (b* ((x        (vl-genelementlist-fix x))
       (st       (vl-implicitst-fix st))
       (warnings (vl-warninglist-fix warnings))
       (implicit (vl-vardecllist-fix implicit))
       (newitems (vl-genelementlist-fix newitems))

       ((when (atom x))
        (mv warnings st implicit newitems))

       ((unless (eq (vl-genelement-kind (car x)) :vl-genbase))
        ;; Ignore generate constructs until unparameterization
        (vl-make-implicit-wires-aux (cdr x) st implicit
                                    (cons (car x) newitems) warnings))

       (elem (vl-genelement-fix (car x)))
       (item (vl-genbase->item elem))
       (tag  (tag item))

       ((when (or (eq tag :vl-interfaceport)
                  (eq tag :vl-regularport)))
        ;; We shouldn't see any ports.
        (raise "We shouldn't see ports here.")
        (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings))

       ((when (eq tag :vl-portdecl))
        ;; We have to first make sure that there aren't undeclared
        ;; identifiers being used in the range, then record that a
        ;; declaration was made.  Doing it in this order lets us catch
        ;; garbage like input [in:0] in;
        (b* ((declname (vl-portdecl->name item))

             ;; BOZO this seems kind of bogus.  Shouldn't we be checking these things?

             ;; Note: We run into trouble here when ports are declared as
             ;; user-defined types, i.e. "input foo_t foo" -- we don't want to
             ;; count foo_t as an undeclared id.  Thinking about it more, it
             ;; doesn't seem like this is the right place to be checking for
             ;; this anyway, so just don't.
             ;; (varnames  (vl-exprlist-varnames (vl-portdecl-allexprs item)))
             ;; (warnings  (vl-warn-about-undeclared-wires item varnames st warnings))

             (st (change-vl-implicitst st
                                       :portdecls
                                       (hons-acons declname item (vl-implicitst->portdecls st))))
             (newitems (cons (car x) newitems)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))

       ((when (or (eq tag :vl-vardecl)
                  (eq tag :vl-paramdecl)))
        (b* (((mv warnings st)
              (vl-blockitem-check-undeclared item st warnings))
             (newitems (cons (car x) newitems)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))

       ;; Module and gate instances are relatively simple.  First, make sure
       ;; all the identifiers in their non-port expressions (like ranges and
       ;; parameter arguments) are declared.  Then, gather all identifiers
       ;; in their port arguments, and add declarations for any of them that
       ;; are not declared.

       ((mv inst-p loc main-exprs other-exprs maybe-name)
        (case tag
          (:vl-modinst
           (b* ((loc              (vl-modinst->loc item))
                ((mv main other)  (vl-modinst-exprs-for-implicit-wires item)))
             (mv t loc main other (vl-modinst->instname item))))
          (:vl-gateinst
           (b* ((loc              (vl-gateinst->loc item))
                ((mv main other)  (vl-gateinst-exprs-for-implicit-wires item)))
             (mv t loc main other (vl-gateinst->name item))))
          (otherwise
           (mv nil nil nil nil nil))))

       ((when inst-p)
        (b* ((other-names (vl-exprlist-varnames other-exprs))
             (main-names  (vl-exprlist-varnames main-exprs))
             (warnings    (vl-warn-about-undeclared-wires item other-names st warnings))
             (imp-names   (mergesort (vl-remove-declared-wires main-names st)))
             (imp-nets    (vl-make-ordinary-implicit-wires loc imp-names))
             (decls       (vl-implicitst->decls st))
             (decls       (make-fal (pairlis$ imp-names nil) decls))
             (decls       (if maybe-name (hons-acons maybe-name t decls) decls))
             (st          (change-vl-implicitst st :decls decls))
             (implicit    (append imp-nets implicit))
             (newitems    (append (vl-modelementlist->genelements imp-nets) newitems))
             (newitems    (cons (car x) newitems)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))

       ;; Assignments are a little complicated to add compatibility
       ;; warnings, but it still isn't too bad.

       ((when (eq tag :vl-assign))
        (b* (((vl-assign item) item)
             (lhs-names        (vl-expr-varnames item.lvalue))
             (imp-lhs          (mergesort (vl-remove-declared-wires lhs-names st)))
             (warnings
              (if (not imp-lhs)
                  warnings
                (warn :type :vl-tricky-implicit
                      :msg "~a0: wire~s1 ~&2 ~s3 implicitly declared by the ~
                            left-hand side of this assignment.  This is ~
                            perfectly valid according to the Verilog-2005 ~
                            standard, but some Verilog tools tools (like ~
                            Verilog-XL) do not support it, so for better ~
                            compatibility you may wish to add ~s4."
                      :args (list item
                                  (if (vl-plural-p imp-lhs) "s" "")
                                  imp-lhs
                                  (if (vl-plural-p imp-lhs) "are" "is")
                                  (if (vl-plural-p imp-lhs)
                                      "explicit declarations for these wires"
                                    "an explicit declaration of this wire")))))

             (decls      (vl-implicitst->decls st))
             (decls      (make-fal (pairlis$ imp-lhs nil) decls))
             (st         (change-vl-implicitst st :decls decls))

             (imp-nets   (vl-make-ordinary-implicit-wires item.loc imp-lhs))
             (implicit   (append imp-nets implicit))
             (newitems   (append (vl-modelementlist->genelements imp-nets) newitems))
             (newitems   (cons (car x) newitems))
             ;; Okay, all done adding implicit nets for the LHS.  Now make sure
             ;; all the other expressions are using declared ids.

             ;; BOZO it seems weird that we do this AFTER adding implicit nets?
             (other-names (vl-exprlist-varnames (cons item.expr (vl-maybe-gatedelay-allexprs item.delay))))
             (warnings    (vl-warn-about-undeclared-wires item other-names st warnings)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))

       ((when (eq tag :vl-alias))
        (b* (((vl-alias item) item)
             (lhs-names        (vl-expr-varnames item.lhs))
             (rhs-names        (vl-expr-varnames item.rhs))
             (imp-names        (mergesort (vl-remove-declared-wires (append lhs-names rhs-names) st)))
             (warnings
              (if (not imp-names)
                  warnings
                (warn :type :vl-tricky-implicit
                      :msg "~a0: wire~s1 ~&2 ~s3 implicitly declared by this ~
                            alias declaration."
                      :args (list item
                                  (if (vl-plural-p imp-names) "s" "")
                                  imp-names
                                  (if (vl-plural-p imp-names) "are" "is")))))

             (decls      (vl-implicitst->decls st))
             (decls      (make-fal (pairlis$ imp-names nil) decls))
             (st         (change-vl-implicitst st :decls decls))
             (imp-nets   (vl-make-ordinary-implicit-wires item.loc imp-names))
             (implicit   (append imp-nets implicit))
             (newitems   (append (vl-modelementlist->genelements imp-nets) newitems))
             (newitems   (cons (car x) newitems)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))

       ((when (or (eq tag :vl-initial)
                  (eq tag :vl-always)))
        ;; Statements are tricky because of named blocks, but we've already
        ;; dealt with how to handle them, and they can't introduce any
        ;; implicit wires, so this is easy.
        (b* ((stmt     (if (eq tag :vl-initial)
                           (vl-initial->stmt item)
                         (vl-always->stmt item)))
             (warnings (vl-stmt-check-undeclared item stmt st warnings))
             (newitems (cons (car x) newitems)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))

       ((when (eq tag :vl-fundecl))
        ;; Functions are tricky because they have their own scope, but we've
        ;; already dealt with how to handle them, and they can't introduce
        ;; any implicit wires, so this is easy.
        (b* ((warnings (vl-fundecl-check-undeclared item st warnings))
             (decls    (vl-implicitst->decls st))
             (decls    (hons-acons (vl-fundecl->name item) nil decls))
             (st       (change-vl-implicitst st :decls decls))
             (newitems (cons (car x) newitems)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))

       ((when (eq tag :vl-taskdecl))
        ;; Tasks are tricky because they have their own scope, but we've
        ;; already dealt with how to handle them, and they can't introduce
        ;; any implicit wires, so this is easy.
        (b* ((warnings (vl-taskdecl-check-undeclared item st warnings))
             (decls    (vl-implicitst->decls st))
             (decls    (hons-acons (vl-taskdecl->name item) nil decls))
             (st       (change-vl-implicitst st :decls decls))
             (newitems (cons (car x) newitems)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))

       ((when (eq tag :vl-import))
        (b* (((vl-import item))
             (package  (vl-scopestack-find-package item.pkg (vl-implicitst->ss st)))
             (warnings (if package
                           (ok)
                         (fatal :type :vl-bad-import
                                :msg "~a0: trying to import from undefined package ~s1."
                                :args (list item item.pkg))))
             (imports  (vl-implicitst->imports st))
             (imports  (if (eq item.part :vl-import*)
                           ;; Add all the names from the package onto imports.
                           (hons-shrink-alist
                            ;; If the package wasn't found and we tried to
                            ;; import foo::* from it, we've already caused a
                            ;; fatal warning, so it's okay to fudge here.
                            (and package
                                 (vl-package-scope-item-alist-top package))
                            imports)
                         (hons-acons (the string item.part) t imports)))
             (st       (change-vl-implicitst st :imports imports))
             (newitems (cons (car x) newitems)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))

       ((when (member tag '(:vl-modport :vl-typedef :vl-fwdtypedef)))
        (b* ((warnings (fatal :type :vl-unexpected-modelement
                              :msg "~a0: unexpected kind of module item."
                              :args (list item)))
             (newitems (cons (car x) newitems)))
          (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))
       ((when (eq tag :vl-genvar))
        ;; Ignore genvars
        (vl-make-implicit-wires-aux (cdr x) st implicit newitems warnings)))
    (impossible)
    (mv warnings st implicit newitems)))


(define vl-make-port-implicit-wires
  :short "@(call vl-make-port-implicit-wires) generates variable declarations
for ports that don't have corresponding variable declarations."
  ((portdecls "Alist binding names to port declarations."
              vl-portdecl-alist-p)
   (decls     "Alist binding names declared in the module to @('nil')."))

  :hooks nil ;; bozo wtf kind of crazy thing is this trying to prove?
  :verbosep t

  :returns
  (implicit vl-vardecllist-p
            "A list of new variable declarations, one for each port declaration
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

       (new-decl (make-vl-vardecl :name    portdecl.name
                                  :type    portdecl.type
                                  ;; [Jared] patch 2016-02-24: I want implicit wires to be
                                  ;; printed as "wire" instead of "logic" for legacy tools
                                  :nettype :vl-wire
                                  :atts    (cons (cons "VL_PORT_IMPLICIT" nil) portdecl.atts)
                                  :loc     portdecl.loc)))
    (cons new-decl
          (vl-make-port-implicit-wires (cdr portdecls) decls))))

(define vl-make-implicit-wires-main
  :short "Augment a list of module elements with declarations for any implicit
nets, and make sure that every identifier being used has a declaration."

  ((loaditems vl-genelementlist-p
              "All of the module elements from a single module, in the order they
               were parsed.")
   (ifports   vl-interfaceportlist-p
              "Interface ports for the module (we implicitly declare them first).")
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p
             "An ordinary @(see warnings) accumulator, which may be extended
              with fatal and/or nonfatal warnings."))
  :returns
  (mv (implicit  vl-vardecllist-p    "Declarations for implicit wires.")
      (newitems  vl-genelementlist-p "Extended loaditems (with implicit wires added).")
      (warnings  vl-warninglist-p    "Possibly extended @(see warnings)."))

  :long "<p>We try to add declarations for any implicit wires.  Unless there is
a fatal warning, the resulting module element list will have declarations for
all of its identifiers.</p>"

    (b* ((ifports (vl-interfaceportlist-fix ifports))
         (st (make-vl-implicitst :decls     (make-fast-alist
                                             (pairlis$ (vl-portlist->names ifports)
                                                       (list-fix ifports)))
                                 :portdecls nil
                                 :imports   nil
                                 :ss        ss))
         (newitems        nil)
         (normal-implicit nil)
         ((mv warnings st normal-implicit newitems)
          (vl-make-implicit-wires-aux loaditems st normal-implicit newitems warnings))
         ;; BOZO would be nice to use nreverse here
         (newitems (rev newitems))
         ((vl-implicitst st))
         (port-implicit (vl-make-port-implicit-wires st.portdecls st.decls))
         (- (fast-alist-free st.portdecls))
         (- (fast-alist-free st.decls))
         (- (fast-alist-free st.imports))
         (all-implicit (append-without-guard normal-implicit port-implicit)))
      (mv all-implicit newitems warnings)))

(define vl-module-make-implicit-wires ((x       vl-module-p)
                                       (ss      vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x))
       ((mv implicit newitems warnings)
        (vl-make-implicit-wires-main x.loaditems x.ifports ss x.warnings))
       (vardecls (append-without-guard implicit x.vardecls)))
    (change-vl-module x
                      :vardecls vardecls
                      :warnings warnings
                      :loaditems newitems)))

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
