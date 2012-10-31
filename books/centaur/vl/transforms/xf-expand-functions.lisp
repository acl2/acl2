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
(include-book "xf-stmt-rewrite")
(include-book "xf-subst")
(include-book "../mlib/context")
(include-book "../mlib/allexprs")
(include-book "../mlib/namefactory")
(include-book "../util/toposort")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(defxdoc expand-functions
  :parents (transforms)
  :short "Expand away function declarations and calls."

  :long "<p>This transform can eliminate a fairly reasonable subset of Verilog
functions by replacing their uses with ordinary assignments.</p>

<p>Note: that our way of handling functions does not really preserve
hierarchical identifiers that lead into functions.</p>


<h3>Supported Subset</h3>

<p>The automatic keyword may be provided or omitted, but the subset we support
makes its use fairly meaningless (essentially we only implement functions that
behave the same whether automatic or not.)</p>

<p>The return type can be @(':vl-signed') or @(':vl-unsigned') (which is our
representation of a \"plain\" return type) and a range is permitted.  But we do
not support functions whose return type is integer, real, realtime, or
time.</p>

<p>There may be any number of inputs of type @(':vl-signed') or
@(':vl-unsigned') (which is our representation for plain and @('reg') type
inputs).  Each input may optionally have a range.  But we do not support inputs
whose types are integer, real, realtime, or time.</p>

<p>There may be any number of reg declarations, each of which may be signed or
not and may have a range.  We do not permit regs with array dimensions.  We
also do not permit regs with initial values (per the Verilog grammar this
shouldn't be possible, but our @(see vl-regdecl-p) representation does not
forbid it.)</p>

<p>There may be any number of plain parameter and localparam declarations.  By
plain, we mean that we do not allow ranges, the signed keyword, etc.  (There
doesn't seem to be any way to initialize parameters in a function, so this is
basically just a way to define function-local constants.)  We do not allow
parameters that have the same names as other parameters in the module, because
this can lead to subtle issues related to declaration order.</p>

<p>We do not permit variable declarations (e.g., integer variables, real
variables, etc.) or event declarations.</p>

<p>The body of the function must contain a <b>flat list of assignments</b>,
starting with assignments to registers that have been declared within the
function (if any), and ending with an assignment to the function's name (in all
cases).  We do not allow any branching, looping, timing, case statements,
etc.</p>

<p>This restriction is overly severe and parts of it may eventually be lifted.
At present we at least do some basic rewriting of the statement, which allows
us to flatten sub-blocks.  In the long run, we may eventually want to try to
support at least some if-then-else statements, case statements, etc.</p>

<p>Finally, we require that <b>every register declared in the function is
completely written before it is read</b>.  This restriction is intended to
ensure that a function's result depends only upon its inputs and the other,
current state of the module that it is inspecting.  For instance, we allow you
to write functions such as:</p>

@({
function foo ;
  input a;
  input b;
  reg r1;
  reg r2;
  begin
   r1 = a & b;
   r2 = r1 & c;  // c is presumably a wire in the module
   foo = r1 ^ r2;
  end
endfunction
})

<p>But we do NOT allow you to switch the order of these statements, e.g.,</p>

@({
  begin
   r2 = r1 & c;  // using the old value of r1
   r1 = a & b;
   foo = r1 ^ r2;
  end
})

<p>Because this can lead to very strange, timing-sensitive interactions when
there are multiple calls of the function, and generally seems like an
unreasonable thing to do.</p>

<p>We do not support recursive functions.  I mean, come on.  Do you think we
are Lisp programmers or something?</p>


<h3>Transformation Approach</h3>

<p>Given the above restrictions, there are a couple of basic approaches that we
could take for eliminating functions and replacing them with ordinary
assignments.  Here is a sample module that we can consider.</p>

@({
module foo (...);
  wire w = ...;

  function f ;
    input a;
    input b;
    f = (a ^ w) | tmp;
  endfunction

  wire r1 = f(v1, v2) & f(v2, v3);
  wire r2 = f(v3, v4);
endmodule
})

<p>An <b>inlining approach</b> would be to mangle the names of the wires in the
function and lift its assignments up into the containing module, e.g.,</p>

@({
module foo (...);
  wire w = ...;

  wire _tmp_f1 = (v1 ^ w) | v2;
  wire _tmp_f2 = (v2 ^ w) | v3;
  wire r1 = _tmp_f1 & _tmp_f2;

  wire _tmp_f3 = (v3 ^ w) | v4;
  wire r2 = _tmp_f2;
endmodule
})

<p>Alternately a <b>submodule approach</b> would be to write a new module that
implements the function, and replace calls of the function with instances of
this submodule.  For instance:</p>

@({
module \foo$f (o, a, b, w);
  input a, b, w;
  output o;
  assign o = (a ^ w) | b;
endmodule

module foo (...);
  wire w = ...;

  wire _tmp_f1, _tmp_f2, _tmp_f3;

  \foo$f _finst_1 (_tmp_f1, v1, v2, w);
  \foo$f _finst_2 (_tmp_f2, v2, v3, w);
  wire r1 = _tmp_f1 & _tmp_f2;

  \foo$f _finst_3 (_tmp_f3, v3, v4, w);
  wire r2 = _tmp_f3;
endmodule
})

<p>Both approaches have some good and bad things about them.  Inlining is nice
because we don't have to think very hard about how the use of non-inputs works.
For instance, in the submodule approach we have to realize that @('f') reads
from @('w'), an ordinary wire in the module, and so @('foo$f') has to take this
extra input.  But with the inlining approach, using @('w') is no big deal and
we can probably avoid some of this complication.</p>

<p>Another nice thing about inlining is that most hierarchical references that
originate within the function will probably still be working correctly.  That
is, if we refer to @('submod.wire') from within the function, then this is
still a submodule that we can see from the expanded code.</p>

<p>The submodule approach is kind of nice in that it avoids introducing a pile
of additional wires and assignments into the main module, and probably helps to
keep the transformed output smaller when the functions involved are large.  It
would probably be possible to account for hierarchical identifiers that are
being used within the function through some kind of flattening, e.g., if
@('submod.wire') is used by the function's code, then the submodule we create
could have an extra input that receives it.</p>

<p>Either approach has problems with hierarchical identifiers that point into
the function itself.  I'm not sure how to resolve that, but it doesn't seem
particularly meaningful to write a HID that points at, say, @('foo.f.a'), since
there are multiple instances of @('f') and so which one is being referred
to?</p>

<p>For now, I use the inlining approach because it seems somewhat simpler.  But
it would probably not be too difficult to switch to the submodule
approach.</p>")



; -----------------------------------------------------------------------------
;
;                        Dependency-Order Sorting
;
; -----------------------------------------------------------------------------

(defsection vl-function-dep-graph
  :parents (vl-depsort-functions)
  :short "Build a dependency graph for function definitions."

  :long "<p>@(call vl-function-dep-graph) takes a list of function declarations
and produces an alist associating funtion names (strings) to the the lists of
all functions that are called in their bodies (string lists, perhaps with
duplicates).  This graph is suitable for sorting with @(see toposort).</p>

<p>If we run into a recursive function, the dep graph will have a
self-dependency.</p>"

  (defund vl-function-dep-graph (x)
    (declare (xargs :guard (vl-fundecllist-p x)))
    (if (atom x)
        nil
      (let* ((fun1  (car x))
             (name1 (vl-fundecl->name fun1))
             (deps1 (vl-exprlist-funnames (vl-fundecl-allexprs fun1))))
        (hons-acons name1 deps1
                    (vl-function-dep-graph (cdr x))))))

  (local (in-theory (enable vl-function-dep-graph)))

  (defthm alist-keys-of-vl-function-dep-graph
    (equal (alist-keys (vl-function-dep-graph x))
           (vl-fundecllist->names x))))


(defsection vl-reorder-fundecls
  :parents (vl-fundecllist-p filtering-by-name vl-depsort-functions)
  :short "@(call vl-reorder-fundecls) extract the named functions from @('x'),
a @(see vl-fundecllist-p), in the same order as @('names')."

  :long "<p>This is similar to @(see vl-keep-fundecls), but
@('vl-keep-fundecls') preserves the order of @('x'), whereas this explicitly
reorders @('x') to match @('names').</p>"

  (defund vl-reorder-fundecls (names x)
    (declare (xargs :guard (and (string-listp names)
                                (vl-fundecllist-p x))))
    (if (atom names)
        nil
      (let ((decl (vl-find-fundecl (car names) x)))
        (if decl
            (cons decl (vl-reorder-fundecls (cdr names) x))
          (vl-reorder-fundecls (cdr names) x)))))

  (local (in-theory (enable vl-reorder-fundecls)))

  (defthm vl-fundecllist-p-of-vl-reorder-fundecls
    (implies (force (vl-fundecllist-p x))
             (vl-fundecllist-p (vl-reorder-fundecls names x))))

  (local (defthm l1
           (implies (not (member-equal (vl-fundecl->name a) names))
                    (not (member-equal a (vl-reorder-fundecls names x))))
           :hints(("Goal" :in-theory (disable (force))))))

  (local (defthm l2-helper
           (implies (vl-find-fundecl name x)
                    (member-equal (vl-find-fundecl name x) x))
           :hints(("Goal" :in-theory (e/d (vl-find-fundecl) ((force)))))))

  (local (defthm l2
           (implies (and (not (member-equal a x)))
                    (not (member-equal a (vl-reorder-fundecls names x))))
           :hints(("Goal" :in-theory (disable (force))))))

  (defthm subsetp-equal-of-vl-reorder-fundecls
    ;; pick-a-point with l2
    (implies (subsetp-equal (double-rewrite names) (vl-fundecllist->names x))
             (subsetp-equal (vl-reorder-fundecls names x) x))
    :hints((set-reasoning)))


  ;; For the other direction we need no-duplicatesp-equal, since "shadowed"
  ;; function definitions wouldn't be included since vl-find-fundecl just
  ;; grabs the first decl by name.

  (local (defthm l3
           (implies (and (member-equal a x)
                         (no-duplicatesp-equal (vl-fundecllist->names x)))
                    (equal (vl-find-fundecl (vl-fundecl->name a) x)
                           a))
           :hints(("Goal" :in-theory (enable vl-find-fundecl)))))

  (local (defthm l4
           (implies (and (member-equal a x)
                         (member-equal (vl-fundecl->name a) names)
                         (no-duplicatesp-equal (vl-fundecllist->names x))
                         (vl-fundecllist-p x))
                    (member-equal a (vl-reorder-fundecls names x)))))

  (defthm member-equal-of-vl-reorder-fundecls
    (implies (and (no-duplicatesp-equal (vl-fundecllist->names x))
                  (force (vl-fundecllist-p x)))
             (iff (member-equal a (vl-reorder-fundecls names x))
                  (and (member-equal a x)
                       (member-equal (vl-fundecl->name a) names)))))


  (local (defthm other-direction ;; pick-a-point
           (implies (and (no-duplicatesp-equal (vl-fundecllist->names x))
                         (subsetp-equal (vl-fundecllist->names x) names)
                         (vl-fundecllist-p x))
                    (subsetp-equal x (vl-reorder-fundecls names x)))
           :hints((acl2::witness :ruleset (acl2::subsetp-equal-witnessing)))))

  (defthm vl-reorder-fundecls-under-set-equivp
    (implies (and (no-duplicatesp-equal (vl-fundecllist->names x))
                  (set-equivp (double-rewrite names) (vl-fundecllist->names x))
                  (force (vl-fundecllist-p x)))
             (set-equivp (vl-reorder-fundecls names x)
                            (double-rewrite x)))
    :hints(("Goal" :in-theory (enable set-equivp)))))




(defsection vl-depsort-functions
  :parents (expand-functions)
  :short "Rearrange function declarations so that they are in dependency order,
if possible."

  :long "<p><b>Signature:</b> @(call vl-depsort-functions) returns @('(mv
successp warnings sorted-fundecls)').</p>

<p>Since functions can call one another and can be listed in any order, it is
useful to be able to put them into a dependency order; we take advantage of
this when we flatten their templates, see @(see vl-flatten-funtemplates).</p>

<p>We will fail if there are any circular function dependencies or recursive
functions; in this case @('successp') is nil and a fatal warning will be
added.</p>"

  (local (defthm crock
           (implies (and (string-listp y)
                         (subsetp-equal x y)
                         (true-listp x))
                    (string-listp x))))

  (local (defthm crock2
           (implies (string-listp (alist-keys graph))
                    (string-listp (mv-nth 1 (toposort graph))))))


  (defund vl-depsort-functions (x warnings)
    "Returns (MV SUCCESSP WARNINGS SORTED-X)"
    (declare (xargs :guard (and (vl-fundecllist-p x)
                                (vl-warninglist-p warnings))))
    (b* ((graph (vl-function-dep-graph x))

         ;; Quick sanity check for unique function names
         (dupes (duplicated-members (alist-keys graph)))
         ((when dupes)
          (fast-alist-free graph)
          (b* ((w (make-vl-warning
                   :type :vl-bad-functions
                   :msg "Multiple function declarations for ~&0."
                   :args (list dupes)
                   :fatalp t
                   :fn 'vl-depsort-functions)))
            (mv nil (cons w warnings) x)))

         ;; Try to topologically sort the dependency graph; if this fails then
         ;; order is just the names of the functions that are in a loop.
         ((mv successp order) (toposort graph))
         (- (fast-alist-free graph))
         ((unless successp)
          (b* ((w (make-vl-warning
                   :type :vl-function-loop
                   :msg "Functions have circular dependencies: ~&0."
                   :args (list order)
                   :fatalp t
                   :fn 'vl-depsort-functions)))
            (mv nil (cons w warnings) x)))

         ;; We successfully put the function names into dependency order, so
         ;; just rearrange the functions into this dependency order.
         (sorted-x (vl-reorder-fundecls order x)))
      (mv t warnings sorted-x)))

  (local (in-theory (enable vl-depsort-functions)))

  (defthm vl-depsort-functions-under-set-equivp
    ;; This shows that no functions are added/lost as a result of depsorting.
    (implies (force (vl-fundecllist-p x))
             (set-equivp (mv-nth 2 (vl-depsort-functions x warnings))
                            x))
    :hints(("Goal" :in-theory (enable set-equivp))))

  (defthm vl-warninglist-p-of-vl-depsort-functions
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-depsort-functions x warnings)))))

  (defthm vl-fundecllist-p-of-vl-depsort-functions
    (implies (force (vl-fundecllist-p x))
             (vl-fundecllist-p (mv-nth 2 (vl-depsort-functions x warnings))))))




; -----------------------------------------------------------------------------
;
;                      Handling Function Parameters
;
; -----------------------------------------------------------------------------

(defsection vl-check-fun-parameters-deforder
  :parents (vl-fundecl-expand-params)
  :short "Ensure that a function's parameters are defined before they are used."

  :long "<p><b>Signature:</b> @(call vl-check-fun-parameters-deforder) returns
@('(mv okp warnings)').</p>

<p>Here, @('bad-params') is initially the list of all parameter declaration
names for this function.  We remove their names as we encounter their
declarations, and add fatal warnings if we find a declaration that is using
@('bad-params').</p>

<p>The Verilog specification does not address whether parameters need to be
introduced before being used, but other tools like Verilog-XL and NCVerilog
require it.</p>

<p>There is probably good reason for us to also require it.  For instance, the
parameters in a function can shadow global parameters, but on Verilog-XL and
NCVerilog the shadowing only happens after they are introduced.  This can lead
to strange behavior, e.g., if we have a function with declarations like
these:</p>

@({
 reg [width-1:0] r;
 parameter width = 5;
 reg [width-1:0] s;
})

<p>Then if there's a @('width') parameter defined outside the function, in the
module, @('r') and @('s') can end up having different widths!</p>

<p>We think that is crazy and therefore don't allow function parameters to
shadow module parameters.  But, it seems useful to still check that if there
are any uses of parameters in other declarations from the function, then they'd
better come after the parameter is introduced.</p>"

  (defund vl-check-fun-parameters-deforder (x bad-params warnings function)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-blockitemlist-p x)
                                (string-listp bad-params)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))
                    :guard-debug t))
    (b* (((when (atom x))
          (mv t warnings))
         (x1     (car x))
         (x1-tag (tag x1))
         (allexprs (case x1-tag
                     (:vl-regdecl   (vl-regdecl-allexprs x1))
                     (:vl-paramdecl (vl-paramdecl-allexprs x1))
                     (:vl-vardecl   (vl-vardecl-allexprs x1))
                     (:vl-eventdecl (vl-eventdecl-allexprs x1))))
         (names    (vl-exprlist-names allexprs))
         (bad-used (intersectp-equal bad-params names))
         ((when bad-used)
          (b* ((w (make-vl-warning
                   :type :vl-function-param-used-before-def
                   :msg "In ~a0, the parameter~s1 ~&2 ~s3 used before being ~
                         declared; we don't permit this since it isn't ~
                         tolerated by other tools such as Verilog-XL and ~
                         NCVerilog."
                   :args (list function
                               (if (vl-plural-p bad-used) "s" "")
                               bad-used
                               (if (vl-plural-p bad-used) "are" "is"))
                   :fatalp t
                   :fn 'vl-check-fun-parameters-deforder)))
            (mv nil (cons w warnings))))
         (bad-params (if (eq x1-tag :vl-paramdecl)
                         (remove-equal (vl-paramdecl->name x1) bad-params)
                       bad-params)))
      (vl-check-fun-parameters-deforder (cdr x) bad-params warnings function)))

  (local (in-theory (enable vl-check-fun-parameters-deforder)))

  (defthm vl-warninglist-p-of-vl-check-fun-parameters-deforder
    (implies (vl-warninglist-p warnings)
             (vl-warninglist-p (mv-nth 1 (vl-check-fun-parameters-deforder x bad-params warnings function))))))



(defsection vl-check-fun-params-no-overlap
  :parents (vl-fundecl-expand-params)
  :short "Ensure that a function's parameters do not shadow other things in the
module."

  :long "<p><b>Signature:</b> @(call vl-check-fun-params-no-overlap) returns
@('(mv okp warnings)').</p>

<p>Here, @('x') is the list of parameter declarations for the function and
@('mod') is the module that the function occurs in; @('warnings') is an
ordinary @(see warnings) accumulator, which may be extended, and @('function')
is just used as a context for error messages.</p>

<p>We don't allow parameters to shadow other things in the module since that
seems weird and has various corner cases with respect to declarations being
defined before use, e.g., see @(see vl-check-fun-parameters-deforder).</p>

<p>We don't expect many parameters in a function, so we use slow moditem
lookups here, figuring that it'll be cheaper than building a @(see
vl-moditem-alist).</p>"

  (defund vl-check-fun-params-no-overlap (x mod warnings function)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-paramdecllist-p x)
                                (vl-module-p mod)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))))
    (b* (((when (atom x))
          (mv t warnings))
         (name1 (vl-paramdecl->name (car x)))
         (item1 (vl-find-moduleitem name1 mod))
         ((unless item1)
          (vl-check-fun-params-no-overlap (cdr x) mod warnings function))
         (w (make-vl-warning
             :type :vl-bad-function-parameter
             :msg "In ~a0, parameter ~s1 has the same name as ~a2; we don't ~
                   allow function parameters to shadow other module items ~
                   because it seems underspecified by the Verilog standard ~
                   and generally somewhat error-prone."
             :args (list function name1 item1)
             :fatalp t
             :fn 'vl-check-fun-params-no-overlap)))
      (mv nil (cons w warnings))))

  (local (in-theory (enable vl-check-fun-params-no-overlap)))

  (defthm vl-warninglist-p-of-vl-check-fun-params-no-overlap
    (implies (vl-warninglist-p warnings)
             (vl-warninglist-p (mv-nth 1 (vl-check-fun-params-no-overlap x mod warnings function))))))


(defsection vl-fun-paramdecllist-types-okp
  :parents (vl-fundecl-expand-params)
  :short "Check that the parameters in a function are sufficiently simple to
handle."

  :long "<p><b>Signature:</b> @(call vl-fun-paramdecllist-types-okp) returns
@('(mv okp warnings)').</p>

<p>We make sure that all of the parameters in the function are plain parameters
with no ranges or weird types.  This restriction might not be necessary, but we
are not sure whether other kinds of parameters would require some special
handling.</p>"

  (defund vl-fun-paramdecllist-types-okp (x warnings function)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-paramdecllist-p x)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))))
    (b* (((when (atom x))
          (mv t warnings))

         ((vl-paramdecl x1) (car x))
         ((unless (eq x1.type :vl-plain))
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-paramdecl
                   :msg "In ~a0, parameter ~s1 has unsupported type ~s2."
                   :args (list function x1.name x1.type)
                   :fatalp t
                   :fn 'vl-fun-paramdecllist-types-okp)))
            (mv nil (cons w warnings))))

         ((when x1.range)
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-paramdecl
                   :msg "In ~a0, parameter ~s1 has a range, but this is not ~
                         supported."
                   :args (list function x1.name)
                   :fatalp t
                   :fn 'vl-fun-paramdecllist-types-okp)))
            (mv nil (cons w warnings)))))

      (vl-fun-paramdecllist-types-okp (cdr x) warnings function)))

  (local (in-theory (enable vl-fun-paramdecllist-types-okp)))

  (defthm vl-warninglist-p-of-vl-fun-paramdecllist-types-okp
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-fun-paramdecllist-types-okp x warnings function))))))


(defsection vl-fundecl-param-sigma
  :parents (vl-fundecl-expand-params)
  :short "@(call vl-fundecl-param-sigma) constructs a @(see vl-sigma-p) that
binds parameter names to their values."

  (defund vl-fundecl-param-sigma (x)
    (declare (xargs :guard (vl-paramdecllist-p x)))
    (if (atom x)
        nil
      (cons (cons (vl-paramdecl->name (car x))
                  (vl-paramdecl->expr (car x)))
            (vl-fundecl-param-sigma (cdr x)))))

  (local (in-theory (enable vl-fundecl-param-sigma)))

  (defthm vl-sigma-p-of-vl-fundecl-param-sigma
    (implies (force (vl-paramdecllist-p x))
             (vl-sigma-p (vl-fundecl-param-sigma x)))))


(defsection vl-fundecl-expand-params
  :parents (expand-functions)
  :short "Eliminate parameters from a function."
  :long "<p><b>Signature:</b> @(call vl-fundecl-expand-params) returns @('(mv
successp warnings x-prime)').</p>

<p>As inputs, @('x') is a @(see vl-fundecl-p) that might have parameters and
@('mod') is the module in which it resides; @('warnings') is an ordinary @(see
warnings) accumulator which may be extended, possibly with fatal warnings.</p>

<p>We try to rewrite @('x') to eliminate any parameters.  There doesn't seem to
be any way to actually provide values for the parameters of a function, so
function parameters seem to just be a way to use named constants within a
function.</p>

<p>The basic idea is to just construct a substitution list from the parameters
and apply it throughout the function.  But we do a lot of sanity checking to
make sure that the parameters are very simple, aren't shadowing other things,
and are defined before they are used (as some Verilog tools require).  While
we're at it, we also check the function's local namespace to make sure it is
okay (since eliminating parameters changes the function's namespace).</p>"

  (defund vl-fundecl-expand-params (x warnings mod)
    "Returns (MV SUCCESSP WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-fundecl-p x)
                                (vl-warninglist-p warnings)
                                (vl-module-p mod))))
    (b* (((vl-fundecl x) x)
         ((mv regdecls vardecls eventdecls paramdecls)
          (vl-filter-blockitems x.decls))

         ((unless paramdecls)
          ;; Common case of no parameters -- no need to check or change anything.
          (mv t warnings x))

         (param-names (vl-paramdecllist->names paramdecls))
         (local-namespace
          (append (list x.name) ;; functions' name needs to be included since it gets assigned to at the end
                  (vl-regdecllist->names regdecls)
                  (vl-vardecllist->names vardecls)
                  (vl-eventdecllist->names eventdecls)
                  param-names))

         ;; Make sure there are no name clashes, for good measure.
         (dupes (duplicated-members local-namespace))
         ((when dupes)
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-namespace
                   :msg "In ~a0, there are multiple declarations for ~&1."
                   :args (list x dupes)
                   :fatalp t
                   :fn 'vl-fundecl-expand-params)))
            (mv nil (cons w warnings) x)))

         ;; Make sure these params don't overlap with other module items in a
         ;; tricky way.
         ((mv okp warnings) (vl-check-fun-params-no-overlap paramdecls mod warnings x))
         ((unless okp) (mv nil warnings x))

         ;; Make sure these params are only used after they are defined.  This
         ;; relies on the function declarations being the same order they're
         ;; found in the file, which should be true of our parser.
         ((mv okp warnings)
          (vl-check-fun-parameters-deforder x.decls param-names warnings x))
         ((unless okp) (mv nil warnings x))

         ;; Make sure the parameters are simple enough for us to handle.
         ((mv okp warnings)
          (vl-fun-paramdecllist-types-okp paramdecls warnings x))
         ((unless okp) (mv nil warnings x))

         ;; Okay, everything looks good.  We want to now just expand the parameters
         ;; away by rewriting them with their values.
         (sigma (vl-fundecl-param-sigma paramdecls))
         ((with-fast sigma))

         (regdecls   (vl-regdecllist-subst regdecls sigma))
         (vardecls   (vl-vardecllist-subst vardecls sigma))
         (eventdecls (vl-eventdecllist-subst eventdecls sigma))
         (body       (vl-stmt-subst x.body sigma))
         (new-x      (change-vl-fundecl x
                                        :decls (append regdecls vardecls eventdecls)
                                        :body body)))

      (mv t warnings new-x)))

  (local (in-theory (enable vl-fundecl-expand-params)))

  (defthm vl-warninglist-p-of-vl-fundecl-expand-params
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-fundecl-expand-params x warnings mod)))))

  (defthm vl-fundecl-p-of-vl-fundecl-expand-params
    (implies (force (vl-fundecl-p x))
             (vl-fundecl-p (mv-nth 2 (vl-fundecl-expand-params x warnings mod))))))


(defsection vl-fundecllist-expand-params
  :parents (expand-functions)
  :short "Eliminate parameters from a list of functions."
  :long "<p>See @(see vl-fundecl-expand-params).</p>"

  (defund vl-fundecllist-expand-params (x warnings mod)
    "Returns (MV SUCCESSP WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-fundecllist-p x)
                                (vl-warninglist-p warnings)
                                (vl-module-p mod))))
    (b* (((when (atom x))
          (mv t warnings nil))
         ((mv car-successp warnings car-prime)
          (vl-fundecl-expand-params (car x) warnings mod))
         ((mv cdr-successp warnings cdr-prime)
          (vl-fundecllist-expand-params (cdr x) warnings mod)))
      (mv (and car-successp cdr-successp)
          warnings
          (cons car-prime cdr-prime))))

  (local (in-theory (enable vl-fundecllist-expand-params)))

  (defthm vl-warninglist-p-of-vl-fundecllist-expand-params
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-fundecllist-expand-params x warnings mod)))))

  (defthm vl-fundecllist-p-of-vl-fundecllist-expand-params
    (implies (force (vl-fundecllist-p x))
             (vl-fundecllist-p (mv-nth 2 (vl-fundecllist-expand-params x warnings mod))))))




; -----------------------------------------------------------------------------
;
;                          Function Body Rules
;
; -----------------------------------------------------------------------------

(defsection vl-fun-assignstmt-okp
  :parents (vl-fun-stmt-okp)
  :short "Ensure an @(see vl-assignstmt-p) conforms to the function statement
rules in 10.4.4."

  :long "<p>Statements in a function's body can't include timing controls,
nonblocking assignments, or procedural continuous assignments.  We check that
an assignment statement satisfies these constraints or issue a fatal
warning.</p>"

  (defund vl-fun-assignstmt-okp (x warnings function)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-assignstmt-p x)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))))
    (b* (((vl-assignstmt x) x)

         ((unless (eq x.type :vl-blocking))
          ;; Per Section 10.4.4 this is illegal
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-stmt
                   :msg "In ~a0, the assignment ~a1 is not allowed because ~
                         all assignments in a function's body must be ~
                         blocking assignments, i.e., a = b.  Other kinds of ~
                         assignments like a <= b, assign a = b, and force a = ~
                         b are not permitted."
                   :args (list function x)
                   :fatalp t
                   :fn 'vl-fun-assignstmt-okp)))
            (mv nil (cons w warnings))))

         ((when x.ctrl)
          ;; Per Section 10.4.4 this is illegal
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-stmt
                   :msg "In ~a0, the assignment ~a1 is not allowed because ~
                         statements in a function's body may not have timing ~
                         statements (i.e., #, @)."
                   :args (list function x)
                   :fatalp t
                   :fn 'vl-fun-assignstmt-okp)))
            (mv nil (cons w warnings)))))

      (mv t warnings)))

  (local (in-theory (enable vl-fun-assignstmt-okp)))

  (defthm vl-warninglist-p-of-vl-fun-assignstmt-okp
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-fun-assignstmt-okp x warnings function))))))


(defsection vl-fun-atomicstmt-okp
  :parents (vl-fun-stmt-okp)
  :short "Ensure an @(see vl-atomicstmt-p) conforms to the function statement
rules in 10.4.4."

  :long "<p>We allow null statements because they seem harmless.</p>

<p>We allow assignment statements as long as they are blocking assignments with
no timing controls, see @(see vl-fun-assignstmt-okp).</p>

<p>Otherwise, an atomic statement is either a deassigns, enable, disable, or
event trigger, and we do not allow it:</p>

<ul>

<li>I think deassigns are considered as procedural assignments, and if that is
true then they are forbidden by 10.4.4, so we don't allow them.</li>

<li>Enables are explicitly forbidden by 10.4.4.</li>

<li>Disables are not explicitly mentioned, but it seems like if enables are
forbidden then disables should also be forbidden, so I'm not going to allow
them.</li>

<li>Event triggers are explicitly forbidden by 10.4.4.</li>

</ul>"

  (defund vl-fun-atomicstmt-okp (x warnings function)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-atomicstmt-p x)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))))
    (cond ((vl-fast-assignstmt-p x)
           (vl-fun-assignstmt-okp x warnings function))
          ((vl-fast-nullstmt-p x)
           (mv t warnings))
          (t
           (b* ((w (make-vl-warning
                    :type :vl-bad-function-stmt
                    :msg "In ~a0, the statement ~a1 is not allowed because a ~
                          function's body cannot include any ~s2."
                    :args (list function x
                                (case (tag x)
                                  (:vl-deassignstmt "procedural assignments")
                                  ((:vl-enablestmt :vl-disablestmt)
                                   "task enables")
                                  (:vl-eventtriggerstmt
                                   "event triggers")))
                    :fatalp t
                    :fn 'vl-fun-atomicstmt-okp)))
             (mv nil (cons w warnings))))))

  (local (in-theory (enable vl-fun-atomicstmt-okp)))

  (defthm vl-warninglist-p-of-vl-fun-atomicstmt-okp
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-fun-atomicstmt-okp x warnings function))))))


(defsection vl-fun-stmt-okp
  :parents (expand-functions)
  :short "Ensure that a function's statement conforms to the Function Rules in
10.4.4."

  :long "<p><b>Signature:</b> @(call vl-fun-stmt-okp) returns @('(mv okp
warnings)').</p>

<p>Here, @('x') is a statement (presumably a function's body or a sub-statement
of a function's body), @('warnings') is an ordinary @(see warnings)
accumulator, and @('function') is just a context for error messages.</p>

<p>We check to see if the statement conforms to the Function Rules in 10.4.4.
In particular, we want to ensure that the function's body:</p>

<ul>
<li>has no time-controlled statements (#, @, wait),</li>
<li>does not enable tasks</li>
<li>has no nonblocking assignments or procedural continuous assignments</li>
<li>has no event triggers</li>
</ul>

<p>Practically speaking there are a lot of other things that our function
expansion code doesn't support (complex case statements, loops, functions that
don't write to registers before reading them, etc.) but that the standard
doesn't prohibit, so this is not a very complete check as far as VL is
concerned.  But, I think it's nice to explicitly check for the \"officially
forbidden\" stuff first.</p>"

  (mutual-recursion

   (defund vl-fun-stmt-okp (x warnings function)
     "Returns (MV OKP WARNINGS)"
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-warninglist-p warnings)
                                 (vl-fundecl-p function))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atomicstmt-p x))
           (vl-fun-atomicstmt-okp x warnings function))
          (type (vl-compoundstmt->type x))

          ((when (or (eq type :vl-timingstmt)
                     (eq type :vl-waitstmt)))
           ;; Per 10.4.4 this is illegal
           (b* ((w (make-vl-warning
                    :type :vl-bad-function-stmt
                    :msg "In ~a0, the statement ~a1 is not allowed because ~
                          statements in a function's body may not have timing ~
                          statements (i.e., #, @, wait)."
                    :args (list function x)
                    :fatalp t
                    :fn 'vl-fun-stmt-okp)))
             (mv nil (cons w warnings)))))

       (vl-fun-stmtlist-okp (vl-compoundstmt->stmts x) warnings function)))

   (defund vl-fun-stmtlist-okp (x warnings function)
     "Returns (MV OKP WARNINGS)"
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-warninglist-p warnings)
                                 (vl-fundecl-p function))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv t warnings))
          ((mv successp1 warnings) (vl-fun-stmt-okp (car x) warnings function))
          ((mv successp2 warnings) (vl-fun-stmtlist-okp (cdr x) warnings function)))
       (mv (and successp1 successp2)
           warnings))))

  (local (in-theory (enable vl-fun-stmt-okp)))

  (flag::make-flag vl-flag-fun-stmt-okp
                   vl-fun-stmt-okp
                   :flag-mapping ((vl-fun-stmt-okp . stmt)
                                  (vl-fun-stmtlist-okp . list)))

  (defthm-vl-flag-fun-stmt-okp

    (defthm vl-warninglist-p-of-vl-fun-stmt-okp
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 (vl-fun-stmt-okp x warnings function))))
      :flag stmt)

    (defthm vl-warninglist-p-of-vl-fun-stmtlist-okp
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 (vl-fun-stmtlist-okp x warnings function))))
      :flag list)

    :hints(("Goal"
            :expand ((vl-fun-stmt-okp x warnings function)
                     (vl-fun-stmtlist-okp x warnings function)))))

  (verify-guards vl-fun-stmt-okp))



; -----------------------------------------------------------------------------
;
;                    Function Body --> Assignment List
;
; -----------------------------------------------------------------------------

(defsection vl-fun-assignorder-okp-aux
  :parents (vl-fun-assignorder-okp)
  :short "Main checking for @(see vl-fun-assignorder-okp)."

  :long "<p><b>Signature:</b> @(call vl-fun-assignorder-okp-aux) returns @('(mv
okp warnings written-regs read-regs read-inputs)').</p>

<ul>

<li>@('x') is a @(see vl-assignlist-p) derived from the function's body.</li>

<li>@('innames') are the names of all inputs to the function.</li>

<li>@('regnames') are the names of all registers declared in the function.</li>

<li>@('written-regs') is an accumulator that names all of the registers we
wrote to so far; this allows us to check that all registers are written before
they are read, and that no register is written to more than once.</li>

<li>@('read-regs') is an accumulator that names all of the registers we've read
from so far; it is just useful for reporting unused registers.</li>

<li>@('read-inputs') is an accumulator that names all the inputs we've read
from so far; it is just useful for unused-input reporting.</li>

<li>@('warnings') is an ordinary @(see warnings) accumulator.</li>

<li>@('function') is the function itself, which is mainly useful as a context
for warnings, but also gives us the function's name so we can check that the
function's name is the last thing written to and isn't written to until the
end.</li>

</ul>"

  (defund vl-fun-assignorder-okp-aux
    (x innames regnames written-regs read-regs read-inputs warnings function)
    "Returns (MV OKP WARNINGS WRITTEN-REGS READ-REGS READ-INPUTS)"
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (string-listp innames)
                                (string-listp regnames)
                                (string-listp written-regs)
                                (string-listp read-regs)
                                (string-listp read-inputs)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))))
    (b* ((funname (vl-fundecl->name function))

         ((when (atom x))
          ;; We sort of shouldn't ever get here unless the list of assignments
          ;; that was produced by VL-FUNBODY-TO-ASSIGNMENTS was empty.
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-stmt
                   :msg "In ~a0, there are no assignments.  There needs to at ~
                         least be an assignment to ~s1 to give it a return ~
                         value."
                   :args (list function funname)
                   :fatalp t
                   :fn 'vl-fun-assignorder-okp)))
            (mv nil (cons w warnings) written-regs read-regs read-inputs)))

         ((vl-assign x1) (car x))
         ((unless (vl-idexpr-p x1.lvalue))
          ;; This is overly restrictive, but should be good enough for now.
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-stmt
                   :msg "In ~a0, the assignment to ~a1 is too complex; we ~
                         only support assigning to a function's registers and ~
                         to its name directly; e.g., you cannot even write ~
                         things like foo[3:0] = 1.  This is overly ~
                         restrictive, and we can work on improving it if ~
                         necessary."
                   :args (list function x1.lvalue)
                   :fatalp t
                   :fn 'vl-fun-assignorder-okp)))
            (mv nil (cons w warnings) written-regs read-regs read-inputs)))

         (lhs-name           (vl-idexpr->name x1.lvalue))
         (rhs-names          (vl-expr-names x1.expr))
         (rhs-reg-names      (intersection-equal rhs-names regnames))
         (rhs-unwritten-regs (set-difference-equal rhs-reg-names written-regs))
         ((when rhs-unwritten-regs)
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-stmt
                   :msg "In ~a0, assignment to ~a1 involves the register~s2 ~
                         ~&3, which ~s4 not yet been assigned at this point ~
                         in the function.  We do not allow this because it ~
                         can lead to very odd behavior when there are ~
                         multiple calls of the function."
                   :args (list function
                               x1.lvalue
                               (if (vl-plural-p rhs-unwritten-regs) "s" "")
                               rhs-unwritten-regs
                               (if (vl-plural-p rhs-unwritten-regs) "have" "has"))
                   :fatalp t
                   :fn 'vl-fun-assignorder-okp)))
            (mv nil (cons w warnings) written-regs read-regs read-inputs)))

         (read-regs   (append rhs-reg-names read-regs))
         (read-inputs (append (intersection-equal innames rhs-names) read-inputs))

         ((when (atom (cdr x)))
          ;; Last assignment.  This one needs to be to the function's name.
          (if (equal lhs-name funname)
              (mv t warnings written-regs read-regs read-inputs)
            (b* ((w (make-vl-warning
                     :type :vl-bad-function-stmt
                     :msg "In ~a0, the final assignment in ~s1 must be to ~
                           ~s1, but instead it is to ~a2."
                     :args (list function funname x1.lvalue)
                     :fatalp t
                     :fn 'vl-fun-assignorder-okp)))
              (mv nil (cons w warnings) written-regs read-regs read-inputs))))

         ;; Not the last assignment, so this one needs to be to a register
         ;; that we haven't written to yet.
         ((when (equal lhs-name funname))
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-stmt
                   :msg "In ~a0, assigning to ~a1 is not permitted except as ~
                         the very last statement in the function."
                   :args (list function x1.lvalue)
                   :fatalp t
                   :fn 'vl-fun-assignorder-okp)))
            (mv nil (cons w warnings) written-regs read-regs read-inputs)))

         ((unless (member-equal lhs-name regnames))
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-stmt
                   :msg "In ~a0, the assignment to ~a1 is not permitted; we ~
                         only allow assignments to the funtion's registers ~
                         and its name."
                   :args (list function x1.lvalue)
                   :fatalp t
                   :fn 'vl-fun-assignorder-okp)))
            (mv nil (cons w warnings) written-regs read-regs read-inputs)))

         ((when (member-equal lhs-name written-regs))
          ;; We could relax this restriction by doing some kind of renaming for
          ;; multiply written registers.
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-stmt
                   :msg "In ~a0, we only allow a single assignment to each of ~
                         the function's registers, but ~a1 is written to more ~
                         than once."
                   :args (list function x1.lvalue)
                   :fatalp t
                   :fn 'vl-fun-assignorder-okp)))
            (mv nil (cons w warnings) written-regs read-regs read-inputs)))

         ;; Else, looking good so far -- record the reg as written and let's go
         ;; on to the rest of the assignments.
         (written-regs (cons lhs-name written-regs)))

      (vl-fun-assignorder-okp-aux (cdr x) innames regnames
                                  written-regs read-regs read-inputs
                                  warnings function)))

  (local (in-theory (enable vl-fun-assignorder-okp-aux)))

  (defthm vl-warninglist-p-of-vl-fun-assignorder-okp-aux
    (let ((ret (vl-fun-assignorder-okp-aux x innames regnames written-regs read-regs read-inputs warnings function)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 ret)))))

  (defthm vl-fun-assignorder-okp-aux-basics
    (let ((ret (vl-fun-assignorder-okp-aux x innames regnames written-regs read-regs read-inputs warnings function)))
      (implies (and (force (vl-assignlist-p x))
                    (force (string-listp innames))
                    (force (string-listp regnames))
                    (force (string-listp written-regs))
                    (force (string-listp read-regs))
                    (force (string-listp read-inputs))
                    (force (vl-fundecl-p function)))
               (and (string-listp (mv-nth 2 ret))
                    (string-listp (mv-nth 3 ret))
                    (string-listp (mv-nth 4 ret)))))))



(defsection vl-fun-assignorder-okp
  :parents (vl-funbody-to-assignments)
  :short "Ensure that the assignments from a function's body always write to
registers before they read from them, never write to a register twice, and end
with a write to the function's name."

  :long "<p><b>Signature:</b> @(call vl-fun-assignorder-okp) returns @('(mv okp
warnings)').</p>

<p>Here, @('x') is a @(see vl-assignlist-p) derived from the function's body
and @('warnings') is an ordinary @(see warnings) accumulator, which may be
extended with fatal warnings.  The @('function') is the function itself, and is
mainly used as a context for error messages, and also to determine the
function's name.</p>

<p>The checks we perform are intended to ensure that it is legitimate to
convert this series of blocking assignments into wiring:</p>

<ul>

<li>Write-before-read ensures that there is no possible interaction with
previous function calls, or other \"simultaneous\" function calls.</li>

<li>No multiple writes ensures that we won't be putting multiple drivers on
some wire when we convert the assignments into continuous assignments; we could
probably drop this restriction easily by doing some kind of renaming.</li>

<li>Writing to the function at the end seems like a basic reasonableness
criteria.</li>

</ul>

<p>We also take this opportunity to issue non-fatal warnings about unused
registers and inputs.</p>"

  (defund vl-fun-assignorder-okp (x warnings function)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))))
    (b* (((mv regdecls ?vardecls ?eventdecls ?paramdecls)
          (vl-filter-blockitems (vl-fundecl->decls function)))
         (regnames (vl-regdecllist->names regdecls))
         (innames  (vl-taskportlist->names (vl-fundecl->inputs function)))
         ((mv okp warnings written-regs read-regs read-inputs)
          (vl-fun-assignorder-okp-aux x innames regnames nil nil nil warnings function))
         ((unless okp)
          (mv nil warnings))

         ;; Check for any unread/unwritten registers, and any unread inputs,
         ;; and add non-fatal warnings if there are any.
         ;;
         ;; There shouldn't be any read-but-never-written regs, but we'll write
         ;; this code as if there might be.

         (innames        (mergesort innames))        ;; Sort things just so the names are in order
         (regnames       (mergesort regnames))       ;; in the warning message.
         (read-inputs    (mergesort read-inputs))
         (read-regs      (mergesort read-regs))
         (written-regs   (mergesort written-regs))

         (unread-inputs  (difference innames read-inputs))
         (unread-regs    (difference regnames read-regs))
         (unwritten-regs (difference regnames written-regs))

         (spurious-regs  (intersect unread-regs unwritten-regs))    ;; unread and unwritten
         (unread-regs    (difference unread-regs spurious-regs))    ;; unread but written
         (unwritten-regs (difference unwritten-regs spurious-regs)) ;; read but unwritten
         (unread-all     (union unread-regs unread-inputs))

         ;; Wow, this is an ugly ball of mud.

         (spurious-sep   (if (or unread-all unwritten-regs) "; " ""))
         (spurious-msg   (cond ((not spurious-regs)
                                "")
                               ((vl-plural-p spurious-regs)
                                (cat "~&1 are never mentioned" spurious-sep))
                               (t
                                (cat "~&1 is never mentioned" spurious-sep))))

         (unread-sep     (if unwritten-regs "; " ""))
         (unread-msg     (cond ((not unread-all)
                                "")
                               ((vl-plural-p unread-all)
                                (cat "~&2 are never read" unread-sep))
                               (t
                                (cat "~&2 is never read" unread-sep))))

         (unwritten-msg  (cond ((not unwritten-regs)
                                "")
                               ((vl-plural-p unwritten-regs)
                                "~&3 are never written")
                               (t
                                "~&3 is never written")))

         (warnings
          (if (or spurious-regs unread-all unwritten-regs)
              (cons (make-vl-warning
                     :type :vl-warn-function-vars
                     :msg (cat "In ~a0, " spurious-msg unread-msg unwritten-msg ".")
                     :args (list function spurious-regs unread-all unwritten-regs)
                     :fatalp nil
                     :fn 'vl-fun-assignorder-okp)
                    warnings)
            warnings)))

      (mv t warnings)))

  (local (in-theory (enable vl-fun-assignorder-okp)))

  (defthm vl-warninglist-p-of-vl-fun-assignorder-okp
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-fun-assignorder-okp x warnings function))))))


(defsection vl-funbody-to-assignments-aux
  :parents (vl-funbody-to-assignments)
  :short "Try to convert a list of statements that make up a function's body
into a @(see vl-assignlist-p)."

  :long "<p><b>Signature:</b> @(call vl-funbody-to-assignments-aux) returns
@('(mv successp warnings assigns)').</p>

<p>Here, @('x') is a \"flattened\" list of statements that come from the
function's body.  If this function is reasonable and in our supported subset,
then @('x') should just be a list of blocking assignment statements.  We
convert each statement into a @(see vl-assign-p) with the same left-hand side
and right-hand-side.  The superior function, @(see vl-funbody-to-assignments),
will then check that this conversion is reasonable.</p>

<p>If @('x') contains anything other than supported, blocking assignment
statements (well, and null statements), we'll just fail because this isn't a
supported function.</p>"

  (defund vl-funbody-to-assignments-aux (x warnings function)
    "Returns (MV SUCCESSP WARNINGS ASSIGNS)"
    (declare (xargs :guard (and (vl-stmtlist-p x)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))))
    (b* (((when (atom x))
          (mv t warnings nil))

         ((when (vl-fast-nullstmt-p (car x)))
          ;; Fine, skip it.
          (vl-funbody-to-assignments-aux (cdr x) warnings function))

         ((unless (vl-fast-assignstmt-p (car x)))
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-stmt
                   :msg "In ~a0, after rewriting, the function's body ~
                         includes ~a1, but only simple assignment statements ~
                         are permitted."
                   :args (list function (car x))
                   :fn 'vl-funbody-to-assignments-aux
                   :fatalp t)))
            (mv nil (cons w warnings) nil)))

         ;; Make sure that X has no delays and is a blocking assignment.  We
         ;; should have already checked this, but we'll check it again just in
         ;; case.
         ((mv okp warnings) (vl-fun-assignstmt-okp (car x) warnings function))
         ((unless okp) (mv nil warnings nil))

         ;; Otherwise, X seems okay, so make an assignment from it.
         ((vl-assignstmt x1) (car x))
         (assign1 (make-vl-assign :lvalue x1.lvalue
                                  :expr   x1.expr
                                  :atts   (acons "VL_FUN_ASSIGN"
                                                 (make-vl-atom :guts (make-vl-string :value (vl-fundecl->name function)))
                                                 x1.atts)
                                  :loc    x1.loc))
         ((mv okp warnings cdr-assigns)
          (vl-funbody-to-assignments-aux (cdr x) warnings function)))

      (mv okp warnings (cons assign1 cdr-assigns))))

  (local (in-theory (enable vl-funbody-to-assignments-aux)))

  (defthm vl-warninglist-p-of-vl-funbody-to-assignments-aux
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-funbody-to-assignments-aux x warnings function)))))

  (defthm vl-assignlist-p-of-vl-funbody-to-assignments-aux
    (implies (and (force (vl-stmtlist-p x))
                  (force (vl-fundecl-p function)))
             (vl-assignlist-p (mv-nth 2 (vl-funbody-to-assignments-aux x warnings function))))))


(defsection vl-funbody-to-assignments
  :parents (expand-functions)
  :short "Transform a function's body into a list of assignment statements if
it is safe to do so."

  :long "<p><b>Signature:</b> @(call vl-funbody-to-assignments) returns @('(mv
successp warnings assigns)').</p>

<p>Here @('x') is a function declaration and @('warnings') is an ordinary @(see
warnings) accumulator.</p>

<p>If @('x') is a function that we think we can safely support, we convert its
body into a list of assignments which capture its effect.  This is a fairly
elaborate process with a lot of checking to make sure things are reasonable.
At a high level:</p>

<ul>

<li>We start by checking that the function's body isn't prohibited because of
one of the Function Rules in 10.4.4 (see @(see vl-fun-stmt-okp)).  This is
important in order to justify our use of rewriting in the next step.</li>

<li>We then rewrite the function's body using our ordinary @(see stmtrewrite)
functions.  This may help to flatten out nested sub-blocks and generally just
helps to expand the class of functions we can support.</li>

<li>We then try to convert the body into a simple @(see vl-assignlist-p) using
a helper routine, @(see vl-funbody-to-assignments-aux).  This only works if the
rewritten function is nothing more than a list of blocking assignments.</li>

<li>If that was successful, we check this sequence of assignments to make sure
that it follows several rules (write-before-read, don't write twice, etc.) to
ensure that it is safe to convert the function into a series of continuous
assignments; see @(see vl-fun-assignorder-okp) for details.</li>

</ul>

<p>If all of this works and everything looks okay, we successfully return the
generated list of assignments.  Otherwise we fail with fatal warnings.</p>"

  (defund vl-funbody-to-assignments (x warnings)
    "Returns (MV SUCCESSP WARNINGS ASSIGNS)"
    (declare (xargs :guard (and (vl-fundecl-p x)
                                (vl-warninglist-p warnings))))

    ;; This is the top-level function for converting function bodies into
    ;; assignments.

    (b* ((body (vl-fundecl->body x))

         ;; We start with a basic check to make sure that the function's body
         ;; isn't prohibited because of one of the rules in 10.4.4.
         ((mv successp warnings) (vl-fun-stmt-okp body warnings x))
         ((unless successp) (mv nil warnings nil))

         ;; So that we can handle functions with nested sub-blocks, etc., we use
         ;; our ordinary rewriter to simplify the body.  Now, vl-stmt-rewrite
         ;; does some rewriting that isn't necessarily okay in the context of
         ;; function statements (i.e., it converts $display calls into null
         ;; statements, but $display statements aren't allowed in function bodies
         ;; whereas null statements are).  But this is okay: we've already
         ;; checked with VL-FUN-STMT-OKP that the function is okay with respect
         ;; to the rules of the Verilog standard, so if we're here then we
         ;; already know the statement is "good," so rewriting the body won't let
         ;; us accidentally accept illegal functions.
         ((mv warnings body) (vl-stmt-rewrite body 1000 warnings))

         ;; The following is intended to let us uniformly treat functions that
         ;; include a "begin/end" and functions that do not.  That is, we can
         ;; have simpler functions like foo and more complex functions like bar:
         ;;
         ;;   function foo;           function bar;
         ;;     input i;                input i;
         ;;     foo = ...;              reg r;
         ;;   endfunction               begin
         ;;                               r = ...;
         ;;                               bar = ...;
         ;;                             end
         ;;                           endfunction
         ;;
         ;; For single-assignment functions, the rewriter will have produced
         ;; a single assignment statement; for multi-assignment functions we'll
         ;; have a block.  So, basically if we have a block we're just going to
         ;; grab its statements (and assume everything's been already flattened
         ;; so it's a single block), but otherwise we'll make a singleton list
         ;; with the rewritten body.
         (body-as-stmt-list
          (if (and (not (vl-fast-atomicstmt-p body))
                   (eq  (vl-compoundstmt->type body) :vl-blockstmt)
                   (vl-blockstmt->sequentialp body)
                   (not (vl-blockstmt->name body))
                   (not (vl-blockstmt->decls body)))
              (vl-blockstmt->stmts body)
            (list body)))

         ((mv okp warnings assigns)
          (vl-funbody-to-assignments-aux body-as-stmt-list warnings x))
         ((unless okp) (mv nil warnings nil))

         ;; Now check that the assigns have good order, add warnings about
         ;; unused regs, etc.
         ((mv okp warnings)
          (vl-fun-assignorder-okp assigns warnings x))
         ((unless okp) (mv nil warnings nil)))

      (mv t warnings assigns)))

  (local (in-theory (enable vl-funbody-to-assignments)))

  (defthm vl-warninglist-p-of-vl-funbody-to-assignments
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-funbody-to-assignments x warnings)))))

  (defthm vl-assignlist-p-of-vl-funbody-to-assignments
    (implies (force (vl-fundecl-p x))
             (vl-assignlist-p (mv-nth 2 (vl-funbody-to-assignments x warnings))))))




; -----------------------------------------------------------------------------
;
;                     Function Expansion Templates
;
; -----------------------------------------------------------------------------

(defaggregate vl-funtemplate
  (name inputs locals out assigns)
  :tag :vl-funtemplate
  :require ((stringp-of-vl-funtemplate->name
             (stringp name)
             :rule-classes :type-prescription)
            (vl-netdecllist-p-of-vl-funtemplate->inputs
             (vl-netdecllist-p inputs))
            (vl-netdecllist-p-of-vl-funtemplate->locals
             (vl-netdecllist-p locals))
            (vl-netdecl-p-of-vl-funtemplate->out
             (vl-netdecl-p out))
            (vl-assignlist-p-of-vl-funtemplate->assigns
             (vl-assignlist-p assigns)))
  :parents (expand-functions)
  :short "Function expansion templates, the intermediate representation of
functions we use while inlining function calls."

  :long "<p>For each of the module's functions, we generate a template that
will allow us to expand calls of the function.  Each template has the same
@('name') as the function, but all of its inputs and reg declarations have been
turned into net declarations (the @('inputs') and @('locals'), respectively),
and we have added a net declaration for the function's return value (@('out')).
The function's body is converted into @('assigns'), an ordinary @(see
vl-assignlist-p), and we assume that these assignments are well-formed in the
sense of @(see vl-fun-assignorder-okp).</p>

<p>Why do we bother introducing these templates at all?  One nice thing about
them is that there is a certain amount of \"static\" processing that needs to
be done on each function declaration (e.g., we need to do well-formedness
checking and extract its body into assignments) and it is somewhat efficient to
do this processing once, in the creation of templates, rather than each time we
want to expand a call of the function.</p>

<p>But a more important reason is that it allows us to support functions that
call other functions in a straightforward way.  In @(see
vl-flatten-funtemplates) we use our ordinary function-expansion code to expand
any function calls within function templates, so that when we expand functions
throughout the rest of the module we only need one pass.</p>")

(deflist vl-funtemplatelist-p (x)
  (vl-funtemplate-p x)
  :guard t
  :elementp-of-nil nil
  :parents (vl-funtemplate-p))

(defsection vl-find-funtemplate
  :parents (vl-funtemplate-p)
  :short "Find a function template by name."

  (defund vl-find-funtemplate (name templates)
    (declare (xargs :guard (and (stringp name)
                                (vl-funtemplatelist-p templates))))
    (cond ((atom templates)
           nil)
          ((equal name (vl-funtemplate->name (car templates)))
           (car templates))
          (t
           (vl-find-funtemplate name (cdr templates)))))

  (local (in-theory (enable vl-find-funtemplate)))

  (defthm vl-funtemplate-p-of-vl-find-funtemplate
    (implies (force (vl-funtemplatelist-p templates))
             (equal (vl-funtemplate-p (vl-find-funtemplate name templates))
                    (if (vl-find-funtemplate name templates)
                        t
                      nil)))))


(defsection vl-taskportlist-types-okp
  :parents (vl-funtemplate-p)
  :short "Ensure that a function's inputs are simple enough to convert into nets."

  (defund vl-taskportlist-types-okp (x warnings function)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-taskportlist-p x)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))))
    (b* (((when (atom x))
          (mv t warnings))

         ((vl-taskport x1) (car x))
         ((unless (or (eq x1.type :vl-unsigned)
                      (eq x1.type :vl-signed)))
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-input
                   :msg "In ~a0, input ~s1 has unsupported type ~s2."
                   :args (list function x1.name x1.type)
                   :fatalp t
                   :fn 'vl-taskportlist-types-okp)))
            (mv nil (cons w warnings)))))
      (vl-taskportlist-types-okp (cdr x) warnings function)))

  (local (in-theory (enable vl-taskportlist-types-okp)))

  (defthm vl-warninglist-p-of-vl-taskportlist-types-okp
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-taskportlist-types-okp x warnings function))))))


(defsection vl-funinput-to-netdecl
  :parents (vl-funtemplate-p)
  :short "Convert a function's input declaration into a net declaration for its
funtemplate."

  :long "<p>We assume the input is okay in the sense of @(see
vl-taskportlist-types-okp).</p>"

  (defund vl-funinput-to-netdecl (x)
    (declare (xargs :guard (vl-taskport-p x)))
    (b* (((vl-taskport x) x)
         (name-atom (make-vl-atom :guts (make-vl-string :value x.name))))
      (make-vl-netdecl :name    x.name
                       :type    :vl-wire
                       :range   x.range
                       :arrdims nil
                       :atts    (acons "VL_FUNCTION_INPUT" name-atom x.atts)
                       :signedp (eq x.type :vl-signed)
                       :loc     x.loc)))

  (local (in-theory (enable vl-funinput-to-netdecl)))

  (defthm vl-netdecl-p-of-vl-funinput-to-netdecl
    (implies (force (vl-taskport-p x))
             (vl-netdecl-p (vl-funinput-to-netdecl x)))))


(defprojection vl-funinputlist-to-netdecls (x)
  (vl-funinput-to-netdecl x)
  :guard (vl-taskportlist-p x)
  :result-type vl-netdecllist-p
  :parents (vl-funtemplate-p))


(defsection vl-fun-regdecllist-types-okp
  :parents (vl-funtemplate-p)
  :short "Ensure that a function's regs are simple enough to convert into nets."

  (defund vl-fun-regdecllist-types-okp (x warnings function)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-regdecllist-p x)
                                (vl-warninglist-p warnings)
                                (vl-fundecl-p function))))
    (b* (((when (atom x))
          (mv t warnings))

         ((vl-regdecl x1) (car x))
         ((when x1.arrdims)
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-regdecl
                   :msg "In ~a0, reg ~s1 has array dimensions, which are not ~
                         supported."
                   :args (list function x1.name)
                   :fatalp t
                   :fn 'vl-fun-regdecllist-types-okp)))
            (mv nil (cons w warnings))))

         ((when x1.initval)
          ;; I don't think this is even allowed by the grammar.
          (b* ((w (make-vl-warning
                   :type :vl-bad-function-regdecl
                   :msg "In ~a0, reg ~s1 has an initial value, which is not ~
                         supported."
                   :args (list function x1.name)
                   :fatalp t
                   :fn 'vl-fun-regdecllist-types-okp)))
            (mv nil (cons w warnings)))))

      (vl-fun-regdecllist-types-okp (cdr x) warnings function)))

  (local (in-theory (enable vl-fun-regdecllist-types-okp)))

  (defthm vl-warninglist-p-of-vl-fun-regdecllist-types-okp
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-fun-regdecllist-types-okp x warnings function))))))



(defsection vl-fun-regdecl-to-netdecl
  :parents (vl-funtemplate-p)
  :short "Convert a function's reg declaration into a net declaration for its
funtemplate."

  :long "<p>We assume the input is okay in the sense of @(see
vl-fun-regdecllist-types-okp).</p>"

  (defund vl-fun-regdecl-to-netdecl (x)
    (declare (xargs :guard (vl-regdecl-p x)))
    (b* (((vl-regdecl x) x)
         (name-atom (make-vl-atom :guts (make-vl-string :value x.name))))
      (make-vl-netdecl :name    x.name
                       :type    :vl-wire
                       :range   x.range
                       :arrdims x.arrdims ;; should be NIL if regdecllist-types-okp.
                       :atts    (acons "VL_FUNCTION_REG" name-atom x.atts)
                       :signedp x.signedp
                       :loc     x.loc)))

  (local (in-theory (enable vl-fun-regdecl-to-netdecl)))

  (defthm vl-netdecl-p-of-vl-fun-regdecl-to-netdecl
    (implies (force (vl-regdecl-p x))
             (vl-netdecl-p (vl-fun-regdecl-to-netdecl x)))))


(defprojection vl-fun-regdecllist-to-netdecls (x)
  (vl-fun-regdecl-to-netdecl x)
  :guard (vl-regdecllist-p x)
  :result-type vl-netdecllist-p
  :parents (vl-funtemplate-p))



(defsection vl-fundecl-expansion-template
  :parents (vl-funtemplate-p)
  :short "Generate the initial template for expanding a function."

  :long "<p><b>Signature:</b> @(call vl-fundecl-expansion-template) returns
@('(mv template/nil warnings)').</p>

<p>Here @('x') is a function declaration and @('warnings') is an ordinary @(see
warnings) accumulator.</p>

<p>We try to generate a @(see vl-funtemplate-p) corresponding to @('x').  On
success, the template we generate is only an <b>initial</b> template; it isn't
necessarily \"flat\" and might have function calls within its assignments.  We
later flatten these initial templates with @(see vl-flatten-funtemplates).</p>

<p>Creating the template for a function is a pretty elaborate process which
involves a lot of sanity checking, and will fail if the function includes
unsupported constructs or doesn't meet our other sanity criteria.</p>"

  (defund vl-fundecl-expansion-template (x warnings)
    "Returns (MV TEMPLATE/NIL WARNINGS)"
    (declare (xargs :guard (and (vl-fundecl-p x)
                                (vl-warninglist-p warnings))))

    (b* (((vl-fundecl x) x)

         ((unless (or (eq x.rtype :vl-unsigned)
                      (eq x.rtype :vl-signed)))
          (b* ((w (make-vl-warning
                   :type :vl-bad-function
                   :msg "In ~a0, we do not support functions with return ~
                         types other than plain/reg or 'signed', but this ~
                         function has type ~s1."
                   :args (list x x.rtype)
                   :fatalp t
                   :fn 'vl-fundecl-expansion-template)))
            (mv nil (cons w warnings))))

         ((mv regdecls vardecls eventdecls paramdecls)
          (vl-filter-blockitems x.decls))

         ((when eventdecls)
          (b* ((w (make-vl-warning
                   :type :vl-bad-function
                   :msg "In ~a0, we do not support functions with event ~
                         declarations."
                   :args (list x)
                   :fatalp t
                   :fn 'vl-fundecl-expansion-template)))
            (mv nil (cons w warnings))))

         ((when vardecls)
          (b* ((w (make-vl-warning
                   :type :vl-bad-function
                   :msg "In ~a0, we do not support functions with non-reg ~
                         variable declarations."
                   :args (list x)
                   :fatalp t
                   :fn 'vl-fundecl-expansion-template)))
            (mv nil (cons w warnings))))

         ((when paramdecls)
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "In ~a0, we expected function parameter declarations ~
                         to be handled before trying to make expansion ~
                         templates.  There must be a bug in VL's ~
                         expand-functions transformation."
                   :args (list x)
                   :fatalp t
                   :fn 'vl-fundecl-expansion-template)))
            (mv nil (cons w warnings))))

         ((mv okp warnings) (vl-fun-regdecllist-types-okp regdecls warnings x))
         ((unless okp) (mv nil warnings)) ;; already warned

         ((mv okp warnings) (vl-taskportlist-types-okp x.inputs warnings x))
         ((unless okp) (mv nil warnings)) ;; already warned

         ((mv okp warnings assigns) (vl-funbody-to-assignments x warnings))
         ((unless okp) (mv nil warnings)) ;; already warned

         (funname-atom (make-vl-atom :guts (make-vl-funname :name x.name)))
         (result-net   (make-vl-netdecl :name    x.name
                                        :range   x.rrange
                                        :type    :vl-wire
                                        :atts    (list (cons "VL_FUNCTION_RETURN" funname-atom))
                                        :signedp (eq x.rtype :vl-signed)
                                        :loc     x.loc))

         (template (make-vl-funtemplate :name    x.name
                                        :inputs  (vl-funinputlist-to-netdecls x.inputs)
                                        :locals  (vl-fun-regdecllist-to-netdecls regdecls)
                                        :out     result-net
                                        :assigns assigns)))

      (mv template warnings)))

  (local (in-theory (enable vl-fundecl-expansion-template)))

  (defthm vl-warninglist-p-of-vl-fundecl-expansion-template
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-fundecl-expansion-template x warnings)))))

  (defthm vl-funtemplate-p-of-vl-fundecl-expansion-template
    (implies (force (vl-fundecl-p x))
             (equal (vl-funtemplate-p (mv-nth 0 (vl-fundecl-expansion-template x warnings)))
                    (if (mv-nth 0 (vl-fundecl-expansion-template x warnings))
                        t
                      nil)))))


(defsection vl-fundecllist-expansion-templates
  :parents (vl-funtemplate-p)
  :short "Generate the initial templates for expanding a list of functions."
  :long "<p>See @(see vl-fundecl-expansion-template).</p>"

  (defund vl-fundecllist-expansion-templates (x warnings)
    "Returns (MV SUCCESSP WARNINGS TEMPLATES)"
    (declare (xargs :guard (and (vl-fundecllist-p x)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv t warnings nil))
         ((mv template1 warnings)
          (vl-fundecl-expansion-template (car x) warnings))
         ((mv cdr-successp warnings cdr-templates)
          (vl-fundecllist-expansion-templates (cdr x) warnings))
         (successp  (and template1 cdr-successp))
         (templates (and successp (cons template1 cdr-templates))))
      (mv successp warnings templates)))

  (local (in-theory (enable vl-fundecllist-expansion-templates)))

  (defthm vl-warninglist-p-of-vl-fundecllist-expansion-templates
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-fundecllist-expansion-templates x warnings)))))

  (defthm vl-funtemplatelist-p-of-vl-fundecllist-expansion-templates
    (implies (force (vl-fundecllist-p x))
             (vl-funtemplatelist-p (mv-nth 2 (vl-fundecllist-expansion-templates x warnings))))))




; -----------------------------------------------------------------------------
;
;                 Expanding Function Calls in Expressions
;
; -----------------------------------------------------------------------------

(defsection vl-fun-make-assignments-to-inputs
  :parents (vl-expand-function-call)
  :short "Generate assignments that supply the inputs to a function call."

  (defund vl-fun-make-assignments-to-inputs (netnames actuals loc)
    (declare (xargs :guard (and (string-listp netnames)
                                (vl-exprlist-p actuals)
                                (vl-location-p loc)
                                (same-lengthp netnames actuals))))
    (if (atom netnames)
        nil
      (cons (make-vl-assign :lvalue (vl-idexpr (car netnames) nil nil)
                            :expr   (car actuals)
                            :loc    loc)
            (vl-fun-make-assignments-to-inputs (cdr netnames) (cdr actuals) loc))))

  (local (in-theory (enable vl-fun-make-assignments-to-inputs)))

  (defthm vl-assignlist-p-of-vl-fun-make-assignments-to-inputs
    (implies (and (force (string-listp netnames))
                  (force (vl-exprlist-p actuals))
                  (force (vl-location-p loc))
                  (force (same-lengthp netnames actuals)))
             (vl-assignlist-p (vl-fun-make-assignments-to-inputs netnames actuals loc)))))


(defsection vl-relocate-assignments
  :parents (vl-expand-function-call)
  :short "Change the location of some assignments."

  (defund vl-relocate-assignments (x loc)
    (declare (xargs :guard (and (vl-assignlist-p x)
                                (vl-location-p loc))))
    (if (atom x)
        nil
      (cons (change-vl-assign (car x) :loc loc)
            (vl-relocate-assignments (cdr x) loc))))

  (local (in-theory (enable vl-relocate-assignments)))

  (defthm vl-assignlist-p-of-vl-relocate-assignments
    (implies (and (force (vl-assignlist-p x))
                  (force (vl-location-p loc)))
             (vl-assignlist-p (vl-relocate-assignments x loc)))))



(defsection vl-funexpand-rename-netdecls
  :parents (vl-expand-function-call)
  :short "Generate new names for a list of net declarations and change their
locations; this is used to give new names to the wires in a function call."

  :long "<p><b>Signature:</b> @(call vl-funexpand-rename-netdecls) returns
@('(mv x-prime nf)').</p>

<p>@('x') is a list of net declarations, typically some nets from a @(see
vl-funtemplate-p); we try to generate names that correspond to the original
names being used in the function.</p>

<p>@('nf') is a @(see vl-namefactory-p) that we use to safely generate fresh
names.</p>

<p>@('loc') is the location of the function call, so that when we introduce the
new wires, we put them near the site of their use.</p>"

  (defund vl-funexpand-rename-netdecls (x nf loc)
    "Returns (MV X-PRIME NF)"
    (declare (xargs :guard (and (vl-netdecllist-p x)
                                (vl-namefactory-p nf)
                                (vl-location-p loc))))
    (b* (((when (atom x))
          (mv nil nf))
         ((mv new-name nf)
          (vl-namefactory-indexed-name (vl-netdecl->name (car x)) nf))
         (car-renamed (change-vl-netdecl (car x)
                                         :name new-name
                                         :loc loc))
         ((mv cdr-renamed nf)
          (vl-funexpand-rename-netdecls (cdr x) nf loc)))
      (mv (cons car-renamed cdr-renamed) nf)))

  (local (in-theory (enable vl-funexpand-rename-netdecls)))

  (defthm vl-funexpand-rename-netdecls-basics
    (let ((ret (vl-funexpand-rename-netdecls x nf loc)))
      (implies (and (force (vl-netdecllist-p x))
                    (force (vl-namefactory-p nf))
                    (force (vl-location-p loc)))
               (and (vl-netdecllist-p (mv-nth 0 ret))
                    (vl-namefactory-p (mv-nth 1 ret))))))

  (defthm consp-of-vl-funexpand-rename-netdecls
    (equal (consp (mv-nth 0 (vl-funexpand-rename-netdecls x nf loc)))
           (consp x)))

  (defthm len-of-vl-funexpand-rename-netdecls
    (equal (len (mv-nth 0 (vl-funexpand-rename-netdecls x nf loc)))
           (len x)))

  (defthm true-listp-of-vl-funexpand-rename-netdecls
    (true-listp (mv-nth 0 (vl-funexpand-rename-netdecls x nf loc)))
    :rule-classes :type-prescription))



(defsection vl-expand-function-call
  :parents (expand-functions)
  :short "Main routine for expanding a single function call."

  :long "<p><b>Signature:</b> @(call vl-expand-function-call) returns @('(mv
successp warnings nf expr netdecls assigns)').</p>

<p>We need several inputs:</p>

<ul>

<li>@('x'), the @(see vl-funtemplate-p) for the function we want to
expand.</li>

<li>@('actuals'), the list of actuals for a particular call of this
function.</li>

<li>@('nf'), a @(see vl-namefactory-p) for generating fresh names.</li>

<li>@('netdecls'), an accumulator for wire declarations that we will need to
add to the module, which we will extend.</li>

<li>@('assigns'), an accumulator for assignments that we will need to add to
the module, which we will extend.</li>

<li>@('warnings'), an ordinary @(see warnings) accumulator, which we may extend
with fatal warnings.</li>

<li>@('ctx'), a @(see vl-modelement-p) that says where this function call
occurs, which we use for warning messages and also to indicate the location the
new module elements (wires and assignments) should be generated at.</li>

</ul>

<p>We might fail if there is an arity problem.  But if everything lines up,</p>

<ul>

<li>We generate fresh wire names that will serve as the inputs, locals, and the
return value wire for this function call; the corresponding declarations are
added to the @('netdecls') accumulator.</li>

<li>We generate new assignments that initialize the generated input wire names
with the actuals; these assignments are added to the @('assigns')
accumulator.</li>

<li>We rewrite the function's assignments so that they use these newly
generated wire names instead of their local names; these assignments are added
to the @('assigns') accumulator.</li>

</ul>

<p>The @('expr') we return is a simple identifier atom for the generated
return-value wire.  The idea is to replace the function-call expression with
this @('expr').</p>"

  (defund vl-expand-function-call (x actuals nf netdecls assigns warnings ctx)
    "Returns (MV SUCCESSP WARNINGS NF EXPR NETDECLS ASSIGNS)"
    (declare (xargs :guard (and (vl-funtemplate-p x)
                                (vl-exprlist-p actuals)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings)
                                (vl-modelement-p ctx)
                                (vl-netdecllist-p netdecls)
                                (vl-assignlist-p assigns))))

    (b* (((vl-funtemplate x) x)

         ((unless (same-lengthp x.inputs actuals))
          ;; Oops, arity error.
          (b* ((funname-atom (make-vl-atom :guts (make-vl-funname :name x.name)))
               (this-call    (make-vl-nonatom :op :vl-funcall
                                              :args (cons funname-atom actuals)))
               (w (make-vl-warning
                   :type :vl-bad-funcall
                   :msg "In ~a0, trying to call function ~w1 with ~x2 argument~s3,
                         but it takes ~x4 input~s5.  Expression: ~a6."
                   :args (list ctx
                               x.name
                               (len actuals)
                               (if (vl-plural-p actuals) "s" "")
                               (len x.inputs)
                               (if (vl-plural-p x.inputs) "s" "")
                               this-call)
                   :fatalp t
                   :fn 'vl-expand-function-call)))
            (mv nil (cons w warnings) nf nil netdecls assigns)))

         ;;  (3) set up assignments to the generated inputs from the actuals.

         ;; Generate fresh wires for everything
         (loc                 (vl-modelement-loc ctx))
         ((mv input-nets nf)  (vl-funexpand-rename-netdecls x.inputs nf loc))
         ((mv local-nets nf)  (vl-funexpand-rename-netdecls x.locals nf loc))
         ((mv ret-nets nf)    (vl-funexpand-rename-netdecls (list x.out) nf loc))
         (ret-net             (car ret-nets))

         (gen-input-names     (vl-netdecllist->names input-nets))
         (gen-local-names     (vl-netdecllist->names local-nets))
         (gen-ret-name        (vl-netdecl->name ret-net))

         (gen-input-wires     (vl-make-idexpr-list gen-input-names nil nil))
         (gen-local-wires     (vl-make-idexpr-list gen-local-names nil nil))
         (gen-ret-wire        (vl-idexpr gen-ret-name nil nil))

         (sigma
          ;; Big renaming alist that we can use to rewrite all of the assignments
          ;; to be in terms of our newly generated variables.
          (cons (cons (vl-netdecl->name x.out) gen-ret-wire)
                (append (pairlis$ (vl-netdecllist->names x.inputs) gen-input-wires)
                        (pairlis$ (vl-netdecllist->names x.locals) gen-local-wires))))
         ((with-fast sigma))

         (body-assigns  (vl-assignlist-subst x.assigns sigma))
         (body-assigns  (vl-relocate-assignments body-assigns loc))

         ;; Assignments to drive the generated input wires with the actuals
         (input-assigns (vl-fun-make-assignments-to-inputs gen-input-names actuals loc))

         (netdecls (append input-nets local-nets ret-nets netdecls))
         (assigns  (append input-assigns body-assigns assigns)))

      (mv t warnings nf gen-ret-wire netdecls assigns)))

  (local (in-theory (enable vl-expand-function-call)))

  (defthm vl-warninglist-p-of-vl-expand-function-call
    (let ((ret (vl-expand-function-call x actuals nf netdecls assigns warnings ctx)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 ret)))))

  (defthm vl-expand-function-call-basics
    (let ((ret (vl-expand-function-call x actuals nf netdecls assigns warnings ctx)))
      (implies (and (force (vl-funtemplate-p x))
                    (force (vl-exprlist-p actuals))
                    (force (vl-namefactory-p nf))
                    (force (vl-netdecllist-p netdecls))
                    (force (vl-assignlist-p assigns))
                    (force (vl-modelement-p ctx)))
               (and (vl-namefactory-p (mv-nth 2 ret))
                    (equal (vl-expr-p (mv-nth 3 ret))
                           (if (mv-nth 0 ret)
                               t
                             nil))
                    (vl-netdecllist-p (mv-nth 4 ret))
                    (vl-assignlist-p (mv-nth 5 ret)))))))


(defsection vl-check-bad-funcalls
  :parents (expand-functions)
  :short "Cause fatal warnings if function calls are in unacceptable places."

  :long "<p><b>Signature:</b> @(call vl-check-bad-funcalls) returns @('(mv okp
warnings)').</p>

<ul>

<li>@('ctx') is some @(see vl-modelement-p) that provides a context for the
error messages we may produce.</li>

<li>@('exprs') are a list of expressions that are <b>not</b> allowed have any
function calls.</li>

<li>@('description') is a short string that says what these expressions
are (some examples: \"delay expressions\", \"left-hand sides of assignments\"),
which will be incorporated into the error message.</li>

<li>@('warnings') is an ordinary @(see warnings) accumulator, which we may
extend.</li>

</ul>

<p>If these expressions contain any function calls, we add a fatal warning and
set @('okp') to @('nil').</p>

<h3>Motivation</h3>

<p>Which expressions should we allow to involve function calls?  Well, clearly
we want to allow function calls on the right-hand sides of assignments, and in
the inputs to module and gate instances.  But there are many other places where
we clearly don't want to allow function calls, for instance what would it mean
to assign to a function call, or to connect a function call to the output port
of a module?  We think these things are crazy and should not be allowed.</p>

<p>In other contexts the right thing to do is less clear.  Should we expand
function calls in a delay statement?  In an parameter-argument?  In a wire's
range declaration?</p>

<p>These things probably make some sense, especially if the function is being
applied to constant arguments and can be completely resolved at \"elaboration
time.\" But it does not seem like it makes any sense for functions that are
dealing with wires.  At any rate, for now I am not going to try to support this
osrt of thing, because (1) handling all of this properly raises so many
questions regarding widths, etc., and (2) it seems more elaborate than we
really need to support.</p>

<p>The moral of the story is:</p>

<ul>

<li>We only expand function calls in \"reasonable\" locations (right hand
sides, inputs to module instances, conditions for if statements, etc.)</li>

<li>We check whether there are any function calls in \"unreasonable\"
locations (left hand sides, outputs of module instances, delays, declaration
ranges, etc.) and cause fatal warnings if we find any.</li>

</ul>

<p>Some day, we might add better support for constant functions, and some of
this could be changed, but there'd better be a really good reason to do so
since it will be so tricky to get right.</p>"

  (defund vl-check-bad-funcalls (ctx exprs description warnings)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-modelement-p ctx)
                                (vl-exprlist-p exprs)
                                (stringp description)
                                (vl-warninglist-p warnings))))
    (b* (((unless (vl-exprlist-has-funcalls exprs))
          (mv t warnings))
         (fns-called (vl-exprlist-funnames exprs))
         (w (make-vl-warning
             :type :vl-bad-funcall
             :msg "In ~a0, function calls in ~s1 are not supported, but we ~
                   found ~s2 of ~&3."
             :args (list ctx
                         description
                         (if (vl-plural-p fns-called) "calls" "a call")
                         (mergesort fns-called))
             :fatalp t
             :fn 'vl-check-bad-funcalls)))
      (mv nil (cons w warnings))))

  (local (in-theory (enable vl-check-bad-funcalls)))

  (defthm vl-warninglist-p-of-vl-check-bad-funcalls
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-check-bad-funcalls ctx exprs description warnings))))))



(defsection vl-expr-expand-function-calls
  :parents (expand-functions)
  :short "Expand function calls throughout an expression."

  :long "<p><b>Signature:</b> @(call vl-expr-expand-function-calls) returns
@('(mv successp warnings nf x-prime netdecls assigns)').</p>

<p>Here, @('x') is the expression to expand function calls in, and
@('templates') is the list of all the templates we've generated from the
function declarations (a @(see vl-funtemplatelist-p)).  The other arguments are
the same as in @(see vl-expand-function-call).</p>

<p>We recursively try to expand function calls throughout @('x').  We return a
new expression, @('x-prime'), which is equivalent to @('x') (assuming that the
generated netdecls and assigns are added to the module), and which is free of
function calls on success.</p>"

  (mutual-recursion

   (defund vl-expr-expand-function-calls (x templates nf netdecls assigns warnings ctx)
     "Returns (MV SUCCESSP WARNINGS NF X-PRIME NETDECLS ASSIGNS)"
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-funtemplatelist-p templates)
                                 (vl-namefactory-p nf)
                                 (vl-netdecllist-p netdecls)
                                 (vl-assignlist-p assigns)
                                 (vl-warninglist-p warnings)
                                 (vl-modelement-p ctx))
                     :measure (two-nats-measure (acl2-count x) 1)
                     :verify-guards nil))
     (b* (((when (vl-fast-atom-p x))
           ;; Not a function call, nothing to do
           (mv t warnings nf x netdecls assigns))

          (op   (vl-nonatom->op x))
          (args (vl-nonatom->args x))

          ;; We don't allow function calls to occur in certain places.  In some
          ;; cases (like replication constants) we might eventaully want to
          ;; allow constant-functions, but at the moment our function handling
          ;; is only appropriate for wiring-related stuff.  The point of
          ;; checking for this stuff here is that we don't want to get into a
          ;; situation where we've replaced, say, a replication constant with a
          ;; wire, and then are failing later because the wire is not a
          ;; resolved constant; we'd rather report that we're unwilling to
          ;; expand function calls in these places.
          ((mv okp warnings)
           (case op
             (:vl-multiconcat
              ;; to avoid {f(3){bar}} --> {f_return_wire{bar}}
              (vl-check-bad-funcalls ctx (list (first args)) "multiple-concatenation constants" warnings))
             (:vl-bitselect
              ;; to avoid f(x)[3] --> f_return_wire[3], but maybe this would be okay?
              (vl-check-bad-funcalls ctx (list (first args)) "bit-select names" warnings))
             ((:vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon)
              ;; to avoid foo[f(3):0] --> foo[f_return_wire:0]
              (vl-check-bad-funcalls ctx args "part-selects" warnings))
             ((:vl-hid-dot :vl-hid-arraydot)
              ;; this would just be to weird
              (vl-check-bad-funcalls ctx args "hierarchical identifiers" warnings))
             (:vl-mintypmax
              ;; this would just be too weird
              (vl-check-bad-funcalls ctx args "minimum/typical/maximum delay expressions" warnings))
             (otherwise
              ;; Else everything seems fine
              (mv t warnings))))

          ((unless okp)
           (mv nil warnings nf x netdecls assigns))

          ((mv okp warnings nf args-prime netdecls assigns)
           (vl-exprlist-expand-function-calls args templates nf netdecls assigns warnings ctx))
          ((unless okp)
           (mv nil warnings nf x netdecls assigns))

          ((unless (eq op :vl-funcall))
           ;; Nothing more to do
           (mv t warnings nf (change-vl-nonatom x :args args-prime) netdecls assigns))

          (funname (and (consp args-prime)
                        (vl-fast-atom-p (car args-prime))
                        (vl-funname-p (vl-atom->guts (car args-prime)))
                        (vl-funname->name (vl-atom->guts (car args-prime)))))
          ((unless funname)
           (b* ((w (make-vl-warning
                    :type :vl-programming-error
                    :msg "In ~a0, found a function call expression whose ~
                          first argument is not a valid function-name atom; ~
                          this is seriously malformed.  Internal ~
                          representation: ~x1."
                    :args (list ctx x)
                    :fatalp t
                    :fn 'vl-expr-expand-function-calls)))
             (mv nil (cons w warnings) nf x netdecls assigns)))

          (template (vl-find-funtemplate funname templates))
          ((unless template)
           (b* ((w (make-vl-warning
                    :type :vl-bad-funcall
                    :msg "In ~a0, there is a call to function ~w1, which is ~
                          not defined: ~a2."
                    :args (list ctx funname x)
                    :fatalp t
                    :fn 'vl-expr-expand-function-calls)))
             (mv nil (cons w warnings) nf x netdecls assigns)))

          ((mv okp warnings nf x-prime netdecls assigns)
           (vl-expand-function-call template (cdr args-prime) nf netdecls assigns warnings ctx))
          ((unless okp)
           (mv nil warnings nf x netdecls assigns)))

       (mv t warnings nf x-prime netdecls assigns)))

   (defund vl-exprlist-expand-function-calls (x templates nf netdecls assigns warnings ctx)
     "Returns (MV SUCCESSP WARNINGS NF X-PRIME NETDECLS ASSIGNS)"
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-funtemplatelist-p templates)
                                 (vl-namefactory-p nf)
                                 (vl-netdecllist-p netdecls)
                                 (vl-assignlist-p assigns)
                                 (vl-warninglist-p warnings)
                                 (vl-modelement-p ctx))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv t warnings nf nil netdecls assigns))
          ((mv okp warnings nf car-prime netdecls assigns)
           (vl-expr-expand-function-calls (car x) templates nf netdecls assigns warnings ctx))
          ((unless okp)
           (mv nil warnings nf nil netdecls assigns))
          ((mv okp warnings nf cdr-prime netdecls assigns)
           (vl-exprlist-expand-function-calls (cdr x) templates nf netdecls assigns warnings ctx))
          ((unless okp)
           (mv nil warnings nf nil netdecls assigns)))
       (mv t warnings nf (cons car-prime cdr-prime) netdecls assigns))))

  (flag::make-flag vl-flag-expr-expand-function-calls
                   vl-expr-expand-function-calls
                   :flag-mapping ((vl-expr-expand-function-calls . expr)
                                  (vl-exprlist-expand-function-calls . list)))

  (local (defun my-induct (x templates nf netdecls assigns warnings ctx)
           (b* (((when (atom x))
                 (mv t warnings nf nil netdecls assigns))
                ((mv okp warnings nf car-prime netdecls assigns)
                 (vl-expr-expand-function-calls (car x) templates nf netdecls assigns warnings ctx))
                ((unless okp)
                 (mv nil warnings nf nil netdecls assigns))
                ((mv okp warnings nf cdr-prime netdecls assigns)
                 (my-induct (cdr x) templates nf netdecls assigns warnings ctx))
                ((unless okp)
                 (mv nil warnings nf nil netdecls assigns)))
             (mv t warnings nf (cons car-prime cdr-prime) netdecls assigns))))

  (defthm true-listp-of-vl-exprlist-expand-function-calls
    (true-listp (mv-nth 3 (vl-exprlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
    :rule-classes :type-prescription
    :hints(("Goal"
            :induct (my-induct x templates nf netdecls assigns warnings ctx)
            :in-theory (enable vl-exprlist-expand-function-calls))))

  (defthm len-of-vl-exprlist-expand-function-calls
    (let ((ret (vl-exprlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
      (implies (mv-nth 0 ret)
               (equal (len (mv-nth 3 ret))
                      (len x))))
    :hints(("Goal"
            :induct (my-induct x templates nf netdecls assigns warnings ctx)
            :in-theory (enable vl-exprlist-expand-function-calls))))

  (defthm consp-of-vl-exprlist-expand-function-calls
    (let ((ret (vl-exprlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
      (implies (mv-nth 0 ret)
               (equal (consp (mv-nth 3 ret))
                      (consp x))))
    :hints(("Goal"
            :induct (my-induct x templates nf netdecls assigns warnings ctx)
            :in-theory (enable vl-exprlist-expand-function-calls))))

  (defthm-vl-flag-expr-expand-function-calls

    (defthm vl-warninglist-p-of-vl-expr-expand-function-calls
      (let ((ret (vl-expr-expand-function-calls x templates nf netdecls assigns warnings ctx)))
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 1 ret))))
      :flag expr)

    (defthm vl-warninglist-p-of-vl-exprlist-expand-function-calls
      (let ((ret (vl-exprlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 1 ret))))
      :flag list)

    :hints(("Goal" :expand ((vl-expr-expand-function-calls x templates nf netdecls assigns warnings ctx)
                            (vl-exprlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))))


  (defthm-vl-flag-expr-expand-function-calls

    (defthm vl-expr-expand-function-calls-basics
      (let ((ret (vl-expr-expand-function-calls x templates nf netdecls assigns warnings ctx)))
        (implies (and (force (vl-expr-p x))
                      (force (vl-funtemplatelist-p templates))
                      (force (vl-namefactory-p nf))
                      (force (vl-netdecllist-p netdecls))
                      (force (vl-assignlist-p assigns))
                      (force (vl-modelement-p ctx)))
                 (and (vl-namefactory-p (mv-nth 2 ret))
                      (vl-expr-p        (mv-nth 3 ret))
                      (vl-netdecllist-p (mv-nth 4 ret))
                      (vl-assignlist-p  (mv-nth 5 ret)))))
      :flag expr)

    (defthm vl-exprlist-expand-function-calls-basics
      (let ((ret (vl-exprlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
        (implies (and (force (vl-exprlist-p x))
                      (force (vl-funtemplatelist-p templates))
                      (force (vl-namefactory-p nf))
                      (force (vl-netdecllist-p netdecls))
                      (force (vl-assignlist-p assigns))
                      (force (vl-modelement-p ctx)))
                 (and (vl-namefactory-p (mv-nth 2 ret))
                      (vl-exprlist-p    (mv-nth 3 ret))
                      (vl-netdecllist-p (mv-nth 4 ret))
                      (vl-assignlist-p  (mv-nth 5 ret)))))
      :flag list)

    :hints(("Goal" :expand ((vl-expr-expand-function-calls x templates nf netdecls assigns warnings ctx)
                            (vl-exprlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))))

  (verify-guards vl-expr-expand-function-calls))



; -----------------------------------------------------------------------------
;
;            Expanding Function Calls throughout Module Elements
;
; -----------------------------------------------------------------------------

(defmacro def-vl-expand-function-calls (name &key type body ctxp)
  (let* ((name-s       (symbol-name name))
         (type-s       (symbol-name type))
         (thm-warn-s   (cat "VL-WARNINGLIST-P-" name-s))
         (thm-basics-s (cat name-s "-BASICS"))
         (thm-warn     (intern-in-package-of-symbol thm-warn-s name))
         (thm-basics   (intern-in-package-of-symbol thm-basics-s name))
         (short        (cat "Expand function calls throughout a @(see " type-s ")"))
         (long         (cat "<p><b>Signature:</b> @(call " name-s ") returns
@('(mv successp warnings nf x-prime netdecls assigns)')</p>"))
         (ctx-part     (if ctxp '(ctx) nil)))

  `(defsection ,name
     :parents (vl-module-expand-functions)
     :short ,short
     :long ,long

    (defund ,name (x templates nf netdecls assigns warnings . ,ctx-part)
      "Returns (MV SUCCESSP WARNINGS NF X-PRIME NETDECLS ASSIGNS)"
      (declare (xargs :guard (and (,type x)
                                  (vl-funtemplatelist-p templates)
                                  (vl-namefactory-p nf)
                                  (vl-netdecllist-p netdecls)
                                  (vl-assignlist-p assigns)
                                  (vl-warninglist-p warnings)
                                  ,(if ctxp '(vl-modelement-p ctx) 't))))
      ,body)

    (local (in-theory (enable ,name)))

    (defthm ,thm-warn
      (let ((ret (,name x templates nf netdecls assigns warnings . ,ctx-part)))
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 1 ret)))))

    (defthm ,thm-basics
      (let ((ret (,name x templates nf netdecls assigns warnings . ,ctx-part)))
        (implies (and (force (,type x))
                      (force (vl-funtemplatelist-p templates))
                      (force (vl-namefactory-p nf))
                      (force (vl-netdecllist-p netdecls))
                      (force (vl-assignlist-p assigns))
                      ,(if ctxp '(force (vl-modelement-p ctx)) 't))
                 (and (vl-namefactory-p (mv-nth 2 ret))
                      (,type            (mv-nth 3 ret))
                      (vl-netdecllist-p (mv-nth 4 ret))
                      (vl-assignlist-p  (mv-nth 5 ret)))))
        :rule-classes ((:rewrite :backchain-limit-lst 0))))))

(defmacro def-vl-expand-function-calls-list (name &key type element ctxp)
  (let* ((name-s      (symbol-name name))
         (type-s      (symbol-name type))
         (thm-warn-s  (cat "VL-WARNINGLIST-P-" name-s))
         (thm-basic-s (cat name-s "-BASICS"))
         (thm-true-s  (cat "TRUE-LISTP-OF-" name-s))
         (thm-warn    (intern-in-package-of-symbol thm-warn-s name))
         (thm-basic   (intern-in-package-of-symbol thm-basic-s name))
         (thm-true    (intern-in-package-of-symbol thm-true-s name))
         (short       (cat "Expand function calls throughout a @(see " type-s ")"))
         (long        (cat "<p><b>Signature:</b> @(call " name-s ") returns
@('(mv successp warnings nf x-prime netdecls assigns)')</p>"))
         (ctx-part    (if ctxp '(ctx) nil)))

  `(defsection ,name
     :parents (vl-module-expand-functions)
     :short ,short
     :long ,long

    (defund ,name (x templates nf netdecls assigns warnings . ,ctx-part)
      "Returns (MV SUCCESSP WARNINGS NF X-PRIME NETDECLS ASSIGNS)"
      (declare (xargs :guard (and (,type x)
                                  (vl-funtemplatelist-p templates)
                                  (vl-namefactory-p nf)
                                  (vl-netdecllist-p netdecls)
                                  (vl-assignlist-p assigns)
                                  (vl-warninglist-p warnings)
                                  ,(if ctxp '(vl-modelement-p ctx) 't))))
      (b* (((when (atom x))
            (mv t warnings nf nil netdecls assigns))
           ((mv successp warnings nf car-prime netdecls assigns)
            (,element (car x) templates nf netdecls assigns warnings . ,ctx-part))
           ((unless successp)
            (mv nil warnings nf nil netdecls assigns))
           ((mv successp warnings nf cdr-prime netdecls assigns)
            (,name (cdr x) templates nf netdecls assigns warnings . ,ctx-part))
           ((unless successp)
            (mv nil warnings nf nil netdecls assigns)))
        (mv t warnings nf (cons car-prime cdr-prime) netdecls assigns)))

    (local (in-theory (enable ,name)))

    (defthm ,thm-warn
      (let ((ret (,name x templates nf netdecls assigns warnings . ,ctx-part)))
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 1 ret)))))

    (defthm ,thm-basic
      (let ((ret (,name x templates nf netdecls assigns warnings . ,ctx-part)))
        (implies (and (force (,type x))
                      (force (vl-funtemplatelist-p templates))
                      (force (vl-namefactory-p nf))
                      (force (vl-netdecllist-p netdecls))
                      (force (vl-assignlist-p assigns))
                      ,(if ctxp '(force (vl-modelement-p ctx)) 't))
                 (and (vl-namefactory-p (mv-nth 2 ret))
                      (,type            (mv-nth 3 ret))
                      (vl-netdecllist-p (mv-nth 4 ret))
                      (vl-assignlist-p  (mv-nth 5 ret)))))
      :rule-classes ((:rewrite :backchain-limit-lst 0)))

    (defthm ,thm-true
      (true-listp (mv-nth 3 (,name x templates nf netdecls assigns warnings . ,ctx-part)))
      :rule-classes :type-prescription))))


(def-vl-expand-function-calls vl-assign-expand-function-calls
  :type vl-assign-p
  :body
  (b* (((vl-assign x) x)
       ((mv okp1 warnings) (vl-check-bad-funcalls x (list x.lvalue) "left-hand sides of assignments" warnings))
       ((mv okp2 warnings) (vl-check-bad-funcalls x (vl-maybe-gatedelay-allexprs x.delay) "delay expressions" warnings))
       ((mv okp3 warnings nf rhs-prime netdecls assigns)
        (vl-expr-expand-function-calls x.expr templates nf netdecls assigns warnings x))
       (okp     (and okp1 okp2 okp3))
       (x-prime (change-vl-assign x :expr rhs-prime)))
    (mv okp warnings nf x-prime netdecls assigns)))

(def-vl-expand-function-calls-list vl-assignlist-expand-function-calls
  :type vl-assignlist-p
  :element vl-assign-expand-function-calls)



(def-vl-expand-function-calls vl-plainarg-expand-function-calls
  :type vl-plainarg-p
  :ctxp t
  :body
  (b* (((vl-plainarg x) x)

       ((unless x.expr)
        ;; Blanks are fine, nothing to do
        (mv t warnings nf x netdecls assigns))

       ((unless (vl-expr-has-funcalls x.expr))
        ;; Most of the time there aren't any function calls, so we don't really
        ;; need to be adding fatal warnings everywhere if a module instance
        ;; isn't resolved, and we don't need to do any re-consing.
        (mv t warnings nf x netdecls assigns))

       ;; Else, double-check the direction.  We definitely don't want to expand
       ;; a function call unless this is an input port, because it doesn't make
       ;; sense for a submodule instance to be outputting a value into a
       ;; function call.
       ((unless x.dir)
        (b* ((w (make-vl-warning
                 :type :vl-bad-instance
                 :msg "In ~a0, expected all arguments to be resolved before ~
                       function expansion."
                 :args (list ctx)
                 :fatalp t
                 :fn 'vl-plainarg-expand-function-calls)))
          (mv nil (cons w warnings) nf x netdecls assigns)))

       ((unless (eq x.dir :vl-input))
        (b* ((w (make-vl-warning
                 :type :vl-bad-argument
                 :msg "In ~a0, we found a function call in a ~s1-port ~
                       connection, ~a2, but we only allow function calls in ~
                       input-port connections."
                 :args (list ctx x.dir x)
                 :fatalp t
                 :fn 'vl-plainarg-expand-function-calls)))
          (mv nil (cons w warnings) nf x netdecls assigns)))

       ;; Else, seems okay to expand the function calls here.
       ((mv okp warnings nf expr-prime netdecls assigns)
        (vl-expr-expand-function-calls x.expr templates nf netdecls assigns warnings ctx))

       (x-prime (change-vl-plainarg x :expr expr-prime)))
    (mv okp warnings nf x-prime netdecls assigns)))

(def-vl-expand-function-calls-list vl-plainarglist-expand-function-calls
  :type vl-plainarglist-p
  :ctxp t
  :element vl-plainarg-expand-function-calls)

(def-vl-expand-function-calls vl-arguments-expand-function-calls
  :type vl-arguments-p
  :ctxp t
  :body
  (b* (((unless (vl-exprlist-has-funcalls (vl-arguments-allexprs x)))
        ;; Common case of no function calls, nothing to do, don't need to
        ;; be adding fatal warnings everywhere in case of unresolved args.
        (mv t warnings nf x netdecls assigns))

       ((when (vl-arguments->namedp x))
        (b* ((w (make-vl-warning
                 :type :vl-bad-instance
                 :msg "In ~a0, we expected all arguments to be resolved ~
                       before function expansion."
                 :args (list ctx)
                 :fatalp t
                 :fn 'vl-arguments-expand-function-calls)))
          (mv nil (cons w warnings) nf x netdecls assigns)))

       ;; Else, seems okay to expand the function calls here.
       ((mv okp warnings nf args-prime netdecls assigns)
        (vl-plainarglist-expand-function-calls (vl-arguments->args x)
                                               templates nf netdecls assigns warnings ctx))

       (x-prime (vl-arguments nil args-prime)))
    (mv okp warnings nf x-prime netdecls assigns)))

(def-vl-expand-function-calls vl-modinst-expand-function-calls
  :type vl-modinst-p
  :body
  (b* (((vl-modinst x) x)
       ((mv okp1 warnings) (vl-check-bad-funcalls x (vl-maybe-range-allexprs x.range) "module instance array ranges" warnings))
       ((mv okp2 warnings) (vl-check-bad-funcalls x (vl-maybe-gatedelay-allexprs x.delay) "delay expressions" warnings))
       ((mv okp3 warnings) (vl-check-bad-funcalls x (vl-arguments-allexprs x.paramargs) "module instance parameter-lists" warnings))
       ((mv okp4 warnings nf portargs-prime netdecls assigns)
        (vl-arguments-expand-function-calls x.portargs templates nf netdecls assigns warnings x))
       (okp (and okp1 okp2 okp3 okp4))
       (x-prime (change-vl-modinst x :portargs portargs-prime)))
    (mv okp warnings nf x-prime netdecls assigns)))

(def-vl-expand-function-calls-list vl-modinstlist-expand-function-calls
  :type vl-modinstlist-p
  :element vl-modinst-expand-function-calls)



(def-vl-expand-function-calls vl-gateinst-expand-function-calls
  :type vl-gateinst-p
  :body
  (b* (((vl-gateinst x) x)
       ((mv okp1 warnings) (vl-check-bad-funcalls x (vl-maybe-range-allexprs x.range) "gate instance array ranges" warnings))
       ((mv okp2 warnings) (vl-check-bad-funcalls x (vl-maybe-gatedelay-allexprs x.delay) "delay expressions" warnings))
       ((mv okp3 warnings nf args-prime netdecls assigns)
        (vl-plainarglist-expand-function-calls x.args templates nf netdecls assigns warnings x))
       (okp     (and okp1 okp2 okp3))
       (x-prime (change-vl-gateinst x :args args-prime)))
    (mv okp warnings nf x-prime netdecls assigns)))

(def-vl-expand-function-calls-list vl-gateinstlist-expand-function-calls
  :type vl-gateinstlist-p
  :element vl-gateinst-expand-function-calls)



(def-vl-expand-function-calls vl-assignstmt-expand-function-calls
  :type vl-assignstmt-p
  :ctxp t
  :body
  (b* (((vl-assignstmt x) x)
       ((mv okp1 warnings) (vl-check-bad-funcalls ctx (list x.lvalue) "left-hand sides of assignment statements" warnings))
       ((mv okp2 warnings) (vl-check-bad-funcalls ctx (vl-maybe-delayoreventcontrol-allexprs x.ctrl) "delay/event controls" warnings))
       ((mv okp3 warnings nf expr-prime netdecls assigns)
        (vl-expr-expand-function-calls x.expr templates nf netdecls assigns warnings ctx))
       (okp     (and okp1 okp2 okp3))
       (x-prime (change-vl-assignstmt x :expr expr-prime)))
    (mv okp warnings nf x-prime netdecls assigns)))

(encapsulate
  ()
  (set-ignore-ok t)
  (def-vl-expand-function-calls vl-deassignstmt-expand-function-calls
    :type vl-deassignstmt-p
    :ctxp t
    :body
    (b* (((vl-deassignstmt x) x)
         ((mv okp warnings) (vl-check-bad-funcalls ctx (list x.lvalue) "deassign statements" warnings)))
      (mv okp warnings nf x netdecls assigns))))

(def-vl-expand-function-calls vl-enablestmt-expand-function-calls
  :type vl-enablestmt-p
  :ctxp t
  :body
  (b* (((vl-enablestmt x) x)
       ((mv okp1 warnings) (vl-check-bad-funcalls ctx (list x.id) "enable statement identifiers" warnings))
       ;; BOZO we probably need to be making input/output distinctions here to prevent function
       ;; calls on task outputs.
       ((mv okp2 warnings nf args-prime netdecls assigns)
        (vl-exprlist-expand-function-calls x.args templates nf netdecls assigns warnings ctx))
       (okp     (and okp1 okp2))
       (x-prime (change-vl-enablestmt x :args args-prime)))
    (mv okp warnings nf x-prime netdecls assigns)))

(encapsulate
  ()
  (set-ignore-ok t)
  (def-vl-expand-function-calls vl-disablestmt-expand-function-calls
    :type vl-disablestmt-p
    :ctxp t
    :body
    (b* (((vl-disablestmt x) x)
         ((mv okp warnings) (vl-check-bad-funcalls ctx (list x.id) "disable statements" warnings)))
      (mv okp warnings nf x netdecls assigns))))

(encapsulate
  ()
  (set-ignore-ok t)
  (def-vl-expand-function-calls vl-eventtriggerstmt-expand-function-calls
    :type vl-eventtriggerstmt-p
    :ctxp t
    :body
    (b* (((vl-eventtriggerstmt x) x)
         ((mv okp warnings) (vl-check-bad-funcalls ctx (list x.id) "event trigger statements" warnings)))
      (mv okp warnings nf x netdecls assigns))))

(def-vl-expand-function-calls vl-atomicstmt-expand-function-calls
  :type vl-atomicstmt-p
  :ctxp t
  :body
  (case (tag x)
    (:vl-nullstmt         (mv t warnings nf x netdecls assigns))
    (:vl-assignstmt       (vl-assignstmt-expand-function-calls       x templates nf netdecls assigns warnings ctx))
    (:vl-deassignstmt     (vl-deassignstmt-expand-function-calls     x templates nf netdecls assigns warnings ctx))
    (:vl-enablestmt       (vl-enablestmt-expand-function-calls       x templates nf netdecls assigns warnings ctx))
    (:vl-disablestmt      (vl-disablestmt-expand-function-calls      x templates nf netdecls assigns warnings ctx))
    (:vl-eventtriggerstmt (vl-eventtriggerstmt-expand-function-calls x templates nf netdecls assigns warnings ctx))
    (otherwise
     (prog2$ (er hard 'vl-atomicstmt-expand-function-calls "impossible")
             (mv t warnings nf x netdecls assigns)))))


(defsection vl-compoundstmt-bad-funcall-check

; It's sort of sad that we have to do this; we separate out the checks for bad
; function calls from within compound statements.  The main problem we're
; solving is that if split into cases on (vl-compoundstmt->type x), then the
; vl-compoundstmt-basic-checksp-of-change-vl-compoundstmt theorem won't match,
; and we'll not be able to prove that this produces a good statement.  I guess
; it's not too bad to do it this way.

  (defund vl-compoundstmt-bad-funcall-check (x warnings ctx)
    "Returns (MV OKP WARNINGS)"
    (declare (xargs :guard (and (vl-stmt-p x)
                                (vl-compoundstmt-p x)
                                (vl-warninglist-p warnings)
                                (vl-modelement-p ctx))))
    (b* ( ;; Globally prohibit function calls in declarations and timing controls
         ((vl-compoundstmt x) x)
         ((mv okp1 warnings) (vl-check-bad-funcalls ctx (vl-blockitemlist-allexprs x.decls) "block declarations" warnings))
         ((mv okp2 warnings) (vl-check-bad-funcalls ctx (vl-maybe-delayoreventcontrol-allexprs x.ctrl) "timing controls" warnings))
         ((mv okp3 warnings)
          (cond ((eq x.type :vl-forstmt)
                 ;; Don't allow function calls in initlhs or nextlhs.
                 (vl-check-bad-funcalls ctx (list (vl-forstmt->initlhs x)
                                                  (vl-forstmt->nextlhs x))
                                        "left-hand sides of for-loop assignments" warnings))
                ((eq x.type :vl-casestmt)
                 ;; Don't allow function calls in match expressions
                 (vl-check-bad-funcalls ctx (vl-casestmt->exprs x)
                                        "case-statement match expressions" warnings))
                (t
                 (mv t warnings)))))
      (mv (and okp1 okp2 okp3)
          warnings)))

  (local (in-theory (enable vl-compoundstmt-bad-funcall-check)))

  (defthm vl-warninglist-p-of-vl-compoundstmt-bad-funcall-check
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-compoundstmt-bad-funcall-check x warnings ctx))))))

(defsection vl-stmt-expand-function-calls

  (mutual-recursion

   (defund vl-stmt-expand-function-calls (x templates nf netdecls assigns warnings ctx)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-funtemplatelist-p templates)
                                 (vl-namefactory-p nf)
                                 (vl-netdecllist-p netdecls)
                                 (vl-assignlist-p assigns)
                                 (vl-warninglist-p warnings)
                                 (vl-modelement-p ctx))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (b* (((when (vl-fast-atomicstmt-p x))
           (vl-atomicstmt-expand-function-calls x templates nf netdecls assigns warnings ctx))
          ((vl-compoundstmt x) x)

          ((mv okp1 warnings)
           (vl-compoundstmt-bad-funcall-check x warnings ctx))
          ((mv okp2 warnings nf exprs-prime netdecls assigns)
           (vl-exprlist-expand-function-calls x.exprs templates nf netdecls assigns warnings ctx))
          ((mv okp3 warnings nf stmts-prime netdecls assigns)
           (vl-stmtlist-expand-function-calls x.stmts templates nf netdecls assigns warnings ctx))
          ((unless (and okp1 okp2 okp3))
           (mv nil warnings nf x netdecls assigns))

          (x-prime (change-vl-compoundstmt x
                                           :exprs exprs-prime
                                           :stmts stmts-prime)))
       (mv t warnings nf x-prime netdecls assigns)))

   (defund vl-stmtlist-expand-function-calls (x templates nf netdecls assigns warnings ctx)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-funtemplatelist-p templates)
                                 (vl-namefactory-p nf)
                                 (vl-netdecllist-p netdecls)
                                 (vl-assignlist-p assigns)
                                 (vl-warninglist-p warnings)
                                 (vl-modelement-p ctx))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (b* (((when (atom x))
           (mv t warnings nf nil netdecls assigns))
          ((mv car-successp warnings nf car-prime netdecls assigns)
           (vl-stmt-expand-function-calls (car x) templates nf netdecls assigns warnings ctx))
          ((mv cdr-successp warnings nf cdr-prime netdecls assigns)
           (vl-stmtlist-expand-function-calls (cdr x) templates nf netdecls assigns warnings ctx)))
       (mv (and car-successp cdr-successp)
           warnings nf
           (cons car-prime cdr-prime)
           netdecls assigns))))

  (flag::make-flag flag-vl-stmt-expand-function-calls
                   vl-stmt-expand-function-calls
                   :flag-mapping ((vl-stmt-expand-function-calls . stmt)
                                  (vl-stmtlist-expand-function-calls . list)))

  (local (defun my-induct (x templates nf netdecls assigns warnings ctx)
           (b* (((when (atom x))
                 (mv t warnings nf nil netdecls assigns))
                ((mv car-successp warnings nf car-prime netdecls assigns)
                 (vl-stmt-expand-function-calls (car x) templates nf netdecls assigns warnings ctx))
                ((mv cdr-successp warnings nf cdr-prime netdecls assigns)
                 (my-induct (cdr x) templates nf netdecls assigns warnings ctx)))
             (mv (and car-successp cdr-successp)
                 warnings nf
                 (cons car-prime cdr-prime)
                 netdecls assigns))))

  (defthm true-listp-of-vl-stmtlist-expand-function-calls
    (true-listp (mv-nth 3 (vl-stmtlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
    :rule-classes :type-prescription
    :hints(("Goal"
            :in-theory (enable vl-stmtlist-expand-function-calls)
            :induct (my-induct x templates nf netdecls assigns warnings ctx))))

  (defthm len-of-vl-stmtlist-expand-function-calls
    (equal (len (mv-nth 3 (vl-stmtlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
           (len x))
    :hints(("Goal"
            :in-theory (enable vl-stmtlist-expand-function-calls)
            :induct (my-induct x templates nf netdecls assigns warnings ctx))))

  (defthm consp-of-vl-stmtlist-expand-function-calls
    (equal (consp (mv-nth 3 (vl-stmtlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
           (consp x))
    :hints(("Goal"
            :in-theory (enable vl-stmtlist-expand-function-calls)
            :induct (my-induct x templates nf netdecls assigns warnings ctx))))

  (defthm-flag-vl-stmt-expand-function-calls

    (defthm vl-warninglist-p-of-vl-stmt-expand-function-calls
      (let ((ret (vl-stmt-expand-function-calls x templates nf netdecls assigns warnings ctx)))
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 1 ret))))
      :flag stmt)

    (defthm vl-warninglist-p-of-vl-stmtlist-expand-function-calls
      (let ((ret (vl-stmtlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
        (implies (force (vl-warninglist-p warnings))
                 (vl-warninglist-p (mv-nth 1 ret))))
      :flag list)

    :hints(("Goal"
            :expand ((vl-stmt-expand-function-calls x templates nf netdecls assigns warnings ctx)
                     (vl-stmtlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))))


  (defthm-flag-vl-stmt-expand-function-calls

    (defthm vl-stmt-expand-function-calls-basics
      (let ((ret (vl-stmt-expand-function-calls x templates nf netdecls assigns warnings ctx)))
        (implies (and (force (vl-stmt-p x))
                      (force (vl-funtemplatelist-p templates))
                      (force (vl-namefactory-p nf))
                      (force (vl-netdecllist-p netdecls))
                      (force (vl-assignlist-p assigns))
                      (force (vl-modelement-p ctx)))
                 (and (vl-namefactory-p (mv-nth 2 ret))
                      (vl-stmt-p        (mv-nth 3 ret))
                      (vl-netdecllist-p (mv-nth 4 ret))
                      (vl-assignlist-p  (mv-nth 5 ret)))))
      :flag stmt)

    (defthm vl-stmtlist-expand-function-calls-basics
      (let ((ret (vl-stmtlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))
        (implies (and (force (vl-stmtlist-p x))
                      (force (vl-funtemplatelist-p templates))
                      (force (vl-namefactory-p nf))
                      (force (vl-netdecllist-p netdecls))
                      (force (vl-assignlist-p assigns))
                      (force (vl-modelement-p ctx)))
                 (and (vl-namefactory-p (mv-nth 2 ret))
                      (vl-stmtlist-p    (mv-nth 3 ret))
                      (vl-netdecllist-p (mv-nth 4 ret))
                      (vl-assignlist-p  (mv-nth 5 ret)))))
      :flag list)

    :hints(("Goal"
            :expand ((vl-stmt-expand-function-calls x templates nf netdecls assigns warnings ctx)
                     (vl-stmtlist-expand-function-calls x templates nf netdecls assigns warnings ctx)))))

  (verify-guards vl-stmt-expand-function-calls))



(def-vl-expand-function-calls vl-always-expand-function-calls
  :type vl-always-p
  :body
  (b* (((vl-always x) x)
       ((mv okp warnings nf stmt-prime netdecls assigns)
        (vl-stmt-expand-function-calls x.stmt templates nf netdecls assigns warnings x))
       (x-prime (change-vl-always x :stmt stmt-prime)))
    (mv okp warnings nf x-prime netdecls assigns)))

(def-vl-expand-function-calls-list vl-alwayslist-expand-function-calls
  :type vl-alwayslist-p
  :element vl-always-expand-function-calls)


(def-vl-expand-function-calls vl-initial-expand-function-calls
  :type vl-initial-p
  :body
  (b* (((vl-initial x) x)
       ((mv okp warnings nf stmt-prime netdecls assigns)
        (vl-stmt-expand-function-calls x.stmt templates nf netdecls assigns warnings x))
       (x-prime (change-vl-initial x :stmt stmt-prime)))
    (mv okp warnings nf x-prime netdecls assigns)))

(def-vl-expand-function-calls-list vl-initiallist-expand-function-calls
  :type vl-initiallist-p
  :element vl-initial-expand-function-calls)




(set-ignore-ok t)

;; We now introduce a bunch of functions that basically just check that the other
;; module elements don't have any function calls in them.

(def-vl-expand-function-calls vl-port-expand-function-calls
    :type vl-port-p
    :body
    (b* (((mv okp warnings) (vl-check-bad-funcalls x (vl-port-allexprs x) "ports" warnings)))
      (mv okp warnings nf x netdecls assigns)))

(def-vl-expand-function-calls-list vl-portlist-expand-function-calls
  :type vl-portlist-p
  :element vl-port-expand-function-calls)

(def-vl-expand-function-calls vl-portdecl-expand-function-calls
  :type vl-portdecl-p
  :body
  (b* (((mv okp warnings) (vl-check-bad-funcalls x (vl-portdecl-allexprs x) "port declarations" warnings)))
    (mv okp warnings nf x netdecls assigns)))

(def-vl-expand-function-calls-list vl-portdecllist-expand-function-calls
  :type vl-portdecllist-p
  :element vl-portdecl-expand-function-calls)


(def-vl-expand-function-calls vl-netdecl-expand-function-calls
  :type vl-netdecl-p
  :body
  (b* (((mv okp warnings) (vl-check-bad-funcalls x (vl-netdecl-allexprs x) "wire declarations" warnings)))
    (mv okp warnings nf x netdecls assigns)))

(def-vl-expand-function-calls-list vl-netdecllist-expand-function-calls
  :type vl-netdecllist-p
  :element vl-netdecl-expand-function-calls)


(def-vl-expand-function-calls vl-regdecl-expand-function-calls
  :type vl-regdecl-p
  :body
  (b* (((mv okp warnings) (vl-check-bad-funcalls x (vl-regdecl-allexprs x) "reg declarations" warnings)))
    (mv okp warnings nf x netdecls assigns)))

(def-vl-expand-function-calls-list vl-regdecllist-expand-function-calls
  :type vl-regdecllist-p
  :element vl-regdecl-expand-function-calls)


(def-vl-expand-function-calls vl-vardecl-expand-function-calls
  :type vl-vardecl-p
  :body
  (b* (((mv okp warnings) (vl-check-bad-funcalls x (vl-vardecl-allexprs x) "variable declarations" warnings)))
    (mv okp warnings nf x netdecls assigns)))

(def-vl-expand-function-calls-list vl-vardecllist-expand-function-calls
  :type vl-vardecllist-p
  :element vl-vardecl-expand-function-calls)


(def-vl-expand-function-calls vl-eventdecl-expand-function-calls
  :type vl-eventdecl-p
  :body
  (b* (((mv okp warnings) (vl-check-bad-funcalls x (vl-eventdecl-allexprs x) "event declarations" warnings)))
    (mv okp warnings nf x netdecls assigns)))

(def-vl-expand-function-calls-list vl-eventdecllist-expand-function-calls
  :type vl-eventdecllist-p
  :element vl-eventdecl-expand-function-calls)


(def-vl-expand-function-calls vl-paramdecl-expand-function-calls
  :type vl-paramdecl-p
  :body
  (b* (((mv okp warnings) (vl-check-bad-funcalls x (vl-paramdecl-allexprs x) "parameter declarations" warnings)))
    (mv okp warnings nf x netdecls assigns)))

(def-vl-expand-function-calls-list vl-paramdecllist-expand-function-calls
  :type vl-paramdecllist-p
  :element vl-paramdecl-expand-function-calls)

(set-ignore-ok nil)




; -----------------------------------------------------------------------------
;
;                        Generating "Flat" Templates
;
; -----------------------------------------------------------------------------

(defsection vl-flatten-funtemplates
  :parents (expand-functions)
  :short "Flatten the templates for each function, inlining any calls of other
functions so that the templates are function-call free."

  :long "<p><b>Signature:</b> @(call vl-flatten-funtemplates) returns @('(mv
successp warnings nf done)').</p>

<p>Our flattening algorithm basically takes two @(see vl-funtemplatelist-p)s,
@('todo') and @('done').  Initially the @('todo') list has the template for
every function and the @('done') list is empty.</p>

<p>We assume that these are in dependency order; see @(see
vl-depsort-functions).  This ensures that the @('done') list contains a
template for any function that is called in the @('todo') list.  Moreover, as
we work we maintain the invariant that the templates in the done-list are
function-call free.</p>

<p>For each @('todo') template, all we need to do is expand any function calls
in the assignments by using our normal function for function inlining, @(see
vl-assignlist-expand-function-calls), using the @('done') list as the
templates.  This produces some new assignments that we add to the template, and
some new net declarations that we add as new locals.</p>

<p>Here is an example of the idea.  Suppose we have:</p>

@({
    function buf;
      input a;
      reg b;
      b = ~a;
      buf = ~b;
    endfunction

    function doublebuf;
      input i;
      reg r;
      r = buf(i);
      doublebuf = buf(r);
    endfunction
})

<p>Then, adopting a pseudo-code for representing the templates, we will have
initial templates that look like this:</p>

@({
  buf_template {
    inputs:  wire a;
    locals:  wire b;
    out:     wire buf;
    assigns: assign b = ~a;
             assign buf = ~b;
  }

  doublebuf_template {
    inputs:  wire i;
    locals:  wire r;
    out:     wire doublebuf;
    assigns: assign r = buf(i);
             assign doublebuf = buf(r);
  }
})

<p>To flatten the doublebuf_template, we basically want to convert it into
this:</p>

@({
  doublebuf_template {
    inputs:  wire i;
    locals:  wire r, a1, b1, buf1, a2, b2, buf2;
    out:     wire doublebuf
    assigns: assign b1 = ~a1;
             assign buf1 = ~b1;
             assign r = buf1;
             assign b2 = ~a2;
             assign buf2 = ~b2;
             assign doublebuf = buf2;
  }
})

<p>And hence we've eliminated all the function calls from
doublebuf_template.</p>"

  (defund vl-flatten-funtemplates (todo done nf warnings)
    "Returns (MV SUCCESSP WARNINGS NF DONE)"
    (declare (xargs :guard (and (vl-funtemplatelist-p todo)
                                (vl-funtemplatelist-p done)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom todo))
          (mv t warnings nf done))
         (t1 (car todo))
         ((vl-funtemplate t1) t1)

         ;; Subtle: we seed the netdecls accumulator with t1.locals so the
         ;; current local wires just get extended with whatever new wires are
         ;; necessary.  But, the initial assigns accumulator must be NIL,
         ;; rather than t1.assigns, because the whole point is to rewrite the
         ;; current assigns, not to keep their old versions (that may have
         ;; function calls).

         ((mv successp warnings nf rw-assigns netdecls add-assigns)
          (vl-assignlist-expand-function-calls t1.assigns done nf
                                               t1.locals ;; netdecl acc
                                               nil       ;; assigns acc
                                               warnings))
         ((unless successp)
          (mv nil warnings nf nil))

         (assigns (append rw-assigns add-assigns))

         ;; Probably unnecessary sanity check to make sure that things really are flat.
         ((when (vl-exprlist-has-funcalls (vl-assignlist-allexprs assigns)))
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg  "While flattening function templates in ~s0, we ~
                          failed to eliminate all the function calls within ~
                          ~s1.  This shouldn't be possible if we have ~
                          properly deporder sorted the functions."
                   :args (list (and (vl-namefactory->mod nf)
                                    (vl-module->name (vl-namefactory->mod nf)))
                               t1.name)
                   :fatalp t
                   :fn 'vl-flatten-funtemplates)))
            (mv nil (cons w warnings) nf nil)))

         (new-t1 (change-vl-funtemplate t1
                                        :locals netdecls
                                        :assigns assigns)))
      (vl-flatten-funtemplates (cdr todo)
                               (cons new-t1 done)
                               nf warnings)))

  (local (in-theory (enable vl-flatten-funtemplates)))

  (defthm vl-warninglist-p-of-vl-flatten-funtemplates
    (implies (vl-warninglist-p warnings)
             (vl-warninglist-p (mv-nth 1 (vl-flatten-funtemplates todo done nf warnings)))))

  (defthm vl-flatten-funtemplates-basics
    (let ((ret (vl-flatten-funtemplates todo done nf warnings)))
      (implies (and (vl-funtemplatelist-p todo)
                    (vl-funtemplatelist-p done)
                    (vl-namefactory-p nf))
               (and (vl-namefactory-p (mv-nth 2 ret))
                    (vl-funtemplatelist-p (mv-nth 3 ret)))))))




; -----------------------------------------------------------------------------
;
;                          Main Transformation
;
; -----------------------------------------------------------------------------

(defsection vl-module-expand-functions
  :parents (expand-functions)
  :short "Eliminate functions from a module by inlining functions wherever
they are called."

  :long "<p>This is our top-level transformation that eliminates functions from
a module.  The major steps are:</p>

<ul>

<li>Dependency-order sort the functions so that our flattening scheme will
work (to supported nested functions); see @(see vl-depsort-functions).</li>

<li>Rewrite the functions to eliminate any uses of parameters, which for
functions seem to be just a way of naming constants.  See @(see
vl-fundecllist-expand-params).</li>

<li>Convert all of the function declarations into templates (see @(see
vl-funtemplate-p)) that can be used to carry out function-inlining.</li>

<li>Rewrite the templates by inlining any function calls within them; see @(see
vl-flatten-funtemplates), so that all of the templates are function-call
free.</li>

<li>Use the flat templates to rewrite all of the other module constructs and
eliminate any function calls.  This can generate additional net declarations
and assignments that need to be added to the module.</li>

</ul>"

  ;; Ugh, all of these accumulators slow ACL2 to a crawl.

  (local (in-theory (disable VL-ASSIGNLIST-P-WHEN-SUBSETP-EQUAL
                             VL-NETDECLLIST-P-WHEN-SUBSETP-EQUAL
                             VL-PARAMDECLLIST-P-WHEN-SUBSETP-EQUAL
                             VL-EVENTDECLLIST-P-WHEN-SUBSETP-EQUAL
                             VL-REGDECLLIST-P-WHEN-SUBSETP-EQUAL
                             VL-VARDECLLIST-P-WHEN-SUBSETP-EQUAL
                             VL-FUNTEMPLATELIST-P-WHEN-SUBSETP-EQUAL
                             VL-PORTDECLLIST-P-WHEN-SUBSETP-EQUAL
                             TRUE-LISTP-WHEN-STRING-LISTP
                             TRUE-LISTP-WHEN-VL-ATTS-P
                             VL-ATTS-P-WHEN-NOT-CONSP
                             CONSP-WHEN-MEMBER-EQUAL-OF-VL-MODITEM-ALIST-P
                             CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                             (:ruleset tag-reasoning))))


  ;; To try to control the case explosion we break the function into a few parts.

  (defund vl-module-expand-functions-aux (x)
    "Returns (MV OKP WARNINGS NF TEMPLATES)"
    (declare (xargs :guard (vl-module-p x)))

    ;; This is just a stupid function to cut down on the amount of cases in
    ;; vl-module-expand-functions.

    (b* (((vl-module x) x)
         (warnings x.warnings)

         ((mv okp warnings fundecls) (vl-depsort-functions x.fundecls warnings))
         ((unless okp)
          (mv nil warnings nil nil))

         ;; Deal with function parameters.
         ((mv okp warnings fundecls) (vl-fundecllist-expand-params fundecls warnings x))
         ((unless okp)
          (mv nil warnings nil nil))

         ;; Make initial (unflattened) templates.
         ((mv okp warnings templates) (vl-fundecllist-expansion-templates fundecls warnings))
         ((unless okp)
          (mv nil warnings nil nil))

         ;; Flatten the templates so that they are function-call free.
         (nf (vl-starting-namefactory x))
         ((mv okp warnings nf templates) (vl-flatten-funtemplates templates nil nf warnings))
         ((unless okp)
          (vl-free-namefactory nf)
          (mv nil warnings nil nil)))

      (mv t warnings nf templates)))

  (defthm vl-module-expand-functions-aux-basics
    (let ((ret (vl-module-expand-functions-aux x)))
      (implies (force (vl-module-p x))
               (and (vl-warninglist-p (mv-nth 1 ret))
                    (equal (vl-namefactory-p (mv-nth 2 ret)) (mv-nth 0 ret))
                    (vl-funtemplatelist-p (mv-nth 3 ret)))))
    :hints(("Goal" :in-theory (enable vl-module-expand-functions-aux))))



  ;; Even this is pushing it.

  (defund vl-module-expand-calls-in-decls (ports portdecls netdecls vardecls regdecls eventdecls paramdecls
                                                 templates nf nacc aacc warnings)
    (declare (xargs :guard (and (vl-portlist-p ports)
                                (vl-portdecllist-p portdecls)
                                (vl-netdecllist-p netdecls)
                                (vl-vardecllist-p vardecls)
                                (vl-regdecllist-p regdecls)
                                (vl-eventdecllist-p eventdecls)
                                (vl-paramdecllist-p paramdecls)
                                (vl-funtemplatelist-p templates)
                                (vl-namefactory-p nf)
                                (vl-netdecllist-p nacc)
                                (vl-assignlist-p aacc)
                                (vl-warninglist-p warnings))))
    (b* (((mv okp1  warnings nf ports      nacc aacc) (vl-portlist-expand-function-calls      ports      templates nf nacc aacc warnings))
         ((mv okp2  warnings nf portdecls  nacc aacc) (vl-portdecllist-expand-function-calls  portdecls  templates nf nacc aacc warnings))
         ((mv okp3  warnings nf netdecls   nacc aacc) (vl-netdecllist-expand-function-calls   netdecls   templates nf nacc aacc warnings))
         ((mv okp4  warnings nf vardecls   nacc aacc) (vl-vardecllist-expand-function-calls   vardecls   templates nf nacc aacc warnings))
         ((mv okp5  warnings nf regdecls   nacc aacc) (vl-regdecllist-expand-function-calls   regdecls   templates nf nacc aacc warnings))
         ((mv okp6  warnings nf eventdecls nacc aacc) (vl-eventdecllist-expand-function-calls eventdecls templates nf nacc aacc warnings))
         ((mv okp7  warnings nf paramdecls nacc aacc) (vl-paramdecllist-expand-function-calls paramdecls templates nf nacc aacc warnings)))
      ;; Using and* here cuts the proof time for the next proof by about 10x.
      (mv (and* okp1 okp2 okp3 okp4 okp5 okp6 okp7)
          warnings nf nacc aacc
          ports portdecls netdecls vardecls regdecls eventdecls paramdecls)))

  (defthm vl-module-expand-calls-in-decls-basics
    (implies (and (force (vl-portlist-p ports))
                  (force (vl-portdecllist-p portdecls))
                  (force (vl-netdecllist-p netdecls))
                  (force (vl-vardecllist-p vardecls))
                  (force (vl-regdecllist-p regdecls))
                  (force (vl-eventdecllist-p eventdecls))
                  (force (vl-paramdecllist-p paramdecls))
                  (force (vl-funtemplatelist-p templates))
                  (force (vl-namefactory-p nf))
                  (force (vl-netdecllist-p nacc))
                  (force (vl-assignlist-p aacc))
                  (force (vl-warninglist-p warnings)))
             (b* (((mv ?okp warnings nf nacc aacc
                       ports portdecls netdecls vardecls regdecls eventdecls paramdecls)
                   (vl-module-expand-calls-in-decls ports portdecls netdecls vardecls regdecls eventdecls paramdecls
                                                    templates nf nacc aacc warnings)))
               (and (vl-portlist-p ports)
                    (vl-portdecllist-p portdecls)
                    (vl-netdecllist-p netdecls)
                    (vl-vardecllist-p vardecls)
                    (vl-regdecllist-p regdecls)
                    (vl-eventdecllist-p eventdecls)
                    (vl-paramdecllist-p paramdecls)
                    (vl-namefactory-p nf)
                    (vl-netdecllist-p nacc)
                    (vl-assignlist-p aacc)
                    (vl-warninglist-p warnings))))
    :hints(("Goal" :in-theory (enable vl-module-expand-calls-in-decls))))


  (defund vl-module-expand-calls-in-nondecls (assigns modinsts gateinsts alwayses initials
                                                      templates nf nacc aacc warnings)
    (declare (xargs :guard (and (vl-assignlist-p assigns)
                                (vl-modinstlist-p modinsts)
                                (vl-gateinstlist-p gateinsts)
                                (vl-alwayslist-p alwayses)
                                (vl-initiallist-p initials)
                                (vl-funtemplatelist-p templates)
                                (vl-namefactory-p nf)
                                (vl-netdecllist-p nacc)
                                (vl-assignlist-p aacc)
                                (vl-warninglist-p warnings))))
    (b* (((mv okp1 warnings nf assigns    nacc aacc) (vl-assignlist-expand-function-calls    assigns    templates nf nacc aacc warnings))
         ((mv okp2 warnings nf modinsts   nacc aacc) (vl-modinstlist-expand-function-calls   modinsts   templates nf nacc aacc warnings))
         ((mv okp3 warnings nf gateinsts  nacc aacc) (vl-gateinstlist-expand-function-calls  gateinsts  templates nf nacc aacc warnings))
         ((mv okp4 warnings nf alwayses   nacc aacc) (vl-alwayslist-expand-function-calls    alwayses   templates nf nacc aacc warnings))
         ((mv okp5 warnings nf initials   nacc aacc) (vl-initiallist-expand-function-calls   initials   templates nf nacc aacc warnings)))
      (mv (and* okp1 okp2 okp3 okp4 okp5)
          warnings nf nacc aacc
          assigns modinsts gateinsts alwayses initials)))

  (defthm vl-module-expand-calls-in-nondecls-basics
    (implies (and (force (vl-assignlist-p assigns))
                  (force (vl-modinstlist-p modinsts))
                  (force (vl-gateinstlist-p gateinsts))
                  (force (vl-alwayslist-p alwayses))
                  (force (vl-initiallist-p initials))
                  (force (vl-funtemplatelist-p templates))
                  (force (vl-namefactory-p nf))
                  (force (vl-netdecllist-p nacc))
                  (force (vl-assignlist-p aacc))
                  (force (vl-warninglist-p warnings)))
             (b* (((mv ?okp warnings nf nacc aacc
                       assigns modinsts gateinsts alwayses initials)
                   (vl-module-expand-calls-in-nondecls assigns modinsts gateinsts alwayses initials
                                                       templates nf nacc aacc warnings)))
               (and (vl-assignlist-p assigns)
                    (vl-modinstlist-p modinsts)
                    (vl-gateinstlist-p gateinsts)
                    (vl-alwayslist-p alwayses)
                    (vl-initiallist-p initials)
                    (vl-namefactory-p nf)
                    (vl-netdecllist-p nacc)
                    (vl-assignlist-p aacc)
                    (vl-warninglist-p warnings))))
    :hints(("Goal" :in-theory (enable vl-module-expand-calls-in-nondecls))))




  (defund vl-module-expand-functions (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         ((when (vl-module->hands-offp x))
          x)

         ;; Warning: don't be tempted to put in an optimization to do nothing if
         ;; there are no function declarations.  Just because there are no function
         ;; declarations doesn't mean there are no function CALLS, and we want to
         ;; go ahead and issue warnings about them.
         ((mv okp warnings nf templates) (vl-module-expand-functions-aux x))
         ((unless okp)
          (change-vl-module x :warnings warnings))

         ;; Apply the templates to expand function calls everywhere throughout
         ;; the module.
         ;;
         ;; We start with empty netdecls and assigns for our accumulators, rather
         ;; than the module's netdecls and assigns, because (especially for
         ;; assigns) as we inline function calls we're going to potentially be
         ;; rewriting assignments, and we don't want to have the old assigns
         ;; sitting in the accumulator.

         (nacc nil) ;; accumulator for new netdecls
         (aacc nil) ;; accumulator for new assignments

         ((mv okp1 warnings nf nacc aacc
              ports portdecls netdecls vardecls regdecls eventdecls paramdecls)
          (vl-module-expand-calls-in-decls x.ports x.portdecls x.netdecls x.vardecls
                                           x.regdecls x.eventdecls x.paramdecls
                                           templates nf nacc aacc warnings))
         ((mv okp2 warnings nf nacc aacc
              assigns modinsts gateinsts alwayses initials)
          (vl-module-expand-calls-in-nondecls x.assigns x.modinsts x.gateinsts
                                              x.alwayses x.initials
                                              templates nf nacc aacc warnings))
         (- (vl-free-namefactory nf))

         (okp (and okp1 okp2))
         ((unless okp)
          (change-vl-module x :warnings warnings))

         ;; Everything was okay.  Then, we can throw away all the function declarations
         ;; and just use the replacements for all of these things.
         (x-prime (change-vl-module x
                                    :ports      ports
                                    :portdecls  portdecls
                                    :netdecls   (append-without-guard nacc netdecls)
                                    :vardecls   vardecls
                                    :regdecls   regdecls
                                    :eventdecls eventdecls
                                    :paramdecls paramdecls
                                    :fundecls   nil
                                    :assigns    (append-without-guard aacc assigns)
                                    :modinsts   modinsts
                                    :gateinsts  gateinsts
                                    :alwayses   alwayses
                                    :initials   initials
                                    :warnings   warnings))

         ;; That should be it, but as a final sanity check, I'll just check to make
         ;; sure that the function really has become function-free.
         (allexprs (vl-module-allexprs-exec x-prime nil))
         ((when (vl-exprlist-has-funcalls allexprs))
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "In module ~m0, there are still function calls after ~
                         successfully expanding functions?  Found calls to ~
                         ~&1."
                   :args (list x.name (mergesort (vl-exprlist-funnames allexprs)))
                   :fn 'vl-module-expand-functions
                   :fatalp t)))
            (change-vl-module x-prime :warnings (cons w warnings)))))

      x-prime))

  (local (in-theory (enable vl-module-expand-functions)))

  (defthm vl-module-p-of-vl-module-expand-functions
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-expand-functions x))))

  (defthm vl-module->name-of-vl-module-expand-functions
    (equal (vl-module->name (vl-module-expand-functions x))
           (vl-module->name x))))



(defprojection vl-modulelist-expand-functions (x)
  (vl-module-expand-functions x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (expand-functions))

(defthm vl-modulelist->names-of-vl-modulelist-expand-functions
  (equal (vl-modulelist->names (vl-modulelist-expand-functions x))
         (vl-modulelist->names x))
  :hints(("Goal" :induct (len x))))

