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
(include-book "always/stmtrewrite") ;; bozo
(include-book "../mlib/reorder")
(include-book "../mlib/range-tools")
(include-book "../mlib/subst")
(include-book "../mlib/allexprs")
(include-book "../mlib/namefactory")
;; (include-book "centaur/depgraph/toposort" :dir :system)
(include-book "../mlib/find")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))

(local (in-theory (disable (tau-system))))

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
shouldn't be possible, but our @(see vl-vardecl-p) representation does not
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
starting with assignments to variables that have been declared within the
function (if any), and ending with an assignment to the function's name (in all
cases).  We do not allow any branching, looping, timing, case statements,
etc.</p>

<p>This restriction is overly severe and parts of it may eventually be lifted.
At present we at least do some basic rewriting of the statement, which allows
us to flatten sub-blocks.  In the long run, we may eventually want to try to
support at least some if-then-else statements, case statements, etc.</p>

<p>Finally, we require that <b>every variable declared in the function is
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

(local (xdoc::set-default-parents expand-functions))

(define vl-remove-fake-function-vardecls ((x vl-vardecllist-p))
  :returns (new-x vl-vardecllist-p)
  (b* (((when (atom x))
        nil)
       (x1 (vl-vardecl-fix (car x)))
       ((when (assoc-equal "VL_HIDDEN_DECL_FOR_TASKPORT" (vl-vardecl->atts x1)))
        (vl-remove-fake-function-vardecls (cdr x))))
    (cons x1 (vl-remove-fake-function-vardecls (cdr x)))))



; -----------------------------------------------------------------------------
;
;                        Dependency-Order Sorting
;
; -----------------------------------------------------------------------------

;; (define vl-function-dep-graph
;;   :parents (vl-depsort-functions)
;;   :short "Build a dependency graph for function definitions."
;;   ((x vl-fundecllist-p))
;;   :returns (alist "Alist associating function names (strings) to the the lists
;;                    of all functions that are called in their bodies (string
;;                    lists, perhaps with duplicates).  Suitable for sorting with
;;                    @(see depgraph::toposort)."
;;                   (equal (alist-keys alist)
;;                          (vl-fundecllist->names x)))
;;   :long "<p>If we run into a recursive function, the dep graph will have a
;;          self-dependency.</p>"
;;   (b* (((when (atom x))
;;         nil)
;;        (fun1  (car x))
;;        (name1 (vl-fundecl->name fun1))
;;        (deps1 (vl-exprlist-funnames (vl-fundecl-allexprs fun1))))
;;     (hons-acons name1 deps1
;;                 (vl-function-dep-graph (cdr x)))))

;; (define vl-depsort-functions
;;   :short "Rearrange function declarations so that they are in dependency order,
;; if possible."
;;   ((x        vl-fundecllist-p)
;;    (warnings vl-warninglist-p))
;;   :returns
;;   (mv (successp)
;;       (warnings vl-warninglist-p)
;;       (sorted-x vl-fundecllist-p))

;;   :long "<p>Since functions can call one another and can be listed in any
;; order, it is useful to be able to put them into a dependency order; we take
;; advantage of this when we flatten their templates, see @(see
;; vl-flatten-funtemplates).</p>

;; <p>We will fail if there are any circular function dependencies or recursive
;; functions; in this case @('successp') is nil and a fatal warning will be
;; added.</p>"
;;   (b* ((x     (vl-fundecllist-fix x))
;;        (graph (vl-function-dep-graph x))

;;        ;; Quick sanity check for unique function names
;;        (dupes (duplicated-members (alist-keys graph)))
;;        ((when dupes)
;;         (fast-alist-free graph)
;;         (mv nil
;;             (fatal :type :vl-bad-functions
;;                    :msg "Multiple function declarations for ~&0."
;;                    :args (list dupes))
;;             x))

;;        ;; Try to topologically sort the dependency graph; if this fails then
;;        ;; order is just the names of the functions that are in a loop.
;;        ((mv successp order) (depgraph::toposort graph))
;;        (- (fast-alist-free graph))
;;        ((unless successp)
;;         (mv nil
;;             (fatal :type :vl-function-loop
;;                    :msg "Functions have circular dependencies: ~&0."
;;                    :args (list order))
;;             x))

;;        ;; We successfully put the function names into dependency order, so
;;        ;; just rearrange the functions into this dependency order.
;;        (sorted-x (vl-reorder-fundecls order x)))
;;     (mv t (ok) sorted-x))

;;   :prepwork
;;   ((local (defthm crock
;;             (implies (and (string-listp y)
;;                           (subsetp-equal x y)
;;                           (true-listp x))
;;                      (string-listp x))))

;;    (local (defthm crock2
;;             (implies (string-listp (alist-keys graph))
;;                      (string-listp (mv-nth 1 (depgraph::toposort graph)))))))

;;   ///
;;   (defthm vl-depsort-functions-under-set-equiv
;;     ;; This shows that no functions are added/lost as a result of depsorting.
;;     (set-equiv (mv-nth 2 (vl-depsort-functions x warnings))
;;                (vl-fundecllist-fix x))
;;     :hints(("Goal" :in-theory (enable set-equiv)))))



; -----------------------------------------------------------------------------
;
;                      Handling Function Parameters
;
; -----------------------------------------------------------------------------


;; (define vl-check-fun-params-no-overlap
;;   :parents (vl-fundecl-expand-params)
;;   :short "Ensure that a function's parameters do not shadow other things in the
;; module."
;;   ((x        vl-paramdecllist-p "Parameter declarations for the function.")
;;    (scope    vl-scope-p         "Scope in which the function occurs.")
;;    (warnings vl-warninglist-p   "Ordinary @(see warnings) accumulator.")
;;    (function vl-fundecl-p       "Context for error messages."))
;;   :returns
;;   (mv (ok booleanp :rule-classes :type-prescription)
;;       (warnings vl-warninglist-p))
;;   :long "<p>We don't allow parameters to shadow other things in the module
;; since that seems weird and has various corner cases with respect to
;; declarations being defined before use, e.g., see @(see
;; vl-check-fun-parameters-deforder).</p>

;; <p>We don't expect many parameters in a function, so we use slow moditem
;; lookups here, figuring that it'll be cheaper than building a @(see
;; vl-make-moditem-alist).</p>"

;;   (b* (((when (atom x))
;;         (mv t (ok)))
;;        (name1 (vl-paramdecl->name (car x)))
;;        ((mv & item1) (vl-scope-find-item-fast name1 scope))
;;        ((unless item1)
;;         (vl-check-fun-params-no-overlap (cdr x) scope warnings function)))
;;     (mv nil
;;         (fatal :type :vl-bad-function-parameter
;;                :msg "In ~a0, parameter ~s1 has the same name as ~a2; we don't ~
;;                      allow function parameters to shadow other module items ~
;;                      because it seems underspecified by the Verilog-2005 ~
;;                      standard and generally somewhat error-prone."
;;                :args (list function name1 item1)))))

(define vl-fun-paramdecllist-types-okp
  :parents (vl-fundecl-expand-params)
  :short "Check that the parameters in a function are sufficiently simple to
handle."
  ((x        vl-paramdecllist-p)
   (warnings vl-warninglist-p)
   (function vl-fundecl-p))
  :returns (mv (okp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p))
  :long "<p>We make sure that all of the parameters in the function are plain
parameters with no ranges or weird types.  This restriction might not be
necessary, but we are not sure whether other kinds of parameters would require
some special handling.</p>"

  (b* (((when (atom x))
        (mv t (ok)))

       ((vl-paramdecl x1) (car x))

       ;; BOZO historically we prohibited any kind of type stuff on parameters
       ;; within a function.  It seems safe to continue to reject that for now.
       ;; Some day we will probably want to revisit this.  Some questions to
       ;; investigate:
       ;;
       ;;   - Is it still the case, in SystemVerilog, that function parameters
       ;;     can't be instantiated in function calls?
       ;;
       ;;   - Does our handling of parameters (turning them into substitutions)
       ;;     make any sense at all with respect to types?  Perhaps we should
       ;;     instead be creating assignments to some appropriate type.
       ((unless (and (eq (vl-paramtype-kind x1.type) :vl-implicitvalueparam)
                     (not (vl-implicitvalueparam->sign x1.type))
                     (not (vl-implicitvalueparam->range x1.type))))
        (mv nil (fatal :type :vl-bad-function-paramdecl
                       :msg "In ~a0, parameter ~s1 has unsupported type ~x2."
                       :args (list function x1.name x1.type))))

       ((unless (vl-implicitvalueparam->default x1.type))
        (mv nil (fatal :type :vl-bad-function-paramdecl
                       :msg "In ~a0, parameter ~s1 has no value, which is not supported."
                       :args (list function x1.name)))))

    (vl-fun-paramdecllist-types-okp (cdr x) warnings function)))

(define vl-fundecl-param-sigma
  :parents (vl-fundecl-expand-params)
  :short "Bind a function's parameter names to their values."
  ((x vl-paramdecllist-p))
  :returns (sigma vl-sigma-p)
  (b* (((when (atom x))
        nil)
       ((vl-paramdecl x1) (vl-paramdecl-fix (car x)))
       ((unless (and (eq (vl-paramtype-kind x1.type) :vl-implicitvalueparam)
                     (vl-implicitvalueparam->default x1.type)))
        ;; Checking paramdecllist-types-okp should prevent this
        (raise "Bad parameter for param-sigma: ~x0." x1)))
    (cons (cons x1.name (vl-implicitvalueparam->default x1.type))
          (vl-fundecl-param-sigma (cdr x)))))

(define vl-fundecl-expand-params
  :short "Eliminate parameters from a function."
  ((x        vl-fundecl-p     "A function that may have parameters.")
   (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator.")
   ;; (scope    vl-scope-p       "Scope where @('x') resides.")
   )
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x vl-fundecl-p))

  :long "<p>We try to rewrite @('x') to eliminate any parameters.  There
doesn't seem to be any way to actually provide values for the parameters of a
function, so function parameters seem to just be a way to use named constants
within a function.</p>

<p>The basic idea is to just construct a substitution list from the parameters
and apply it throughout the function.  But we do a lot of sanity checking to
make sure that the parameters are very simple, aren't shadowing other things,
and are defined before they are used (as some Verilog tools require).  While
we're at it, we also check the function's local namespace to make sure it is
okay (since eliminating parameters changes the function's namespace).</p>"

  (b* ((x (vl-fundecl-fix x))
       ((vl-fundecl x) x)
       (real-vardecls (vl-remove-fake-function-vardecls x.vardecls))

       ((unless x.paramdecls)
        ;; Common case of no parameters -- no need to check or change anything.
        (mv t (ok) x))

       (param-names (vl-paramdecllist->names x.paramdecls))
       (local-namespace
        (append (list x.name) ;; functions' name needs to be included since it gets assigned to at the end
                (vl-vardecllist->names real-vardecls)
                param-names))

       ;; Make sure there are no name clashes, for good measure.
       (dupes (duplicated-members local-namespace))
       ((when dupes)
        (mv nil
            (fatal :type :vl-bad-function-namespace
                   :msg "In ~a0, there are multiple declarations for ~&1."
                   :args (list x dupes))
            x))


       ;; Make sure the parameters are simple enough for us to handle.
       ((mv okp warnings)
        (vl-fun-paramdecllist-types-okp x.paramdecls warnings x))
       ((unless okp) (mv nil warnings x))

       ;; Okay, everything looks good.  We want to now just expand the parameters
       ;; away by rewriting them with their values.
       (sigma (vl-fundecl-param-sigma x.paramdecls))
       ((with-fast sigma))

       (vardecls   (vl-vardecllist-subst x.vardecls sigma))
       (body       (vl-stmt-subst x.body sigma))
       (new-x      (change-vl-fundecl x
                                      :vardecls vardecls
                                      :body body)))

    (mv t warnings new-x)))

(define vl-fundecllist-expand-params
  :short "Eliminate parameters from a list of functions."
  ((x        vl-fundecllist-p)
   (warnings vl-warninglist-p)
   ;; (scope    vl-scope-p)
   )
  :returns (mv (okp      booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-fundecllist-p))
  :long "<p>See @(see vl-fundecl-expand-params).</p>"
  (b* (((when (atom x))
        (mv t (ok) nil))
       ((mv car-successp warnings car-prime)
        (vl-fundecl-expand-params (car x) warnings))
       ((mv cdr-successp warnings cdr-prime)
        (vl-fundecllist-expand-params (cdr x) warnings)))
    (mv (and car-successp cdr-successp)
        warnings
        (cons car-prime cdr-prime))))


; -----------------------------------------------------------------------------
;
;                          Function Body Rules
;
; -----------------------------------------------------------------------------

(defines vl-fun-stmt-okp
  :short "Ensure that a function's statement conforms to the Function Rules in
10.4.4."

  :long "<p>We check to see if the statement conforms to the Function Rules in
10.4.4.  In particular, we want to ensure that the function's body:</p>

<ul>
<li>has no time-controlled statements (#, @, wait),</li>
<li>does not enable tasks</li>
<li>has no nonblocking assignments or procedural continuous assignments</li>
<li>has no event triggers</li>
</ul>

<p>Practically speaking there are a lot of other things that our function
expansion code doesn't support (complex case statements, loops, functions that
don't write to variables before reading them, etc.) but that the Verilog-2005
standard doesn't prohibit, so this is not a very complete check as far as VL is
concerned.  But, I think it's nice to at least explicitly check for the
\"officially forbidden\" stuff first.</p>"

  (define vl-fun-stmt-okp
    ((x        vl-stmt-p        "Statement found within a function's body.")
     (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator.")
     (function vl-fundecl-p     "Context for error messages."))
    :returns (mv (okp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p))
    :verify-guards nil
    :measure (vl-stmt-count x)
    :flag :stmt
    (b* ((x        (vl-stmt-fix x))
         (warnings (vl-warninglist-fix warnings))

         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)

            (:vl-nullstmt
             ;; We allow null statements because they seem harmless.
             (mv t (ok)))

            (:vl-assignstmt
             ;; We allow assignment statements as long as they are blocking
             ;; assignments with no timing controls.
             (b* (((vl-assignstmt x) x)
                  ((unless (eq x.type :vl-blocking))
                   ;; Per Section 10.4.4 this is illegal
                   (mv nil (fatal :type :vl-bad-function-stmt
                                  :msg "In ~a0, the assignment ~a1 is not ~
                                        allowed because all assignments in a ~
                                        function's body must be blocking ~
                                        assignments, i.e., a = b.  Other ~
                                        kinds of assignments like a <= b, ~
                                        assign a = b, and force a = b are not ~
                                        permitted."
                                  :args (list function x))))
                  ((when x.ctrl)
                   ;; Per Section 10.4.4 this is illegal
                   (mv nil (fatal :type :vl-bad-function-stmt
                                  :msg "In ~a0, the assignment ~a1 is not ~
                                        allowed because statements in a ~
                                        function's body may not have timing ~
                                        statements (i.e., #, @)."
                                  :args (list function x)))))
               (mv t (ok))))

            (otherwise
             ;; Otherwise it's a deassign, enable, disable, or event trigger,
             ;; and we do not allow it.
             ;;
             ;; - I think deassigns are considered as procedural assignments,
             ;; and if that is true then they are forbidden by 10.4.4, so we
             ;; don't allow them.
             ;;
             ;; - Enables are explicitly forbidden by 10.4.4.
             ;;
             ;; - Disables are not explicitly mentioned, but it seems like if
             ;; enables are forbidden then disables should also be forbidden,
             ;; so I'm not going to allow them.
             ;;
             ;; - Event triggers are explicitly forbidden by 10.4.4.
             (mv nil (fatal :type :vl-bad-function-stmt
                            :msg "In ~a0, the statement ~a1 is not allowed ~
                                  because a function's body cannot include ~
                                  any ~s2."
                            :args (list function x
                                        (case (vl-stmt-kind x)
                                          (:vl-deassignstmt
                                           "procedural assignments")
                                          ((:vl-enablestmt :vl-disablestmt)
                                           "task enables")
                                          (:vl-eventtriggerstmt
                                           "event triggers"))))))))

         (kind (vl-stmt-kind x))
         ((when (or (eq kind :vl-timingstmt)
                    (eq kind :vl-waitstmt)))
          ;; Per 10.4.4 this is illegal
          (mv nil (fatal :type :vl-bad-function-stmt
                         :msg "In ~a0, the statement ~a1 is not allowed ~
                               because statements in a function's body may ~
                               not have timing statements (i.e., #, @, wait)."
                         :args (list function x)))))
      (vl-fun-stmtlist-okp (vl-compoundstmt->stmts x) warnings function)))

  (define vl-fun-stmtlist-okp
    ((x        vl-stmtlist-p "Statements found within a function's body")
     (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator.")
     (function vl-fundecl-p     "Context for error messages."))
    :returns (mv (okp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p))
    :measure (vl-stmtlist-count x)
    :flag :list
    (b* (((when (atom x))
          (mv t (ok)))
         ((mv successp1 warnings) (vl-fun-stmt-okp (car x) warnings function))
         ((mv successp2 warnings) (vl-fun-stmtlist-okp (cdr x) warnings function)))
      (mv (and successp1 successp2)
          warnings)))
  ///
  (verify-guards vl-fun-stmt-okp))



; -----------------------------------------------------------------------------
;
;                    Function Body --> Assignment List
;
; -----------------------------------------------------------------------------

(define vl-fun-assignorder-okp-aux
  :parents (vl-fun-assignorder-okp)
  :short "Main checking for @(see vl-fun-assignorder-okp)."

  ((x            vl-assignlist-p  "Assignments derived from a function's body.")
   (innames      string-listp     "Names of all inputs to the functions.")
   (varnames     string-listp     "Names of all variables declared in the function.")
   (written-vars string-listp     "Accumulator.  Names of all variables written
                                   to so far.  This lets us check that all variables
                                   are written before they are read, and that no
                                   variable is written to more than once.")
   (read-vars    string-listp     "Accumulator.  Names of all variables we've read
                                   from so far.  This is useful for reporting
                                   unused variables.")
   (read-inputs  string-listp     "Accumulator.  Names all the inputs we've read
                                   from so far.  This is useful for reporting
                                   unused inputs.")
   (warnings     vl-warninglist-p "Ordinary @(see warnings) accumulator.")
   (function     vl-fundecl-p     "The function itself, mostly useful as a context
                                   for error messages, but also gives us the function's
                                   name so we can check that the function's name
                                   is the last thing written to and isn't written
                                   to until the end."))
  :returns
  (mv (okp           booleanp :rule-classes :type-prescription)
      (warnings      vl-warninglist-p)
      (written-vars  string-listp :hyp :fguard)
      (read-vars     string-listp :hyp :fguard)
      (read-inputs   string-listp :hyp :fguard))

  (b* ((funname (vl-fundecl->name function))

       ((when (atom x))
        ;; We sort of shouldn't ever get here unless the list of assignments
        ;; that was produced by VL-FUNBODY-TO-ASSIGNMENTS was empty.
        (mv nil
            (fatal :type :vl-bad-function-stmt
                   :msg "In ~a0, there are no assignments.  There needs to at ~
                         least be an assignment to ~s1 to give it a return ~
                         value."
                 :args (list function funname))
            written-vars read-vars read-inputs))

       ((vl-assign x1) (car x))
       ((unless (vl-idexpr-p x1.lvalue))
        ;; This is overly restrictive, but should be good enough for now.
        (mv nil
            (fatal :type :vl-bad-function-stmt
                   :msg "In ~a0, the assignment to ~a1 is too complex; we ~
                         only support assigning to a function's variables and ~
                         to its name directly; e.g., you cannot even write ~
                         things like foo[3:0] = 1.  This is overly ~
                         restrictive, and we can work on improving it if ~
                         necessary."
                 :args (list function x1.lvalue))
            written-vars read-vars read-inputs))

       (lhs-name           (vl-idexpr->name x1.lvalue))
       (rhs-names          (vl-expr-names x1.expr))
       (rhs-var-names      (intersection-equal rhs-names varnames))
       (rhs-unwritten-vars (set-difference-equal rhs-var-names written-vars))
       ((when rhs-unwritten-vars)
        (mv nil
            (fatal :type :vl-bad-function-stmt
                   :msg "In ~a0, assignment to ~a1 involves the variable~s2 ~
                         ~&3, which ~s4 not yet been assigned at this point ~
                         in the function.  We do not allow this because it ~
                         can lead to very odd behavior when there are ~
                         multiple calls of the function."
                   :args (list function
                               x1.lvalue
                               (if (vl-plural-p rhs-unwritten-vars) "s" "")
                               rhs-unwritten-vars
                               (if (vl-plural-p rhs-unwritten-vars) "have" "has")))
            written-vars read-vars read-inputs))

       (read-vars   (append rhs-var-names read-vars))
       (read-inputs (append (intersection-equal innames rhs-names) read-inputs))

       ((when (atom (cdr x)))
        ;; Last assignment.  This one needs to be to the function's name.
        (if (equal lhs-name funname)
            (mv t (ok) written-vars read-vars read-inputs)
          (mv nil
              (fatal :type :vl-bad-function-stmt
                     :msg "In ~a0, the final assignment in ~s1 must be to ~
                           ~s1, but instead it is to ~a2."
                     :args (list function funname x1.lvalue))
              written-vars read-vars read-inputs)))

       ;; Not the last assignment, so this one needs to be to a variable
       ;; that we haven't written to yet.
       ((when (equal lhs-name funname))
        (mv nil
            (fatal :type :vl-bad-function-stmt
                   :msg "In ~a0, assigning to ~a1 is not permitted except as ~
                         the very last statement in the function."
                   :args (list function x1.lvalue))
            written-vars read-vars read-inputs))

       ((unless (member-equal lhs-name varnames))
        (mv nil
            (fatal :type :vl-bad-function-stmt
                   :msg "In ~a0, the assignment to ~a1 is not permitted; we ~
                         only allow assignments to the function's variables ~
                         and its name."
                   :args (list function x1.lvalue))
            written-vars read-vars read-inputs))

       ((when (member-equal lhs-name written-vars))
        ;; We could relax this restriction by doing some kind of renaming for
        ;; multiply written variables.
        (mv nil
            (fatal :type :vl-bad-function-stmt
                   :msg "In ~a0, we only allow a single assignment to each of ~
                         the function's variables, but ~a1 is written to more ~
                         than once."
                   :args (list function x1.lvalue))
            written-vars read-vars read-inputs))

       ;; Else, looking good so far -- record the variable as written and let's
       ;; go on to the rest of the assignments.
       (written-vars (cons lhs-name written-vars)))

    (vl-fun-assignorder-okp-aux (cdr x) innames varnames
                                written-vars read-vars read-inputs
                                warnings function)))

(define vl-fun-assignorder-okp
  :parents (vl-funbody-to-assignments)
  :short "Ensure that the assignments from a function's body always write to
variables before they read from them, never write to a variable twice, and end
with a write to the function's name."

  ((x        vl-assignlist-p  "Assignments derived from a function's body.")
   (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator.")
   (function vl-fundecl-p     "The function itself: used as a context for error
                               messages, and also to determine the function's name
                               to check the final assignment."))
  :returns (mv (okp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p))

  :long "<p>The checks we perform are intended to ensure that it is legitimate
to convert this series of blocking assignments into wiring:</p>

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
variables and inputs.</p>"

  :prepwork ((local (in-theory (disable not
                                        union
                                        subset
                                        difference
                                        mergesort
                                        intersect
                                        subsetp-equal-when-first-two-same-yada-yada
                                        set::subset-difference))))

  (b* ((vardecls (vl-remove-fake-function-vardecls (vl-fundecl->vardecls function)))
       (varnames (vl-vardecllist->names vardecls))
       (innames  (vl-portdecllist->names (vl-fundecl->portdecls function)))
       ((mv okp warnings written-vars read-vars read-inputs)
        (vl-fun-assignorder-okp-aux x innames varnames nil nil nil warnings function))
       ((unless okp)
        (mv nil warnings))

       ;; Check for any unread/unwritten variables, and any unread inputs,
       ;; and add non-fatal warnings if there are any.
       ;;
       ;; There shouldn't be any read-but-never-written vars, but we'll write
       ;; this code as if there might be.

       (innames        (mergesort innames)) ;; Sort things just so the names are in order
       (varnames       (mergesort varnames)) ;; in the warning message.
       (read-inputs    (mergesort read-inputs))
       (read-vars      (mergesort read-vars))
       (written-vars   (mergesort written-vars))

       (unread-inputs  (difference innames read-inputs))
       (unread-vars    (difference varnames read-vars))
       (unwritten-vars (difference varnames written-vars))

       (spurious-vars  (intersect unread-vars unwritten-vars)) ;; unread and unwritten
       (unread-vars    (difference unread-vars spurious-vars)) ;; unread but written
       (unwritten-vars (difference unwritten-vars spurious-vars)) ;; read but unwritten
       (unread-all     (union unread-vars unread-inputs))

       ;; Wow, this is an ugly ball of mud.

       (spurious-sep   (if (or unread-all unwritten-vars) "; " ""))
       (spurious-msg   (cond ((not spurious-vars)
                              "")
                             ((vl-plural-p spurious-vars)
                              (cat "~&1 are never mentioned" spurious-sep))
                             (t
                              (cat "~&1 is never mentioned" spurious-sep))))

       (unread-sep     (if unwritten-vars "; " ""))
       (unread-msg     (cond ((not unread-all)
                              "")
                             ((vl-plural-p unread-all)
                              (cat "~&2 are never read" unread-sep))
                             (t
                              (cat "~&2 is never read" unread-sep))))

       (unwritten-msg  (cond ((not unwritten-vars)
                              "")
                             ((vl-plural-p unwritten-vars)
                              "~&3 are never written")
                             (t
                              "~&3 is never written")))

       (warnings
        (if (or spurious-vars unread-all unwritten-vars)
            (warn :type :vl-warn-function-vars
                  :msg (cat "In ~a0, " spurious-msg unread-msg unwritten-msg ".")
                  :args (list function spurious-vars unread-all unwritten-vars))
          (ok))))

    (mv t warnings)))

(define vl-funbody-to-assignments-aux
  :parents (vl-funbody-to-assignments)
  :short "Try to convert a list of statements that make up a function's body
into a @(see vl-assignlist-p)."

  ((x        vl-stmtlist-p    "A flattened list of statements that come from
                               the function's body.")
   (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator.")
   (function vl-fundecl-p     "The function itself."))

  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (assigns  vl-assignlist-p))

  :long "<p>If this function is reasonable and in our supported subset, then
@('x') should just be a list of blocking assignment statements.  We convert
each statement into a @(see vl-assign-p) with the same left-hand side and
right-hand-side.  The superior function, @(see vl-funbody-to-assignments), will
then check that this conversion is reasonable.</p>

<p>If @('x') contains anything other than supported, blocking assignment
statements (well, and null statements), we'll just fail because this isn't a
supported function.</p>"

  (b* (((when (atom x))
        (mv t (ok) nil))

       ((when (vl-nullstmt-p (car x)))
        ;; Fine, skip it.
        (vl-funbody-to-assignments-aux (cdr x) warnings function))

       ((unless (vl-assignstmt-p (car x)))
        (mv nil
            (fatal :type :vl-bad-function-stmt
                   :msg "In ~a0, after rewriting, the function's body ~
                         includes ~a1, but only simple assignment statements ~
                         are permitted."
                   :args (list function (car x)))
            nil))

       ;; Make sure that X has no delays and is a blocking assignment.  We
       ;; should have already checked this, but we'll check it again just in
       ;; case.
       ((mv okp warnings) (vl-fun-stmt-okp (car x) warnings function))
       ((unless okp) (mv nil warnings nil))

       ;; Otherwise, X seems okay, so make an assignment from it.
       ((vl-assignstmt x1) (car x))
       (assign1 (make-vl-assign
                 :lvalue x1.lvalue
                 :expr   x1.expr
                 :atts   (acons "VL_FUN_ASSIGN"
                                (make-vl-atom
                                 :guts (make-vl-string
                                        :value (vl-fundecl->name function)))
                                x1.atts)
                 :loc    x1.loc))
       ((mv okp warnings cdr-assigns)
        (vl-funbody-to-assignments-aux (cdr x) warnings function)))
    (mv okp warnings (cons assign1 cdr-assigns))))

(define vl-funbody-to-assignments
  :short "Transform a function's body into a list of assignment statements if
it is safe to do so."

  ((x        vl-fundecl-p     "Function to convert.")
   (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (assigns  vl-assignlist-p))

  :long "<p>This is the top-level function for converting function bodies into
assignments.</p>

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
       ;; to the rules of the Verilog-2005 standard, so if we're here then we
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
       ;; For single-assignment functions, the rewriter will have produced a
       ;; single assignment statement; for multi-assignment functions we'll
       ;; have a block.  So, basically if we have a block we're just going to
       ;; grab its statements (and assume everything's been already flattened
       ;; so it's a single block), but otherwise we'll make a singleton list
       ;; with the rewritten body.
       (body-as-stmt-list
        (if (and (not (vl-atomicstmt-p body))
                 (vl-blockstmt-p body)
                 (vl-blockstmt->sequentialp body)
                 (not (vl-blockstmt->name body))
                 (not (vl-blockstmt->vardecls body))
                 (not (vl-blockstmt->paramdecls body))
                 (not (vl-blockstmt->imports body)))
            (vl-blockstmt->stmts body)
          (list body)))

       ((mv okp warnings assigns)
        (vl-funbody-to-assignments-aux body-as-stmt-list warnings x))
       ((unless okp) (mv nil warnings nil))

       ;; Now check that the assigns have good order, add warnings about
       ;; unused vars, etc.
       ((mv okp warnings)
        (vl-fun-assignorder-okp assigns warnings x))
       ((unless okp) (mv nil warnings nil)))

    (mv t warnings assigns)))


; -----------------------------------------------------------------------------
;
;                     Function Expansion Templates
;
; -----------------------------------------------------------------------------

(defprod vl-funtemplate
  :short "Function expansion templates, the intermediate representation of
functions we use while inlining function calls."
  :tag :vl-funtemplate
  :layout :tree
  ((name    stringp :rule-classes :type-prescription)
   (inputs  vl-vardecllist-p)
   (locals  vl-vardecllist-p)
   (out     vl-vardecl-p)
   (assigns vl-assignlist-p))

  :long "<p>For each of the module's functions, we generate a template that
will allow us to expand calls of the function.  Each template has the same
@('name') as the function, but all of its inputs and var declarations have been
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
call other functions in a straightforward way.  BOZO: previously we claimed
that ``in @('vl-flatten-funtemplates') we use our ordinary function-expansion
code to expand any function calls within function templates, so that when we
expand functions throughout the rest of the module we only need one pass.'' but
that function no longer exists and Jared does not remember whether we changed
how this worked.</p>")

(fty::deflist vl-funtemplatelist :elt-type vl-funtemplate-p
  :elementp-of-nil nil
  :parents (vl-funtemplate-p))

(define vl-find-funtemplate
  :parents (vl-funtemplate-p)
  :short "Find a function template by name."
  ((name      stringp)
   (templates vl-funtemplatelist-p))
  :returns (template? (equal (vl-funtemplate-p template?)
                             (if template? t nil))
                      :hyp :fguard)
  (cond ((atom templates)
         nil)
        ((equal name (vl-funtemplate->name (car templates)))
         (car templates))
        (t
         (vl-find-funtemplate name (cdr templates)))))

(define vl-portdecllist-types-okp
  :parents (vl-funtemplate-p)
  :short "Ensure that a function's inputs are simple enough to convert into nets."
  ((x        vl-portdecllist-p)
   (warnings vl-warninglist-p)
   (function vl-fundecl-p))
  :returns
  (mv (okp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv t (ok)))
       ((vl-portdecl x1) (car x))
       ((unless (and (eq (vl-datatype-kind x1.type) :vl-coretype)
                     (member (vl-coretype->name x1.type) '(:vl-logic :vl-reg))))
        (mv nil (fatal :type :vl-bad-function-input
                       :msg "In ~a0, input ~s1 has unsupported type ~s2."
                       :args (list function x1.name x1.type)))))
    (vl-portdecllist-types-okp (cdr x) warnings function)))

(define vl-funinput-to-vardecl
  :parents (vl-funtemplate-p)
  :short "Convert a function's input declaration into a net declaration for its
funtemplate."
  ((x vl-portdecl-p))
  :returns (vardecl vl-vardecl-p)
  :long "<p>We assume the input is okay in the sense of @(see
vl-portdecllist-types-okp).</p>

<p>We implement a special hack for Verilog-2005 compatibility.  In particular,
consider a basic function such as:</p>

@({
     function [3:0] AndFn(input [3:0] a, input [3:0] b);
       AndFn = a & b;
     endfunction
})

<p>Our internal representation of function inputs now uses @('logic') types for
@('a') and @('b'), which is perfectly fine and sensible.  But, when we are
trying to cosimulate our simplified modules against the original modules, e.g.,
in the VL <i>systest</i> directory, then this can cause problems because plain
Verilog-2005 simulators don't know about @('logic') types.</p>

<p>To avoid this, when we convert function inputs into wires, we'll just go
ahead and ensure the net type is :vl-wire.</p>"

  (b* (((vl-portdecl x) x)
       (name-atom (make-vl-atom :guts (make-vl-string :value x.name))))
    (make-vl-vardecl :name    x.name
                     :type    x.type
                     :nettype :vl-wire
                     :atts    (acons "VL_FUNCTION_INPUT" name-atom x.atts)
                     :loc     x.loc)))

(defprojection vl-funinputlist-to-vardecls ((x vl-portdecllist-p))
  :parents (vl-funtemplate-p)
  :returns (nets vl-vardecllist-p)
  (vl-funinput-to-vardecl x))

(define vl-fun-vardecllist-types-okp
  :parents (vl-funtemplate-p)
  :short "Ensure that a function's variables are simple enough to convert into nets."
  ((x        vl-vardecllist-p)
   (warnings vl-warninglist-p)
   (function vl-fundecl-p))
  :returns
  (mv (okp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p))
  (b* (((when (atom x))
        (mv t (ok)))
       (x1 (vl-vardecl-fix (car x)))
       ((vl-vardecl x1) x1)
       ((unless (vl-simplereg-p x1))
        (mv nil (fatal :type :vl-bad-function-vardecl
                       :msg "In ~a0, variable ~s1 is not a simple register.  ~
                             Other types of variables are not yet supported."
                       :args (list function x1.name))))
       ;; ruled out by simplereg-p
       ;; ((when x1.arrdims)
       ;;  (mv nil (fatal :type :vl-bad-function-vardecl
       ;;                 :msg "In ~a0, ~s1 has array dimensions, which are ~
       ;;                       not supported."
       ;;                 :args (list function x1.name))))
       ((when x1.initval)
        ;; I don't think this is even allowed by the grammar.
        (mv nil (fatal :type :vl-bad-function-vardecl
                       :msg "In ~a0, ~s1 has an initial value, which is ~
                             not supported."
                       :args (list function x1.name)))))
    (vl-fun-vardecllist-types-okp (cdr x) warnings function))
  ///
  (defthm vl-simplereglist-p-when-vl-fun-vardecllist-types-okp
    (b* (((mv okp ?warnings) (vl-fun-vardecllist-types-okp x warnings function)))
      (implies okp
               (vl-simplereglist-p x)))))

(define vl-fun-vardecl-to-vardecl
  :parents (vl-funtemplate-p)
  :short "Convert a function's var declaration into a net declaration for its
funtemplate."
  ((x vl-vardecl-p))
  :guard (vl-simplereg-p x)
  :returns (vardecl vl-vardecl-p)
  :long "<p>We assume the input is okay in the sense of @(see
vl-fun-vardecllist-types-okp).</p>"
  (b* (((vl-vardecl x) x)
       (name-atom (make-vl-atom :guts (make-vl-string :value x.name)))
       (range     (vl-simplereg->range x))
       (type      (make-vl-coretype :name :vl-logic
                                    :pdims (and range (list range))
                                    :signedp (vl-simplereg->signedp x))))
    (make-vl-vardecl :name  x.name
                     :type  type
                     :nettype :vl-wire
                     :atts  (acons "VL_FUNCTION_VAR" name-atom x.atts)
                     :loc   x.loc)))

(defprojection vl-fun-vardecllist-to-vardecls ((x vl-vardecllist-p))
  :parents (vl-funtemplate-p)
  :returns (nets vl-vardecllist-p)
  :guard (vl-simplereglist-p x)
  (vl-fun-vardecl-to-vardecl x))


(define vl-fundecl-expansion-template
  :parents (vl-funtemplate-p)
  :short "Generate the initial template for expanding a function."
  ((x        vl-fundecl-p)
   (warnings vl-warninglist-p))
  :returns (mv (template? (equal (vl-funtemplate-p template?)
                                 (if template? t nil)))
               (warnings vl-warninglist-p))
  :long "<p>We try to generate a @(see vl-funtemplate-p) corresponding to
@('x').  On success, the template we generate is only an <b>initial</b>
template; it isn't necessarily \"flat\" and might have function calls within
its assignments.  BOZO we previously claimed: ``We later flatten these initial
templates with @('vl-flatten-funtemplates').'' but that function no longer
exists and Jared doesn't remember whether we changed how it works.</p>

<p>Creating the template for a function is a pretty elaborate process which
involves a lot of sanity checking, and will fail if the function includes
unsupported constructs or doesn't meet our other sanity criteria.</p>"

  (b* (((vl-fundecl x) x)
       (vardecls (vl-remove-fake-function-vardecls x.vardecls))

       ;; ((unless (or (eq x.rtype :vl-unsigned)
       ;;              (eq x.rtype :vl-signed)))
       ;;  (mv nil (fatal :type :vl-bad-function
       ;;                 :msg "In ~a0, we do not support functions with return ~
       ;;                       types other than plain/reg or 'signed', but this ~
       ;;                       function has type ~s1."
       ;;                 :args (list x x.rtype))))

       ((mv okp warnings) (vl-fun-vardecllist-types-okp vardecls warnings x))
       ((unless okp) (mv nil warnings)) ;; already warned

       ((mv okp warnings) (vl-portdecllist-types-okp x.portdecls warnings x))
       ((unless okp) (mv nil warnings)) ;; already warned

       ((mv okp warnings assigns) (vl-funbody-to-assignments x warnings))
       ((unless okp) (mv nil warnings)) ;; already warned

       (funname-atom (make-vl-atom :guts (make-vl-funname :name x.name)))
       (result-var   (make-vl-vardecl :name    x.name
                                      :type    x.rettype
                                      :nettype :vl-wire ;; Special hack for better compatibility with Verilog-2005
                                      :atts    (list (cons "VL_FUNCTION_RETURN" funname-atom))
                                      :loc     x.loc))
       (template     (make-vl-funtemplate
                      :name    x.name
                      :inputs  (vl-funinputlist-to-vardecls x.portdecls)
                      :locals  (vl-fun-vardecllist-to-vardecls vardecls)
                      :out     result-var
                      :assigns assigns)))

    (mv template warnings)))

(define vl-fundecllist-expansion-templates
  :parents (vl-funtemplate-p)
  :short "Generate the initial templates for expanding a list of functions."
  ((x        vl-fundecllist-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (okp booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (templates vl-funtemplatelist-p))
  :long "<p>See @(see vl-fundecl-expansion-template).</p>"
  (b* (((when (atom x))
        (mv t (ok) nil))
       ((mv template1 warnings)
        (vl-fundecl-expansion-template (car x) warnings))
       ((mv cdr-successp warnings cdr-templates)
        (vl-fundecllist-expansion-templates (cdr x) warnings))
       (successp  (and template1 cdr-successp))
       (templates (and successp (cons template1 cdr-templates))))
    (mv successp warnings templates)))


; -----------------------------------------------------------------------------
;
;                 Expanding Function Calls in Expressions
;
; -----------------------------------------------------------------------------

(define vl-fun-make-assignments-to-inputs
  :parents (vl-expand-function-call)
  :short "Generate assignments that supply the inputs to a function call."
  ((netnames string-listp)
   (actuals  vl-exprlist-p)
   (loc      vl-location-p))
  :guard (same-lengthp netnames actuals)
  :returns (assigns vl-assignlist-p)
  (if (atom netnames)
      nil
    (cons (make-vl-assign :lvalue (vl-idexpr (car netnames) nil nil)
                          :expr   (car actuals)
                          :loc    loc)
          (vl-fun-make-assignments-to-inputs (cdr netnames) (cdr actuals) loc))))

(define vl-relocate-assignments
  :parents (vl-expand-function-call)
  :short "Change the location of some assignments."
  ((x   vl-assignlist-p)
   (loc vl-location-p))
  :returns (new-x vl-assignlist-p)
  (if (atom x)
      nil
    (cons (change-vl-assign (car x) :loc loc)
          (vl-relocate-assignments (cdr x) loc))))

(define vl-funexpand-rename-vardecls
  :parents (vl-expand-function-call)
  :short "Generate new names for a list of net declarations and change their
locations; this is used to give new names to the wires in a function call."
  ((x   vl-vardecllist-p "Var declarations from a @(see vl-funtemplate-p).  We
                          use this to try to generate names that correspond to
                          the original names being used in the function.")
   (nf  vl-namefactory-p "Name factory for fresh name generation.")
   (loc vl-location-p    "Location of the function call, so we can generate the
                          new wires near the site of their use."))
  :returns
  (mv (new-x vl-vardecllist-p)
      (nf    vl-namefactory-p))
  (b* (((when (atom x))
        (mv nil (vl-namefactory-fix nf)))
       ((mv new-name nf)
        (vl-namefactory-indexed-name (vl-vardecl->name (car x)) nf))
       (car-renamed (change-vl-vardecl (car x)
                                       :name new-name
                                       :loc loc))
       ((mv cdr-renamed nf)
        (vl-funexpand-rename-vardecls (cdr x) nf loc)))
    (mv (cons car-renamed cdr-renamed) nf))
  ///
  (defthm consp-of-vl-funexpand-rename-vardecls
    (equal (consp (mv-nth 0 (vl-funexpand-rename-vardecls x nf loc)))
           (consp x)))

  (defthm len-of-vl-funexpand-rename-vardecls
    (equal (len (mv-nth 0 (vl-funexpand-rename-vardecls x nf loc)))
           (len x)))

  (defthm true-listp-of-vl-funexpand-rename-vardecls
    (true-listp (mv-nth 0 (vl-funexpand-rename-vardecls x nf loc)))
    :rule-classes :type-prescription))

(define vl-expand-function-call
  :short "Main routine for expanding a single function call."

  ((x        vl-funtemplate-p "Template for the function we want to expand.")
   (actuals  vl-exprlist-p    "Actuals for a particular call of this function.")
   (nf       vl-namefactory-p "For fresh name generation.")
   (vardecls vl-vardecllist-p "Accumulator: wire declarations to add to the module.")
   (assigns  vl-assignlist-p  "Accumulator: assignments to add to the module.")
   (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator.")
   (ctx      vl-context-p     "Where the function call occurs; used as a context
                               for error messages and also to get the location
                               for the new wires/assignments.")
   (loc      vl-location-p    "The location of the element containing the original
                               function call."))

  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (nf       vl-namefactory-p)
      (expr?    (equal (vl-expr-p expr?) successp)
                "A simple identifier atom for the generated return-value wire.
                 The idea is to replace the function-call expression with this
                 @('expr').")
      (vardecls vl-vardecllist-p)
      (assigns  vl-assignlist-p))

  :long "<p>We might fail if there is an arity problem.  But if everything
lines up,</p>

<ul>

<li>We generate fresh wire names that will serve as the inputs, locals, and the
return value wire for this function call; the corresponding declarations are
added to the @('vardecls') accumulator.</li>

<li>We generate new assignments that initialize the generated input wire names
with the actuals; these assignments are added to the @('assigns')
accumulator.</li>

<li>We rewrite the function's assignments so that they use these newly
generated wire names instead of their local names; these assignments are added
to the @('assigns') accumulator.</li>

</ul>"

  (b* ((nf       (vl-namefactory-fix nf))
       (vardecls (vl-vardecllist-fix vardecls))
       (assigns  (vl-assignlist-fix assigns))
       ((vl-funtemplate x) x)

       ((unless (same-lengthp x.inputs actuals))
        ;; Oops, arity error.
        (b* ((funname-atom (make-vl-atom :guts (make-vl-funname :name x.name)))
             (this-call    (make-vl-nonatom :op :vl-funcall
                                            :args (cons funname-atom actuals))))
          (mv nil
              (fatal :type :vl-bad-funcall
                     :msg "In ~a0, trying to call function ~w1 with ~x2 ~
                           argument~s3, but it takes ~x4 input~s5.  ~
                           Expression: ~a6."
                     :args (list ctx
                                 x.name
                                 (len actuals)
                                 (if (vl-plural-p actuals) "s" "")
                                 (len x.inputs)
                                 (if (vl-plural-p x.inputs) "s" "")
                                 this-call))
              nf nil vardecls assigns)))

       ;; Generate fresh wires for everything
       ((mv input-vars nf)  (vl-funexpand-rename-vardecls x.inputs nf loc))
       ((mv local-vars nf)  (vl-funexpand-rename-vardecls x.locals nf loc))
       ((mv ret-vars nf)    (vl-funexpand-rename-vardecls (list x.out) nf loc))
       (ret-var             (car ret-vars))

       (gen-input-names     (vl-vardecllist->names input-vars))
       (gen-local-names     (vl-vardecllist->names local-vars))
       (gen-ret-name        (vl-vardecl->name ret-var))

       (gen-input-wires     (vl-make-idexpr-list gen-input-names nil nil))
       (gen-local-wires     (vl-make-idexpr-list gen-local-names nil nil))
       (gen-ret-wire        (vl-idexpr gen-ret-name nil nil))

       (sigma
        ;; Big renaming alist that we can use to rewrite all of the assignments
        ;; to be in terms of our newly generated variables.
        (cons (cons (vl-vardecl->name x.out) gen-ret-wire)
              (append (pairlis$ (vl-vardecllist->names x.inputs) gen-input-wires)
                      (pairlis$ (vl-vardecllist->names x.locals) gen-local-wires))))
       ((with-fast sigma))

       (body-assigns  (vl-assignlist-subst x.assigns sigma))
       (body-assigns  (vl-relocate-assignments body-assigns loc))

       ;; Assignments to drive the generated input wires with the actuals
       (input-assigns (vl-fun-make-assignments-to-inputs gen-input-names actuals loc))

       (vardecls (append input-vars local-vars ret-vars vardecls))
       (assigns  (append input-assigns body-assigns assigns)))

    (mv t (ok) nf gen-ret-wire vardecls assigns)))

(define vl-check-bad-funcalls
  :short "Cause fatal warnings if function calls are in unacceptable places."
  ((ctx         vl-context-p "Context for error messages.")
   (exprs       vl-exprlist-p   "A list of expressions that aren't allowed to have
                                 function calls.")
   (description stringp         "A short explanation of what these expressions
                                 are, e.g., @('delay expressions') or @('left-hand
                                 sides of assignments').")
   (warnings    vl-warninglist-p "Ordinary @(see warnings) accumulator."))
  :returns
  (mv (okp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p))

  :long "<p>If these expressions contain any function calls, we add a fatal
warning and set @('okp') to @('nil').</p>

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
sort of thing, because (1) handling all of this properly raises so many
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

  (b* (((unless (vl-exprlist-has-funcalls exprs))
        (mv t (ok)))
       (fns-called (vl-exprlist-funnames exprs)))
    (mv nil (fatal :type :vl-bad-funcall
                   :msg "In ~a0, function calls in ~s1 are not supported, but ~
                         we found ~s2 of ~&3."
                   :args (list ctx
                               description
                               (if (vl-plural-p fns-called) "calls" "a call")
                               (mergesort fns-called))))))


(local (defthm crock
         (equal (len (vl-exprlist-fix x))
                (len x))))

(local (defthm crock2
         (equal (len (cdr (vl-exprlist-fix x)))
                (len (cdr x)))))

(local (in-theory (disable VL-WARNINGLIST-P-WHEN-SUBSETP-EQUAL
                           MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF
                           DEFAULT-CAR
                           DEFAULT-CDR
                           ACL2::CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP
                           ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP
                           acl2::CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP
                           acl2::true-listp-member-equal
                           double-containment)))

(defprojection vl-assignlist->rhses ((x vl-assignlist-p))
  :returns (rhses vl-exprlist-p)
  (vl-assign->expr x))


(with-output :evisc (:gag-mode (evisc-tuple 5 10 nil nil))
  (defines vl-expr-expand-function-calls
    :short "Expand function calls throughout an expression."

    :long "<p>We recursively try to expand function calls throughout an
expression (list).  We return a new expression (list) that is equivalent,
assuming that the generated variables and assigns are added to the module, and
which is free of function calls on success.</p>"

    :hints (("goal" :expand ((vl-assignlist->rhses x))))
    :prepwork ((local (Defthm vl-expr-fix-type
                        (consp (vl-expr-fix x))
                        :hints(("Goal" :in-theory (enable (tau-system))))
                        :rule-classes :type-prescription))
               (local (in-theory (disable (tau-system)
                                          acl2::subsetp-when-atom-right
                                          subsetp-equal-when-cdr-atom
                                          acl2::subsetp-when-atom-left
                                          vl-assignlist-p-when-not-consp
                                          vl-vardecllist-p-when-not-consp
                                          vl-warninglist-p-when-not-consp)))
               (local (std::set-returnspec-mrec-default-hints
                     ;; for whatever reason, it is faster here NOT to wait until
                     ;; stable-under-simplification to expand calls, so we pass NIL as
                     ;; the wait-until-stablep parameter.
                     ((acl2::just-expand-mrec-default-hint 'std::fnname id nil world)))))

    (define vl-expr-expand-function-calls
      ((x         vl-expr-p)
       (ss        vl-scopestack-p)
       (nf        vl-namefactory-p)
       (vardecls  vl-vardecllist-p)
       (assigns   vl-assignlist-p)
       (warnings  vl-warninglist-p)
       (ctx       vl-context-p)
       (loc       vl-location-p)
       (reclimit  natp))
      :returns (mv (successp booleanp :rule-classes :type-prescription)
                   (warnings vl-warninglist-p)
                   (nf       vl-namefactory-p)
                   (new-x    vl-expr-p)
                   (vardecls vl-vardecllist-p)
                   (assigns  vl-assignlist-p))
      :measure (two-nats-measure reclimit (vl-expr-count x))
      :verify-guards nil
      :flag :expr
      (b* ((x        (vl-expr-fix x))
           (nf       (vl-namefactory-fix nf))
           (vardecls (vl-vardecllist-fix vardecls))
           (assigns  (vl-assignlist-fix assigns))
           (warnings (vl-warninglist-fix warnings))

           ((when (vl-atom-p x))
            ;; Not a function call, nothing to do
            (mv t (ok) nf x vardecls assigns))

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
               (vl-check-bad-funcalls ctx (list (first args)) "replication constants" warnings))
              (:vl-bitselect
               ;; to avoid f(x)[3] --> f_return_wire[3], but maybe this would be okay?
               (vl-check-bad-funcalls ctx (list (first args)) "bit-select names" warnings))
              ((:vl-partselect-colon :vl-partselect-pluscolon :vl-partselect-minuscolon)
               ;; to avoid foo[f(3):0] --> foo[f_return_wire:0]
               (vl-check-bad-funcalls ctx args "part-selects" warnings))
              ((:vl-hid-dot :vl-index)
               ;; this would just be to weird
               (vl-check-bad-funcalls ctx args "hierarchical identifiers" warnings))
              (:vl-mintypmax
               ;; this would just be too weird
               (vl-check-bad-funcalls ctx args "minimum/typical/maximum delay expressions" warnings))
              (otherwise
               ;; Else everything seems fine
               (mv t warnings))))

           ((unless okp)
            (mv nil warnings nf x vardecls assigns))

           ((mv okp warnings nf args-prime vardecls assigns)
            (vl-exprlist-expand-function-calls
             args ss nf vardecls assigns warnings ctx loc reclimit))
           ((unless okp)
            (mv nil warnings nf x vardecls assigns))

           ((unless (eq op :vl-funcall))
            ;; Nothing more to do
            (mv t warnings nf (change-vl-nonatom x :args args-prime) vardecls assigns))

           (funname (and (consp args-prime)
                         (vl-atom-p (car args-prime))
                         (vl-funname-p (vl-atom->guts (car args-prime)))
                         (vl-funname->name (vl-atom->guts (car args-prime)))))
           ((unless funname)
            (mv nil
                (fatal :type :vl-programming-error
                       :msg "In ~a0, found a function call expression whose ~
                           first argument is not a valid function-name atom; ~
                           this is seriously malformed.  Internal ~
                           representation: ~x1."
                       :args (list ctx x))
                nf x vardecls assigns))

           ((mv okp warnings template)
            (vl-fnname->template funname ss warnings reclimit))
           ((unless okp)
            (mv nil
                (fatal :type :vl-bad-funcall
                       :msg "In ~a0, there is a call to function ~w1, which ~
                           could not be expanded: ~a2."
                       :args (list ctx funname x))
                nf x vardecls assigns))

           ((mv okp warnings nf x-prime vardecls assigns)
            (vl-expand-function-call template (cdr args-prime)
                                     nf vardecls assigns warnings ctx loc))
           ((unless okp)
            (mv nil warnings nf x vardecls assigns)))

        (mv t warnings nf x-prime vardecls assigns)))

    (define vl-exprlist-expand-function-calls
      ((x         vl-exprlist-p)
       (ss        vl-scopestack-p)
       (nf        vl-namefactory-p)
       (vardecls  vl-vardecllist-p)
       (assigns   vl-assignlist-p)
       (warnings  vl-warninglist-p)
       (ctx       vl-context-p)
       (loc       vl-location-p)
       (reclimit  natp))
      :returns (mv (successp booleanp :rule-classes :type-prescription)
                   (warnings vl-warninglist-p)
                   (nf       vl-namefactory-p)
                   (new-x    (and (vl-exprlist-p new-x)
                                  (equal (len new-x) (len x))))
                   (vardecls vl-vardecllist-p)
                   (assigns  vl-assignlist-p))
      :measure (two-nats-measure reclimit (vl-exprlist-count x))
      :flag :list
      (b* ((nf       (vl-namefactory-fix nf))
           (vardecls (vl-vardecllist-fix vardecls))
           (assigns  (vl-assignlist-fix assigns))
           ((when (atom x))
            (mv t (ok) nf nil vardecls assigns))
           ((mv okp1 warnings nf car-prime vardecls assigns)
            (vl-expr-expand-function-calls (car x) ss nf vardecls assigns warnings ctx loc reclimit))
           ((mv okp2 warnings nf cdr-prime vardecls assigns)
            (vl-exprlist-expand-function-calls (cdr x) ss nf vardecls assigns warnings ctx loc reclimit)))
        (mv (and okp1 okp2) warnings nf (cons car-prime cdr-prime) vardecls assigns)))


    (define vl-fnname->template ((funname stringp)
                                 (ss vl-scopestack-p)
                                 (warnings vl-warninglist-p)
                                 (reclimit natp))
      :returns (mv (successp booleanp :rule-classes :type-prescription)
                   (warnings vl-warninglist-p)
                   (template (implies successp (vl-funtemplate-p template))))
      :measure (two-nats-measure reclimit 0)
      (b* (((when (zp reclimit))
            (mv nil
                (warn :type :vl-expand-functions-fail
                      :msg "Failed to expand call of function ~s0 because the ~
                            recursion limit ran out."
                      :args (list funname))
                nil))
           ((mv fndecl fndecl-ss) (vl-scopestack-find-item/ss funname ss))
           ((unless (and fndecl (eq (tag fndecl) :vl-fundecl)))
            (mv nil
                (warn :type :vl-expand-functions-fail
                      :msg "Failed to expand call of function ~s0 because the ~
                            function declaration wasn't found."
                      :args (list funname))
                nil))
           ((mv ok warnings fndecl) (vl-fundecl-expand-params fndecl warnings))
           ((unless ok) (mv nil warnings nil))
           ((mv template1 warnings) (vl-fundecl-expansion-template fndecl warnings))
           ((unless template1) (mv nil warnings nil))
           ((vl-funtemplate template1))
           (nf (vl-starting-namefactory
                (make-vl-module :name funname
                                :origname funname
                                :vardecls
                                (cons template1.out
                                      (append-without-guard template1.inputs template1.locals))
                                :minloc *vl-fakeloc*
                                :maxloc *vl-fakeloc*)))

           ((mv ok warnings nf assigns vardecls new-assigns)
            (vl-assignlist-expand-function-calls template1.assigns fndecl-ss nf
                                                 nil ;; vardecls
                                                 nil ;; assigns
                                                 warnings
                                                 (1- reclimit)))
           (- (vl-free-namefactory nf))
           ((unless ok) (mv nil warnings nil))
           (template (change-vl-funtemplate
                      template1
                      :locals (append-without-guard vardecls template1.locals)
                      :assigns (append-without-guard new-assigns assigns))))
        (mv t warnings template)))

    (define vl-assignlist-expand-function-calls
      ((x vl-assignlist-p)
       (ss vl-scopestack-p)
       (nf vl-namefactory-p)
       (vardecls  vl-vardecllist-p)
       (assigns   vl-assignlist-p)
       (warnings  vl-warninglist-p)
       (reclimit  natp))
      :measure (two-nats-measure reclimit (+ (len x) (vl-exprlist-count (vl-assignlist->rhses x))))
      :returns (mv (successp booleanp :rule-classes :type-prescription)
                   (warnings vl-warninglist-p)
                   (nf       vl-namefactory-p)
                   (new-x    (and (vl-assignlist-p new-x)
                                  (equal (len new-x) (len x))))
                   (vardecls vl-vardecllist-p)
                   (assigns  vl-assignlist-p))
      (b* ((warnings (vl-warninglist-fix warnings))
           (nf       (vl-namefactory-fix nf))
           (vardecls (vl-vardecllist-fix vardecls))
           (assigns  (vl-assignlist-fix assigns))
           ((When (atom x))
            (mv t warnings nf nil vardecls assigns))
           ((mv ok1 warnings nf first vardecls assigns)
            (vl-assign-expand-function-calls
             (car x) ss nf vardecls assigns warnings reclimit))
           ((mv ok2 warnings nf rest vardecls assigns)
            (vl-assignlist-expand-function-calls
             (cdr x) ss nf vardecls assigns warnings reclimit)))
        (mv (and ok1 ok2) warnings nf (cons first rest) vardecls assigns)))

    (define vl-assign-expand-function-calls
      ((x vl-assign-p)
       (ss vl-scopestack-p)
       (nf vl-namefactory-p)
       (vardecls  vl-vardecllist-p)
       (assigns   vl-assignlist-p)
       (warnings  vl-warninglist-p)
       (reclimit  natp))
      :measure (two-nats-measure reclimit (+ 1 (vl-expr-count (vl-assign->expr x))))

      :returns (mv (successp booleanp :rule-classes :type-prescription)
                   (warnings vl-warninglist-p)
                   (nf       vl-namefactory-p)
                   (new-x    vl-assign-p)
                   (vardecls vl-vardecllist-p)
                   (assigns  vl-assignlist-p))
      (b* (((vl-assign x) x)
           ((mv okp1 warnings)
            (vl-check-bad-funcalls x (list x.lvalue)
                                   "left-hand sides of assignments" warnings))
           ((mv okp2 warnings)
            (vl-check-bad-funcalls x (vl-maybe-gatedelay-allexprs x.delay)
                                   "delay expressions" warnings))
           ((mv okp3 warnings nf rhs-prime vardecls assigns)
            (vl-expr-expand-function-calls x.expr ss nf vardecls
                                           assigns warnings x x.loc reclimit))
           (okp     (and okp1 okp2 okp3))
           (x-prime (change-vl-assign x :expr rhs-prime)))
        (mv okp warnings nf x-prime vardecls assigns)))




    ///
    (verify-guards vl-expr-expand-function-calls
      :guard-debug t)))


; -----------------------------------------------------------------------------
;
;            Expanding Function Calls throughout Module Elements
;
; -----------------------------------------------------------------------------

(defmacro def-vl-expand-function-calls (name &key type body ctxp)
  `(define ,name
     :parents (vl-module-expand-functions)
     :short ,(cat "Expand function calls throughout a @(see " (symbol-name type) ")")
     ((x         ,type)
      (ss        vl-scopestack-p)
      (nf        vl-namefactory-p)
      (vardecls  vl-vardecllist-p)
      (assigns   vl-assignlist-p)
      (warnings  vl-warninglist-p)
      . ,(and ctxp '((ctx vl-context-p)
                     (loc vl-location-p))))
     :returns (mv (successp booleanp :rule-classes :type-prescription)
                  (warnings vl-warninglist-p)
                  (nf       vl-namefactory-p)
                  (x-prime  ,type)
                  (vardecls vl-vardecllist-p)
                  (assigns  vl-assignlist-p))
     (b* ((nf       (vl-namefactory-fix nf))
          (assigns  (vl-assignlist-fix assigns))
          (vardecls (vl-vardecllist-fix vardecls)))
       ,body)))

(defmacro def-vl-expand-function-calls-list (name &key type element ctxp)
  `(define ,name
     :parents (vl-module-expand-functions)
     :short ,(cat "Expand function calls throughout a @(see " (symbol-name type) ")")
     ((x         ,type)
      (ss        vl-scopestack-p)
      (nf        vl-namefactory-p)
      (vardecls  vl-vardecllist-p)
      (assigns   vl-assignlist-p)
      (warnings  vl-warninglist-p)
      . ,(and ctxp '((ctx vl-context-p)
                     (loc vl-location-p))))
     :returns
     (mv (successp booleanp :rule-classes :type-prescription)
         (warnings vl-warninglist-p)
         (nf       vl-namefactory-p)
         (x-prime  ,type)
         (vardecls vl-vardecllist-p)
         (assigns  vl-assignlist-p))
     (b* (((when (atom x))
           (mv t (ok) (vl-namefactory-fix nf) nil (vl-vardecllist-fix vardecls) (vl-assignlist-fix assigns)))
          ((mv successp warnings nf car-prime vardecls assigns)
           (,element (car x) ss nf vardecls assigns warnings
                     . ,(and ctxp '(ctx loc))))
          ((unless successp)
           (mv nil warnings nf nil vardecls assigns))
          ((mv successp warnings nf cdr-prime vardecls assigns)
           (,name (cdr x) ss nf vardecls assigns warnings
                  . ,(and ctxp '(ctx loc))))
          ((unless successp)
           (mv nil warnings nf nil vardecls assigns)))
       (mv t warnings nf (cons car-prime cdr-prime) vardecls assigns))
     ///
     (defmvtypes ,name (nil nil nil true-listp nil nil))))



(def-vl-expand-function-calls vl-plainarg-expand-function-calls
  :type vl-plainarg-p
  :ctxp t
  :body
  (b* ((x (vl-plainarg-fix x))
       ((vl-plainarg x) x)

       ((unless x.expr)
        ;; Blanks are fine, nothing to do
        (mv t (ok) nf x vardecls assigns))

       ((unless (vl-expr-has-funcalls x.expr))
        ;; Most of the time there aren't any function calls, so we don't really
        ;; need to be adding fatal warnings everywhere if a module instance
        ;; isn't resolved, and we don't need to do any re-consing.
        (mv t (ok) nf x vardecls assigns))

       ;; Else, double-check the direction.  We definitely don't want to expand
       ;; a function call unless this is an input port, because it doesn't make
       ;; sense for a submodule instance to be outputting a value into a
       ;; function call.
       ((unless x.dir)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "In ~a0, expected all arguments to be resolved before ~
                         function expansion."
                   :args (list ctx))
            nf x vardecls assigns))

       ((unless (eq x.dir :vl-input))
        (mv nil
            (fatal :type :vl-bad-argument
                   :msg "In ~a0, we found a function call in a ~s1-port ~
                         connection, ~a2, but we only allow function calls in ~
                         input-port connections."
                   :args (list ctx x.dir x))
            nf x vardecls assigns))

       ;; Else, seems okay to expand the function calls here.
       ((mv okp warnings nf expr-prime vardecls assigns)
        (vl-expr-expand-function-calls x.expr ss nf vardecls
                                       assigns warnings ctx loc 100))

       (x-prime (change-vl-plainarg x :expr expr-prime)))
    (mv okp warnings nf x-prime vardecls assigns)))

(def-vl-expand-function-calls-list vl-plainarglist-expand-function-calls
  :type vl-plainarglist-p
  :ctxp t
  :element vl-plainarg-expand-function-calls)

(def-vl-expand-function-calls vl-arguments-expand-function-calls
  :type vl-arguments-p
  :ctxp t
  :body
  (b* ((x (vl-arguments-fix x))
       ((unless (vl-exprlist-has-funcalls (vl-arguments-allexprs x)))
        ;; Common case of no function calls, nothing to do, don't need to
        ;; be adding fatal warnings everywhere in case of unresolved args.
        (mv t (ok) nf x vardecls assigns))
       ((when (eq (vl-arguments-kind x) :vl-arguments-named))
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "In ~a0, we expected all arguments to be resolved ~
                         before function expansion."
                   :args (list ctx))
            nf x vardecls assigns))
       ;; Else, seems okay to expand the function calls here.
       ((mv okp warnings nf args-prime vardecls assigns)
        (vl-plainarglist-expand-function-calls (vl-arguments-plain->args x)
                                               ss nf vardecls assigns
                                               warnings ctx loc))
       (x-prime (make-vl-arguments-plain :args args-prime)))
    (mv okp warnings nf x-prime vardecls assigns)))

(def-vl-expand-function-calls vl-modinst-expand-function-calls
  :type vl-modinst-p
  :body
  (b* (((vl-modinst x) x)
       ((mv okp1 warnings)
        (vl-check-bad-funcalls x (vl-maybe-range-allexprs x.range)
                               "module instance array ranges" warnings))
       ((mv okp2 warnings)
        (vl-check-bad-funcalls x (vl-maybe-gatedelay-allexprs x.delay)
                               "delay expressions" warnings))
       ((mv okp3 warnings)
        (vl-check-bad-funcalls x (vl-paramargs-allexprs x.paramargs)
                               "module instance parameter-lists" warnings))
       ((mv okp4 warnings nf portargs-prime vardecls assigns)
        (vl-arguments-expand-function-calls x.portargs ss nf
                                            vardecls assigns warnings x x.loc))
       (okp (and okp1 okp2 okp3 okp4))
       (x-prime (change-vl-modinst x :portargs portargs-prime)))
    (mv okp warnings nf x-prime vardecls assigns)))

(def-vl-expand-function-calls-list vl-modinstlist-expand-function-calls
  :type vl-modinstlist-p
  :element vl-modinst-expand-function-calls)



(def-vl-expand-function-calls vl-gateinst-expand-function-calls
  :type vl-gateinst-p
  :body
  (b* (((vl-gateinst x) x)
       ((mv okp1 warnings)
        (vl-check-bad-funcalls x (vl-maybe-range-allexprs x.range)
                               "gate instance array ranges" warnings))
       ((mv okp2 warnings)
        (vl-check-bad-funcalls x (vl-maybe-gatedelay-allexprs x.delay)
                               "delay expressions" warnings))
       ((mv okp3 warnings nf args-prime vardecls assigns)
        (vl-plainarglist-expand-function-calls x.args ss nf vardecls
                                               assigns warnings x x.loc))
       (okp     (and okp1 okp2 okp3))
       (x-prime (change-vl-gateinst x :args args-prime)))
    (mv okp warnings nf x-prime vardecls assigns)))

(def-vl-expand-function-calls-list vl-gateinstlist-expand-function-calls
  :type vl-gateinstlist-p
  :element vl-gateinst-expand-function-calls)



(with-output
  :evisc (:gag-mode (evisc-tuple 5 10 nil nil))
  (defines vl-stmt-expand-function-calls
    :prepwork ((local (std::set-returnspec-mrec-default-hints
                       ;; for whatever reason, it is faster here NOT to wait until
                       ;; stable-under-simplification to expand calls, so we pass NIL as
                       ;; the wait-until-stablep parameter.
                       ((acl2::just-expand-mrec-default-hint 'std::fnname id nil world))))
               (local (in-theory (disable vl-vardecllist-p-when-subsetp-equal
                                          vl-assignlist-p-when-subsetp-equal
                                          vl-warninglist-p-when-not-consp
                                          vl-assignlist-p-when-not-consp
                                          vl-vardecllist-p-when-not-consp))))
    (define vl-stmt-expand-function-calls ((x         vl-stmt-p)
                                           (ss        vl-scopestack-p)
                                           (nf        vl-namefactory-p)
                                           (vardecls  vl-vardecllist-p)
                                           (assigns   vl-assignlist-p)
                                           (warnings  vl-warninglist-p)
                                           (ctx       vl-context-p)
                                           (loc       vl-location-p))
      :returns (mv (okp booleanp :rule-classes :type-prescription)
                   (warnings vl-warninglist-p)
                   (nf       vl-namefactory-p)
                   (new-x    vl-stmt-p)
                   (vardecls vl-vardecllist-p)
                   (assigns  vl-assignlist-p))
      :verify-guards nil
      :measure (vl-stmt-count x)
      :flag :stmt
      (b* ((x        (vl-stmt-fix x))
           (nf       (vl-namefactory-fix nf))
           (vardecls (vl-vardecllist-fix vardecls))
           (assigns  (vl-assignlist-fix assigns))
           (warnings (vl-warninglist-fix warnings))

           ((when (vl-atomicstmt-p x))

            (case (vl-stmt-kind x)
              (:vl-nullstmt
               (mv t (ok) nf x vardecls assigns))

              (:vl-assignstmt
               (b* (((vl-assignstmt x) x)
                    ((mv okp1 warnings)
                     (vl-check-bad-funcalls ctx (list x.lvalue)
                                            "left-hand sides of assignment statements" warnings))
                    ((mv okp2 warnings)
                     (vl-check-bad-funcalls ctx (vl-maybe-delayoreventcontrol-allexprs x.ctrl)
                                            "delay/event controls" warnings))
                    ((mv okp3 warnings nf expr-prime vardecls assigns)
                     (vl-expr-expand-function-calls x.expr ss nf vardecls
                                                    assigns warnings ctx loc 100))
                    (okp     (and okp1 okp2 okp3))
                    (x-prime (change-vl-assignstmt x :expr expr-prime)))
                 (mv okp warnings nf x-prime vardecls assigns)))

              (:vl-deassignstmt
               (b* (((vl-deassignstmt x) x)
                    ((mv okp warnings) (vl-check-bad-funcalls ctx (list x.lvalue) "deassign statements" warnings)))
                 (mv okp warnings nf x vardecls assigns)))

              (:vl-enablestmt
               (b* (((vl-enablestmt x) x)
                    ((mv okp1 warnings)
                     (vl-check-bad-funcalls ctx (list x.id)
                                            "enable statement identifiers" warnings))
                    ;; BOZO we probably need to be making input/output distinctions here to
                    ;; prevent function calls on task outputs.
                    ((mv okp2 warnings nf args-prime vardecls assigns)
                     (vl-exprlist-expand-function-calls x.args ss nf vardecls
                                                        assigns warnings ctx loc 100))
                    (okp     (and okp1 okp2))
                    (x-prime (change-vl-enablestmt x :args args-prime)))
                 (mv okp warnings nf x-prime vardecls assigns)))

              (:vl-disablestmt
               (b* (((vl-disablestmt x) x)
                    ((mv okp warnings)
                     (vl-check-bad-funcalls ctx (list x.id) "disable statements" warnings)))
                 (mv okp warnings nf x vardecls assigns)))

              (:vl-returnstmt
               (b* (((vl-returnstmt x) x)
                    ((mv okp warnings)
                     (if x.val
                         (vl-check-bad-funcalls ctx (list x.val) "disable statements" warnings)
                       (mv t warnings))))
                 (mv okp warnings nf x vardecls assigns)))

              (otherwise
               (b* (((vl-eventtriggerstmt x) x)
                    ((mv okp warnings)
                     (vl-check-bad-funcalls ctx (list x.id) "event trigger statements" warnings)))
                 (mv okp warnings nf x vardecls assigns)))))

           (x.exprs (vl-compoundstmt->exprs x))
           (x.stmts (vl-compoundstmt->stmts x))
           (x.vardecls (vl-compoundstmt->vardecls x))
           (x.paramdecls (vl-compoundstmt->paramdecls x))
           (x.ctrl  (vl-compoundstmt->ctrl x))

           ((mv okp1 warnings) (vl-check-bad-funcalls ctx (vl-vardecllist-allexprs x.vardecls)
                                                      "variable declarations" warnings))
           ((mv okp2 warnings) (vl-check-bad-funcalls ctx (vl-paramdecllist-allexprs x.paramdecls)
                                                      "parameter declarations" warnings))
           ((mv okp3 warnings) (vl-check-bad-funcalls ctx (vl-maybe-delayoreventcontrol-allexprs x.ctrl)
                                                      "timing controls" warnings))
           ((mv okp4 warnings)
            (cond ;; Used to check LHSes in for loop initializations/steps, but
                  ;; now that should be taken care of by the recursive call
                  ((vl-casestmt-p x)
                   ;; Don't allow function calls in match expressions
                   (vl-check-bad-funcalls ctx
                                          (flatten (alist-keys (vl-casestmt->caselist x)))
                                          "case-statement match expressions"
                                          warnings))
                  (t
                   (mv t warnings))))

           ((mv okp5 warnings nf exprs-prime vardecls assigns)
            (vl-exprlist-expand-function-calls x.exprs ss nf vardecls assigns warnings ctx loc 100))
           ((mv okp6 warnings nf stmts-prime vardecls assigns)
            (vl-stmtlist-expand-function-calls x.stmts ss nf vardecls assigns warnings ctx loc))
           ((unless (and okp1 okp2 okp3 okp4 okp5 okp6))
            (mv nil warnings nf x vardecls assigns))
           (x-prime (change-vl-compoundstmt x
                                            :exprs exprs-prime
                                            :stmts stmts-prime)))
        (mv t warnings nf x-prime vardecls assigns)))

    (define vl-stmtlist-expand-function-calls ((x         vl-stmtlist-p)
                                               (ss        vl-scopestack-p)
                                               (nf        vl-namefactory-p)
                                               (vardecls  vl-vardecllist-p)
                                               (assigns   vl-assignlist-p)
                                               (warnings  vl-warninglist-p)
                                               (ctx       vl-context-p)
                                               (loc       vl-location-p))
      :returns (mv (okp booleanp :rule-classes :type-prescription)
                   (warnings vl-warninglist-p)
                   (nf       vl-namefactory-p)
                   (new-x    (and (equal (len new-x) (len x))
                                  (vl-stmtlist-p new-x)))
                   (vardecls vl-vardecllist-p)
                   (assigns  vl-assignlist-p))
      :measure (vl-stmtlist-count x)
      :flag :list
      (b* ((nf       (vl-namefactory-fix nf))
           (vardecls (vl-vardecllist-fix vardecls))
           (assigns  (vl-assignlist-fix assigns))
           ((when (atom x))
            (mv t (ok) nf nil vardecls assigns))
           ((mv car-successp warnings nf car-prime vardecls assigns)
            (vl-stmt-expand-function-calls (car x) ss nf vardecls
                                           assigns warnings ctx loc))
           ((mv cdr-successp warnings nf cdr-prime vardecls assigns)
            (vl-stmtlist-expand-function-calls (cdr x) ss nf vardecls
                                               assigns warnings ctx loc)))
        (mv (and car-successp cdr-successp)
            warnings nf
            (cons car-prime cdr-prime)
            vardecls assigns)))
    ///
    (verify-guards vl-stmt-expand-function-calls)))


(def-vl-expand-function-calls vl-always-expand-function-calls
  :type vl-always-p
  :body
  (b* (((vl-always x) x)
       ((mv okp warnings nf stmt-prime vardecls assigns)
        (vl-stmt-expand-function-calls x.stmt ss nf vardecls assigns warnings x x.loc))
       (x-prime (change-vl-always x :stmt stmt-prime)))
    (mv okp warnings nf x-prime vardecls assigns)))

(def-vl-expand-function-calls-list vl-alwayslist-expand-function-calls
  :type vl-alwayslist-p
  :element vl-always-expand-function-calls)


(def-vl-expand-function-calls vl-initial-expand-function-calls
  :type vl-initial-p
  :body
  (b* (((vl-initial x) x)
       ((mv okp warnings nf stmt-prime vardecls assigns)
        (vl-stmt-expand-function-calls x.stmt ss nf vardecls assigns warnings x x.loc))
       (x-prime (change-vl-initial x :stmt stmt-prime)))
    (mv okp warnings nf x-prime vardecls assigns)))

(def-vl-expand-function-calls-list vl-initiallist-expand-function-calls
  :type vl-initiallist-p
  :element vl-initial-expand-function-calls)




(set-ignore-ok t)

;; We now introduce a bunch of functions that basically just check that the other
;; module elements don't have any function calls in them.

(def-vl-expand-function-calls vl-port-expand-function-calls
  :type vl-port-p
  :body
  (b* ((x (vl-port-fix x))
       ((mv okp warnings)
        (vl-check-bad-funcalls (vl-context x) (vl-port-allexprs x) "ports" warnings)))
    (mv okp warnings nf x vardecls assigns)))

(def-vl-expand-function-calls-list vl-portlist-expand-function-calls
  :type vl-portlist-p
  :element vl-port-expand-function-calls)

(def-vl-expand-function-calls vl-portdecl-expand-function-calls
  :type vl-portdecl-p
  :body
  (b* ((x (vl-portdecl-fix x))
       ((mv okp warnings)
        (vl-check-bad-funcalls x (vl-portdecl-allexprs x)
                               "port declarations" warnings)))
    (mv okp warnings nf x vardecls assigns)))

(def-vl-expand-function-calls-list vl-portdecllist-expand-function-calls
  :type vl-portdecllist-p
  :element vl-portdecl-expand-function-calls)

(def-vl-expand-function-calls vl-vardecl-expand-function-calls
  :type vl-vardecl-p
  :body
  (b* ((x (vl-vardecl-fix x))
       ((mv okp warnings)
        (vl-check-bad-funcalls x (vl-vardecl-allexprs x)
                               "variable declarations" warnings)))
    (mv okp warnings nf x vardecls assigns)))

(def-vl-expand-function-calls-list vl-vardecllist-expand-function-calls
  :type vl-vardecllist-p
  :element vl-vardecl-expand-function-calls)


(def-vl-expand-function-calls vl-paramdecl-expand-function-calls
  :type vl-paramdecl-p
  :body
  (b* ((x (vl-paramdecl-fix x))
       ((mv okp warnings)
        (vl-check-bad-funcalls x (vl-paramdecl-allexprs x)
                               "parameter declarations" warnings)))
    (mv okp warnings nf x vardecls assigns)))

(def-vl-expand-function-calls-list vl-paramdecllist-expand-function-calls
  :type vl-paramdecllist-p
  :element vl-paramdecl-expand-function-calls)

(set-ignore-ok nil)





; -----------------------------------------------------------------------------
;
;                          Main Transformation
;
; -----------------------------------------------------------------------------

;; Ugh, all of these accumulators slow ACL2 to a crawl.


(define vl-module-expand-calls-in-decls
  :parents (vl-module-expand-functions)
  ((ports vl-portlist-p)
   (portdecls vl-portdecllist-p)
   (vardecls vl-vardecllist-p)
   (paramdecls vl-paramdecllist-p)
   (ss        vl-scopestack-p)
   (nf vl-namefactory-p)
   (vacc vl-vardecllist-p)
   (aacc vl-assignlist-p)
   (warnings vl-warninglist-p))
  :returns (mv (okp        booleanp :rule-classes :type-prescription)
               (warnings   vl-warninglist-p   )
               (nf         vl-namefactory-p   )
               (vacc       vl-vardecllist-p   )
               (aacc       vl-assignlist-p    )
               (ports      vl-portlist-p      )
               (portdecls  vl-portdecllist-p  )
               (vardecls   vl-vardecllist-p   )
               (paramdecls vl-paramdecllist-p ))
  (b* (((mv okp1  warnings nf ports      vacc aacc) (vl-portlist-expand-function-calls      ports      ss nf vacc aacc warnings))
       ((mv okp2  warnings nf portdecls  vacc aacc) (vl-portdecllist-expand-function-calls  portdecls  ss nf vacc aacc warnings))
       ((mv okp3  warnings nf vardecls   vacc aacc) (vl-vardecllist-expand-function-calls   vardecls   ss nf vacc aacc warnings))
       ((mv okp4  warnings nf paramdecls vacc aacc) (vl-paramdecllist-expand-function-calls paramdecls ss nf vacc aacc warnings)))
    ;; Using and* here cuts the proof time for the next proof by about 10x.
    (mv (and* okp1 okp2 okp3 okp4)
        warnings nf vacc aacc
        ports portdecls vardecls paramdecls)))


(define vl-module-expand-calls-in-nondecls
  :parents (vl-module-expand-functions)
  ((assigns   vl-assignlist-p)
   (modinsts  vl-modinstlist-p)
   (gateinsts vl-gateinstlist-p)
   (alwayses  vl-alwayslist-p)
   (initials  vl-initiallist-p)
   (ss        vl-scopestack-p)
   (nf        vl-namefactory-p)
   (vacc      vl-vardecllist-p)
   (aacc      vl-assignlist-p)
   (warnings  vl-warninglist-p))
  :returns
  (mv (okp booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (nf        vl-namefactory-p  )
      (vacc      vl-vardecllist-p  )
      (aacc      vl-assignlist-p   )
      (assigns   vl-assignlist-p   )
      (modinsts  vl-modinstlist-p  )
      (gateinsts vl-gateinstlist-p )
      (alwayses  vl-alwayslist-p   )
      (initials  vl-initiallist-p  ))
  (b* (((mv okp1 warnings nf assigns    vacc aacc) (vl-assignlist-expand-function-calls    assigns    ss nf vacc aacc warnings 100))
       ((mv okp2 warnings nf modinsts   vacc aacc) (vl-modinstlist-expand-function-calls   modinsts   ss nf vacc aacc warnings))
       ((mv okp3 warnings nf gateinsts  vacc aacc) (vl-gateinstlist-expand-function-calls  gateinsts  ss nf vacc aacc warnings))
       ((mv okp4 warnings nf alwayses   vacc aacc) (vl-alwayslist-expand-function-calls    alwayses   ss nf vacc aacc warnings))
       ((mv okp5 warnings nf initials   vacc aacc) (vl-initiallist-expand-function-calls   initials   ss nf vacc aacc warnings)))
    (mv (and* okp1 okp2 okp3 okp4 okp5)
        warnings nf vacc aacc
        assigns modinsts gateinsts alwayses initials)))


(define vl-module-expand-functions
  :short "Eliminate functions from a module by inlining functions wherever
they are called."
  ((x vl-module-p)
   (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  :long "<p>This is the top-level routine to eliminates functions from a
module.  We walk over the expressions in the module.  For each function call,
we find the called function and process its body into a template consisting of
a series of variable declarations and assignments.  We then add the contents of
that template to the module, with names mangled so as not to conflict with
existing names.</p>

<p>We used to preprocess all of the function declarations in the module into
templates before walking over the expressions.  This could be a performance win
because each function is only turned into a template once.  However, this
couldn't account for functions that were declared in the global scope or
imported from packages.  For the moment we will just expand each function
however many times it is called.  If this negatively impacts performance,
consider memoizing @(see vl-fnname->template).</p>"
  (b* ((x (vl-module-fix x))
       ((vl-module x) x)
       ((when (vl-module->hands-offp x))
        x)

       ;; Expand function calls everywhere throughout the module.
       ;;
       ;; We start with empty vardecls and assigns for our accumulators, rather
       ;; than the module's vardecls and assigns, because (especially for
       ;; assigns) as we inline function calls we're going to potentially be
       ;; rewriting assignments, and we don't want to have the old assigns
       ;; sitting in the accumulator.

       (ss (vl-scopestack-push x ss))

       (nf (vl-starting-namefactory x))
       (warnings x.warnings)

       (vacc nil)   ;; accumulator for new vardecls
       (aacc nil)   ;; accumulator for new assignments

       ((mv okp1 warnings nf vacc aacc
            ports portdecls vardecls paramdecls)
        (vl-module-expand-calls-in-decls x.ports x.portdecls x.vardecls
                                         x.paramdecls ss nf vacc aacc warnings))
       ((mv okp2 warnings nf vacc aacc
            assigns modinsts gateinsts alwayses initials)
        (vl-module-expand-calls-in-nondecls x.assigns x.modinsts x.gateinsts
                                            x.alwayses x.initials ss nf vacc aacc warnings))
       (- (vl-free-namefactory nf))

       (okp (and okp1 okp2))
       ((unless okp)
        (change-vl-module x :warnings warnings))

       ;; Everything was okay.  Then, we can throw away all the function declarations
       ;; and just use the replacements for all of these things.
       (x-prime (change-vl-module x
                                  :ports      ports
                                  :portdecls  portdecls
                                  :vardecls   (append-without-guard vacc vardecls)
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
       (allexprs (vl-module-allexprs x-prime))
       ((when (vl-exprlist-has-funcalls allexprs))
        (b* ((w (make-vl-warning
                 :type :vl-programming-error
                 :msg "In module ~m0, there are still function calls after ~
                       successfully expanding functions?  Found calls to ~&1."
                 :args (list x.name (mergesort (vl-exprlist-funnames allexprs)))
                 :fn 'vl-module-expand-functions
                 :fatalp t)))
          (change-vl-module x-prime :warnings (cons w warnings)))))

    x-prime))

(defprojection vl-modulelist-expand-functions ((x vl-modulelist-p) (ss vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-expand-functions x ss))

(define vl-design-expand-functions
  :short "Top-level @(see expand-functions) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (res (change-vl-design x :mods (vl-modulelist-expand-functions x.mods ss))))
    (vl-scopestacks-free)
    res))
