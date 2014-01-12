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
(include-book "expr-tools")
(include-book "hid-tools")
(include-book "stmt-tools")
(local (include-book "../util/arithmetic"))


(defxdoc lvalues
  :parents (mlib)
  :short "Tools for gathering up lvalues and checking the well-formedness of
expressions in lvalue positions.")


(defsection vl-expr-lvaluep
  :parents (lvalues vl-expr-p)

  :short "@(call vl-expr-lvaluep) determines if an expression looks like a good
lvalue."

  :long "<p>We say the <i>lvalue expressions</i> are the subset of expressions
formed by recursively closing</p>

<ul>

<li>the identifiers (whether simple or hierarchical), and</li>

<li>bit- and part-selects, including indexed part-selects like @('[i +:
3]')</li>

</ul>

<p>under concatenation.  This definition is permissive enough to include the
structural net expressions (see section 12.3.9.2) used in port connections and
also the lvalues which are permitted in continuous and procedural assignment
statements.</p>"

  (mutual-recursion

   (defund vl-expr-lvaluep (x)
     (declare (xargs :guard (vl-expr-p x)
                     :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atom-p x)
            (let ((guts (vl-atom->guts x)))
              (or (vl-fast-hidpiece-p guts)
                  (vl-fast-id-p guts))))

           ((mbe :logic (not (consp x))
                 :exec nil)
            ;; Stupid termination hack
            nil)

           (t
            ;; An lvalue should consist of identifiers, part selects, bit
            ;; selects, concatenations, and multiple concatenations.
            (let ((op   (vl-nonatom->op x))
                  (args (vl-nonatom->args x)))
              (case op
                ((:vl-bitselect :vl-partselect-colon :vl-partselect-pluscolon
                                :vl-partselect-minuscolon)
                 ;; foo[index] or foo[a:b] or foo[a+:b] or foo[a-:b] is an okay
                 ;; lvalue as long as foo is an identifier or hierarchical id.
                 (or (vl-idexpr-p (first args))
                     (vl-hidexpr-p (first args))))
                ((:vl-concat)
                 ;; { foo, bar, baz, ... } is valid if all the components are
                 ;; lvalues.
                 (vl-exprlist-lvaluesp args))
                ((:vl-hid-dot :vl-hid-arraydot)
                 ;; hierarchical identifiers are okay for lvalues
                 (vl-hidexpr-p x))
                (otherwise
                 ;; nothing else is permitted.
                 nil))))))

   (defund vl-exprlist-lvaluesp (x)
     (declare (xargs :guard (vl-exprlist-p x)
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         t
       (and (vl-expr-lvaluep (car x))
            (vl-exprlist-lvaluesp (cdr x))))))

  (defthm vl-exprlist-lvaluesp-when-not-consp
    (implies (not (consp x))
             (equal (vl-exprlist-lvaluesp x)
                    t))
    :hints(("Goal" :in-theory (enable vl-exprlist-lvaluesp))))

  (defthm vl-exprlist-lvaluesp-of-cons
    (equal (vl-exprlist-lvaluesp (cons a x))
           (and (vl-expr-lvaluep a)
                (vl-exprlist-lvaluesp x)))
    :hints(("Goal" :in-theory (enable vl-exprlist-lvaluesp))))

  (deflist vl-exprlist-lvaluesp (x)
    (vl-expr-lvaluep x)
    :already-definedp t
    :elementp-of-nil nil)

  (defthm vl-exprlist-lvaluesp-of-vl-nonatom->args-when-concat
    (implies (and (equal (vl-nonatom->op x) :vl-concat)
                  (force (not (vl-atom-p x)))
                  (force (vl-expr-p x))
                  (force (vl-expr-lvaluep x)))
             (vl-exprlist-lvaluesp (vl-nonatom->args x)))
    :hints(("Goal" :in-theory (enable vl-expr-lvaluep)))))




(defxdoc lvalexprs
  :parents (mlib)

  :short "Functions for gathering all the expressions used in lvalue positions
throughout a module item."

  :long "<p>Like the @(see allexprs) family of functions, these functions
gather up \"top level\" expressions found throughout various module items that
occur in \"lvalue positions.\"</p>

<p>Roughly speaking, the lvalexprs functions try to return all expressions that
are being driven by assignments or submodules.  But lvalue gathering is
something of a crapshoot, and you should regard these functions as a sort of
best-effort, heuristic approximation of the actual expressions that are being
driven.  More specifically, you should <b>never</b> assume that the expressions
returned by lvalexprs functions are in any way accurate or complete.</p>

<p>In some cases, the syntax of the module item makes clear which expressions
should be gathered by the corresponding @('lvalexprs') functions.  For example,
every assignment statement has a well-defined left-hand and right-hand side,
and we just need to collect the expression on the left.</p>

<p>But gathering the lvalues from module instances is more involved.  Here, we
need to know which ports are inputs and outputs, which we do not know until the
@(see argresolve) transform is run.  Even then, the situation is complicated
because (1) due to @(see backflow) it is not necessarily the case that inputs
to the submodule are undriven, and (2) the submodule might not actually drive
all of its outputs.</p>

<p>We try to take these into account as best we can.  For the most accurate
results you should typically only run lvalexprs after first running argresolve
and the backflow detector.  If we see that an output has been flagged as
undriven, we will not include the connected wire as an lvalue.  Similarly, if
we see that an input has some backflow, it will be included.</p>

<p>We guarantee that every expression returned by the lvalexprs functions will
satisfy @(see vl-expr-lvaluep).  In certain cases, this may require us to omit
certain \"bad\" expressions.  We print warnings to standard out when this
happens, but there is no way for the caller to programmatically determine if
this has happened.</p>

<p><b>BOZO</b> proper handling for port expressions?</p>

<p><b>BOZO</b> we don't do anything with function declarations.  This seems
basically reasonable; if the functions can be expanded away then we shouldn't
see them, and if they aren't expanded away then we don't really want to include
their \"wires\" since they're in a different namespace.</p>")

(defmacro def-vl-lvalexprs (&key type
                                 exec-body
                                 body)

  (let* ((mksym-package-symbol 'vl::foo)

         (rec            (mksym type '-p))
         (collect-exec   (mksym type '-lvalexprs-exec))
         (collect        (mksym type '-lvalexprs))
         (remove-thm     (mksym collect-exec '-removal))
         (true-list-thm  (mksym 'true-listp-of- collect))
         (type-thm       (mksym 'vl-exprlist-p-of- collect))
         (lv-thm         (mksym 'vl-exprlist-lvaluesp-of- collect))

         (rec-s           (symbol-name rec))
         (collect-s       (symbol-name collect))

         (short          (cat
"Gather lvalue-position expressions from a @(see " rec-s ")."))
         (long           (cat
"<p><b>Signature</b> @(call " collect-s ") returns a @(see vl-exprlist-p).</p>

<p>We return a list of all the top-level lvalue-positioned expressions used
throughout a @(see " rec-s "), as described in @(see lvalexprs).</p>

<p>For efficiency we use a tail-recursive, accumulator-style functions to do
the collection.  Under the hood, we also use @('nreverse')
optimization.</p>")))

    `(defsection ,collect
       :parents (,rec lvalexprs)
       :short ,short
       :long ,long

       (definlined ,collect-exec (x acc)
         (declare (xargs :guard (,rec x)))
         ,exec-body)

       (defund ,collect (x)
         (declare (xargs :guard (,rec x)
                         :verify-guards nil))
         (mbe :logic ,body
              :exec (reverse (,collect-exec x nil))))

       (local (in-theory (enable ,collect-exec ,collect)))

       (defthm ,remove-thm
         (equal (,collect-exec x acc)
                (append (rev (,collect x))
                        acc))
         :hints(("Goal" :in-theory (disable (force)))))

       (verify-guards ,collect)

       (defthm ,true-list-thm
         (true-listp (,collect x))
         :rule-classes :type-prescription)

       (defthm ,type-thm
         (implies (force (,rec x))
                  (vl-exprlist-p (,collect x))))

       (defthm ,lv-thm
         (implies (force (,rec x))
                  (vl-exprlist-lvaluesp (,collect x))))

       (defttag vl-optimize)
       (never-memoize ,collect-exec)
       (progn! (set-raw-mode t)
               (defun ,collect (x)
                 (nreverse (,collect-exec x nil))))
       (defttag nil))))


(defmacro def-vl-lvalexprs-list (&key list element)
  (let* ((mksym-package-symbol 'vl::foo)

         (list-rec             (mksym list '-p))
         (list-collect         (mksym list '-lvalexprs))
         (element-collect      (mksym element '-lvalexprs))
         (element-collect-exec (mksym element '-lvalexprs-exec))
         (type-thm             (mksym 'vl-exprlist-p-of- list-collect))
         (lv-thm               (mksym 'vl-exprlist-lvaluesp-of- list-collect))

         (list-rec-s          (symbol-name list-rec))
         (list-collect-s      (symbol-name list-collect))

         (short          (cat
"Gather lvalue-positioned expressions from a @(see " list-rec-s ")."))
         (long           (cat
"<p><b>Signature</b> @(call " list-collect-s ") returns a @(see vl-exprlist-p).</p>

<p>We return a list of all the top-level lvalue-positioned expressions used
throughout a @(see " list-rec-s "), as described in @(see lvalexprs).</p>")))

    `(defmapappend ,list-collect (x)
       (,element-collect x)
       :guard (,list-rec x)
       :transform-true-list-p t
       :transform-exec ,element-collect-exec
       :parents (,list-rec lvalexprs)
       :short ,short
       :long ,long
       :rest
       ((defthm ,type-thm
          (implies (force (,list-rec x))
                   (vl-exprlist-p (,list-collect x))))

        (defthm ,lv-thm
          (implies (force (,list-rec x))
                   (vl-exprlist-lvaluesp (,list-collect x))))))))

(def-vl-lvalexprs
  :type vl-plainarg
  :exec-body
  (b* (((vl-plainarg x) x))
      (cond ((not x.expr)
             ;; Fine, no expression, nothing to collect.
             acc)
            ((not x.dir)
             (prog2$
              (cw "; vl-plainarg-lvalexprs: note skipping unresolved argument~%")
              acc))
            ((or (eq x.dir :vl-output)
                 (eq x.dir :vl-inout))
             (cond ((assoc-equal "VL_UNSET_OUTPUT" x.atts)
                    ;; Not actually driven by submodule, so don't consider it an lvalue.
                    acc)
                   ((vl-expr-lvaluep x.expr)
                    (cons x.expr acc))
                   (t
                    (prog2$
                     (cw "; vl-plainarg-lvalexprs note: skipping ill-formed output/inout~%")
                     acc))))
            ((assoc-equal "VL_LVALUE_INPUT" x.atts)
             ;; It's connected to an input, but the input is used as an lvalue
             ;; in the submodule.  I.e., this is a backflow case.
             (if (vl-expr-lvaluep x.expr)
                 (cons x.expr acc)
               (prog2$
                (cw "; vl-plainarg-lvalexprs note: skipping non-lvalue backflow input~%")
                acc)))
            (t
             acc)))
  :body
  (b* (((vl-plainarg x) x))
      (cond ((not x.expr)
             nil)
            ((not x.dir)
             nil)
            ((or (eq x.dir :vl-output)
                 (eq x.dir :vl-inout))
             (cond ((assoc-equal "VL_UNSET_OUTPUT" x.atts)
                    nil)
                   ((vl-expr-lvaluep x.expr)
                    (list x.expr))
                   (t
                    nil)))
            ((assoc-equal "VL_LVALUE_INPUT" x.atts)
             (if (vl-expr-lvaluep x.expr)
                 (list x.expr)
               nil))
            (t
             nil))))

(def-vl-lvalexprs-list
  :list vl-plainarglist
  :element vl-plainarg)

(def-vl-lvalexprs
  :type vl-gateinst
  :exec-body (vl-plainarglist-lvalexprs-exec (vl-gateinst->args x) acc)
  :body (vl-plainarglist-lvalexprs (vl-gateinst->args x)))

(def-vl-lvalexprs-list
  :list vl-gateinstlist
  :element vl-gateinst)

(def-vl-lvalexprs
  :type vl-modinst
  :exec-body
  (let ((args (vl-modinst->portargs x)))
    (if (vl-arguments->namedp args)
        (prog2$
         (cw "; vl-modinst-lvalexprs: skipping unresolved instance ~s0 of ~s1~%"
             (vl-modinst->instname x)
             (vl-modinst->modname x))
         acc)
      (vl-plainarglist-lvalexprs-exec (vl-arguments->args args) acc)))
  :body
  (let ((args (vl-modinst->portargs x)))
    (if (vl-arguments->namedp args)
        nil
      (vl-plainarglist-lvalexprs (vl-arguments->args args)))))

(def-vl-lvalexprs-list
  :list vl-modinstlist
  :element vl-modinst)

(def-vl-lvalexprs
  :type vl-assign
  :exec-body
  (b* (((vl-assign x) x))
      (if (vl-expr-lvaluep x.lvalue)
          (cons x.lvalue acc)
        (prog2$
         (cw "vl-assign-lvalexprs: skipping ill-formed lvalue~%")
         acc)))
  :body
  (b* (((vl-assign x) x))
      (if (vl-expr-lvaluep x.lvalue)
          (list x.lvalue)
        nil)))

(def-vl-lvalexprs-list
  :list vl-assignlist
  :element vl-assign)

(def-vl-lvalexprs
  :type vl-assignstmt
  :exec-body
  (b* (((vl-assignstmt x) x))
      (if (vl-expr-lvaluep x.lvalue)
          (cons x.lvalue acc)
        (prog2$
         (cw "vl-assignstmt-lvalexprs: skipping ill-formed lvalue~%")
         acc)))
  :body
  (b* (((vl-assignstmt x) x))
      (if (vl-expr-lvaluep x.lvalue)
          (list x.lvalue)
        nil)))

(def-vl-lvalexprs
  :type vl-atomicstmt
  :exec-body
  (if (eq (tag x) :vl-assignstmt)
      (vl-assignstmt-lvalexprs-exec x acc)
    acc)
  :body
  (if (eq (tag x) :vl-assignstmt)
      (vl-assignstmt-lvalexprs x)
    nil))

(def-vl-lvalexprs-list
  :list vl-atomicstmtlist
  :element vl-atomicstmt)

(def-vl-lvalexprs
  :type vl-stmt
  :exec-body (vl-atomicstmtlist-lvalexprs-exec (vl-stmt-atomicstmts x) acc)
  :body (vl-atomicstmtlist-lvalexprs (vl-stmt-atomicstmts x)))

(def-vl-lvalexprs
  :type vl-initial
  :exec-body (vl-stmt-lvalexprs-exec (vl-initial->stmt x) acc)
  :body (vl-stmt-lvalexprs (vl-initial->stmt x)))

(def-vl-lvalexprs-list
  :list vl-initiallist
  :element vl-initial)

(def-vl-lvalexprs
  :type vl-always
  :exec-body (vl-stmt-lvalexprs-exec (vl-always->stmt x) acc)
  :body (vl-stmt-lvalexprs (vl-always->stmt x)))

(def-vl-lvalexprs-list
  :list vl-alwayslist
  :element vl-always)

(def-vl-lvalexprs
  :type vl-module
  :exec-body
  (b* (((vl-module x) x)
       (acc (vl-assignlist-lvalexprs-exec x.assigns acc))
       (acc (vl-modinstlist-lvalexprs-exec x.modinsts acc))
       (acc (vl-gateinstlist-lvalexprs-exec x.gateinsts acc))
       (acc (vl-alwayslist-lvalexprs-exec x.alwayses acc))
       (acc (vl-initiallist-lvalexprs-exec x.initials acc)))
      acc)
  :body
  (b* (((vl-module x) x))
      (append (vl-assignlist-lvalexprs x.assigns)
              (vl-modinstlist-lvalexprs x.modinsts)
              (vl-gateinstlist-lvalexprs x.gateinsts)
              (vl-alwayslist-lvalexprs x.alwayses)
              (vl-initiallist-lvalexprs x.initials))))

(def-vl-lvalexprs-list
  :list vl-modulelist
  :element vl-module)


(defxdoc lvaluecheck
  :parents (lvalues well-formedness)
  :short "Checks to ensure that expressions used in lvalue positions are valid
in the sense of @(see vl-expr-lvaluep)."

  :long "<p>Note that to determine which arguments to gate and module instances
must be checked, we assume that @(see argresolve) has been run prior to running
these functions.</p>")

(defmacro def-vl-lvaluecheck (&key type body extra-formals (guard 't) (long '""))
  (let* ((mksym-package-symbol 'vl::foo)

         (rec            (mksym type '-p))
         (chk            (mksym type '-lvaluecheck))
         (rec-s          (symbol-name rec))

         (short (cat "Check well-formedness of lvalues in a @(see " rec-s ")."))

         (long (cat "<p>We check the lvalues throughout @('x') for well-formedness
in the sense of @(see vl-expr-lvaluep), and generate non-fatal warnings for any
problematic lvalues encountered.</p>" long)))

    `(define ,chk
       ((x ,rec)
        ,@extra-formals
        (warnings vl-warninglist-p "Ordinary @(see warnings) accumulator."))
       :returns (new-warnings vl-warninglist-p
                              :hyp (force (vl-warninglist-p warnings)))
       :parents (,rec lvaluecheck)
       :short ,short
       :long ,long
       :guard ,guard
       ,body)))

(def-vl-lvaluecheck
  :type vl-assign
  :body
  (b* ((lvalue (vl-assign->lvalue x))
       ((when (vl-expr-lvaluep lvalue))
        warnings)
       (loc (vl-assign->loc x)))
    (warn :type :vl-bad-lvalue
          :msg "~l0: assignment to bad lvalue ~a1."
          :args (list loc lvalue))))

(def-vl-lvaluecheck
  :type vl-assignlist
  :body
  (if (atom x)
      warnings
    (b* ((warnings (vl-assign-lvaluecheck (car x) warnings)))
      (vl-assignlist-lvaluecheck (cdr x) warnings))))

; BOZO this is broken -- need to consider ports, can't just look at :dir in general.

(def-vl-lvaluecheck
  :type vl-plainarg
  :extra-formals (loc instname)
  :guard (and (vl-location-p loc)
              (maybe-stringp instname))
  :body
  (b* ((dir  (vl-plainarg->dir x))
       (expr (vl-plainarg->expr x))
       ((unless expr)
        ;; Nothing to check.
        warnings)
       ((unless dir)
        (warn :type :vl-programming-error
              :msg "~l0: expected arguments of instance ~w1 to be resolved, ~
                    but no :DIR is present."
              :args (list loc instname)))
       ((when (eq dir :vl-input))
        ;; Input to a submodule -- not an lvalue, nothing to check.
        warnings)
       ((when (vl-expr-lvaluep expr))
        ;; Good lvalue to an lvalue port.
        warnings))
    (warn :type :vl-bad-lvalue
          :msg "~l0: expression for ~s1 port ~s2 of instance ~w3 is not a ~
                valid lvalue: ~a4.~%"
          :args (list loc
                      (if (eq dir :vl-inout) "inout" "output")
                      (vl-plainarg->portname x)
                      instname
                      expr))))

(def-vl-lvaluecheck
  :type vl-plainarglist
  :extra-formals (loc instname)
  :guard (and (vl-location-p loc)
              (maybe-stringp instname))
  :body
  (if (atom x)
      warnings
    (b* ((warnings (vl-plainarg-lvaluecheck (car x) loc instname warnings)))
      (vl-plainarglist-lvaluecheck (cdr x) loc instname warnings))))

(def-vl-lvaluecheck
  :type vl-arguments
  :extra-formals (loc instname)
  :guard (and (vl-location-p loc)
              (maybe-stringp instname))
  :body
  (if (vl-arguments->namedp x)
      (warn :type :vl-programming-error
            :msg "~l0: expected arguments of instance ~s1 to be resolved, but ~
                  args are still named."
            :args (list loc instname))
    (vl-plainarglist-lvaluecheck (vl-arguments->args x) loc instname warnings)))

(def-vl-lvaluecheck
  :type vl-modinst
  :body
  (vl-arguments-lvaluecheck (vl-modinst->portargs x)
                            (vl-modinst->loc x)
                            (vl-modinst->instname x)
                            warnings))

(def-vl-lvaluecheck
  :type vl-modinstlist
  :body
  (if (atom x)
      warnings
    (b* ((warnings (vl-modinst-lvaluecheck (car x) warnings)))
      (vl-modinstlist-lvaluecheck (cdr x) warnings))))

(def-vl-lvaluecheck
  :type vl-gateinst
  :body
  (vl-plainarglist-lvaluecheck (vl-gateinst->args x)
                               (vl-gateinst->loc x)
                               (vl-gateinst->name x)
                               warnings))

(def-vl-lvaluecheck
  :type vl-gateinstlist
  :body
  (if (atom x)
      warnings
    (b* ((warnings (vl-gateinst-lvaluecheck (car x) warnings)))
      (vl-gateinstlist-lvaluecheck (cdr x) warnings))))

(def-vl-lvaluecheck
  :type vl-assignstmt
  :body
  (b* ((lvalue (vl-assignstmt->lvalue x))
       ((when (vl-expr-lvaluep lvalue))
        warnings)
       (loc (vl-assignstmt->loc x)))
    (warn :type :vl-bad-lvalue
          :msg "~l0: assignment to bad lvalue, ~a1."
          :args (list loc lvalue))))

(def-vl-lvaluecheck
  :type vl-deassignstmt
  :body
  (b* ((lvalue (vl-deassignstmt->lvalue x))
       ((when (vl-expr-lvaluep lvalue))
        warnings))
    (warn :type :vl-bad-lvalue
          ;; BOZO add locations to deassign statements
          :msg "Deassignment to bad lvalue, ~a0."
          :args (list lvalue))))

(def-vl-lvaluecheck
  :type vl-atomicstmt
  :body
  (case (tag x)
    (:vl-assignstmt   (vl-assignstmt-lvaluecheck x warnings))
    (:vl-deassignstmt (vl-deassignstmt-lvaluecheck x warnings))
    (otherwise        warnings)))

(defsection vl-stmt-lvaluecheck

  (mutual-recursion

   (defund vl-stmt-lvaluecheck (x warnings)
     (declare (xargs :guard (and (vl-stmt-p x)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :measure (two-nats-measure (acl2-count x) 1)))
     (cond ((vl-fast-atomicstmt-p x)
            (vl-atomicstmt-lvaluecheck x warnings))

; It looks to me like none of the compound statements have lvalues except for
; for loops, which have the initial and next lhs.  So I explicitly check for
; this here, then recursively check the substatements.

           ((vl-forstmt-p x)
            (b* (((vl-forstmt x) x)
                 (warnings (if (vl-expr-lvaluep x.initlhs)
                               warnings
                             (warn :type :vl-bad-lvalue
                                   :msg "Bad lvalue in for-loop initialization: ~a0."
                                   :args (list x.initlhs)
                                   :fn 'vl-stmt-lvaluecheck)))
                 (warnings (if (vl-expr-lvaluep x.nextlhs)
                               warnings
                             (warn :type :vl-bad-lvalue
                                   :msg "Bad lvalue in for-loop step: ~a0."
                                   :args (list x.nextlhs)
                                   :fn 'vl-stmt-lvaluecheck))))
              (vl-stmtlist-lvaluecheck (vl-compoundstmt->stmts x) warnings)))

           (t
            (vl-stmtlist-lvaluecheck (vl-compoundstmt->stmts x) warnings))))

   (defund vl-stmtlist-lvaluecheck (x warnings)
     (declare (xargs :guard (and (vl-stmtlist-p x)
                                 (vl-warninglist-p warnings))
                     :measure (two-nats-measure (acl2-count x) 0)))
     (if (atom x)
         warnings
       (let ((warnings (vl-stmt-lvaluecheck (car x) warnings)))
         (vl-stmtlist-lvaluecheck (cdr x) warnings)))))

  (flag::make-flag vl-flag-stmt-lvaluecheck
                   vl-stmt-lvaluecheck
                   :flag-mapping ((vl-stmt-lvaluecheck . stmt)
                                  (vl-stmtlist-lvaluecheck . list)))

  (defthm-vl-flag-stmt-lvaluecheck lemma
    (stmt (implies (vl-warninglist-p warnings)
                   (vl-warninglist-p (vl-stmt-lvaluecheck x warnings)))
          :name vl-warninglist-p-of-vl-stmt-lvaluecheck)
    (list (implies (vl-warninglist-p warnings)
                   (vl-warninglist-p (vl-stmtlist-lvaluecheck x warnings)))
          :name vl-warninglist-p-of-vl-stmtlist-lvaluecheck)
    :hints(("Goal"
            :induct (vl-flag-stmt-lvaluecheck flag x warnings)
            :expand ((vl-stmt-lvaluecheck x warnings)
                     (vl-stmtlist-lvaluecheck x warnings)))))

  (verify-guards vl-stmt-lvaluecheck))

(def-vl-lvaluecheck
  :type vl-always
  :body (vl-stmt-lvaluecheck (vl-always->stmt x) warnings))

(def-vl-lvaluecheck
  :type vl-alwayslist
  :body
  (if (atom x)
      warnings
    (b* ((warnings (vl-always-lvaluecheck (car x) warnings)))
        (vl-alwayslist-lvaluecheck (cdr x) warnings))))

(def-vl-lvaluecheck
  :type vl-initial
  :body (vl-stmt-lvaluecheck (vl-initial->stmt x) warnings))

(def-vl-lvaluecheck
  :type vl-initiallist
  :body
  (if (atom x)
      warnings
    (b* ((warnings (vl-initial-lvaluecheck (car x) warnings)))
        (vl-initiallist-lvaluecheck (cdr x) warnings))))

(def-vl-lvaluecheck
  :type vl-fundecl
  :body (vl-stmt-lvaluecheck (vl-fundecl->body x) warnings))

(def-vl-lvaluecheck
  :type vl-fundecllist
  :body
  (if (atom x)
      warnings
    (b* ((warnings (vl-fundecl-lvaluecheck (car x) warnings)))
        (vl-fundecllist-lvaluecheck (cdr x) warnings))))

(def-vl-lvaluecheck
  :type vl-taskdecl
  :body (vl-stmt-lvaluecheck (vl-taskdecl->body x) warnings))

(def-vl-lvaluecheck
  :type vl-taskdecllist
  :body
  (if (atom x)
      warnings
    (b* ((warnings (vl-taskdecl-lvaluecheck (car x) warnings)))
        (vl-taskdecllist-lvaluecheck (cdr x) warnings))))



(defsection vl-module-lvaluecheck

  (defund vl-module-lvaluecheck (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         (warnings  x.warnings)
         (warnings  (vl-assignlist-lvaluecheck   x.assigns   warnings))
         (warnings  (vl-modinstlist-lvaluecheck  x.modinsts  warnings))
         (warnings  (vl-gateinstlist-lvaluecheck x.gateinsts warnings))
         (warnings  (vl-alwayslist-lvaluecheck   x.alwayses  warnings))
         (warnings  (vl-initiallist-lvaluecheck  x.initials  warnings))
         (warnings  (vl-fundecllist-lvaluecheck  x.fundecls  warnings))
         (warnings  (vl-taskdecllist-lvaluecheck x.taskdecls warnings)))
      (change-vl-module x :warnings warnings)))

  (local (in-theory (enable vl-module-lvaluecheck)))

  (defthm vl-module-p-of-vl-module-lvaluecheck
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-lvaluecheck x))))

  (defthm vl-module->name-of-vl-module-lvaluecheck
    (equal (vl-module->name (vl-module-lvaluecheck x))
           (vl-module->name x))))



(defprojection vl-modulelist-lvaluecheck (x)
  (vl-module-lvaluecheck x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-lvaluecheck
     (equal (vl-modulelist->names (vl-modulelist-lvaluecheck x))
            (vl-modulelist->names x)))))


