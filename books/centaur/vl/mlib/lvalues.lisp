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
(include-book "expr-tools")
(include-book "hid-tools")
(include-book "stmt-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defxdoc lvalues
  :parents (mlib)
  :short "Tools for gathering up lvalues and checking the well-formedness of
expressions in lvalue positions.")


(defines vl-expr-lvaluep
  :parents (lvalues vl-expr-p)
  :short "Determine if an expression looks like a good lvalue."
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

  (define vl-expr-lvaluep ((x vl-expr-p))
    :measure (vl-expr-count x)
    (vl-expr-case x
      :vl-index t
      :vl-concat (vl-exprlist-lvaluesp x.parts)
      :otherwise nil))
  (define vl-exprlist-lvaluesp ((x vl-exprlist-p))
    :measure (vl-exprlist-count x)
    (if (atom x)
        t
      (and (vl-expr-lvaluep (car x))
           (vl-exprlist-lvaluesp (cdr x)))))

  ///
  (xdoc::without-xdoc
    (deflist vl-exprlist-lvaluesp (x)
      (vl-expr-lvaluep x)
      :already-definedp t
      :elementp-of-nil nil))

  (deffixequiv-mutual vl-expr-lvaluep)

  (defthm vl-exprlist-lvaluesp-of-vl-concat-parts
    (implies (and (vl-expr-case x :vl-concat)
                  (force (vl-expr-lvaluep x)))
             (vl-exprlist-lvaluesp (vl-concat->parts x)))
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
because (1) due to \"backflow\" it is not necessarily the case that inputs to
the submodule are undriven, and (2) the submodule might not actually drive all
of its outputs.</p>

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

(defmacro def-vl-lvalexprs (&key type nrev-body body)

  (let* ((mksym-package-symbol (pkg-witness "VL"))
         (rec            (mksym type '-p))
         (fix            (mksym type '-fix))
         (collect-nrev   (mksym type '-lvalexprs-nrev))
         (collect        (mksym type '-lvalexprs))
         (short          (cat "Gather lvalue-position expressions from a @(see "
                              (symbol-name rec) ").")))

    `(progn

       (define ,collect-nrev ((x ,rec) (nrev))
         :parents (,collect)
         :inline t
         (b* ((x (,fix x)))
           ,nrev-body))

       (define ,collect ((x ,rec))
         :returns (exprs vl-exprlist-p)
         :parents (lvalexprs)
         :short ,short
         :verify-guards nil
         (mbe :logic (b* ((x (,fix x)))
                       ,body)
              :exec (with-local-nrev (,collect-nrev x nrev)))
         ///
         (defthm ,(mksym collect-nrev '-removal)
           (equal (,collect-nrev x nrev)
                  (append nrev (,collect x)))
           :hints(("Goal" :in-theory (enable acl2::rcons
                                             ,collect-nrev))))

         (verify-guards ,collect)

         (defthm ,(mksym 'true-listp-of- collect)
           (true-listp (,collect x))
           :rule-classes :type-prescription)

         (defthm ,(mksym 'vl-exprlist-lvaluesp-of- collect)
           (vl-exprlist-lvaluesp (,collect x)))))))


(defmacro def-vl-lvalexprs-list (&key list element)
  (let* ((mksym-package-symbol (pkg-witness "VL"))
         (list-rec             (mksym list '-p))
         (list-collect         (mksym list '-lvalexprs))
         (list-collect-nrev    (mksym list '-lvalexprs-nrev))
         (element-collect      (mksym element '-lvalexprs))
         (element-collect-nrev (mksym element '-lvalexprs-nrev))
         (short                (cat "Gather all top-level expressions from a @(see "
                                    (symbol-name list-rec) ").")))
    `(progn
       (define ,list-collect-nrev ((x ,list-rec) nrev)
         :parents (,list-collect)
         (if (atom x)
             (nrev-fix nrev)
           (let ((nrev (,element-collect-nrev (car x) nrev)))
             (,list-collect-nrev (cdr x) nrev))))

       (define ,list-collect ((x ,list-rec))
         :returns (exprs vl-exprlist-p)
         :parents (lvalexprs)
         :short ,short
         :verify-guards nil
         (mbe :logic (if (atom x)
                         nil
                       (append (,element-collect (car x))
                               (,list-collect (cdr x))))
              :exec (with-local-nrev
                      (,list-collect-nrev x nrev)))
         ///
         (defthm ,(mksym 'true-listp-of- list-collect)
           (true-listp (,list-collect x))
           :rule-classes :type-prescription)

         (defthm ,(mksym list-collect-nrev '-removal)
           (equal (,list-collect-nrev x nrev)
                  (append nrev (,list-collect x)))
           :hints(("Goal" :in-theory (enable acl2::rcons
                                             ,list-collect-nrev))))

         (verify-guards ,list-collect)

         (defmapappend ,list-collect (x)
           (,element-collect x)
           :already-definedp t
           :transform-true-list-p t
           :parents nil)

         (defthm ,(mksym 'vl-exprlist-lvaluesp-of- list-collect)
           (vl-exprlist-lvaluesp (,list-collect x)))))))

(local (defthm alistp-when-vl-atts-p-rw
         (implies (vl-atts-p x)
                  (alistp x))
         :hints(("Goal" :in-theory (enable (tau-system))))))

(def-vl-lvalexprs
  :type vl-plainarg
  :nrev-body
  (b* (((vl-plainarg x) x))
      (cond ((not x.expr)
             ;; Fine, no expression, nothing to collect.
             (nrev-fix nrev))
            ((not x.dir)
             (prog2$
              (cw "; vl-plainarg-lvalexprs: note skipping unresolved argument~%")
              (nrev-fix nrev)))
            ((or (eq x.dir :vl-output)
                 (eq x.dir :vl-inout))
             (cond ((assoc-equal "VL_UNSET_OUTPUT" x.atts)
                    ;; Not actually driven by submodule, so don't consider it an lvalue.
                    (nrev-fix nrev))
                   ((vl-expr-lvaluep x.expr)
                    (nrev-push x.expr nrev))
                   (t
                    (prog2$
                     (cw "; vl-plainarg-lvalexprs note: skipping ill-formed output/inout~%")
                     (nrev-fix nrev)))))
            ((assoc-equal "VL_LVALUE_INPUT" x.atts)
             ;; It's connected to an input, but the input is used as an lvalue
             ;; in the submodule.  I.e., this is a backflow case.
             (if (vl-expr-lvaluep x.expr)
                 (nrev-push x.expr nrev)
               (prog2$
                (cw "; vl-plainarg-lvalexprs note: skipping non-lvalue backflow input~%")
                (nrev-fix nrev))))
            (t
             (nrev-fix nrev))))
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
  :nrev-body (vl-plainarglist-lvalexprs-nrev (vl-gateinst->args x) nrev)
  :body (vl-plainarglist-lvalexprs (vl-gateinst->args x)))

(def-vl-lvalexprs-list
  :list vl-gateinstlist
  :element vl-gateinst)

(def-vl-lvalexprs
  :type vl-modinst
  :nrev-body
  (let ((args (vl-modinst->portargs x)))
    (if (eq (vl-arguments-kind args) :vl-arguments-named)
        (prog2$
         (cw "; vl-modinst-lvalexprs: skipping unresolved instance ~s0 of ~s1~%"
             (vl-modinst->instname x)
             (vl-modinst->modname x))
         (nrev-fix nrev))
      (vl-plainarglist-lvalexprs-nrev (vl-arguments-plain->args args) nrev)))
  :body
  (let ((args (vl-modinst->portargs x)))
    (if (eq (vl-arguments-kind args) :vl-arguments-named)
        nil
      (vl-plainarglist-lvalexprs (vl-arguments-plain->args args)))))

(def-vl-lvalexprs-list
  :list vl-modinstlist
  :element vl-modinst)

(def-vl-lvalexprs
  :type vl-assign
  :nrev-body
  (b* (((vl-assign x) x))
      (if (vl-expr-lvaluep x.lvalue)
          (nrev-push x.lvalue nrev)
        (prog2$
         (cw "vl-assign-lvalexprs: skipping ill-formed lvalue~%")
         (nrev-fix nrev))))
  :body
  (b* (((vl-assign x) x))
      (if (vl-expr-lvaluep x.lvalue)
          (list x.lvalue)
        nil)))

(def-vl-lvalexprs-list
  :list vl-assignlist
  :element vl-assign)


;; BOZO statements should also get initlhs and nextlhs from for loops

(defines vl-stmt-lvalexprs-nrev
  :flag-local nil
  (define vl-stmt-lvalexprs-nrev ((x vl-stmt-p) nrev)
    :measure (vl-stmt-count x)
    :flag :stmt
    (let ((x (vl-stmt-fix x)))
      (if (vl-atomicstmt-p x)
          (case (vl-stmt-kind x)
            (:vl-assignstmt (b* (((vl-assignstmt x) x))
                              (if (vl-expr-lvaluep x.lvalue)
                                  (nrev-push x.lvalue nrev)
                                (prog2$
                                 (cw "vl-stmt-lvalexprs: skipping ill-formed lvalue~%")
                                 (nrev-fix nrev)))))
            (otherwise
             (nrev-fix nrev)))
        (vl-stmtlist-lvalexprs-nrev (vl-compoundstmt->stmts x) nrev))))

  (define vl-stmtlist-lvalexprs-nrev ((x vl-stmtlist-p) nrev)
    :measure (vl-stmtlist-count x)
    :flag :list
    (b* (((when (atom x))
          (nrev-fix nrev))
         (nrev (vl-stmt-lvalexprs-nrev (car x) nrev)))
      (vl-stmtlist-lvalexprs-nrev (cdr x) nrev))))

(defines vl-stmt-lvalexprs
  :parents (lvalexprs)

  (define vl-stmt-lvalexprs ((x vl-stmt-p))
    :measure (vl-stmt-count x)
    :returns (exprs (and (vl-exprlist-p exprs)
                         (vl-exprlist-lvaluesp exprs)))
    (mbe :logic
         (let ((x (vl-stmt-fix x)))
           (if (vl-atomicstmt-p x)
               (case (vl-stmt-kind x)
                 (:vl-assignstmt (b* (((vl-assignstmt x) x))
                                   (if (vl-expr-lvaluep x.lvalue)
                                       (list x.lvalue)
                                     nil)))
                 (otherwise
                  nil))
             (vl-stmtlist-lvalexprs (vl-compoundstmt->stmts x))))
         :exec
         (with-local-nrev (vl-stmt-lvalexprs-nrev x nrev))))

  (define vl-stmtlist-lvalexprs ((x vl-stmtlist-p))
    :measure (vl-stmtlist-count x)
    :returns (exprs (and (vl-exprlist-p exprs)
                         (vl-exprlist-lvaluesp exprs)))
    :verify-guards nil
    (mbe :logic (if (atom x)
                    nil
                  (append (vl-stmt-lvalexprs (car x))
                          (vl-stmtlist-lvalexprs (cdr x))))
         :exec
         (with-local-nrev (vl-stmtlist-lvalexprs-nrev x nrev))))

  ///
  (defthm-vl-stmt-lvalexprs-nrev-flag
    (defthm vl-stmt-lvalexprs-nrev-removal
      (equal (vl-stmt-lvalexprs-nrev x nrev)
             (append nrev (vl-stmt-lvalexprs x)))
      :flag :stmt)
    (defthm vl-stmtlist-lvalexprs-nrev-removal
      (equal (vl-stmtlist-lvalexprs-nrev x nrev)
             (append nrev (vl-stmtlist-lvalexprs x)))
      :flag :list)
    :hints(("Goal"
            :in-theory (enable acl2::rcons)
            :expand ((vl-stmtlist-lvalexprs-nrev x nrev)
                     (vl-stmt-lvalexprs-nrev x nrev)))))
  (verify-guards vl-stmt-lvalexprs))

(def-vl-lvalexprs
  :type vl-initial
  :nrev-body (vl-stmt-lvalexprs-nrev (vl-initial->stmt x) nrev)
  :body (vl-stmt-lvalexprs (vl-initial->stmt x)))

(def-vl-lvalexprs-list
  :list vl-initiallist
  :element vl-initial)

(def-vl-lvalexprs
  :type vl-always
  :nrev-body (vl-stmt-lvalexprs-nrev (vl-always->stmt x) nrev)
  :body (vl-stmt-lvalexprs (vl-always->stmt x)))

(def-vl-lvalexprs-list
  :list vl-alwayslist
  :element vl-always)

(def-vl-lvalexprs
  :type vl-module
  :nrev-body
  (b* (((vl-module x) x)
       (nrev (vl-assignlist-lvalexprs-nrev x.assigns nrev))
       (nrev (vl-modinstlist-lvalexprs-nrev x.modinsts nrev))
       (nrev (vl-gateinstlist-lvalexprs-nrev x.gateinsts nrev))
       (nrev (vl-alwayslist-lvalexprs-nrev x.alwayses nrev))
       (nrev (vl-initiallist-lvalexprs-nrev x.initials nrev)))
      nrev)
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
       :returns (new-warnings vl-warninglist-p)
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
        (ok))
       (loc (vl-assign->loc x)))
    (warn :type :vl-bad-lvalue
          :msg "~l0: assignment to bad lvalue ~a1."
          :args (list loc lvalue))))

(def-vl-lvaluecheck
  :type vl-assignlist
  :body
  (if (atom x)
      (ok)
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
        (ok))
       ((unless dir)
        ;; (warn :type :vl-programming-error
        ;;       :msg "~l0: expected arguments of instance ~w1 to be resolved, ~
        ;;             but no :DIR is present."
        ;;       :args (list loc instname))

        ;; NOTE: We used to warn about this, but now if there are interface
        ;; ports it's correct for argresolve to leave the direction blank.
        (ok))
       ((when (eq dir :vl-input))
        ;; Input to a submodule -- not an lvalue, nothing to check.
        (ok))
       ((when (vl-expr-lvaluep expr))
        ;; Good lvalue to an lvalue port.
        (ok)))
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
      (ok)
    (b* ((warnings (vl-plainarg-lvaluecheck (car x) loc instname warnings)))
      (vl-plainarglist-lvaluecheck (cdr x) loc instname warnings))))

(def-vl-lvaluecheck
  :type vl-arguments
  :extra-formals (loc instname)
  :guard (and (vl-location-p loc)
              (maybe-stringp instname))
  :body
  (if (eq (vl-arguments-kind x) :vl-arguments-named)
      (warn :type :vl-programming-error
            :msg "~l0: expected arguments of instance ~s1 to be resolved, but ~
                  args are still named."
            :args (list loc instname))
    (vl-plainarglist-lvaluecheck (vl-arguments-plain->args x) loc instname warnings)))

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
      (ok)
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
      (ok)
    (b* ((warnings (vl-gateinst-lvaluecheck (car x) warnings)))
      (vl-gateinstlist-lvaluecheck (cdr x) warnings))))



(defines vl-stmt-lvaluecheck

  (define vl-stmt-lvaluecheck ((x        vl-stmt-p)
                               (warnings vl-warninglist-p))
    :returns (new-warnings vl-warninglist-p)
    :measure (vl-stmt-count x)
    :verify-guards nil
    :flag :stmt
    (b* ((x (vl-stmt-fix x))
         ((when (vl-atomicstmt-p x))
          (case (vl-stmt-kind x)
            (:vl-assignstmt (b* ((lvalue (vl-assignstmt->lvalue x))
                                 ((when (vl-expr-lvaluep lvalue))
                                  (ok))
                                 (loc (vl-assignstmt->loc x)))
                              (warn :type :vl-bad-lvalue
                                    :msg "~l0: assignment to bad lvalue, ~a1."
                                    :args (list loc lvalue))))
            (:vl-deassignstmt (b* ((lvalue (vl-deassignstmt->lvalue x))
                                   ((when (vl-expr-lvaluep lvalue))
                                    (ok)))
                                (warn :type :vl-bad-lvalue
                                      ;; BOZO add locations to deassign statements
                                      :msg "Deassignment to bad lvalue, ~a0."
                                      :args (list lvalue))))
            (otherwise (ok)))))

         ;; It looks like none of the compound statements have lvalues, now
         ;; including the for loop, which used to have initial and next lhs but
         ;; now just have substmts.
      (vl-stmtlist-lvaluecheck (vl-compoundstmt->stmts x) warnings)))

  (define vl-stmtlist-lvaluecheck ((x vl-stmtlist-p)
                                   (warnings vl-warninglist-p))
    :returns (new-warnings vl-warninglist-p)
    :measure (vl-stmtlist-count x)
    :flag :list
    (if (atom x)
        (ok)
      (let ((warnings (vl-stmt-lvaluecheck (car x) warnings)))
        (vl-stmtlist-lvaluecheck (cdr x) warnings))))
  ///
  (verify-guards vl-stmt-lvaluecheck)
  (deffixequiv-mutual vl-stmt-lvaluecheck
    :hints(("Goal"
            :expand ((vl-stmt-lvaluecheck x warnings)
                     (vl-stmt-lvaluecheck (vl-stmt-fix x) warnings))))))

(def-vl-lvaluecheck
  :type vl-always
  :body (vl-stmt-lvaluecheck (vl-always->stmt x) warnings))

(def-vl-lvaluecheck
  :type vl-alwayslist
  :body
  (if (atom x)
      (ok)
    (b* ((warnings (vl-always-lvaluecheck (car x) warnings)))
        (vl-alwayslist-lvaluecheck (cdr x) warnings))))

(def-vl-lvaluecheck
  :type vl-initial
  :body (vl-stmt-lvaluecheck (vl-initial->stmt x) warnings))

(def-vl-lvaluecheck
  :type vl-initiallist
  :body
  (if (atom x)
      (ok)
    (b* ((warnings (vl-initial-lvaluecheck (car x) warnings)))
        (vl-initiallist-lvaluecheck (cdr x) warnings))))

(def-vl-lvaluecheck
  :type vl-fundecl
  :body (vl-stmt-lvaluecheck (vl-fundecl->body x) warnings))

(def-vl-lvaluecheck
  :type vl-fundecllist
  :body
  (if (atom x)
      (ok)
    (b* ((warnings (vl-fundecl-lvaluecheck (car x) warnings)))
        (vl-fundecllist-lvaluecheck (cdr x) warnings))))

(def-vl-lvaluecheck
  :type vl-taskdecl
  :body (vl-stmt-lvaluecheck (vl-taskdecl->body x) warnings))

(def-vl-lvaluecheck
  :type vl-taskdecllist
  :body
  (if (atom x)
      (ok)
    (b* ((warnings (vl-taskdecl-lvaluecheck (car x) warnings)))
        (vl-taskdecllist-lvaluecheck (cdr x) warnings))))


(define vl-module-lvaluecheck ((x vl-module-p))
  :returns (new-x vl-module-p "Perhaps extended with some warnings.")
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

(defprojection vl-modulelist-lvaluecheck (x)
  :guard (vl-modulelist-p x)
  :returns (new-x vl-modulelist-p)
  (vl-module-lvaluecheck x))

(define vl-design-lvaluecheck ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-lvaluecheck x.mods))))

