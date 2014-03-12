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
(include-book "xf-subst")
(include-book "../mlib/remove-bad")
(include-book "../mlib/print-warnings")
(include-book "../wf-ranges-resolved-p")
(include-book "../util/cwtime")
(local (include-book "../util/arithmetic"))
(local (include-book "../mlib/modname-sets"))
(local (include-book "../util/osets"))

(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))


(define vl-annotate-modules-with-warning ((x vl-modulelist-p)
                                          (warning vl-warning-p))
  ;; BOZO find me a home
  :parents (warnings)
  :short "Add a warning to each module in a list of modules."
  :returns (new-x vl-modulelist-p :hyp :fguard)
  (if (atom x)
      nil
    (cons (change-vl-module
           (car x)
           :warnings (cons warning (vl-module->warnings (car x))))
          (vl-annotate-modules-with-warning (cdr x) warning))))


(defxdoc unparameterization
  :parents (transforms)
  :short "Expand away modules with parameters."

  :long "<p>Unparameterization is a Verilog transformation which, given a set
of Verilog modules, is supposed to produce an equivalent, parameter-free set of
modules.</p>

<p>There are two kinds of parameter declarations, @('parameter') and
@('localparam'), examples of which are shown below.  Parameters have default
values, and their defaults can refer to other parameters in the module.</p>

@({
    module m (a, b, c) ;
      ...
      parameter size = 4 ;
      localparam twosize = 2 * size ;
      ...
    endmodule
})

<p>And a module which uses parameters can be instantiated like this:</p>

@({
    module uses_m (x y z) ;
      ...
      m #(6)        m_instance_1 (.a(x), .b(y), .c(z)) ; // size 6
      m #(.size(6)) m_instance_2 (.a(x), .b(y), .c(z)) ; // size 6
      m             m_instance_3 (.a(x), .b(y), .c(z)) ; // size 4
      ...
    endmodule
})

<p>Local parameters are just like parameters except that they cannot be
assigned to from outside the module.  They are not used at Centaur so we have
not tried to support them.  On the other hand, it does not seem like it would
be difficult to add support for them.</p>

<p>Verilog also includes a @('defparam') statement, which we do not currently
support, that can be used to override parameters in other modules.  If
supporting this is desired, we should first use a separate transform to
eliminate any uses of @('defparam'), then unparameterize as we do today.</p>

<p>The basic idea behind unparameterization is pretty simple.  Suppose we are
dealing with a parameterized module called @('plus'), which takes a single
parameter called @('size').  There may be several modules, say @('m1'),
@('m2'), and @('m3'), which contain instances of @('plus') with different
sizes, say @('8'), @('16'), and @('32').</p>

<p>Our general strategy is to eliminate @('plus') from our module list by
replacing it with three new modules, @('plus$size=8'), @('plus$size=16'), and
@('plus$size=32'), which are copies of @('plus') except that @('size') has been
replaced everywhere with @('8'), @('16'), or @('32') as suggested by their
names.  At the same time, we need to change the instances of @('plus')
throughout @('m1'), @('m2'), and @('m3') with appropriate instances of the new
modules.  Finally, once all of the instances of the generic @('plus') have been
done away with, we can safely remove @('plus') from our module list.</p>")

(local (xdoc::set-default-parents unparameterization))


; We extend the notion of a resolved expression to say an instantiation of a
; parameterized module (e.g., an instance of PLUS within M1, M2, and M3) is
; resolved when all of its parameter expressions (e.g., its choice of SIZE) are
; resolved expressions.

(define vl-namedarg-resolved-p ((x vl-namedarg-p))
  :parents (vl-expr-resolved-p)
  (and (vl-namedarg->expr x)
       (vl-expr-resolved-p (vl-namedarg->expr x)))
  ///
  (defthm vl-expr-resolved-p-of-vl-namedarg->expr-when-vl-namedarg-resolved-p
    (implies (vl-namedarg-resolved-p arg)
             (vl-expr-resolved-p (vl-namedarg->expr arg)))))

(deflist vl-namedarglist-resolved-p (x)
  (vl-namedarg-resolved-p x)
  :guard (vl-namedarglist-p x)
  :parents (vl-expr-resolved-p)
  :elementp-of-nil nil)

(define vl-plainarg-resolved-p ((x vl-plainarg-p))
  :parents (vl-expr-resolved-p)
  (and (vl-plainarg->expr x)
       (vl-expr-resolved-p (vl-plainarg->expr x)))
  ///
  (defthm vl-expr-resolved-p-of-vl-plainarg->expr-when-vl-plainarg-resolved-p
    (implies (vl-plainarg-resolved-p arg)
             (vl-expr-resolved-p (vl-plainarg->expr arg)))))

(deflist vl-plainarglist-resolved-p (x)
  (vl-plainarg-resolved-p x)
  :guard (vl-plainarglist-p x)
  :elementp-of-nil nil
  :parents (vl-expr-resolved-p))

(define vl-arguments-resolved-p ((x vl-arguments-p))
  :parents (vl-expr-resolved-p)
  (if (vl-arguments->namedp x)
      (vl-namedarglist-resolved-p (vl-arguments->args x))
    (vl-plainarglist-resolved-p (vl-arguments->args x))))

(define vl-modinst-resolvedparams-p ((x vl-modinst-p))
  :parents (unparameterization)
  :long "Are the parameter arguments for a module instance all resolved
expressions, in the sense of @(see vl-expr-resolved-p)?"
  (vl-arguments-resolved-p (vl-modinst->paramargs x)))

(deflist vl-modinstlist-resolvedparams-p (x)
  (vl-modinst-resolvedparams-p x)
  :guard (vl-modinstlist-p x)
  :elementp-of-nil t
  :parents (unparameterization))



(defsection vl-good-paramdecl-p
  :parents (unparameterization)
  :short "Parameters which are simple enough to unparameterize."

  :long "<p>In Verilog, parameter declarations can have a type, range, and
signedness, and the expression involved could be complex.  They can also be
introduced with @('localparam') instead of @('parameter').</p>

<p>But in practice, at Centaur, all of our parameter declarations look
something like this:</p>

@({
   parameter width = 1 ;
})

<p>That is, there is no type or range, they are not signed (well, the
expression shown above, @('1'), is a signed decimal constant, but the keyword
'signed' does not occur in the parameter declaration), they are never
localparams, and their default value is always a resolved expression.</p>

<p>Being pragmatic, we insist upon these restrictions and introduce the notion
of a \"good\" parameter declaration.  Eventually, we may wish to weaken these
limits so that more flexible paramter declarations are supported.</p>"

  (defwellformed vl-good-paramdecl-p (x)
    :guard (vl-paramdecl-p x)
    :body
    (@wf-progn
     (@wf-assert (eq (vl-paramdecl->type x) :vl-plain)
                 :vl-bad-paramdecl
                 "~l0: We only support plain parameter declarations, but ~s1 ~
                  has type ~s2."
                 (list (vl-paramdecl->loc x)
                       (vl-paramdecl->name x)
                       (vl-paramdecl->type x)))

     (@wf-assert (not (vl-paramdecl->range x))
                 :vl-bad-paramdecl
                 "~l0: We only support range-free parameter declarations, but ~
                  ~s1 has range ~s2."
                 (list (vl-paramdecl->loc x)
                       (vl-paramdecl->name x)
                       (vl-pps-range (vl-paramdecl->range x))))

     (@wf-assert (not (vl-paramdecl->localp x))
                 :vl-bad-paramdecl
                 "~l0: We only support non-local parameters, but ~s1 is local."
                 (list (vl-paramdecl->loc x)
                       (vl-paramdecl->name x)))

     (@wf-assert (vl-expr-resolved-p (vl-paramdecl->expr x))
                 :vl-bad-paramdecl
                 "~l0: We only support parameters with constant integer ~
                  defaults, but ~s1 has default value ~s2. (simp expr: ~s3)"
                 (list (vl-paramdecl->loc x)
                       (vl-paramdecl->name x)
                       (vl-pps-origexpr (vl-paramdecl->expr x))
                       (vl-pps-expr (vl-paramdecl->expr x)))))))

(defwellformed-list vl-good-paramdecllist-p-aux (x)
  :element vl-good-paramdecl-p
  :guard (vl-paramdecllist-p x))

(defsection vl-good-paramdecllist-p
  :parents (unparameterization)

  (defwellformed vl-good-paramdecllist-p (x)
    :guard (vl-paramdecllist-p x)
    :body
    (let ((names (vl-paramdecllist->names x)))
      (@wf-progn
       (@wf-assert (uniquep names)
                   :vl-bad-paramdecl
                   "Multiple declarations of parameters: ~&0."
                   (list names))
       (@wf-call vl-good-paramdecllist-p-aux x)))))

(defsection vl-good-paramdecllist-list-p
  :parents (unparameterization)

  (defwellformed-list vl-good-paramdecllist-list-p (x)
    :element vl-good-paramdecllist-p
    :guard (vl-paramdecllist-list-p x)))


(define vl-module-check-good-paramdecls
  :parents (unparameterization)
  :short "Cause a fatal warning unless all parameters in a module are simple
enough to unparameterize, e.g., as in @(see vl-good-paramdecl-p)."
  ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard)

  (b* (((vl-module x) x)
       ((mv okp warnings)
        (vl-good-paramdecllist-p-warn x.paramdecls x.warnings))
       (warnings (if okp
                     warnings
                   (fatal :type :vl-bad-paramdecls
                          :msg "Module ~m0 has unsupported parameter declarations."
                          :args (list x.name)))))
    (change-vl-module x :warnings warnings))
  ///
  (defthm vl-module->name-of-vl-module-check-good-paramdecls
    (equal (vl-module->name (vl-module-check-good-paramdecls x))
           (vl-module->name x))))

(defprojection vl-modulelist-check-good-paramdecls (x)
  (vl-module-check-good-paramdecls x)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p
  :parents (unparameterization)
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-check-good-paramdecls
     (equal (vl-modulelist->names (vl-modulelist-check-good-paramdecls x))
            (vl-modulelist->names x)))))

(define vl-design-check-good-paramdecls
  :short "Add fatal warnings to any modules with parameters that are too
          complicated."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-check-good-paramdecls x.mods))))

(define vl-good-paramdecllist-list-p-of-vl-modulelist->paramdecls
  :parents (unparameterization)
  :short "Simple fused operation.  We leave this enabled."
  ((x vl-modulelist-p))
  :enabled t
  (mbe :logic
       (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls x))
       :exec
       (if (consp x)
           (and (vl-good-paramdecllist-p (vl-module->paramdecls (car x)))
                (vl-good-paramdecllist-list-p-of-vl-modulelist->paramdecls (cdr x)))
         t)))


(define vl-modules-with-params
  :parents (unparameterization)
  :short "@(call vl-modules-with-params) gathers all modules within the module
list @('x') that have any parameters, and returns them as a new module list."
  ((mods vl-modulelist-p))
  :returns (mods-with-params vl-modulelist-p :hyp :fguard)
  (cond ((atom mods)
         nil)
        ((consp (vl-module->paramdecls (car mods)))
         (cons (car mods)
               (vl-modules-with-params (cdr mods))))
        (t
         (vl-modules-with-params (cdr mods))))
  ///
  (defthm subsetp-equal-of-vl-modules-with-params
    (subsetp-equal (vl-modules-with-params mods) mods))
  (defthm uniquep-of-vl-modulelist->names-of-vl-modules-with-params
    (implies (uniquep (vl-modulelist->names mods))
             (uniquep (vl-modulelist->names (vl-modules-with-params mods))))))


(define vl-delete-top-level-modules-with-params
  :parents (unparameterization)
  :short "Procedure for eliminating parameterized modules which are no longer used."
  ((mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :guard (vl-modulelist-complete-p mods mods)
  :returns (new-mods vl-modulelist-p :hyp :fguard)
  :long "<p>Once all occurrences of a parameterized module like @('plus') have
been replaced with instances of concrete modules like @('plus$size=16'), we
need to eliminate the generic @('plus') from the list of modules in order to
finally arrive at a list of modules which are parameter-free.  We do this with
@(call vl-delete-top-level-modules-with-params).</p>"

  (b* ((topnames   (vl-modulelist-toplevel mods))
       (topmods    (vl-fast-find-modules topnames mods modalist))
       (withparams (vl-modules-with-params topmods))
       (delmods    (vl-modulelist->names withparams)))
    (cw "Removing now-unnecessary modules: ~&0.~%" delmods)
    (vl-delete-modules delmods mods)))


(define vl-find-named-arg ((name stringp)
                           (args vl-namedarglist-p))
  :returns (arg (equal (vl-namedarg-p arg) (if arg t nil))
                :hyp (force (vl-namedarglist-p args)))
  (cond ((atom args)
         nil)
        ((equal (vl-namedarg->name (car args)) name)
         (car args))
        (t
         (vl-find-named-arg name (cdr args))))
  ///
  (defthm vl-expr-resolved-p-of-vl-find-named-arg
    (implies (and (force (vl-namedarglist-p args))
                  (force (vl-namedarglist-resolved-p args)))
             (equal (vl-namedarg-resolved-p (vl-find-named-arg name args))
                    (if (vl-find-named-arg name args)
                        t
                      nil)))))


(define vl-match-namedargs-with-paramdecls
  :parents (vl-match-paramargs-with-decls)
  :short "Matches formals and actuals for named args."
  ((args     vl-namedarglist-p)
   (decls    (and (vl-paramdecllist-p decls)
                  (vl-good-paramdecllist-p decls)))
   (warnings vl-warninglist-p)
   (inst     vl-modinst-p))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (sigma    alistp))

  :long "<p>We build a @(see vl-sigma-p) which maps the formals (the parameter
declarations) to the actuals, for a list of named parameter arguments.  That
is, given module @('mod') with parameters @('p1'), @('p2'), ..., and an
instance of @('mod') such as:</p>

@({
    mod #(.p1(5), .p2(8), ...) my_inst (...)
})

<p>We construct a @(see vl-sigma-p) mapping @('p1') to @('5'), @('p2') to
@('8'), and so on.</p>

<p>We recur over the declarations, rather than the formals, because the user is
allowed to omit formals and we want to give those parameters their default
values.</p>

<p>This function may fail if the actuals are blank, and in such a case an
updated list of warnings is generated.  The @('inst') argument is only used to
provide the context for error reporting, and should be the @(see vl-modinst-p)
that this mapping is being carried out for.</p>"
  :verify-guards nil
  (b* (((when (atom decls))
        (mv t (ok) nil))
       (thisdecl  (car decls))
       (name      (vl-paramdecl->name thisdecl))
       (default   (vl-paramdecl->expr thisdecl))
       (lookup    (vl-find-named-arg name args))
       ((when (and lookup
                   (not (vl-namedarg->expr lookup))))
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: \"blank\" binding for parameter ~s1."
                   :args (list inst name))
            nil))
       (value (if lookup
                  (vl-namedarg->expr lookup)
                default))
       ((mv successp warnings sigma)
        (vl-match-namedargs-with-paramdecls args (cdr decls) warnings inst)))
    (mv successp
        warnings
        (acons name value sigma)))
  ///
  (defthm alist-keys-of-vl-match-namedargs-with-paramdecls
    (implies (mv-nth 0 (vl-match-namedargs-with-paramdecls args decls warnings inst))
             (equal (alist-keys (mv-nth 2 (vl-match-namedargs-with-paramdecls args decls warnings inst)))
                    (vl-paramdecllist->names decls))))

  (defthm vl-exprlist-p-of-alist-vals-of-vl-match-namedargs-with-paramdecls
    (implies (and (force (vl-namedarglist-p args))
                  (force (vl-paramdecllist-p decls)))
             (vl-exprlist-p (alist-vals (mv-nth 2 (vl-match-namedargs-with-paramdecls args decls warnings inst))))))

  (defthm vl-exprlist-resolved-p-of-alist-vals-of-vl-match-namedargs-with-paramdecls
    (implies (and (force (vl-namedarglist-p args))
                  (force (vl-paramdecllist-p decls))
                  (force (vl-namedarglist-resolved-p args))
                  (force (vl-good-paramdecllist-p decls)))
             (vl-exprlist-resolved-p
              (alist-vals
               (mv-nth 2
                (vl-match-namedargs-with-paramdecls args decls warnings inst)))))
    :hints(("Goal" :in-theory (enable vl-good-paramdecllist-p
                                      vl-good-paramdecllist-p-aux
                                      vl-good-paramdecl-p))))

  (verify-guards vl-match-namedargs-with-paramdecls
                 :hints(("Goal" :in-theory (enable vl-good-paramdecllist-p)))))



(define vl-match-plainargs-with-paramdecls
  :parents (vl-match-paramargs-with-decls)
  :short "Matches formals and actuals for plain args."

  ((args     vl-plainarglist-p)
   (decls    (and (vl-paramdecllist-p decls)
                  (vl-good-paramdecllist-p decls)))
   (warnings vl-warninglist-p)
   (inst     vl-modinst-p))
  :guard (<= (len args) (len decls))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (sigma    alistp))

  :long "<p>This is much like @(see vl-match-namedargs-with-paramdecls), but
for plain argument lists.  We recur over decls, because Verilog permits the
argument list to be partial.  That is, if a module had three parameters, and
only one param argument is provided to it, then the other two get the default
values.</p>"
  :verify-guards nil
  (b* (((when (atom decls))
        (mv t (ok) nil))
       (name    (vl-paramdecl->name (car decls)))
         (default (vl-paramdecl->expr (car decls)))
         ((when (and (consp args)
                     (not (vl-plainarg->expr (car args)))))
          (mv nil
              (fatal :type :vl-bad-instance
                     :msg "~a0: \"blank\" binding for parameter ~s3."
                     :args (list inst name))
              nil))
         (value (if (atom args)
                    default
                  (vl-plainarg->expr (car args))))
         ((mv successp warnings sigma)
          (vl-match-plainargs-with-paramdecls (if (atom args) nil (cdr args))
                                              (cdr decls) warnings inst)))
      (mv successp
          warnings
          (acons name value sigma)))
  ///
  (defthm alist-keys-of-vl-match-plainargs-with-paramdecls
    (implies (mv-nth 0 (vl-match-plainargs-with-paramdecls args decls warnings inst))
             (equal (alist-keys (mv-nth 2 (vl-match-plainargs-with-paramdecls args decls warnings inst)))
                    (vl-paramdecllist->names decls))))

  (defthm vl-exprlist-p-of-alist-vals-of-vl-match-plainargs-with-paramdecls
    (implies (and (force (vl-plainarglist-p args))
                  (force (vl-paramdecllist-p decls))
                  (force (<= (len args) (len decls))))
             (vl-exprlist-p
              (alist-vals
               (mv-nth 2
                (vl-match-plainargs-with-paramdecls args decls warnings inst))))))

  (defthm vl-exprlist-resolved-p-of-alist-vals-of-vl-match-plainargs-with-paramdecls
    (implies (and (force (vl-plainarglist-p args))
                  (force (vl-paramdecllist-p decls))
                  (force (vl-good-paramdecllist-p decls))
                  (force (vl-plainarglist-resolved-p args))
                  (force (<= (len args) (len decls))))
             (vl-exprlist-resolved-p
              (alist-vals
               (mv-nth 2
                (vl-match-plainargs-with-paramdecls args decls warnings inst)))))
    :hints(("Goal" :in-theory (enable vl-good-paramdecllist-p
                                      vl-good-paramdecllist-p-aux
                                      vl-good-paramdecl-p))))

  (verify-guards vl-match-plainargs-with-paramdecls
                 :hints(("Goal" :in-theory (enable vl-good-paramdecllist-p)))))



(define vl-match-paramargs-with-decls
  :parents (unparameterization)
  :short "Build a @(see vl-sigma-p) mapping parameter formals to actuals."

  ((inst vl-modinst-p)
   (mod  vl-module-p)
   (warnings vl-warninglist-p))
  :guard (and (vl-good-paramdecllist-p (vl-module->paramdecls mod))
              (equal (vl-modinst->modname inst) (vl-module->name mod)))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (sigma alistp))

  :long "<p>A basic operation in unparameterization is being able to pair up
the <i>formals</i> and <i>actuals</i>.  That is, the module declares that it
has a bunch of parameters (\"formals\"), and each instance of the module gives
some expressions (\"actuals\") to be substituted in for these formals.</p>

<p>We are given a module and an instance of that module.  We might fail for
various reasons, e.g., maybe we try to instantiate a missing parameter, or use
a \"blank\" value, etc.  In such a case, @('successp') is @('nil') and some
new, fatal @(see warnings) will be added to @('warnings') to form
@('warnings-prime').</p>

<p>On success, @('sigma') will be a @(see vl-sigma-p) that maps the names of
the parameters to their values.  This can then be substituted (@(see
substitution)) into the module being instantiated to form an unparameterized
version of the module.</p>

<p>The pairing is a little tricky because the argument lists can be given in
either a named or an ordered format, so we write separate functions to handle
these cases.</p>"

  (b* ((paramdecls (vl-module->paramdecls mod))
       (paramargs  (vl-modinst->paramargs inst))
       (namedp     (vl-arguments->namedp paramargs))
       (args       (vl-arguments->args paramargs))
       ((when namedp)
        (let ((argnames   (vl-namedarglist->names args))
              (paramnames (vl-paramdecllist->names paramdecls)))
          (if (not (subsetp-equal argnames paramnames))
              (b* ((bad (set-difference-equal argnames paramnames)))
                (mv nil
                    (fatal :type :vl-bad-instance
                           :msg "~a0 mentions non-existent parameter~s1 ~&2."
                           :args (list inst (if (vl-plural-p bad) "s" "") bad))
                    nil))
            (vl-match-namedargs-with-paramdecls args paramdecls warnings inst))))
       ((unless (<= (len args) (len paramdecls)))
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0 provides ~x1 parameters where at most ~x2 are permitted."
                   :args (list inst (len args) (len paramdecls)))
            nil)))
    (vl-match-plainargs-with-paramdecls args paramdecls warnings inst))
  ///
  (defthm alist-keys-of-vl-match-paramargs-with-decls
    (implies (mv-nth 0 (vl-match-paramargs-with-decls inst mod warnings))
             (equal (alist-keys (mv-nth 2 (vl-match-paramargs-with-decls inst mod warnings)))
                    (vl-paramdecllist->names (vl-module->paramdecls mod)))))

  (defthm vl-exprlist-p-of-vl-match-paramargs-with-decls
    (implies (and (mv-nth 0 (vl-match-paramargs-with-decls inst mod warnings))
                  (force (vl-module-p mod))
                  (force (vl-modinst-p inst)))
             (vl-exprlist-p
              (alist-vals
               (mv-nth 2
                (vl-match-paramargs-with-decls inst mod warnings))))))

  (defthm vl-exprlist-resolved-p-of-vl-match-paramargs-with-decls
    (implies (and (mv-nth 0 (vl-match-paramargs-with-decls inst mod warnings))
                  (force (vl-good-paramdecllist-p (vl-module->paramdecls mod)))
                  (force (vl-arguments-resolved-p (vl-modinst->paramargs inst)))
                  (force (vl-module-p mod))
                  (force (vl-modinst-p inst)))
             (vl-exprlist-resolved-p
              (alist-vals
               (mv-nth 2
                (vl-match-paramargs-with-decls inst mod warnings)))))
    :hints(("Goal" :in-theory (enable vl-arguments-resolved-p))))

  (verify-guards vl-match-paramargs-with-decls)

  (local (defthm lemma
           (implies (alistp x)
                    (equal (vl-sigma-p x)
                           (and (string-listp (alist-keys x))
                                (vl-exprlist-p (alist-vals x)))))
           :hints(("Goal" :in-theory (enable alistp vl-sigma-p)))))

  (defthm vl-sigma-p-of-vl-match-paramargs-with-decls
    (implies (and (mv-nth 0 (vl-match-paramargs-with-decls inst mod warnings))
                  (force (vl-module-p mod))
                  (force (vl-modinst-p inst)))
             (vl-sigma-p (mv-nth 2 (vl-match-paramargs-with-decls inst mod warnings))))))


(define vl-unparam-newname-aux
  :parents (vl-unparam-newname)
  ((origname stringp)
   (sigma    vl-sigma-p))
  :guard (vl-exprlist-resolved-p (alist-vals sigma))
  :returns (new-name stringp :rule-classes :type-prescription)
  :verify-guards t
  (b* (((when (atom sigma))
        (string-fix origname))
       (param-name    (caar sigma))
       (param-val     (vl-resolved->val (cdar sigma)))
       (param-val-str (natstr param-val)))
    (vl-unparam-newname-aux
     (cat origname "$" param-name "=" param-val-str)
     (cdr sigma))))

(define vl-unparam-newname
  :parents (unparameterization)
  :short "Generate a new name for an unparameterized module."
  ((origname stringp    "Original name of the module, e.g., @('my_adder').")
   (sigma    vl-sigma-p "Binds parameters to values, e.g., @('size <-- 5')."))
  :guard (vl-exprlist-resolved-p (alist-vals sigma))
  :returns (new-name stringp :rule-classes :type-prescription
                     "New, mangled name, e.g., @('my_adder$size=5').")
  :long "<p>This is a dumb but probably sufficient way to generate new names.
Note that we explicitly check (later on) that no name conflicts are
introduced.</p>"

  (progn$
   ;; Extralogical check: there really shouldn't be duplicates.
   (or (uniquep (alist-keys sigma))
       (raise "Programming error: duplicate keys in sigma.  Origname is ~s0, ~
               duplicated keys are ~&1, sigma is ~x2."
              origname (duplicated-members (alist-keys sigma)) sigma))

   ;; We previously shrunk and sorted the sigma.  This was fine but silly since
   ;; the parameter names for any reasonable module should be unique and, at any
   ;; rate, we just checked that they were in the above extralogical check.
   ;;
   ;; I no longer want to do this sorting because other tools, like Synopsys
   ;; Design Compiler, seem to generate the names of their unparameterized modules
   ;; just using the parameter declaration order.  So, by not sorting the names,
   ;; we can come up with names that more closely agree with these other tools.
   ;;
   ;; Implicitly here, are assuming that SIGMA comes in with its keys in the same
   ;; order as the module's parameter declarations.

   (hons-copy (vl-unparam-newname-aux origname sigma))))

(define vl-unsafe-to-unparameterize-modules
  :parents (unparameterization)
  :short "Gathers the names of modules that might not be safe to
unparameterize, and returns them as fast alist."
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods)))))
  :returns (fal alistp)
  :long "<p>During our unparameterization process, we want to ensure that at no
point are conflicting versions of any module ever generated.  However, if in
every pass we blindly try to unparameterize every module instance whose
parameters are resolved, we can violate this property.</p>

<p>Illustrating the problem takes some setup.  In particular, suppose we have
the following modules hierarchy:</p>

@({
outer
 |
 |------ foo #(6) inst1 ;
 |        |
 |        mid #(width) foo_mid ;
 |         |
 |         bot #(width) mid_bot ;
 |
 |------ mid #(6) inst2 ;
          |
          bot #(width) mid_bot ;
})

<p>If we blindly start unparameterizing every module we see, then after one
round of unparameterization we have:</p>

@({
outer
 |
 |------ foo$size=6 inst1 ;
 |        |
 |        mid #(6) foo_mid ;
 |         |
 |         bot #(width) mid_bot ;
 |
 |------ mid$size=6 inst2 ;
          |
          bot #(6) mid_bot ;
})

<p>Then, in the next round:</p>

@({
outer
 |
 |------ foo$size=6 inst1 ;
 |        |
 |        mid$size=6 foo_mid ;
 |         |
 |         bot #(6) mid_bot ;
 |
 |------ mid$size=6 inst2 ;
          |
          bot$size=6 mid_bot ;
})

<p>And now we're hosed, because we now have two different versions of
@('mid$size=6'), one where the @('bot') instance has already been
unparameterized, and one where it has not.  These eventually will converge, but
we think it seems better to never let them diverge in the first place.</p>

<p>Toward this end, we say that certain modules are unsafe to unparameterize.
In particular, we don't want to unparameterize instances of any module @('foo')
that is ever instantiated by another parameterized module @('bar').  In the
above example, this means we want to consider both @('mid') and @('bot') to be
initially off-limits, and only unparameterize @('foo') in the first round.
After that, mid will become okay to unparameterize, etc.</p>"

  (b* ((mods          (mergesort mods))
       (modalist      (vl-modalist mods))
       (parameterized (vl-modules-with-params mods))
       (instanced     (vl-modulelist-everinstanced parameterized))
       ;; It might be that instanced might be enough, but it seems
       ;; safer to also exclude all transitively instanced modules.
       (necessary     (vl-necessary-modules instanced mods modalist)))
    (make-lookup-alist necessary)))

(define hfind-bound-key (keys alist)
  :parents (vl-maybe-unparam-inst)
  (declare (xargs :guard t))
  (if (atom keys)
      nil
    (or (hons-get (car keys) alist)
        (hfind-bound-key (cdr keys) alist))))

(define vl-maybe-unparam-inst
  :parents (unparameterization)
  :short "Try to unparameterize a single module instance."

  ((inst     vl-modinst-p "Instance of some module to unparameterize.")
   (unsafe   alistp "Fast alist from @(see vl-unsafe-to-unparameterize-modules);
                     it's not ok to unparameterize instances of these modules.")
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (warnings vl-warninglist-p))
  :guard (and (vl-has-module (vl-modinst->modname inst) mods)
              (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (insts    vl-modinst-p    :hyp :fguard)
      (new-mods vl-modulelist-p :hyp :fguard))

  :verify-guards nil

  :long "<p>We assume that all of the modules in mods have \"good\" parameter
declaration lists (in the sense of @(see vl-good-paramdecl-p)), and so as a
consequence we know that this also holds for whichever particular module
@('inst') refers to.</p>

<p>If the module being instantiated has no parameters, or when we are unable to
unparameterize because some parameter expression has not yet been resolved,
this function is not very interesting.  In such a case it returns successfully
without adding any warnings or new modules, and keeps @('inst') unchanged.</p>

<p>The interesting case is when the module has parameters, and all of the
parameter arguments have been resolved.  For instance, suppose we are dealing
with an instance of the module @('plus') and the @('size') parameter has been
resolved to @('16').  In this case,</p>

<ul>

 <li>@('inst-prime') is an \"updated\" copy of @('inst') which, instead of
pointing to @('plus'), points to the new, parameter-free module named
@('plus$size=16'), and </li>

 <li>@('new-mods') is (typically) a singleton list containing one new,
parameter-free module, @('plus$size=16'), which has been derived from @('plus')
by replacing all occurrences of @('size') with @('16').</li>

</ul>"

; BOZO Performance.  Consider building the substitutions (above) with hons, and
; then memoizing vl-module-subst?  This way, as we run into multiple instances
; of a module that have the same parameters, we wouldn't have to
; re-unparameterize it.

  (b* ((modname (vl-modinst->modname inst))
       (mod     (vl-fast-find-module modname mods modalist))
       ((when (atom (vl-module->paramdecls mod)))
        ;; No parameters -- no changes are necessary.
        (mv t (ok) inst nil))

       ((when (not (vl-modinst-resolvedparams-p inst)))
        ;; Some parameter expressions in this instance aren't resolved yet, so we
        ;; can't do the unparameterization yet.
        (mv t (ok) inst nil))

       ((when (hons-get modname unsafe))
        ;; Not safe to unparameterize this yet.  Don't do anything.
        (mv t (ok) inst nil))

       ((mv successp warnings sigma)
        (vl-match-paramargs-with-decls inst mod warnings))
       ((with-fast sigma))
       ((unless successp)
        (mv nil warnings inst nil))

       ;; Check function decls for shadowing names...
       (fundecl-clash (hfind-bound-key
                       (vl-fundecllist->namespaces
                        (vl-module->fundecls mod))
                       sigma))
       ((when fundecl-clash)
        (b* ((warning (make-vl-warning
                       :type :vl-name-clash
                       :msg "A function declares a name that is already used ~
                             as a parameter in its parent module: ~x0"
                       :args (list (car fundecl-clash))
                       :fatalp nil
                       :fn 'vl-maybe-unparam-inst)))
          (mv nil (cons warning warnings) inst nil)))

       ;; Horrible stupid thing that never worked
       ;; ((when (equal modname "VL_N_BIT_ONEHOT"))
       ;;  ;; Special case for one-hot detection.
       ;;  (b* ((width (cdr (assoc-equal "width" sigma)))
       ;;       (val   (if (and width
       ;;                       (vl-expr-resolved-p width)
       ;;                       (posp (vl-resolved->val width)))
       ;;                  (vl-resolved->val width)
       ;;                (prog2$ (er hard? 'vl-maybe-unparam-inst
       ;;                            "Bad width for VL_N_BIT_ONEHOT: ~x0"
       ;;                            width)
       ;;                        1)))
       ;;       (newmods (vl-make-n-bit-onehot val))
       ;;       (newname (vl-module->name (car newmods)))
       ;;       (newinst (change-vl-modinst inst
       ;;                                   :modname newname
       ;;                                   :paramargs (vl-arguments nil nil))))
       ;;    (mv t warnings newinst newmods)))

       ;; Else, ordinary case for any other module.
       (newname (vl-unparam-newname modname sigma))
       (newmod  (change-vl-module (vl-module-subst mod sigma)
                                  :name newname
                                  :paramdecls nil))
       (newinst (change-vl-modinst inst
                                   :modname newname
                                   :paramargs (vl-arguments nil nil))))
    ;; We always generate the new module, even if it's already been
    ;; generated before.  Then, at the end, as a sanity check, we check
    ;; to ensure that all modules of the same name are equal.
    (mv t warnings newinst (list newmod)))

  :prepwork
  ((local (defthm lemma
            (implies (and (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))
                          (member a mods))
                     (vl-good-paramdecllist-p (vl-module->paramdecls a)))
            :hints(("Goal" :induct (len mods))))))
  ///
  (verify-guards vl-maybe-unparam-inst
    :hints(("Goal" :in-theory (enable vl-modinst-resolvedparams-p))))

  (defmvtypes vl-maybe-unparam-inst (booleanp nil nil true-listp nil)))


(define vl-maybe-unparam-instlist
  :parents (unparameterization)
  :short "Extension of @(see vl-maybe-unparam-inst) to a list of instances."

  ((insts    vl-modinstlist-p)
   (unsafe   alistp)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (warnings vl-warninglist-p))
  :guard
  (and (vl-has-modules (vl-modinstlist->modnames insts) mods)
       (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (new-insts vl-modinstlist-p :hyp :fguard)
      (new-mods  vl-modulelist-p :hyp :fguard))
  (b* (((when (atom insts))
        (mv t (ok) nil nil))
       ((mv successp1 warnings car-prime car-newmods)
        (vl-maybe-unparam-inst (car insts) unsafe mods modalist warnings))
       ((mv successp2 warnings cdr-prime cdr-newmods)
        (vl-maybe-unparam-instlist (cdr insts) unsafe mods modalist warnings)))
    (mv (and successp1 successp2)
        warnings
        (cons car-prime cdr-prime)
        (append car-newmods cdr-newmods)))
  ///
  (defmvtypes vl-maybe-unparam-instlist (booleanp nil true-listp true-listp)))


(define vl-unparameterize-module
  :parents (unparameterization)
  :short "Extension of @(see vl-maybe-unparam-inst) to a module."

  ((mod      vl-module-p)
   (unsafe   alistp)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))

  :guard (and (vl-module-complete-p mod mods)
              (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))

  :returns (mv (successp booleanp :rule-classes :type-prescription
                         "<b>NOTE</b> Success does <b>NOT</b> mean that the instances
                          in new-mod are parameter-free.  It only says that there
                          were no errors during the course of unparameterization
                          (e.g., we didn't try to do something silly like instantiate
                          a missing parameter).")
               (new-mod vl-module-p :hyp :fguard)
               (new-mods vl-modulelist-p :hyp :fguard))

  :long "<p>The resulting @('new-mod') can still contain parameters if the
\"actuals\" have not yet been resolved.  This can happen, e.g., in the case of
a module which itself has parameters that it uses in order to instantiate its
submodules.  For example, given:</p>

@({
  module whatever ( a, b, c, d );
    parameter size = 1;
    ...;
    submodule #(size) inst1 (a, b);
    submodule #(size) inst2 (c, d);
  endmodule
})

<p>If we try to unparameterize @('whatever'), we will not fail, but the
resulting @('new-mod') will be unchanged.  It is not until we have
unparameterized the particular instances of @('whatever') and arrived at a
module like:</p>

@({
  module \\whatever$size=2 (a, b, c, d) ;
    ...;
    submodule #(2) inst1 (a, b);
    submodule #(2) inst2 (c, d);
  endmodule
})

<p>that we will be able to actually produce a parameter-free @('new-mod').</p>

<p>When there is an error, the resulting @('new-mod') will have been annotated
with some warnings explaining the problem.  However, its instances will not be
changed.  Such modules will be eliminated.</p>"

  (b* ((insts    (vl-module->modinsts mod))
       (warnings (vl-module->warnings mod))

       ((mv successp warnings insts-prime new-mods)
        (vl-maybe-unparam-instlist insts unsafe mods modalist warnings))

       (mod-prime (if successp
                      (change-vl-module mod
                                        :warnings warnings
                                        :modinsts insts-prime)
                    (change-vl-module mod :warnings warnings))))
    (if (not successp)
        (mv nil mod-prime nil)
      (mv t mod-prime new-mods)))

  ///
  (defmvtypes vl-unparameterize-module (booleanp nil true-listp)))


(define vl-unparameterize-pass-aux
  :parents (unparameterization)
  :short "Extension of @(see vl-maybe-unparam-inst) to a module list."

  ((x        vl-modulelist-p)
   (unsafe   alistp)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods))))
  :guard (and (vl-modulelist-complete-p x mods)
              (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))
  :returns
  (mv (success-mods vl-modulelist-p :hyp :fguard
                    "Modules we unparameterized successfully.")
      (fail-mods    vl-modulelist-p :hyp :fguard
                    "Modules we failed to unparameterize.")
      (new-mods     vl-modulelist-p :hyp :fguard
                    "New modules produced by unparameterization, e.g.,
                     @('my_adder$width=5')."))

  :long "<p>This is almost a full pass of unparameterization, except that it
doesn't do much in the way of error checking and throwing away bad modules.  We
try to apply @(see vl-unparameterize-module) to every module in the list.</p>"

  (b* (((when (atom x))
        (mv nil nil nil))
       ((mv car-successp car-prime car-newmods)
        (vl-unparameterize-module (car x) unsafe mods modalist))
       ((mv cdr-successes cdr-fails cdr-newmods)
        (vl-unparameterize-pass-aux (cdr x) unsafe mods modalist))
       ((when car-successp)
        (mv (cons car-prime cdr-successes)
            cdr-fails
            (append car-newmods cdr-newmods))))
    (mv cdr-successes
        (cons car-prime cdr-fails)
        (append car-newmods cdr-newmods)))
  ///
  (defmvtypes vl-unparameterize-pass-aux (true-listp true-listp true-listp)))



(define vl-find-modules-alt ((names string-listp)
                             (x     vl-modulelist-p))
  :returns (new-x vl-modulelist-p :hyp (force (vl-modulelist-p x)))
  (cond ((atom x)
         nil)
        ((member-equal (vl-module->name (car x)) names)
         (cons (car x)
               (vl-find-modules-alt names (cdr x))))
        (t
         (vl-find-modules-alt names (cdr x)))))

(define vl-unparameterize-pass
  :parents (unparameterization)
  :short "One full pass of unparameterization over a module list."
  ((mods vl-modulelist-p))
  :guard
  (and (uniquep (vl-modulelist->names mods))
       (vl-modulelist-complete-p mods mods)
       (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))
  :returns
  (mv (success-mods vl-modulelist-p :hyp :fguard)
      (fail-mods    vl-modulelist-p :hyp :fguard))
  :long "<p>We perform one full pass of unparameterization.  This involves</p>

<ul>
<li>Determining which modules are safe to unparameterize,</li>
<li>Applying @(see vl-unparameterize-pass-aux) to do most of the work,</li>
<li>Eliminating any remaining top level modules with parameters,</li>
<li>Propagating any errors via @(see vl-remove-bad-modules), and</li>
<li>Ensuring that we did not introduce any conflicting module definitions
    or incompleteness.</li>
</ul>

<p>Some day we might try to prove that this incompleteness check is
unnecessary.</p>"

  (b* ( ;(-                 (cw "; Starting unparameterize pass. ~x0 mods.~%" (len mods)))
       (modalist          (vl-modalist mods))
       (unsafe            (cwtime (vl-unsafe-to-unparameterize-modules mods)
                                  :mintime 1/3
                                  :name determine-safe-modules))
;(-                 (cw "; ~x0 modules are not safe to unparameterize yet: ~&1.~%"
;                       (len unsafe)
;                       (alist-keys unsafe)))
       ((mv good bad new) (vl-unparameterize-pass-aux mods unsafe mods modalist))
       (-                 (flush-hons-get-hash-table-link unsafe))
       (-                 (flush-hons-get-hash-table-link modalist))
       (badnames          (vl-modulelist->names bad))
       (merged            (mergesort (append good new)))

;(-                 (cw "; After vl-unparameterize-pass-aux: ~
;                          ~x0 good, ~x1 bad, ~x2 new mods; ~x3 merged.~%"
;                       (len good) (len bad) (len new) (len merged)))


       ((unless (uniquep (vl-modulelist->names merged)))

; At this point, if there are any bad modules, we want to throw them out, and
; we also want to remove from merged any modules that depend upon them.
;
; We have a good function to do this, namely vl-remove-bad-modules.  However,
; vl-remove-bad-modules requires that the list of modules we give it is a set
; that has unique names, which is actually important to knowing whether or not
; a module should actually be deleted.
;
; So, the question on the table is, do we know that the modules in merged have
; unique names?  I really, really hope this is the case.  But I do not have a
; proof of it yet.  Instead, I just explicitly check for it here.
;
; My response to this error is probably too severe.  If there are conflicting
; modules, it might make sense to just throw them out, and similarly to throw
; out anything that depends on them.  But for now, I'm just throwing away ALL
; MODULES since it is easier.  I'm sure that some day in the future I'll have
; to come and fix this in a hurry.  Such as life.

        (b* ((dupe-names (duplicated-members (vl-modulelist->names merged)))
             (dupe-mods  (vl-find-modules-alt dupe-names merged))
             (warning
              (make-vl-warning
               :type :vl-programming-error
               :msg "Generated modules do not have unique names.  ~
                       Conflicting modules: ~&0. Abandoning hope and throwing ~
                       away all modules.  Conflicting definitions: ~%~% ~s1"
               :args (list dupe-names (vl-pps-modulelist dupe-mods))
               :fn 'vl-unparameterize-pass))
             (- (vl-cw-ps-seq (vl-print-warning warning)))
             (merged-prime
              (vl-annotate-modules-with-warning merged warning)))
          (mv nil (append merged-prime bad))))

       ((mv survivors victims)
        (vl-remove-bad-modules badnames merged))

       (bad
        (append victims bad))

       (modalist
        (vl-modalist survivors))

       ((unless (vl-fast-modulelist-complete-p survivors survivors modalist))

; We want to make sure that the list of survivors is complete.  It would be
; great to some day prove this is the case, but for now we'll just explicitly
; check for it.  If this is violated, as before I'll throw out all modules.  It
; would arguably be better to just throw out whatever depends on these modules,
; but I really don't expect this case to happen.

        (b* ((warning
              (make-vl-warning
               :type :vl-programming-error
               :msg "Expected resulting modules to be complete, but the ~
                     following modules are missing: ~&0.  Abandoning hope and ~
                     throwing away all modules."
               :args (list (vl-modulelist-missing survivors))
               :fn 'vl-unparameterize-pass))
             (- (cw "~f0~%" (with-local-ps (vl-print-warning warning))))
             (survivors-prime
              (vl-annotate-modules-with-warning survivors warning)))
          (mv nil (append survivors-prime bad))))

; At this point, everything is looking good.  We can now eliminate any top
; level modules with parameters, since they are no longer necessary.

       (survivors (vl-delete-top-level-modules-with-params survivors modalist))
       (-         (flush-hons-get-hash-table-link modalist))



; We now run some final sanity checks.  Some day we should prove these never
; happen.  For now, these are needed to make our guards happy.

       ((unless (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls survivors)))
        (b* ((warning
              (make-vl-warning
               :type :vl-programming-error
               :msg "Expected resulting modules to have good parameter decls. ~
                     Abandoing hope, throwing away all modules."
               :fn 'vl-unparameterize-pass))
             (- (cw "~f0~%" (with-local-ps (vl-print-warning warning))))
             (survivors-prime
              (vl-annotate-modules-with-warning survivors warning)))
          (mv nil (append survivors-prime bad))))

       ((unless (vl-modulelist-complete-p survivors survivors))
        (b* ((warning
              (make-vl-warning
               :type :vl-programming-error
               :msg "Deleting top level modules with parameters caused ~
                     incompleteness??  Jared thinks this is impossible.  ~
                     Missing modules: ~&0."
               :args (list (vl-modulelist-missing survivors))
               :fn 'vl-unparameterize-pass))
             (- (cw "~f0~%" (with-local-ps (vl-print-warning warning))))
             (survivors-prime
              (vl-annotate-modules-with-warning survivors warning)))
          (mv nil (append survivors-prime bad))))

       ((unless (uniquep (vl-modulelist->names survivors)))
        (b* ((warning
              (make-vl-warning
               :type :vl-programming-error
               :msg "Modules are not unique after unparam pass?? Conflicting ~
                     module names: ~&0."
               :args (list (duplicated-members (vl-modulelist->names survivors)))
               :fn 'vl-unparameterize-pass))
             (- (cw "~f0~%" (with-local-ps (vl-print-warning warning))))
             (survivors-prime
              (vl-annotate-modules-with-warning survivors warning)))
          (mv nil (append survivors-prime bad)))))

    (mv survivors bad))

  ///
  (defmvtypes vl-unparameterize-pass (true-listp true-listp))

  (local (in-theory (enable vl-unparameterize-pass)))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-unparameterize-pass-0
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (vl-modulelist-complete-p mods mods))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (no-duplicatesp-equal (vl-modulelist->names (mv-nth 0 (vl-unparameterize-pass mods))))))

  (defthm vl-modulelist-complete-p-of-vl-unparameterize-pass-0
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (vl-modulelist-complete-p mods mods))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-complete-p (mv-nth 0 (vl-unparameterize-pass mods))
                                       (mv-nth 0 (vl-unparameterize-pass mods)))))

  (defthm vl-good-paramdecllist-list-p-of-vl-modulelist->paramdecls-of-vl-unparameterize-pass-0
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (vl-modulelist-complete-p mods mods))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-good-paramdecllist-list-p
              (vl-modulelist->paramdecls
               (mv-nth 0 (vl-unparameterize-pass mods)))))))


(define vl-handle-unparam-fail-aux
  :short "Annotate each module in mods with a warning saying we failed to
          unparameterize it."
  ((mods      vl-modulelist-p)
   (bad-names string-listp))
  :returns (new-mods vl-modulelist-p :hyp :fguard)
  (b* (((when (atom mods))
        nil)
       ((unless (member-equal (vl-module->name (car mods)) bad-names))
        (cons (car mods) (vl-handle-unparam-fail-aux (cdr mods) bad-names)))
       (warning (make-vl-warning
                 :type :vl-unparameterize-fail
                 :msg "Unable to eliminate remaining parameters, ~&0."
                 :args (list (vl-paramdecllist->names
                              (vl-module->paramdecls (car mods))))
                 :fatalp t
                 :fn 'vl-handle-unparam-fail)))
    (cons (change-vl-module
           (car mods)
           :warnings (cons warning (vl-module->warnings (car mods))))
          (vl-handle-unparam-fail-aux (cdr mods) bad-names)))
  ///
  (defthm vl-modulelist->names-of-vl-handle-unparam-fail-aux
    (equal (vl-modulelist->names (vl-handle-unparam-fail-aux mods bad-names))
           (vl-modulelist->names mods))))

(define vl-handle-unparam-fail
  :short "Throw away all modules that still have parameters and all modules
          that depend on them."
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods)))))
  :returns
  (mv (survivors vl-modulelist-p :hyp (force (vl-modulelist-p mods)))
      (victims   vl-modulelist-p :hyp (force (vl-modulelist-p mods))))
  (b* ((withparams (vl-modules-with-params mods))
       (bad-names  (vl-modulelist->names withparams))
       (mods       (vl-handle-unparam-fail-aux mods bad-names))
       ((mv survivors victims)
        (vl-remove-bad-modules bad-names mods)))
    (mv survivors victims))
  ///
  (defmvtypes vl-handle-unparam-fail (true-listp true-listp))
  (defthm vl-handle-unparam-fail-does-not-cause-name-conflict
    (implies (and (vl-modulelist-p mods)
                  (uniquep (vl-modulelist->names mods)))
             (b* (((mv survivors victims) (vl-handle-unparam-fail mods)))
               (uniquep (vl-modulelist->names (append survivors victims)))))))


(define vl-modulelist-unparameterize
  :parents (unparameterization)
  :short "Main unparamterization routine."
  ((mods vl-modulelist-p   "Modules to unparameterize.")
   (n    natp              "How many passes of unparameterization to try."))
  :guard
  (and (uniquep (vl-modulelist->names mods))
       (vl-modulelist-complete-p mods mods)
       (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))
  :returns (mv (success-mods vl-modulelist-p :hyp :fguard
                             :hints(("Goal" :in-theory (disable (force)))))
               (fail-mods vl-modulelist-p :hyp :fguard
                          :hints(("Goal" :in-theory (disable (force))))))
  :verify-guards nil
  :measure (acl2-count n)
  :long "<p>Our hope is that after some number of iterations, all parameterized
modules have been eliminated.  If so, @('successp') is set to true and the
modules are partitioned into @('success-mods') and @('fail-mods').  If modules
with parameters are still left, we throw them away and annotate them, saying
that we were unable to unparameterize them.</p>"

  (b* ((withparams (vl-modules-with-params mods))
       (- (cw ";; vl-unparameterize round ~x0: ~x1 mods, ~x2 w/params.~%"
              n (len mods) (len withparams)))

       ((unless withparams)
        ;; Success, all modules are parameter-free.
        ;;(cw "; vl-unparameterize: all remaining modules are parameter-free.~%")
        (mv (redundant-list-fix mods) nil))

       ((when (zp n))
        ;; Ran out of steps.  Throw away all modules with params and everything
        ;; that depends on them.
        (cw "; vl-unparameterize: counter exhausted before fixed point reached.~%")
        (cw "; modules that still have parameters: ~&0"
            (vl-modulelist->names withparams))
        (vl-handle-unparam-fail mods))

       ((mv success-mods fail-mods) (cwtime (vl-unparameterize-pass mods)))
       ((when (and (not fail-mods)
                   (equal (mergesort mods) (mergesort success-mods))))
        (cw "; vl-unparameterize: fixed point reached with n = ~x0~%~
             ; Modules that still have parameters: ~&1~%"
            n (vl-modulelist->names withparams))
        (vl-handle-unparam-fail mods))

       ((mv success-rest fail-rest)
        (vl-modulelist-unparameterize success-mods (- n 1))))
    (mv success-rest (append fail-mods fail-rest)))

  :prepwork
  ((local (in-theory (disable vl-modulelist-complete-p))))
  ///
  (verify-guards vl-modulelist-unparameterize)

  (defmvtypes vl-modulelist-unparameterize (true-listp true-listp)))


(define vl-design-unparameterize
  :short "Top-level @(see unparameterize) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x)
       (mods x.mods)

       ;; (- (cw "Starting unparameterization of ~x0 modules.~%" (len mods)))

       ;; BOZO: We previously deleted top-level modules with params and warned
       ;; that they might be dead code before unparameterizing.  Do we want to
       ;; bring that back?
       ((unless (xf-cwtime (uniquep (vl-modulelist->names mods))
                           :name doublecheck-unique-names))
        (raise "Programming error: module names are not unique.")
        x)
       ((unless (xf-cwtime (vl-modulelist-complete-p mods mods)
                           :name doublecheck-completeness))
        (raise "Programming error: modules are not complete.")
        x)
       ((unless (xf-cwtime
                 (vl-good-paramdecllist-list-p-of-vl-modulelist->paramdecls mods)
                 :name doublecheck-paramdecls))
        (raise "Programming error: modules don't have good parameter decls.")
        x)

       ((mv goodmods badmods)
        (xf-cwtime (vl-modulelist-unparameterize mods 1000)
                   :name vl-modulelist-unparameterize))
       ;;(- (cw "GOOD: ~x0.~%" (vl-modulelist->names goodmods)))
       ;;(- (cw "BAD: ~x0.~%" (vl-modulelist->names badmods)))
       (mods (append goodmods badmods))
       ;;(- (sneaky-save :good goodmods))
       ;;(- (sneaky-save :bad badmods))
       ((unless (xf-cwtime (uniquep (vl-modulelist->names mods))
                           :name doublecheck-unique-names))
        (raise "Programming error.  Unparam name clash.  Thought this was ~
                impossible.")
        x))
    (cw "; vl-unparameterize: ~x0 => ~x1 modules.~%" (len x.mods) (len mods))
    (change-vl-design x :mods mods)))