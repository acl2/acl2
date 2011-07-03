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
(include-book "xf-subst")
(include-book "../mlib/remove-bad")
(include-book "../mlib/warnings")
(include-book "../wf-ranges-resolved-p")
(include-book "../onehot")
(include-book "../util/cwtime")
(local (include-book "../util/arithmetic"))
(local (include-book "../mlib/modname-sets"))
(local (include-book "../util/osets"))

(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))



(defund vl-annotate-modules-with-warning (x warning)
  (declare (xargs :guard (and (vl-modulelist-p x)
                              (vl-warning-p warning))))
  (if (atom x)
      nil
    (cons (change-vl-module
           (car x)
           :warnings (cons warning (vl-module->warnings (car x))))
          (vl-annotate-modules-with-warning (cdr x) warning))))

(defthm vl-modulelist-p-of-vl-annotate-modules-with-warning
  (implies (and (force (vl-modulelist-p x))
                (vl-warning-p warning))
           (vl-modulelist-p (vl-annotate-modules-with-warning x warning)))
  :hints(("Goal" :in-theory (enable vl-annotate-modules-with-warning))))




(defxdoc unparameterization
  :parents (transforms)
  :short "Expand away modules with parameters."

  :long "<p>Unparameterization is a Verilog transformation which, given a set
of Verilog modules, is supposed to produce an equivalent, parameter-free set of
modules.</p>

<p>There are two kinds of parameter declarations, <tt>parameter</tt> and
<tt>localparam</tt>, examples of which are shown below.  Parameters have
default values, and their defaults can refer to other parameters in the
module.</p>

<code>
    module m (a, b, c) ;
      ...
      parameter size = 4 ;
      localparam twosize = 2 * size ;
      ...
    endmodule
</code>

<p>And a module which uses parameters can be instantiated like this:</p>

<code>
    module uses_m (x y z) ;
      ...
      m #(6)        m_instance_1 (.a(x), .b(y), .c(z)) ; // size 6
      m #(.size(6)) m_instance_2 (.a(x), .b(y), .c(z)) ; // size 6
      m             m_instance_3 (.a(x), .b(y), .c(z)) ; // size 4
      ...
    endmodule
</code>

<p>Local parameters are just like parameters except that they cannot be
assigned to from outside the module.  They are not used at Centaur so we have
not tried to support them.  On the other hand, it does not seem like it would
be difficult to add support for them.</p>

<p>Verilog also includes a <tt>defparam</tt> statement, which we do not
currently support, that can be used to override parameters in other modules.
If supporting this is desired, we should first use a separate transform to
eliminate any uses of <tt>defparam</tt>, then unparameterize as we do
today.</p>

<p>The basic idea behind unparameterization is pretty simple.  Suppose we are
dealing with a parameterized module called <tt>plus</tt>, which takes a single
parameter called <tt>size</tt>.  There may be several modules, say <tt>m1</tt>,
<tt>m2</tt>, and <tt>m3</tt>, which contain instances of <tt>plus</tt> with
different sizes, say <tt>8</tt>, <tt>16</tt>, and <tt>32</tt>.</p>

<p>Our general strategy is to eliminate <tt>plus</tt> from our module list by
replacing it with three new modules, <tt>plus$size=8</tt>,
<tt>plus$size=16</tt>, and <tt>plus$size=32</tt>, which are copies of
<tt>plus</tt> except that <tt>size</tt> has been replaced everywhere with
<tt>8</tt>, <tt>16</tt>, or <tt>32</tt> as suggested by their names.  At the
same time, we need to change the instances of <tt>plus</tt> throughout
<tt>m1</tt>, <tt>m2</tt>, and <tt>m3</tt> with appropriate instances of the new
modules.  Finally, once all of the instances of the generic <tt>plus</tt> have
been done away with, we can safely remove <tt>plus</tt> from our module
list.</p>")



; We extend the notion of a resolved exprsesion to say an instantiation of a
; parameterized module (e.g., an instance of PLUS within M1, M2, and M3) is is
; resolved when all of its parameter expressions (e.g., its choice of SIZE) are
; resolved expressions.

(defund vl-namedarg-resolved-p (x)
  (declare (xargs :guard (vl-namedarg-p x)))
  (and (vl-namedarg->expr x)
       (vl-expr-resolved-p (vl-namedarg->expr x))))

(defthm vl-expr-resolved-p-of-vl-namedarg->expr-when-vl-namedarg-resolved-p
  (implies (vl-namedarg-resolved-p arg)
           (vl-expr-resolved-p (vl-namedarg->expr arg)))
  :hints(("Goal" :in-theory (enable vl-namedarg-resolved-p))))

(deflist vl-namedarglist-resolved-p (x)
  (vl-namedarg-resolved-p x)
  :guard (vl-namedarglist-p x)
  :elementp-of-nil nil)



(defund vl-plainarg-resolved-p (x)
  (declare (xargs :guard (vl-plainarg-p x)))
  (and (vl-plainarg->expr x)
       (vl-expr-resolved-p (vl-plainarg->expr x))))

(defthm vl-expr-resolved-p-of-vl-plainarg->expr-when-vl-plainarg-resolved-p
  (implies (vl-plainarg-resolved-p arg)
           (vl-expr-resolved-p (vl-plainarg->expr arg)))
  :hints(("Goal" :in-theory (enable vl-plainarg-resolved-p))))

(deflist vl-plainarglist-resolved-p (x)
  (vl-plainarg-resolved-p x)
  :guard (vl-plainarglist-p x)
  :elementp-of-nil nil)


(defund vl-arguments-resolved-p (x)
  (declare (xargs :guard (vl-arguments-p x)))
  (if (vl-arguments->namedp x)
      (vl-namedarglist-resolved-p (vl-arguments->args x))
    (vl-plainarglist-resolved-p (vl-arguments->args x))))

(defund vl-modinst-resolvedparams-p (x)
  (declare (xargs :guard (vl-modinst-p x)))
  (vl-arguments-resolved-p (vl-modinst->paramargs x)))

(deflist vl-modinstlist-resolvedparams-p (x)
  (vl-modinst-resolvedparams-p x)
  :guard (vl-modinstlist-p x)
  :elementp-of-nil t)



(defsection vl-good-paramdecl-p
  :parents (unparameterization)
  :short "Parameters which are simple enough to unparameterize."

  :long "<p>In Verilog, parameter declarations can have a type, range, and
signedness, and the expression involved could be complex.  They can also be
introduced with <tt>localparam</tt> instead of <tt>parameter</tt>.</p>

<p>But in practice, at Centaur, all of our parameter declarations look
something like this:</p>

<code>
   parameter width = 1 ;
</code>

<p>That is, there is no type or range, they are not signed (well, the
expression shown above, <tt>1</tt>, is a signed decimal constant, but the
keyword 'signed' does not occur in the parameter declaration), they are never
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

(defwellformed vl-good-paramdecllist-p (x)
  :guard (vl-paramdecllist-p x)
  :body
  (let ((names (vl-paramdecllist->names x)))
    (@wf-progn
     (@wf-assert (uniquep names)
                 :vl-bad-paramdecl
                 "Multiple declarations of parameters: ~&0."
                 (list names))
     (@wf-call vl-good-paramdecllist-p-aux x))))

(defwellformed-list vl-good-paramdecllist-list-p (x)
  :element vl-good-paramdecllist-p
  :guard (vl-paramdecllist-list-p x))

(defsection vl-module-check-good-paramdecls

;; BOZO document me

  (defund vl-module-check-good-paramdecls (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         ((mv okp warnings)
          (vl-good-paramdecllist-p-warn x.paramdecls x.warnings))
         (warnings (if okp
                       warnings
                     (cons (make-vl-warning
                            :type :vl-bad-paramdecls
                            :msg "Module ~m0 has unsupported parameter declarations."
                            :args (list x.name)
                            :fatalp t
                            :fn 'vl-module-check-good-paramdecls)
                           warnings))))
        (change-vl-module x :warnings warnings)))

  (local (in-theory (enable vl-module-check-good-paramdecls)))

  (defthm vl-module-p-of-vl-module-check-good-paramdecls
    (implies (force (vl-module-p x))
             (vl-module-p (vl-module-check-good-paramdecls x))))

  (defthm vl-module->name-of-vl-module-check-good-paramdecls
    (equal (vl-module->name (vl-module-check-good-paramdecls x))
           (vl-module->name x))))

(defsection vl-modulelist-check-good-paramdecls

;; BOZO document me

  (defprojection vl-modulelist-check-good-paramdecls (x)
    (vl-module-check-good-paramdecls x)
    :guard (vl-modulelist-p x)
    :result-type vl-modulelist-p)

  (defthm vl-modulelist->names-of-vl-modulelist-check-good-paramdecls
    (equal (vl-modulelist->names (vl-modulelist-check-good-paramdecls x))
           (vl-modulelist->names x))
    :hints(("Goal" :induct (len x)))))

(defun vl-good-paramdecllist-list-p-of-vl-modulelist->paramdecls (x)
  ;; Simple fused operation.  We leave this enabled.
  (declare (xargs :guard (vl-modulelist-p x)))
  (mbe :logic
       (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls x))
       :exec
       (if (consp x)
           (and (vl-good-paramdecllist-p (vl-module->paramdecls (car x)))
                (vl-good-paramdecllist-list-p-of-vl-modulelist->paramdecls (cdr x)))
         t)))



(defsection vl-modules-with-params
  :parents (unparameterization)
  :short "@(call vl-modules-with-params) gathers all modules within the
module list <tt>x</tt> that have any parameters, and returns them as a
new module list."

  (defund vl-modules-with-params (mods)
    (declare (xargs :guard (vl-modulelist-p mods)))
    (cond ((atom mods)
           nil)
          ((consp (vl-module->paramdecls (car mods)))
           (cons (car mods)
                 (vl-modules-with-params (cdr mods))))
          (t
           (vl-modules-with-params (cdr mods)))))

  (local (in-theory (enable vl-modules-with-params)))

  (defthm vl-modulelist-p-of-vl-modules-with-params
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (vl-modules-with-params mods))))

  (defthm subsetp-equal-of-vl-modules-with-params
    (subsetp-equal (vl-modules-with-params mods) mods)))



(defsection vl-delete-top-level-modules-with-params
  :parents (unparameterization)

  :short "Procedure for eliminating parameterized modules which are no longer used."

  :long "<p>Once all occurrences of a parameterized module like <tt>plus</tt> have
been replaced with instances of concrete modules like <tt>plus$size=16</tt>, we
need to eliminate the generic <tt>plus</tt> from the list of modules in order
to finally arrive at a list of modules which are parameter-free.  We do this
with @(call vl-delete-top-level-modules-with-params).</p>"

  (defund vl-delete-top-level-modules-with-params (mods modalist)
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (vl-modulelist-complete-p mods mods)
                                (equal modalist (vl-modalist mods)))))
    (b* ((topnames   (vl-modulelist-toplevel mods))
         (topmods    (vl-fast-find-modules topnames mods modalist))
         (withparams (vl-modules-with-params topmods))
         (delmods    (vl-modulelist->names withparams))
         ;(- (cw "Removing now-unnecessary modules: ~&0.~%" delmods))
         )
        (vl-delete-modules delmods mods)))

  (local (in-theory (enable vl-delete-top-level-modules-with-params)))

  (defthm vl-modulelist-p-of-vl-delete-top-level-modules-with-params
    (implies (and (force (vl-modulelist-p mods))
                  (force (vl-modulelist-complete-p mods mods))
                  (force (equal modalist (vl-modalist mods))))
             (vl-modulelist-p (vl-delete-top-level-modules-with-params mods modalist)))))




(defsection vl-match-namedargs-with-paramdecls
  :parents (vl-match-paramargs-with-decls)
  :short "Matches formals and actuals for named args."

  :long "<p><b>Signature: </b> @(call vl-match-paramargs-with-decls) returns
<tt>(mv successp warnings-prime sigma)</tt>.</p>

<p>We build a @(see vl-sigma-p) which maps the formals (the parameter
declarations) to the actuals, for a list of named parameter arguments.  That
is, given module <tt>mod</tt> with parameters <tt>p1</tt>, <tt>p2</tt>, ...,
and an instance of <tt>mod</tt> such as:</p>

<code>
    mod #(.p1(5), .p2(8), ...) my_inst (...)
</code>

<p>We construct a @(see vl-sigma-p) mapping <tt>p1</tt> to <tt>5</tt>,
<tt>p2</tt> to <tt>8</tt>, and so on.</p>

<p>We recur over the declarations, rather than the formals, because the user is
allowed to omit formals and we want to give those parameters their default
values.</p>

<h5>Failures</h5>

<p>This function may fail if the actuals are blank, and in such a case an
updated list of warnings is generated.  The <tt>inst</tt> argument is only used
to provide the context for error reporting, and should be the @(see vl-modinst-p)
that this mapping is being carried out for.</p>"

  (defund vl-find-named-arg (name args)
    (declare (xargs :guard (and (stringp name)
                                (vl-namedarglist-p args))))
    (cond ((atom args)
           nil)
          ((equal (vl-namedarg->name (car args)) name)
           (car args))
          (t
           (vl-find-named-arg name (cdr args)))))

  (defthm vl-namedarg-p-of-vl-find-named-arg
    (implies (force (vl-namedarglist-p args))
             (equal (vl-namedarg-p (vl-find-named-arg name args))
                    (if (vl-find-named-arg name args)
                        t
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-named-arg))))

  (defthm vl-expr-resolved-p-of-vl-find-named-arg
    (implies (and (force (vl-namedarglist-p args))
                  (force (vl-namedarglist-resolved-p args)))
             (equal (vl-namedarg-resolved-p (vl-find-named-arg name args))
                    (if (vl-find-named-arg name args)
                        t
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-named-arg))))

  (defund vl-match-namedargs-with-paramdecls (args decls warnings inst)
    (declare (xargs :guard (and (vl-namedarglist-p args)
                                (vl-paramdecllist-p decls)
                                (vl-good-paramdecllist-p decls)
                                (vl-warninglist-p warnings)
                                (vl-modinst-p inst))
                    :verify-guards nil))
    (b* (((when (atom decls))
          (mv t warnings nil))
         (thisdecl  (car decls))
         (name      (vl-paramdecl->name thisdecl))
         (default   (vl-paramdecl->expr thisdecl))
         (lookup    (vl-find-named-arg name args))
         ((when (and lookup
                     (not (vl-namedarg->expr lookup))))
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0: \"blank\" binding for parameter ~s1."
                   :args (list inst name)
                   :fatalp t
                   :fn 'vl-match-namedargs-with-paramdecls)))
            (mv nil (cons w warnings) nil)))
         (value (if lookup
                    (vl-namedarg->expr lookup)
                  default))
         ((mv successp warnings sigma)
          (vl-match-namedargs-with-paramdecls args (cdr decls) warnings inst)))
      (mv successp
          warnings
          (acons name value sigma))))

  (local (in-theory (enable vl-match-namedargs-with-paramdecls)))

  (defthm vl-warninglist-p-of-vl-match-namedargs-with-paramdecls
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-match-namedargs-with-paramdecls args decls warnings inst)))))

  (defthm alistp-of-vl-match-namedargs-with-paramdecls
    (alistp (mv-nth 2 (vl-match-namedargs-with-paramdecls args decls warnings inst))))

  (defthm strip-cars-of-vl-match-namedargs-with-paramdecls
    (implies (mv-nth 0 (vl-match-namedargs-with-paramdecls args decls warnings inst))
             (equal (strip-cars (mv-nth 2 (vl-match-namedargs-with-paramdecls args decls warnings inst)))
                    (vl-paramdecllist->names decls))))

  (defthm vl-exprlist-p-of-strip-cdrs-of-vl-match-namedargs-with-paramdecls
    (implies (and (force (vl-namedarglist-p args))
                  (force (vl-paramdecllist-p decls)))
             (vl-exprlist-p (strip-cdrs (mv-nth 2 (vl-match-namedargs-with-paramdecls args decls warnings inst))))))

  (defthm vl-exprlist-resolved-p-of-strip-cdrs-of-vl-match-namedargs-with-paramdecls
    (implies (and (force (vl-namedarglist-p args))
                  (force (vl-paramdecllist-p decls))
                  (force (vl-namedarglist-resolved-p args))
                  (force (vl-good-paramdecllist-p decls)))
             (vl-exprlist-resolved-p
              (strip-cdrs
               (mv-nth 2
                (vl-match-namedargs-with-paramdecls args decls warnings inst)))))
    :hints(("Goal" :in-theory (enable vl-good-paramdecllist-p
                                      vl-good-paramdecllist-p-aux
                                      vl-good-paramdecl-p))))

  (verify-guards vl-match-namedargs-with-paramdecls
                 :hints(("Goal" :in-theory (enable vl-good-paramdecllist-p)))))



(defsection vl-match-plainargs-with-paramdecls
  :parents (vl-match-paramargs-with-decls)
  :short "Matches formals and actuals for plain args."

  :long "<p><b>Signature:</b> @(call vl-match-plainargs-with-paramdecls)
returns <tt>(mv successp warnings-prime sigma)</tt>.</p>

<p>This is much like @(see vl-match-namedargs-with-paramdecls), but for plain
argument lists.</p>

<p>We recur over decls, because Verilog permits the argument list to be
partial.  That is, if a module had three parameters, and only one param
argument is provided to it, then the other two get the default values.</p>"

  (defund vl-match-plainargs-with-paramdecls (args decls warnings inst)
    (declare (xargs :guard (and (vl-plainarglist-p args)
                                (vl-paramdecllist-p decls)
                                (vl-good-paramdecllist-p decls)
                                (<= (len args) (len decls))
                                (vl-warninglist-p warnings)
                                (vl-modinst-p inst))
                    :verify-guards nil))
    (b* (((when (atom decls))
          (mv t warnings nil))
         (name    (vl-paramdecl->name (car decls)))
         (default (vl-paramdecl->expr (car decls)))
         ((when (and (consp args)
                     (not (vl-plainarg->expr (car args)))))
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0: \"blank\" binding for parameter ~s3."
                   :args (list inst name)
                   :fatalp t
                   :fn 'vl-match-plainargs-with-paramdecls)))
            (mv nil (cons w warnings) nil)))
         (value (if (atom args)
                    default
                  (vl-plainarg->expr (car args))))
         ((mv successp warnings sigma)
          (vl-match-plainargs-with-paramdecls (if (atom args) nil (cdr args))
                                              (cdr decls) warnings inst)))
      (mv successp
          warnings
          (acons name value sigma))))

  (local (in-theory (enable vl-match-plainargs-with-paramdecls)))

  (defthm vl-warninglist-p-of-vl-match-plainargs-with-paramdecls
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-match-plainargs-with-paramdecls args decls warnings inst)))))

  (defthm alistp-of-vl-match-plainargs-with-paramdecls
    (alistp (mv-nth 2 (vl-match-plainargs-with-paramdecls args decls warnings inst))))

  (defthm strip-cars-of-vl-match-plainargs-with-paramdecls
    (implies (mv-nth 0 (vl-match-plainargs-with-paramdecls args decls warnings inst))
             (equal (strip-cars (mv-nth 2 (vl-match-plainargs-with-paramdecls args decls warnings inst)))
                    (vl-paramdecllist->names decls))))

  (defthm vl-exprlist-p-of-strip-cdrs-of-vl-match-plainargs-with-paramdecls
    (implies (and (force (vl-plainarglist-p args))
                  (force (vl-paramdecllist-p decls))
                  (force (<= (len args) (len decls))))
             (vl-exprlist-p
              (strip-cdrs
               (mv-nth 2
                (vl-match-plainargs-with-paramdecls args decls warnings inst))))))

  (defthm vl-exprlist-resolved-p-of-strip-cdrs-of-vl-match-plainargs-with-paramdecls
    (implies (and (force (vl-plainarglist-p args))
                  (force (vl-paramdecllist-p decls))
                  (force (vl-good-paramdecllist-p decls))
                  (force (vl-plainarglist-resolved-p args))
                  (force (<= (len args) (len decls))))
             (vl-exprlist-resolved-p
              (strip-cdrs
               (mv-nth 2
                (vl-match-plainargs-with-paramdecls args decls warnings inst)))))
    :hints(("Goal" :in-theory (enable vl-good-paramdecllist-p
                                      vl-good-paramdecllist-p-aux
                                      vl-good-paramdecl-p))))

  (verify-guards vl-match-plainargs-with-paramdecls
                 :hints(("Goal" :in-theory (enable vl-good-paramdecllist-p)))))



(defsection vl-match-paramargs-with-decls
  :parents (unparameterization)
  :short "Build a @(see vl-sigma-p) mapping parameter formals to actuals."

  :long "<p><b>Signature:</b> @(call vl-match-paramargs-with-decls) returns
<tt>(mv successp warnings-prime sigma)</tt>.</p>

<p>A basic operation in unparameterization is being able to pair up
the <i>formals</i> and <i>actuals</i>.  That is, the module declares that it
has a bunch of parameters (\"formals\"), and each instance of the module gives
some expressions (\"actuals\") to be substituted in for these formals.</p>

<p>We are given a module and an instance of that module.  We might fail for
various reasons, e.g., maybe we try to instantiate a missing parameter, or use
a \"blank\" value, etc.  In such a case, <tt>successp</tt> is <tt>nil</tt> and
some new, fatal @(see warnings) will be added to <tt>warnings</tt> to form
<tt>warnings-prime</tt>.</p>

<p>On success, <tt>sigma</tt> will be a @(see vl-sigma-p) that maps the names
of the parameters to their values.  This can then be substituted (@(see
substitution)) into the module being instantiated to form an unparameterized
version of the module.</p>

<p>The pairing is a little tricky because the argument lists can be given in
either a named or an ordered format, so we write separate functions to handle
these cases.</p>"

  (defund vl-match-paramargs-with-decls (inst mod warnings)
    (declare (xargs :guard (and (vl-modinst-p inst)
                                (vl-module-p mod)
                                (vl-good-paramdecllist-p (vl-module->paramdecls mod))
                                (equal (vl-modinst->modname inst) (vl-module->name mod))
                                (vl-warninglist-p warnings))
                    :verify-guards nil))
    (b* ((paramdecls (vl-module->paramdecls mod))
         (paramargs  (vl-modinst->paramargs inst))
         (namedp     (vl-arguments->namedp paramargs))
         (args       (vl-arguments->args paramargs))
         ((when namedp)
          (let ((argnames   (vl-namedarglist->names args))
                (paramnames (vl-paramdecllist->names paramdecls)))
            (if (not (subsetp-equal argnames paramnames))
                (b* ((bad (set-difference-equal argnames paramnames))
                     (w   (make-vl-warning
                           :type :vl-bad-instance
                           :msg "~a0 mentions non-existent parameter~s1 ~&2."
                           :args (list inst (if (vl-plural-p bad) "s" "") bad)
                           :fatalp t
                           :fn 'vl-match-paramargs-with-decls)))
                  (mv nil (cons w warnings) nil))
              (vl-match-namedargs-with-paramdecls args paramdecls warnings inst))))
         ((unless (<= (len args) (len paramdecls)))
          (b* ((w (make-vl-warning
                       :type :vl-bad-instance
                       :msg "~a0 provides ~x1 parameters where at most ~x2 are permitted."
                       :args (list inst (len args) (len paramdecls))
                       :fatalp t
                       :fn 'vl-match-paramargs-with-decls)))
            (mv nil (cons w warnings) nil))))
      (vl-match-plainargs-with-paramdecls args paramdecls warnings inst)))

  (local (in-theory (enable vl-match-paramargs-with-decls)))

  (defthm vl-warninglist-p-of-vl-match-paramargs-with-decls
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-match-paramargs-with-decls inst mod warnings)))))

  (defthm alistp-of-vl-match-paramargs-with-decls
    (alistp (mv-nth 2 (vl-match-paramargs-with-decls inst mod warnings))))

  (defthm strip-cars-of-vl-match-paramargs-with-decls
    (implies (mv-nth 0 (vl-match-paramargs-with-decls inst mod warnings))
             (equal (strip-cars (mv-nth 2 (vl-match-paramargs-with-decls inst mod warnings)))
                    (vl-paramdecllist->names (vl-module->paramdecls mod)))))

  (defthm vl-exprlist-p-of-vl-match-paramargs-with-decls
    (implies (and (mv-nth 0 (vl-match-paramargs-with-decls inst mod warnings))
                  (force (vl-module-p mod))
                  (force (vl-modinst-p inst)))
             (vl-exprlist-p
              (strip-cdrs
               (mv-nth 2
                (vl-match-paramargs-with-decls inst mod warnings))))))

  (defthm vl-exprlist-resolved-p-of-vl-match-paramargs-with-decls
    (implies (and (mv-nth 0 (vl-match-paramargs-with-decls inst mod warnings))
                  (force (vl-good-paramdecllist-p (vl-module->paramdecls mod)))
                  (force (vl-arguments-resolved-p (vl-modinst->paramargs inst)))
                  (force (vl-module-p mod))
                  (force (vl-modinst-p inst)))
             (vl-exprlist-resolved-p
              (strip-cdrs
               (mv-nth 2
                (vl-match-paramargs-with-decls inst mod warnings)))))
    :hints(("Goal" :in-theory (enable vl-arguments-resolved-p))))

  (verify-guards vl-match-paramargs-with-decls)

  (local (defthm lemma
           (implies (alistp x)
                    (equal (vl-sigma-p x)
                           (and (string-listp (strip-cars x))
                                (vl-exprlist-p (strip-cdrs x)))))
           :hints(("Goal" :in-theory (enable alistp vl-sigma-p)))))

  (defthm vl-sigma-p-of-vl-match-paramargs-with-decls
    (implies (and (mv-nth 0 (vl-match-paramargs-with-decls inst mod warnings))
                  (force (vl-module-p mod))
                  (force (vl-modinst-p inst)))
             (vl-sigma-p (mv-nth 2 (vl-match-paramargs-with-decls inst mod warnings))))))




(defsection vl-unparam-newname
  :parents (unparameterization)
  :short "Generate a new name for an unparameterized module."

  :long "<p>@(call vl-unparam-newname) is used to introduce the new name for
unparameterized modules.</p>

<p><tt>Origname</tt> is the original name of the module, e.g., <tt>plus</tt>,
and <tt>sigma</tt> is a @(see vl-sigma-p) that maps the parameter names to
their values, say <tt>size</tt> &lt;-- 5 and <tt>width</tt> &lt;-- 32.  We
generate a new name by appending on the attributes and their bindings as
strings of the form <tt>$key=val</tt>, e.g., <tt>plus$size=5$width=32</tt>.</p>

<p>At Centaur, this is very likely to form unique new names since, since we do
not use dollar signs in the names of modules.  But we explicitly check in our
unparameterization code that no conflicts are introduced.</p>"

  (defund vl-unparam-newname-aux (origname sigma)
    (declare (xargs :guard (and (stringp origname)
                                (vl-sigma-p sigma)
                                (vl-exprlist-resolved-p (strip-cdrs sigma)))
                    :verify-guards nil))
    (cond ((atom sigma)
           (mbe :logic (string-fix origname)
                :exec origname))
          (t
           (let* ((param-name    (caar sigma))
                  (param-val     (vl-resolved->val (cdar sigma)))
                  (param-val-str (str::natstr param-val)))
             (vl-unparam-newname-aux
              (str::cat origname "$" param-name "=" param-val-str)
              (cdr sigma))))))

  (local (in-theory (enable vl-unparam-newname-aux)))

  (local (defthm lemma
           (implies (vl-exprlist-resolved-p (strip-cdrs sigma))
                    (and (equal (vl-constint-p (vl-atom->guts (cdar sigma)))
                                (consp sigma))
                         (equal (vl-atom-p (cdar sigma))
                                (consp sigma))))
           :hints(("Goal" :in-theory (enable vl-exprlist-resolved-p
                                             vl-expr-resolved-p)))))

  (verify-guards vl-unparam-newname-aux)

  (defthm stringp-of-vl-unparam-newname-aux
    (stringp (vl-unparam-newname-aux origname sigma))
    :rule-classes :type-prescription)

  (local (defthm vl-sigma-p-of-hons-shrink-alist
           (implies (and (vl-sigma-p x)
                         (vl-sigma-p acc))
                    (vl-sigma-p (hons-shrink-alist x acc)))
           :hints(("Goal" :in-theory (enable (:induction hons-shrink-alist))))))

  (local (defthm vl-exprlist-resolved-p-of-strip-cdrs-of-hons-shrink-alist
           (implies (and (vl-exprlist-resolved-p (strip-cdrs x))
                         (vl-exprlist-resolved-p (strip-cdrs acc)))
                    (vl-exprlist-resolved-p (strip-cdrs (hons-shrink-alist x acc))))
           :hints(("Goal" :in-theory (enable (:induction hons-shrink-alist))))))

  (local (include-book "finite-set-theory/osets/set-order" :dir :system))

  (local (defthm vl-sigma-p-of-insert
           (implies (and (vl-sigma-p x)
                         (consp a)
                         (stringp (car a))
                         (vl-expr-p (cdr a)))
                    (vl-sigma-p (insert a x)))
           :hints(("Goal" :in-theory (enable sets::insert sets::primitive-reasoning)))))

  (local (defthm vl-sigma-p-of-mergesort
           (implies (vl-sigma-p x)
                    (vl-sigma-p (mergesort x)))))

  (local (defthm vl-exprlist-resolved-p-of-strip-cdrs-of-insert
           (implies (and (vl-exprlist-resolved-p (strip-cdrs x))
                         (vl-expr-resolved-p (cdr a)))
                    (vl-exprlist-resolved-p (strip-cdrs (insert a x))))
           :hints(("Goal" :in-theory (enable sets::insert sets::primitive-reasoning)))))

  (local (defthm vl-exprlist-resolved-p-of-strip-cdrs-of-mergesort
           (implies (vl-exprlist-resolved-p (strip-cdrs x))
                    (vl-exprlist-resolved-p (strip-cdrs (mergesort x))))
           :hints(("Goal" :in-theory (enable sets::insert sets::primitive-reasoning)))))

  (defund vl-unparam-newname (origname sigma)
    (declare (xargs :guard (and (stringp origname)
                                (vl-sigma-p sigma)
                                (vl-exprlist-resolved-p (strip-cdrs sigma)))))
    (progn$
     ;; Extralogical check: there really shouldn't be duplicates.
     (or (uniquep (strip-cars sigma))
         (er hard? 'vl-unparam-newname
             "Programming error: duplicate keys in sigma.  Origname is ~s0,
              duplicated keys are ~&1, sigma is ~x2."
             origname (duplicated-members (strip-cars sigma)) sigma))

     ;; We just standardize the sigma a little bit: we eliminate any duplicates
     ;; and sort all of the parameters.
     (b* ((shrink (hons-shrink-alist sigma nil))
          (-      (flush-hons-get-hash-table-link shrink))
          (sorted (mergesort shrink)))
         (hons-copy (vl-unparam-newname-aux origname sorted)))))

  (defthm stringp-of-vl-unparam-newname
    (stringp (vl-unparam-newname origname sigma))
    :rule-classes :type-prescription))




(defsection vl-unsafe-to-unparameterize-modules
  :parents (unparameterization)

  :short "@(call vl-unsafe-to-unparameterize-modules) gathers the names of
modules that might not be safe to unparameterize, and returns them as fast <see
topic=\"@(url make-lookup-alist)\">lookup alist</see>."

  :long "<p>During our unparameterization process, we want to ensure that at no
point are conflicting versions of any module ever generated.  However, if in
every pass we blindly try to unparameterize every module instance whose
parameters are resolved, we can violate this property.</p>

<p>Illustrating the problem takes some setup.  In particular, suppose we have
the following modules hierarchy:</p>

<code>
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
</code>

<p>If we blindly start unparameterizing every module we see, then after one
round of unparameterization we have:</p>

<code>
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
</code>

<p>Then, in the next round:</p>

<code>
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
</code>

<p>And now we're hosed, because we now have two different versions of
<tt>mid$size=6</tt>, one where the <tt>bot</tt> instance has already been
unparameterized, and one where it has not.  These eventually will converge, but
we think it seems better to never let them diverge in the first place.</p>

<p>Toward this end, we say that certain modules are unsafe to unparameterize.
In particular, we don't want to unparameterize instances of any module
<tt>foo</tt> that is ever instantiated by another parameterized module
<tt>bar</tt>.  In the above example, this means we want to consider both
<tt>mid</tt> and <tt>bot</tt> to be initially off-limits, and only
unparameterize <tt>foo</tt> in the first round.  After that, mid will become
okay to unparameterize, etc.</p>

<p>Note that this function is memoized for efficiency.</p>"

  (defund vl-unsafe-to-unparameterize-modules (mods)
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods)))))
    (let* ((mods          (mergesort mods))
           (modalist      (vl-modalist mods))
           (parameterized (vl-modules-with-params mods))
           (instanced     (vl-modulelist-everinstanced parameterized))
           ;; It might be that instanced might be enough, but it seems
           ;; safer to also exclude all transitively instanced modules.
           (necessary     (vl-necessary-modules instanced mods modalist)))
      (make-lookup-alist necessary)))

  (local (in-theory (enable vl-unsafe-to-unparameterize-modules)))

  (defthm alistp-of-vl-unsafe-to-unparameterize-modules
    (alistp (vl-unsafe-to-unparameterize-modules mods))))




(defsection vl-maybe-unparam-inst
  :parents (unparameterization)
  :short "Try to unparameterize a single module instance."

  :long "<p><b>Signature:</b> @(call vl-maybe-unparam-inst) returns
<tt>(mv successp warnings-prime inst-prime new-mods)</tt>.</p>

<p>We assume we are looking at an instantiation, inst, of some module found in
mods.  We also assume that all of the modules in mods have \"good\" parameter
declaration lists (in the sense of @(see vl-good-paramdecl-p)), and so as a
consequence we know that this also holds for whichever particular module
<tt>inst</tt> refers to.</p>

<p>Unsafe is the fast alist produced by @(see
vl-unsafe-to-unparameterize-modules).  We never unparameterize an instance of a
modules in this alist to avoid introducing certain conflicts.</p>

<p>If the module being instantiated has no parameters, or when we are unable to
unparameterize because some parameter expression has not yet been resolved,
this function is not very interesting.  In such a case it returns successfully,
with <tt>warnings-prime</tt> as just <tt>warnings</tt>, <tt>inst-prime</tt> as
<tt>inst</tt>, and <tt>new-mod</tt> as <tt>nil</tt>.</p>

<p>The interesting case is when the module has parameters, and all of the
parameter arguments have been resolved.  For instance, suppose we are dealing
with an instance of the module <tt>plus</tt> and the <tt>size</tt> parameter
has been resolved to <tt>16</tt>.  In this case,</p>

<ul>

 <li><tt>inst-prime</tt> is an \"updated\" copy of <tt>inst</tt> which, instead
of pointing to <tt>plus</tt>, points to the new, parameter-free module named
<tt>plus$size=16</tt>, and </li>

 <li><tt>new-mods</tt> is (typically) a singleton list containing one new,
parameter-free module, <tt>plus$size=16</tt>, which has been derived from
<tt>plus</tt> by replacing all occurrences of <tt>size</tt> with
<tt>16</tt>.</li>
</ul>

<p>Historically, we used to return only a single module instead of a list of
<tt>new-mods</tt>.  However, this function now takes special care to support
@(see onehot) detection, so that when find instances of <tt>VL_N_BIT_ONEHOT</tt>
we may need to generate several modules.  See @(see vl-make-n-bit-onehot) for
additional details.</p>"

  (defund vl-maybe-unparam-inst (inst unsafe mods modalist warnings)
    "Returns (MV SUCCESSP WARNINGS' INSTS' NEW-MODS)"
; BOZO Performance.  Consider building the substitutions (above) with hons, and
; then memoizing vl-module-subst?  This way, as we run into multiple instances
; of a module that have the same parameters, we wouldn't have to
; re-unparameterize it.

    (declare (xargs :guard (and (vl-modinst-p inst)
                                (alistp unsafe)
                                (vl-modulelist-p mods)
                                (vl-has-module (vl-modinst->modname inst) mods)
                                (equal modalist (vl-modalist mods))
                                (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))
                                (vl-warninglist-p warnings))
                    :verify-guards nil))

    (let* ((modname (vl-modinst->modname inst))
           (mod     (vl-fast-find-module modname mods modalist)))
      (cond

       ((atom (vl-module->paramdecls mod))
        ;; No parameters -- no changes are necessary.
        (mv t warnings inst nil))

       ((not (vl-modinst-resolvedparams-p inst))
        ;; Some parameter expressions in this instance aren't resolved yet, so we
        ;; can't do the unparameterization yet.
        (mv t warnings inst nil))

       ((hons-get modname unsafe)
        ;; Not safe to unparameterize this yet.  Don't do anything.
        (mv t warnings inst nil))

       (t
        (b* (((mv successp warnings sigma)
              (vl-match-paramargs-with-decls inst mod warnings))
             ((unless successp)
              (mv nil warnings inst nil))

             ((when (equal modname "VL_N_BIT_ONEHOT"))
              ;; Special case for one-hot detection.
              (b* ((width (cdr (assoc-equal "width" sigma)))
                   (val   (if (and width
                                   (vl-expr-resolved-p width)
                                   (posp (vl-resolved->val width)))
                              (vl-resolved->val width)
                            (prog2$ (er hard? 'vl-maybe-unparam-inst
                                        "Bad width for VL_N_BIT_ONEHOT: ~x0"
                                        width)
                                    1)))
                   (newmods (vl-make-n-bit-onehot val))
                   (newname (vl-module->name (car newmods)))
                   (newinst (change-vl-modinst inst
                                               :modname newname
                                               :paramargs (vl-arguments nil nil))))
                (mv t warnings newinst newmods)))

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
          (mv t warnings newinst (list newmod)))))))

  (local (defthm lemma
           (implies (and (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))
                         (member a mods))
                    (vl-good-paramdecllist-p (vl-module->paramdecls a)))
           :hints(("Goal" :induct (len mods)))))

  (verify-guards vl-maybe-unparam-inst
    :hints(("Goal" :in-theory (enable vl-modinst-resolvedparams-p))))

  (defmvtypes vl-maybe-unparam-inst (booleanp nil nil true-listp nil))

  (local (in-theory (enable vl-maybe-unparam-inst)))

  (defthm vl-warninglist-p-of-vl-maybe-unparam-inst
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-maybe-unparam-inst inst unsafe mods modalist warnings)))))

  (defthm vl-modinst-p-of-vl-maybe-unparam-inst
    (implies (and (force (vl-modinst-p inst))
                  (force (alistp unsafe))
                  (force (vl-modulelist-p mods))
                  (force (vl-has-module (vl-modinst->modname inst) mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modinst-p (mv-nth 2 (vl-maybe-unparam-inst inst unsafe mods modalist warnings)))))

  (defthm vl-modulelist-p-of-vl-maybe-unparam-inst
    (implies (and (force (vl-modinst-p inst))
                  (force (alistp unsafe))
                  (force (vl-modulelist-p mods))
                  (force (vl-has-module (vl-modinst->modname inst) mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p
              (mv-nth 3 (vl-maybe-unparam-inst inst unsafe mods modalist warnings))))))



(defsection vl-maybe-unparam-instlist
  :parents (unparameterization)
  :short "Extension of @(see vl-maybe-unparam-inst) to a list of instances."

  :long "<p><b>Signature:</b> @(call vl-maybe-unparam-instlist) returns <tt>(mv
successp warnings-prime insts-prime new-mods)</tt>.</p>

<ul>
 <li><tt>successp</tt> indicates whether all of the module instances were
successfully unparameterized.</li>
 <li><tt>insts-prime</tt> are replacements for <tt>insts</tt> that point
to the updated modules.</li>
 <li><tt>new-mods</tt> are any newly generated modules, e.g.,
<tt>plus$size=16</tt>.</li>
</ul>"

  (defund vl-maybe-unparam-instlist (insts unsafe mods modalist warnings)
    "Returns (MV SUCCESSP WARNINGS' INSTS' NEW-MODS)"
    (declare (xargs :guard (and (vl-modinstlist-p insts)
                                (alistp unsafe)
                                (vl-modulelist-p mods)
                                (vl-has-modules (vl-modinstlist->modnames insts) mods)
                                (equal modalist (vl-modalist mods))
                                (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))
                                (vl-warninglist-p warnings))))
    (if (atom insts)
        (mv t warnings nil nil)
      (b* (((mv successp1 warnings car-prime car-newmods)
            (vl-maybe-unparam-inst (car insts) unsafe mods modalist warnings))
           ((mv successp2 warnings cdr-prime cdr-newmods)
            (vl-maybe-unparam-instlist (cdr insts) unsafe mods modalist warnings)))
          (mv (and successp1 successp2)
              warnings
              (cons car-prime cdr-prime)
              (append car-newmods cdr-newmods)))))

  (defmvtypes vl-maybe-unparam-instlist (booleanp nil true-listp true-listp))

  (local (in-theory (enable vl-maybe-unparam-instlist)))

  (defthm vl-warninglist-p-of-vl-maybe-unparam-instlist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-maybe-unparam-instlist instlist unsafe mods modalist warnings)))))

  (defthm vl-modinstlist-p-of-vl-maybe-unparam-instlist
    (implies (and (force (vl-modinstlist-p insts))
                  (force (alistp unsafe))
                  (force (vl-modulelist-p mods))
                  (force (vl-has-modules (vl-modinstlist->modnames insts) mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modinstlist-p (mv-nth 2 (vl-maybe-unparam-instlist insts unsafe mods modalist warnings)))))

  (defthm vl-modulelist-p-of-vl-maybe-unparam-instlist
    (implies (and (force (vl-modinstlist-p insts))
                  (force (alistp unsafe))
                  (force (vl-modulelist-p mods))
                  (force (vl-has-modules (vl-modinstlist->modnames insts) mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p (mv-nth 3 (vl-maybe-unparam-instlist insts unsafe mods modalist warnings))))))




(defsection vl-unparameterize-module
  :parents (unparameterization)
  :short "Extension of @(see vl-maybe-unparam-inst) to a module."

  :long "<p><b>Signature:</b> @(call vl-unparameterize-module) returns
<tt>(mv successp mod-prime new-mods)</tt>.</p>

<p>Note!  <tt>Successp</tt> does <b>NOT</b> indicate that the instances of
<tt>mod-prime</tt> are parameter-free; it only says that there were no errors
during the course of unparameterization (e.g., trying to instantiate missing
parameters or some such.)</p>

<p>The resulting <tt>mod-prime</tt> can still contain parameters if the
\"actuals\" have not yet been resolved.  This can happen, e.g., in the case of
a module which itself has parameters that it uses in order to instantiate its
submodules.  For example, given:</p>

<code>
  module whatever ( a, b, c, d );
    parameter size = 1;
    ...;
    submodule #(size) inst1 (a, b);
    submodule #(size) inst2 (c, d);
  endmodule
</code>

<p>If we try to unparameterize <tt>whatever</tt>, we will not fail, but
the resulting <tt>mod-prime</tt> will be unchanged.  It is not until
we have unparameterized the particular instances of <tt>whatever</tt>
and arrived at a module like:</p>

<code>
  module \\whatever$size=2 (a, b, c, d) ;
    ...;
    submodule #(2) inst1 (a, b);
    submodule #(2) inst2 (c, d);
  endmodule
</code>

<p>that we will be able to actually produce a parameter-free
<tt>mod-prime</tt>.</p>

<p>When there is an error, the resulting <tt>mod-prime</tt> will have been
annotated with some warnings explaining the problem.  However, its instances
will not be changed.  Such modules will be eliminated.</p>"

  (defund vl-unparameterize-module (mod unsafe mods modalist)
    (declare (xargs :guard (and (vl-module-p mod)
                                (alistp unsafe)
                                (vl-modulelist-p mods)
                                (vl-module-complete-p mod mods)
                                (equal modalist (vl-modalist mods))
                                (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))))
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
          (mv t mod-prime new-mods))))

  (defmvtypes vl-unparameterize-module (booleanp nil true-listp))

  (local (in-theory (enable vl-unparameterize-module)))

  (defthm vl-module-p-of-vl-unparameterize-module
    (implies (and (force (vl-module-p mod))
                  (force (alistp unsafe))
                  (force (vl-modulelist-p mods))
                  (force (vl-module-complete-p mod mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-module-p (mv-nth 1 (vl-unparameterize-module mod unsafe mods modalist)))))

  (defthm vl-modulelist-p-of-vl-unparameterize-module
    (implies (and (force (vl-module-p mod))
                  (force (alistp unsafe))
                  (force (vl-modulelist-p mods))
                  (force (vl-module-complete-p mod mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p (mv-nth 2 (vl-unparameterize-module mod unsafe mods modalist))))))


(defsection vl-unparameterize-pass-aux
  :parents (unparameterization)
  :short "Extension of @(see vl-maybe-unparam-inst) to a module list."

  :long "<p><b>Signature:</b> @(call vl-unparameterize-pass-aux) returns
<tt>(mv success-mods fail-mods new-mods)</tt>.</p>

<p>This is almost a full pass of unparameterization, except that it doesn't do
much in the way of error checking and throwing away bad modules.  We try to
apply @(see vl-unparameterize-module) to every module in the list.  We produce
three lists as outputs:</p>

<ul>
  <li><tt>success-mods</tt> are those modules in <tt>x</tt> for which no errors
      were encountered,</li>
  <li><tt>fail-mods</tt> are those modules in <tt>x</tt> which had errors in
      unparameterization, and </li>
  <li><tt>new-mods</tt> are any newly generated modules that are formed in this
      pass of unparameterization.</li>
</ul>"

  (defund vl-unparameterize-pass-aux (x unsafe mods modalist)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (alistp unsafe)
                                (vl-modulelist-p mods)
                                (vl-modulelist-complete-p x mods)
                                (equal modalist (vl-modalist mods))
                                (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))))
    (if (atom x)
        (mv nil nil nil)
      (b* (((mv car-successp car-prime car-newmods)
            (vl-unparameterize-module (car x) unsafe mods modalist))
           ((mv cdr-successes cdr-fails cdr-newmods)
            (vl-unparameterize-pass-aux (cdr x) unsafe mods modalist)))
          (if car-successp
              (mv (cons car-prime cdr-successes)
                  cdr-fails
                  (append car-newmods cdr-newmods))
            (mv cdr-successes
                (cons car-prime cdr-fails)
                (append car-newmods cdr-newmods))))))

  (defmvtypes vl-unparameterize-pass-aux (true-listp true-listp true-listp))

  (local (in-theory (enable vl-unparameterize-pass-aux)))

  (defthm vl-modulelist-p-of-vl-unparameterize-pass-aux-0
    (implies (and (force (vl-modulelist-p x))
                  (force (alistp unsafe))
                  (force (vl-modulelist-p mods))
                  (force (vl-modulelist-complete-p x mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p (mv-nth 0 (vl-unparameterize-pass-aux x unsafe mods modalist)))))

  (defthm vl-modulelist-p-of-vl-unparameterize-pass-aux-1
    (implies (and (force (vl-modulelist-p x))
                  (force (alistp unsafe))
                  (force (vl-modulelist-p mods))
                  (force (vl-modulelist-complete-p x mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p (mv-nth 1 (vl-unparameterize-pass-aux x unsafe mods modalist)))))

  (defthm vl-modulelist-p-of-vl-unparameterize-pass-aux-2
    (implies (and (force (vl-modulelist-p x))
                  (force (alistp unsafe))
                  (force (vl-modulelist-p mods))
                  (force (vl-modulelist-complete-p x mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p (mv-nth 2 (vl-unparameterize-pass-aux x unsafe mods modalist))))))



(defund vl-find-modules-alt (names x)
  (declare (xargs :guard (and (string-listp names)
                              (vl-modulelist-p x))))
  (cond ((atom x)
         nil)
        ((member-equal (vl-module->name (car x)) names)
         (cons (car x)
               (vl-find-modules-alt names (cdr x))))
        (t
         (vl-find-modules-alt names (cdr x)))))

(defthm vl-modulelist-p-of-vl-find-modules-alt
  (implies (force (vl-modulelist-p x))
           (vl-modulelist-p (vl-find-modules-alt names x)))
  :hints(("Goal" :in-theory (enable vl-find-modules-alt))))


(defsection vl-unparameterize-pass
  :parents (unparameterization)
  :short "One full pass of unparameterization over a module list."

  :long "<p><b>Signature:</b> @(call vl-unparameterize-pass) returns
<tt>(mv success-mods fail-mods)</tt>.</p>

<p>We perform one full pass of unparameterization.  This involves</p>
<ul>
 <li>Determining which modules are safe to unparameterize,</li>
 <li>Applying @(see vl-unparameterize-pass-aux) to do most of the work,</li>
 <li>Eliminating any remaining top level modules with parameters,</li>
 <li>Propagating any errors via @(see vl-remove-bad-modules), and</li>
 <li>Ensuring that we did not introduce any conflicting module definitions
     or incompleteness.</li>
</ul>

<p>We hope to eventually prove that the incompleteness check is unnecessary,
and this should lead to better performance.  However, the proof would be
somewhat involved, so we have not yet attempted it.</p>"

  (defund vl-unparameterize-pass (mods)
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods))
                                (vl-modulelist-complete-p mods mods)
                                (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))))
    (b* (;(-                 (cw "; Starting unparameterize pass. ~x0 mods.~%" (len mods)))
         (modalist          (vl-modalist mods))
         (unsafe            (cwtime (vl-unsafe-to-unparameterize-modules mods)
                                    :mintime 1/3
                                    :name determine-safe-modules))
         ;(-                 (cw "; ~x0 modules are not safe to unparameterize yet: ~&1.~%"
         ;                       (len unsafe)
         ;                       (strip-cars unsafe)))
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
                 :msg "Expected resulting modules to be complete, but ~
                       the following modules are missing: ~&0.  Abandoning ~
                       hope and throwing away all modules."
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
                 :msg "Modules are not unique after unparam pass?? ~
                       Conflicting module names: ~&0."
                 :args (list (duplicated-members (vl-modulelist->names survivors)))
                 :fn 'vl-unparameterize-pass))
               (- (cw "~f0~%" (with-local-ps (vl-print-warning warning))))
               (survivors-prime
                (vl-annotate-modules-with-warning survivors warning)))
              (mv nil (append survivors-prime bad)))))

        (mv survivors bad)))

  (defmvtypes vl-unparameterize-pass (true-listp true-listp))

  (local (in-theory (enable vl-unparameterize-pass)))

  (defthm vl-modulelist-p-of-vl-unparameterize-pass-0
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (vl-modulelist-complete-p mods mods))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p (mv-nth 0 (vl-unparameterize-pass mods)))))

  (defthm vl-modulelist-p-of-vl-unparameterize-pass-1
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (vl-modulelist-complete-p mods mods))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p (mv-nth 1 (vl-unparameterize-pass mods)))))

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



(defsection vl-handle-unparam-fail

  (defund vl-handle-unparam-fail-aux (mods)
    ;; Annotate each module in mods with a warning saying we failed to
    ;; unparameterize it.
    (declare (xargs :guard (vl-modulelist-p mods)))
    (if (atom mods)
        nil
      (let ((warning (make-vl-warning
                      :type :vl-unparameterize-fail
                      :msg "Unable to eliminate remaining parameters, ~&0."
                      :args (list (vl-paramdecllist->names
                                   (vl-module->paramdecls (car mods))))
                      :fn 'vl-handle-unparam-fail)))
        (cons (change-vl-module
               (car mods)
               :warnings (cons warning (vl-module->warnings (car mods))))
              (vl-handle-unparam-fail-aux (cdr mods))))))

  (defthm vl-modulelist-p-of-vl-handle-unparam-fail-aux
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (vl-handle-unparam-fail-aux mods)))
    :hints(("Goal" :in-theory (enable vl-handle-unparam-fail-aux))))



  (defund vl-handle-unparam-fail (mods)
    ;; Throw away all modules that still have parameters and all modules
    ;; that depend on them; return (mv survivors victims).
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods)))))
    (b* ((withparams             (vl-modules-with-params mods))
         (withparams-warn        (vl-handle-unparam-fail-aux withparams))
         (badnames               (vl-modulelist->names withparams))
         ((mv survivors victims) (vl-remove-bad-modules badnames (mergesort mods))))
        (mv survivors (append victims withparams-warn))))

  (defmvtypes vl-handle-unparam-fail (true-listp true-listp))

  (local (in-theory (enable vl-handle-unparam-fail)))

  (defthm vl-modulelist-p-of-vl-handle-unparam-fail-0
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (mv-nth 0 (vl-handle-unparam-fail mods)))))

  (defthm vl-modulelist-p-of-vl-handle-unparam-fail-1
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (mv-nth 1 (vl-handle-unparam-fail mods))))))



(defsection vl-unparameterize
  :parents (unparameterization)
  :short "Top level unparamterization routine."

  :long "<p><b>Signature:</b> @(call vl-unparameterize) returns <tt>(mv
successp success-mods fail-mods)</tt>.</p>

<p>We perform up to <tt>n</tt> passes of unparameterization via @(see
vl-unparameterize-pass).  Our hope is that after some number of iterations, all
parameterized modules have been eliminated.  If so, <tt>successp</tt> is set to
true and the modules are partitioned into <tt>success-mods</tt> and
<tt>fail-mods</tt>.</p>

<p>If modules with parameters are still left, we throw them away and annotate
them, saying that we were unable to unparameterize them.</p>"

  (defund vl-unparameterize (mods n)
    (declare (xargs :guard (and (natp n)
                                (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods))
                                (vl-modulelist-complete-p mods mods)
                                (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods)))
                    :verify-guards nil
                    :measure (acl2-count n)))

    (b* ((withparams (vl-modules-with-params mods))
         ;(- (cw "; vl-unparameterize: starting round ~x0: ~x1 modules, ~x2 have params.~%"
         ;       n (len mods) (len withparams)))
         )
      (cond ((not withparams)

; Success, all modules are parameter-free.

             (progn$
              ;(cw "; vl-unparameterize: all remaining modules are parameter-free.~%")
              (mv (redundant-list-fix mods) nil)))

            ((zp n)

; Ran out of steps.  Throw away all modules with params and everything
; that depends on them.

             (progn$
              (cw "; vl-unparameterize: counter exhausted before fixed point reached.~%")
              (vl-handle-unparam-fail mods)))


            (t
             (b* (((mv success-mods fail-mods)
                   (vl-unparameterize-pass mods)))
                 (if (and (not fail-mods)
                          (equal (mergesort mods) (mergesort success-mods)))
                     (progn$
                      (cw "; vl-unparameterize: fixed point reached with n = ~x0, but ~
                           there are still modules with parameters: ~%" n)
                      (vl-handle-unparam-fail mods))

                   (mv-let (success-rest fail-rest)
                           (vl-unparameterize success-mods (- n 1))
                           (mv success-rest (append fail-mods fail-rest)))))))))

  (local (in-theory (enable vl-unparameterize)))
  (local (in-theory (disable vl-modulelist-complete-p)))

  (verify-guards vl-unparameterize)

  (defmvtypes vl-unparameterize (true-listp true-listp))

  (defthm vl-modulelist-p-of-vl-unparamterize-0
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (vl-modulelist-complete-p mods mods))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p (mv-nth 0 (vl-unparameterize mods n))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-modulelist-p-of-vl-unparamterize-1
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods)))
                  (force (vl-modulelist-complete-p mods mods))
                  (force (vl-good-paramdecllist-list-p (vl-modulelist->paramdecls mods))))
             (vl-modulelist-p (mv-nth 1 (vl-unparameterize mods n))))
    :hints(("Goal" :in-theory (disable (force))))))


