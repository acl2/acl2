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
(include-book "xf-unparam-check")
(include-book "../mlib/consteval")
(include-book "../mlib/subst")
(include-book "../mlib/typesubst")
(include-book "../mlib/fmt")
(include-book "../mlib/hierarchy")
(include-book "../mlib/remove-bad")
(include-book "../mlib/scopestack")
(local (include-book "../util/arithmetic"))
(local (include-book "../mlib/modname-sets"))
(local (include-book "../util/osets"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable vl-maybe-module-p-when-vl-module-p)))

(define vl-annotate-modules-with-warning ((x vl-modulelist-p)
                                          (warning vl-warning-p))
  :parents (warnings)
  :short "Add a warning to each module in a list of modules."
  :returns (new-x vl-modulelist-p)
  (b* (((when (atom x))
        nil)
       ((vl-module x1) (car x))
       (new-warnings   (cons (vl-warning-fix warning) x1.warnings))
       (new-x1         (change-vl-module x1 :warnings new-warnings)))
    (cons new-x1 (vl-annotate-modules-with-warning (cdr x) warning))))

(define vl-paramtype->default ((x vl-paramtype-p))
  :parents (vl-paramtype-p)
  :short "Get the default value from any @(see vl-paramtype-p)."
  :returns (value vl-maybe-paramvalue-p)
  (vl-paramtype-case x
    (:vl-implicitvalueparam x.default)
    (:vl-explicitvalueparam x.default)
    (:vl-typeparam          x.default))
  :prepwork ((local (in-theory (enable vl-maybe-paramvalue-p))))
  ///
  (defthm vl-paramtype->default-forward
    (or (not (vl-paramtype->default x))
        (vl-expr-p (vl-paramtype->default x))
        (vl-datatype-p (vl-paramtype->default x)))
    :rule-classes ((:forward-chaining :trigger-terms ((vl-paramtype->default x))))))


(defconst *vl-unparam-debug* nil)

(defmacro vl-unparam-debug (&rest args)
  `(and *vl-unparam-debug*
        (progn$ (cw "; UNPARAM: ~s0: " __function__)
                (vl-cw-ps-seq (vl-cw . ,args)))))

(defxdoc unparameterization
  :parents (transforms)
  :short "Expand away modules with parameters; similar to the idea of
<i>elaboration</i> of the design."

  :long "<p>Unparameterization is a Verilog transformation which, given a set
of Verilog modules, is supposed to produce an equivalent, parameter-free set of
modules.</p>


<h3>Background on Parameters</h3>

<p>See @(see vl-paramtype) and @(see vl-paramdecl) for background on our
representation of parameter declarations.  Parameters can be declared as either
ordinary @('parameter')s or as @('localparam')s.  Parameters may have default
values, and their defaults can refer to other parameters in the module.  Some
simple examples of parameters are:</p>

@({
    module m (a, b, c) ;
      ...
      parameter size = 4 ;
      localparam twosize = 2 * size ;
      ...
    endmodule
})

<p>Such a module can be instantiated in various ways, e.g.,:</p>

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
assigned to from outside the module.  They seem like about the cleanest way to
introduce named constants, as unlike @('`define') they don't pollute the global
namespace.</p>

<p>Parameters can also be given values via the @('defparam') statement, but
this construct is being deprecated (see SystemVerilog-2012 section C.4.1) and
may be removed from future versions of the language.  We generally think that
using @('defparam') is bad form.  VL does not support @('defparam'), so we do
not consider it here.</p>


<h3>Unparameterization</h3>

<p>The basic idea behind unparameterization is pretty simple.</p>

<p>Suppose we are dealing with a parameterized module called @('plus'), which
takes a single parameter called @('size').  There may be several modules, say
@('m1'), @('m2'), and @('m3'), which contain instances of @('plus') with
different sizes, say @('8'), @('16'), and @('32').</p>

<p>Our general goal is to eliminate @('plus') from our module list by replacing
it with three new modules, @('plus$size=8'), @('plus$size=16'), and
@('plus$size=32'), which are copies of @('plus') except that @('size') has been
replaced everywhere with @('8'), @('16'), or @('32') as suggested by their
names.</p>

<p>At the same time, we need to change the instances of @('plus') throughout
@('m1'), @('m2'), and @('m3') with appropriate instances of the new modules.
Finally, once all of the instances of the generic @('plus') have been done away
with, we can safely remove @('plus') from our module list.</p>")


; Overriding Parameter Defaults with New Expressions or Data Types ------------
;
; We now focus on how to override a single parameter with whatever datatype or
; value it is supposed to ultimately become.
;
; Suppose we have an instance, INST, of some parameterized module MOD.  For any
; particular parameter P, INST may specify a new value or datatype for P, or it
; may not, in which case P should assume its default value, which may be stated
; in terms of other parameters.
;
; When INST does override P, there are fairly elaborate rules for how these
; overrides are to be carried out.  The parameter can have its own type
; attributes and these have to be reconciled with the type of the override.
; The way this reconciliation is done follows strict rules, but rules which are
; somewhat elaborate and have a rather arbitrary feel.
;
; We now develop vl-override-parameter-value, which, we think, correctly
; implements these rules and allows us to correctly override a single parameter
; with the value supplied by the module instance.

(local (xdoc::set-default-parents vl-override-parameter-value))

(define vl-override-parameter-with-type
  :short "Try to override a parameter with a new datatype."
  ((decl     vl-paramdecl-p        "Some parameter from the submodule.")
   (datatype vl-datatype-p         "A new datatype to override this parameter with.")
   (warnings vl-warninglist-p      "Warnings accumulator for the submodule.")
   (ctx      vl-context-p          "Context for error messages."))
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (new-decl  vl-paramdecl-p
                          "Rewritten parameter declaration, overwritten as
                           specified by the submodule."))
  (b* ((decl     (vl-paramdecl-fix decl))
       (datatype (vl-datatype-fix datatype))
       (ctx     (vl-context-fix ctx))

       ((vl-paramdecl decl) decl)
       ((unless (eq (vl-paramtype-kind decl.type) :vl-typeparam))
        (vl-unparam-debug "~a0: trying to override value parameter ~a1 with datatype ~a2.~%"
                          ctx decl datatype)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: can't override parameter ~s1 with datatype ~a2: ~
                         ~s1 is a value parameter, not a type parameter."
                   :args (list ctx decl.name datatype))
            decl))

       ;; It seems like we might want to do some other kinds of sanity/error
       ;; checking here, but I'm not sure what that would look like.  Well
       ;; maybe we don't?  After all, this is basically just setting up a type
       ;; alias.  What kinds of things could go wrong?
       ;;
       ;;   - The type might be sort of malformed or non-existent, e.g., the
       ;;     instance could say use foo_t but this might not be a defined
       ;;     type, or could say to use a struct { foo_t a; int b; } when foo_t
       ;;     doesn't exist, or something like that.
       ;;
       ;;   - The type might not make sense in a context where it's used.  For
       ;;     instance, suppose that somewhere in the module we try to add one
       ;;     to a variable of this type.  That won't make sense if the
       ;;     instance overrides this type with, say, an unpacked struct.
       ;;
       ;;   - Probably other things I haven't thought through very well yet.
       ;;
       ;; Well, so what?  I think all of these could also be problems with the
       ;; parameter's default type.  So, it seems like probably we don't have
       ;; to be especially worried with sanity checking this kind of stuff at
       ;; override time.
       (new-type (change-vl-typeparam decl.type :default datatype))
       (new-decl (change-vl-paramdecl decl :type new-type)))
    (vl-unparam-debug "~a0: parameter ~a1 becomes ~a2.~%" ctx decl new-decl)
    (mv t (ok) new-decl)))

(define vl-convert-parameter-value-to-explicit-type
  :short "Alter the expression given to an explicitly typed parameter so that
          it has the correct type."
  ((type     vl-datatype-p    "The type of the parameter.")
   (expr     vl-expr-p        "The override expression given to this parameter.")
   (ss       vl-scopestack-p  "Scopestack")
   (warnings vl-warninglist-p "Warnings accumulator for the submodule.")
   (ctx      vl-context-p     "Context for error messages.")
   (paramname stringp         "More context for error messages."))

  :returns (mv (okp      booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-expr vl-expr-p
                         "On success, the possibly rewritten expression, with
                          its type and width now agreeing with type."))

  :long "<p>It seems generally tricky to coerce arbitrary expressions to have
arbitrary types.  We don't try very hard yet, for instance we don't yet
understand things like structs or user-defined types.  We do at least try to do
basic evaluation using @(see vl-consteval) and handle coercions for integer
types.</p>"

  (b* ((type      (vl-datatype-fix type))
       (expr      (vl-expr-fix expr))
       (ctx      (vl-context-fix ctx))
       (paramname (string-fix paramname))

       ((mv ok reduced-expr) (vl-consteval expr ss))
       ((unless ok)
        (vl-unparam-debug "~a0: only reduced ~a1 to ~a2 (not a constant).~%"
                          ctx expr reduced-expr)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: can't override parameter ~s1: failed to reduce ~
                         expression ~a2 to a constant integer."
                   :args (list ctx paramname expr))
            expr))

       ;; Otherwise, VAL is a resolved expression and we know its actual size
       ;; and type.  We want to convert it from whatever size/type it currently
       ;; happens to have into the type that is specified by this parameter.
       ;; That means getting the type and size from a datatype.
       ((mv warning desired-width) (vl-packed-datatype-size type))
       ((mv okp2 errmsg2 desired-type)  (vl-datatype-exprtype type))
       ((unless (and (not warning) okp2 desired-width desired-type))
        (vl-unparam-debug "~a0: can't override ~a1: width or type unknown: width ~a2, type ~a3; ~s4/~s5."
                          ctx paramname desired-width desired-type
                          warning errmsg2)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: can't override parameter ~s1: don't know the ~
                         correct width/signedness for type ~a2; ~s3/~s4."
                   :args (list ctx paramname type warning errmsg2))
            expr))

       ;; Theory: correct way to do conversion is:
       ;;   (1) truncate any parameter that is too large (with a warning)
       ;;   (2) sign-extend signed values to the desired width
       ;;   (3) zero-extend unsigned values to the desired width
       ;; I don't think we care about the final type for anything?
       ;; BOZO develop evidence for this theory, i.e., as new systests.
       (actual-val    (vl-resolved->val reduced-expr))
       (actual-width  (vl-expr->finalwidth reduced-expr))
       (actual-type   (vl-expr->finaltype reduced-expr))

       (signed-interp (if (eq actual-type :vl-signed)
                          (acl2::fast-logext actual-width actual-val)
                        actual-val))
       (fits-p        (if (eq desired-type :vl-signed)
                          (signed-byte-p desired-width signed-interp)
                        (unsigned-byte-p desired-width actual-val)))

       (warnings
        (if fits-p
            (ok)
          (warn :type :vl-truncated-parameter
                :msg "~a0: overriding parameter ~s1 (~x2 bits) with ~
                       value ~x3 (~x4 bits).  It doesn't fit and has ~
                       to get truncated!"
                :args (list ctx paramname desired-width
                            actual-val actual-width))))

       (new-value (cond ((<= desired-width actual-width)
                         ;; Maybe a truncation, but definitely not an
                         ;; extension.
                         (acl2::loghead desired-width actual-val))
                        ((eq actual-type :vl-signed)
                         ;; Sign extension
                         (acl2::loghead desired-width signed-interp))
                        (t
                         ;; Zero extension
                         actual-val)))

       (new-expr  (vl-consteval-ans :value new-value
                                    :width desired-width
                                    :type desired-type)))

    (vl-unparam-debug "~a0: overriding parameter ~a1, new expr is ~a2: ~x2.~%"
                      ctx paramname new-expr)
    (mv t warnings new-expr))

  :prepwork
  ((local (defthm l0
            (implies (and (vl-expr-resolved-p x)
                          (vl-expr-welltyped-p x))
                     (< (vl-resolved->val x)
                        (expt 2 (vl-expr->finalwidth x))))
            :rule-classes ((:rewrite) (:linear))
            :hints(("Goal" :in-theory (enable vl-expr-resolved-p
                                              vl-expr-welltyped-p
                                              vl-atom-welltyped-p
                                              vl-expr->finalwidth
                                              vl-resolved->val))))))

  :guard-hints(("Goal"
                :in-theory (disable l0)
                :use ((:instance l0
                       (x (mv-nth 1 (vl-consteval expr ss))))))))

(define vl-override-parameter-with-expr
  :short "Try to override a parameter with a new expression."
  ((decl     vl-paramdecl-p        "Some parameter from the submodule.")
   (expr     vl-expr-p             "The value expression to override this parameter with.")
   (ss       vl-scopestack-p       "Scopestack")
   (warnings vl-warninglist-p      "Warnings accumulator for the submodule.")
   (ctx      vl-context-p          "Context for error messages."))
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (new-decl  vl-paramdecl-p
                          "Rewritten parameter declaration, overwritten as
                           specified by the submodule."))

  (b* (((vl-paramdecl decl) (vl-paramdecl-fix decl))
       (expr (vl-expr-fix expr))
       (ctx (vl-context-fix ctx)))

    (vl-paramtype-case decl.type
      (:vl-typeparam
       (vl-unparam-debug "~a0: can't override type parameter ~a1 width expression ~a2.~%"
                         ctx decl expr)
       (mv nil
           (fatal :type :vl-bad-instance
                  :msg "~a0: can't override parameter ~s1 with expression, ~
                        ~a2: ~s1 is a type parameter, not a value parameter."
                  :args (list ctx decl.name expr))
           decl))

      (:vl-explicitvalueparam
       ;; See the rules in SystemVerilog 23.10.  I think we should regard this
       ;; case as having an "explicit type and range specification", even
       ;; though that's pretty vague.  (We might not *really* have an explicit
       ;; range, but might have a datatype like "integer", which sort of
       ;; implicitly has a range.) If this is right, then we are supposed to
       ;; convert the override value (expr) so that it has the type and range
       ;; of this parameter.
       (b* (((mv okp warnings coerced-expr)
             (vl-convert-parameter-value-to-explicit-type decl.type.type expr ss warnings ctx decl.name))
            ((unless okp)
             ;; Already warned.
             (mv nil warnings decl))
            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            (new-type (change-vl-explicitvalueparam decl.type :default coerced-expr))
            (new-decl (change-vl-paramdecl decl :type new-type)))
         (vl-unparam-debug "~a0: successfully overriding value parameter ~a1 with ~a2.~%"
                           ctx decl new-decl)
         (mv t (ok) new-decl)))

      (:vl-implicitvalueparam
       ;; See the rules in SystemVerilog-2012 Section 23.10.
       (b* (((mv ok reduced-expr) (vl-consteval expr ss))
            ((unless ok)
             (vl-unparam-debug "~a0: can't override ~a1, only reduced expr ~a2 to ~a3 (not a constant)."
                               ctx decl expr reduced-expr)
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "~a0: can't override parameter ~s1: failed to ~
                              reduce expression ~a2 to a constant integer."
                        :args (list ctx decl.name expr))
                 decl))

            (new-dims
             ;; After looking through the cases, the rule seems to be: if the
             ;; parameter provides a range, then that's the range that will be
             ;; used.  Otherwise, use the range from the final value.
             (cond (decl.type.range
                    (list decl.type.range))
                   ;; For nice cosmetics, don't use a range if we don't need one.
                   ((eql 1 (vl-expr->finalwidth reduced-expr))
                    ;; One bit, no dims needed
                    nil)
                   (t
                    (list (vl-make-n-bit-range (vl-expr->finalwidth reduced-expr))))))

            (new-signedp
             (cond ((and (not decl.type.range) (not decl.type.sign))
                    ;; "A value parameter declaration with no type or range
                    ;; specification shall default to the type and range of the
                    ;; final override value assigned to the parameter."
                    (eq (vl-expr->finaltype reduced-expr) :vl-signed))
                   ;; Otherwise, after looking through the cases, the rule
                   ;; seems to be: if there's an explicit signedness on the
                   ;; parameter, that's what we are to use.  Otherwise, since
                   ;; we know (by the WHEN check above) that we're in the case
                   ;; where we have at least a sign or a range, this should be
                   ;; unsigned.
                   (decl.type.sign
                    (eq decl.type.sign :vl-signed))
                   (t
                    ;; Explicit range but no sign: unsigned.
                    nil)))

            ;; Now we know enough to figure out our explicit final type.
            (explicit-type (make-vl-coretype :name :vl-logic
                                             :signedp new-signedp
                                             :pdims new-dims))
            ((mv okp warnings coerced-expr)
             ;; Do the conversion explicitly, which gives us all the nice warnings.
             (vl-convert-parameter-value-to-explicit-type explicit-type reduced-expr ss warnings ctx decl.name))
            ((unless okp)
             ;; Already warned
             (mv nil warnings decl))
            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            (new-type (make-vl-explicitvalueparam :type explicit-type :default coerced-expr))
            (new-decl (change-vl-paramdecl decl :type new-type)))
         (vl-unparam-debug "~a0: successfully overriding ~a1 with ~a2.~%"
                           ctx decl new-decl)
         (mv t (ok) new-decl))))))

(define vl-override-parameter-value
  :parents (unparameterization)
  :short "Try to override an arbitrary parameter with its final value."
  ((decl     vl-paramdecl-p     "Some parameter from the submodule.")
   (value    vl-paramvalue-p    "Final value to override the parameter with.")
   (ss       vl-scopestack-p    "Scopestack")
   (warnings vl-warninglist-p   "Warnings accumulator for the submodule.")
   (ctx      vl-context-p       "Context for error messages."))
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (new-decl  vl-paramdecl-p
                          "Rewritten parameter declaration, overwritten as
                           specified by the submodule."))
  :guard-hints(("Goal" :in-theory (enable vl-maybe-paramvalue-p)))
  (b* ((decl  (vl-paramdecl-fix decl))
       (value (vl-paramvalue-fix value))
       ((when (vl-paramvalue-datatype-p value))
        (vl-override-parameter-with-type decl value warnings ctx)))
    (vl-override-parameter-with-expr decl value ss warnings ctx)))


; Lining Up Parameter Declarations with Override Values -----------------------
;
; Instances can have override parameters using either named or unnamed format.
; We now pair up the parameter declarations with their replacements.  We
; produce the list in parameter-declaration order, so that later we can
; properly account for dependencies between the parameters.

(local (xdoc::set-default-parents vl-make-paramdecloverrides))

(defprojection vl-namedparamvaluelist->names ((x vl-namedparamvaluelist-p))
  :returns (names string-listp)
  (vl-namedparamvalue->name x))

(define vl-find-namedparamvalue ((name stringp)
                                 (args vl-namedparamvaluelist-p))
  :returns (arg (equal (vl-namedparamvalue-p arg) (if arg t nil)))
  (b* (((when (atom args))
        nil)
       (arg1 (vl-namedparamvalue-fix (car args)))
       ((when (equal (vl-namedparamvalue->name arg1)
                     (string-fix name)))
        arg1))
    (vl-find-namedparamvalue name (cdr args)))
  ///
  (defthm vl-find-namedparamvalue-when-member-of-vl-namedparamvaluelist->names
    (implies (and (member name (vl-namedparamvaluelist->names args))
                  (stringp name))
             (vl-find-namedparamvalue name args))))

(define vl-nonlocal-paramdecls
  :short "Filter parameter declarations, keeping only the non-local declarations."
  ((x vl-paramdecllist-p))
  :returns (nonlocal-params vl-paramdecllist-p)
  (cond ((atom x)
         nil)
        ((vl-paramdecl->localp (car x))
         (vl-nonlocal-paramdecls (cdr x)))
        (t
         (cons (vl-paramdecl-fix (car x))
               (vl-nonlocal-paramdecls (cdr x)))))
  ///
  (defthm vl-nonlocal-paramdecls-of-atom
    (implies (atom x)
             (equal (vl-nonlocal-paramdecls x)
                    nil)))
  (defthm vl-nonlocal-paramdecls-of-cons
    (equal (vl-nonlocal-paramdecls (cons a x))
           (if (vl-paramdecl->localp a)
               (vl-nonlocal-paramdecls x)
             (cons (vl-paramdecl-fix a) (vl-nonlocal-paramdecls x))))))

(defprod vl-paramdecloverride
  :short "Paired up parameter declaration with its override values from a
          module instance."
  ((decl     vl-paramdecl-p)
   (override vl-maybe-paramvalue-p)))

(fty::deflist vl-paramdecloverridelist
  :elt-type vl-paramdecloverride-p
  :elementp-of-nil nil
  :true-listp nil)

(define vl-make-paramdecloverrides-named
  :parents (unparameterization)
  :short "Line up named parameter arguments with parameter declarations."
  ((formals vl-paramdecllist-p       "In proper order, from the submodule.")
   (actuals vl-namedparamvaluelist-p "From the instance."))
  :returns (overrides vl-paramdecloverridelist-p)
  (b* (((when (atom formals))
        nil)
       ((vl-paramdecl decl1) (vl-paramdecl-fix (car formals)))

       ((when decl1.localp)
        ;; Local parameters don't get any explicit overrides.
        (cons (make-vl-paramdecloverride :decl decl1
                                         :override nil)
              (vl-make-paramdecloverrides-named (cdr formals) actuals)))

       (look  (vl-find-namedparamvalue decl1.name actuals))
       (value (and look
                   (vl-namedparamvalue->value look))))

    (cons (make-vl-paramdecloverride :decl decl1
                                     :override value)
          (vl-make-paramdecloverrides-named (cdr formals) actuals))))

(define vl-make-paramdecloverrides-indexed
  :short "Line up positional parameter arguments with parameter declarations."
  ((formals vl-paramdecllist-p  "In proper order, from the submodule.")
   (actuals vl-paramvaluelist-p "In proper order, from the instance."))
  :guard (<= (len actuals) (len (vl-nonlocal-paramdecls formals)))
  :returns (overrides vl-paramdecloverridelist-p)
  (b* (((when (atom formals))
        nil)
       ((vl-paramdecl decl1) (vl-paramdecl-fix (car formals)))

       ((when decl1.localp)
        ;; Local parameters don't get any explicit overrides.
        (cons (make-vl-paramdecloverride :decl decl1
                                         :override nil)
              (vl-make-paramdecloverrides-indexed (cdr formals) actuals)))

       ;; We can run out of actuals and that's okay, all remaining formals
       ;; just get no explicit values.
       (value (and (consp actuals)
                   (vl-paramvalue-fix (first actuals)))))

    (cons (make-vl-paramdecloverride :decl decl1
                                     :override value)
          (vl-make-paramdecloverrides-indexed (cdr formals)
                                              (and (consp actuals)
                                                   (rest actuals))))))

(define vl-make-paramdecloverrides
  :parents (unparameterization)
  :short "Line up parameter arguments with parameter declarations."
  ((formals  vl-paramdecllist-p "In proper order, from the submodule.")
   (actuals  vl-paramargs-p     "From the instance.")
   (warnings vl-warninglist-p   "Warnings accumulator for the superior module.")
   (ctx     vl-context-p       "Context for error messages."))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (overrides vl-paramdecloverridelist-p))
  (b* ((formals           (vl-paramdecllist-fix formals))
       (ctx               (vl-context-fix ctx))

       ((unless (uniquep (vl-paramdecllist->names formals)))
        ;; Not a great place to check for this, but better safe than sorry.
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: parameters are not unique: ~&1."
                   :args (list ctx (duplicated-members (vl-paramdecllist->names formals))))
            nil)))

    (vl-paramargs-case actuals

      (:vl-paramargs-named
       (b* ((actual-names (vl-namedparamvaluelist->names actuals.args))
            (formal-names (vl-paramdecllist->names (vl-nonlocal-paramdecls formals)))

            ((unless (uniquep actual-names))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "~a0: multiple occurrences of parameter arguments: ~&1."
                        :args (list ctx (duplicated-members actual-names)))
                 nil))

            (illegal-names
             ;; Actuals that are NOT actually declarations.
             (difference (mergesort actual-names) (mergesort formal-names)))
            ((when illegal-names)
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "~a0: parameter~s1 ~&2 ~s2."
                        :args (list ctx
                                    (if (vl-plural-p illegal-names) "s" "")
                                    illegal-names
                                    (if (vl-plural-p illegal-names) "do not exist" "does not exist")))
                 nil))

            ;; No confusion: everything is unique, the instance mentions only
            ;; the non-localparams, etc.  Good enough.
            (overrides (vl-make-paramdecloverrides-named formals actuals.args)))
         (mv t (ok) overrides)))

      (:vl-paramargs-plain
       (b* ((num-formals (len (vl-nonlocal-paramdecls formals)))
            (num-actuals (len actuals.args))
            ((unless (<= num-actuals num-formals))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "~a0: too many parameter values: ~x1 (non-local) ~
                              parameter~s2, but is given ~x3 parameter argument~s5."
                        :args (list ctx
                                    num-formals
                                    (if (eql num-formals 1) "" "s")
                                    num-actuals
                                    (if (eql num-actuals 1) "" "s")))
                 nil))

            ;; Else no worries, not too many parameters
            (overrides (vl-make-paramdecloverrides-indexed formals actuals.args)))
         (mv t (ok) overrides))))))


; Final Parameter Preparation -------------------------------------------------
;
; We're now going to march through the list of overrides, which binds each
; parameter to its final override value/type (if any) from the instance.  We
; work in parameter-declaration order, which is important for parameters that
; depend on earlier parameters.
;
; For each parameter, we try to apply the override that we've been given (if
; applicable).  This involves a lot of error checking to make sure that things
; are of compatible-enough types.
;
; On success we produce a two substitutions:
;
;   ValSigma - a vl-sigma-p (names to expressions) for the value parameters,
;   TypeSigma  - a vl-typesigma-p (names to datatypes) for the type parameters.
;
; The general idea is to then substitute these sigmas throughout the module.


; Subtle: as we process each parameter, we need to substitute the sigmas for
; the previous parameters at the correct time.
;
; Suppose that X is a vl-paramdecloverride-p.
; Consider: Where in X might the previous parameters be mentioned?
;
;   (1) They can be mentioned in the type of x.decl.  For instance:
;
;          parameter maxidx = 6;
;          parameter logic [maxidx:0] foo = 0;   <-- uses maxidx
;
;   (2) They can be mentioned in the default value of x.decl.  For instance:
;
;          parameter maxidx = 6;
;          parameter twomaxidx = maxidx * 2;     <-- uses maxidx
;
;   (3) They can NOT be used in the override value.  That is, it doesn't make
;       sense to do:
;
;       module mymod (...) ;
;          parameter maxidx = 3;
;          parameter otheridx = 4;
;          ...
;       endmodule
;
;       module superior (...) ;
;          mymod (.otheridx(maxidx * 2)) inst (...);   <-- nonsense, maxidx is in the other module!
;       endmodule
;
; So, the order of operations here is important.
;
;   Step 1: substitute the current sigmas into the declaration
;           (but not the override value)
;
;   Step 2: try to apply the override to the rewritten declaration
;
; If you are tempted to change how any of this works, especially consider the
; following example:

#||
    module foo (o);
      parameter maxidx = 6;
      parameter logic [maxidx:0] ans = 0;
      output [63:0] o;
      assign o = ans;
    endmodule

    module top () ;
      wire [63:0] o1;
      foo #(.ans(3'sb101)) inst (o1);
      initial begin
        #10;
        $display("o1 is %d", o1);
      end
    endmodule
||#

; On NCV and VCS this example prints 125.  It can only possibly work this way
; if the maxidx parameter is substituted into the ans parameter's type before
; the override is applied!

(local (xdoc::set-default-parents vl-override-parameters))

(define vl-pre-substitute-param
  ((x         vl-paramdecl-p    "Parameter declaration we're preparing.")
   (valsigma  vl-sigma-p        "Value substitution we've accumulated so far, fast alist.")
   (typesigma vl-typesigma-p    "Type substitution we've accumulated so far, fast alist.")
   (warnings  vl-warninglist-p  "Warnings accumulator for the submodule.")
   (ctx       vl-context-p      "Context for error messages."))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (new-x    vl-paramdecl-p))
  (b* ((ctx (vl-context-fix ctx))
       ((vl-paramdecl x) x)
       ;; BOZO can the order of the substitutions possibly matter?  I don't
       ;; think it should be able to, at least if parameters are always defined
       ;; before use, but I haven't really thought it through very clearly yet.
       (type x.type)
       (type                   (vl-paramtype-subst type valsigma))
       ((mv okp warnings type) (vl-paramtype-typesubst type typesigma
                                                       (vl-context->elem ctx)
                                                       warnings))
       (new-x (change-vl-paramdecl x :type type)))
    (mv okp warnings new-x)))

(define vl-override-parameter-1
  :short "Override a single parameter, extending the value and type sigmas."
  ((x         vl-paramdecloverride-p "Parameter and its final override to process.")
   (valsigma  vl-sigma-p             "Value substitution we're accumulating.")
   (typesigma vl-typesigma-p         "Type substitution we're accumulating.")
   (ss        vl-scopestack-p        "Scopestack")
   (warnings  vl-warninglist-p       "Warnings accumulator for the submodule.")
   (ctx       vl-context-p           "Context for error messages."))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (valsigma  vl-sigma-p        "Extended on success.")
      (typesigma vl-typesigma-p    "Extended on success."))
  (b* ((valsigma  (vl-sigma-fix valsigma))
       (typesigma (vl-typesigma-fix typesigma))
       (ctx      (vl-context-fix ctx))

       ;; Substitute the sigmas so far into the param decl, possibly fixing up
       ;; its datatype and default value.  Do NOT substitute them into the
       ;; override --- it comes from the submodule instance.
       ((mv okp warnings decl)
        (vl-pre-substitute-param (vl-paramdecloverride->decl x) valsigma typesigma warnings ctx))
       ((unless okp)
        ;; Already warned.
        (vl-unparam-debug "~a0: failed to pre-substitute into ~a1.~%"
                          ctx (vl-paramdecloverride->decl x))
        (mv nil warnings valsigma typesigma))

       (name (vl-paramdecl->name decl))
       (override
        ;; Determine the final value to override this parameter with.  If the
        ;; instance provided a value, we use that.  Otherwise, if the parameter
        ;; has a default, we use that.
        (or (vl-paramdecloverride->override x)
            (vl-paramtype->default (vl-paramdecl->type decl))))

       ((unless override)
        ;; No default value and no value provided by the instance: whoops.
        (vl-unparam-debug "~a0: no value for ~s1.~%" ctx name)
        (mv nil
            (fatal :type :vl-bad-inst
                   :msg "~a0: no value for parameter ~s1."
                   :args (list ctx name))
            valsigma
            typesigma))

       ;; Coerce the override value into the correct type.
       ((mv okp warnings decl)
        (vl-override-parameter-value decl override ss warnings ctx))
       ((unless okp)
        (vl-unparam-debug "~a0: failed to override ~a1 with ~a2.~%" ctx decl override)
        ;; Already warned.
        (mv nil warnings valsigma typesigma))

       ;; Extend the appropriate sigma.
       (final (vl-paramtype->default (vl-paramdecl->type decl)))
       ((unless final)
        (vl-unparam-debug "~a0: after overriding, no default value?? new, raw decl: ~x1" ctx decl)
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: paramdecl ~x1 somehow has no value?"
                   :args (list ctx name))
            valsigma typesigma))

       ((when (vl-paramvalue-expr-p final))
        (vl-unparam-debug "~a0: OK - extending valsigma: ~a1 --> ~a2.~%" ctx name final)
        (mv t (ok) (hons-acons! name final valsigma) typesigma)))

    (vl-unparam-debug "~a0: OK - extending typesigma: ~a1 --> ~a2.~%" ctx name final)
    (mv t (ok) valsigma (hons-acons! name final typesigma))))

(define vl-override-parameters
  :parents (unparameterization)
  :short "Override all parameters, creating value and type sigmas."
  ((x         vl-paramdecloverridelist-p "Overrides from @(see vl-make-paramdecloverrides).")
   (valsigma  vl-sigma-p                 "Value substitution we're accumulating.")
   (typesigma vl-typesigma-p             "Type substitution we're accumulating.")
   (ss        vl-scopestack-p            "Scopestack")
   (warnings  vl-warninglist-p           "Warnings accumulator for the submodule.")
   (ctx       vl-context-p               "Context for error messages."))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (valsigma  vl-sigma-p        "Extended on success.")
      (typesigma vl-typesigma-p    "Extended on success."))
  (b* (((when (atom x))
        (mv t (ok) (vl-sigma-fix valsigma) (vl-typesigma-fix typesigma)))

       ((mv okp warnings valsigma typesigma)
        (vl-override-parameter-1 (car x) valsigma typesigma ss warnings ctx))
       ((unless okp)
        (mv nil warnings valsigma typesigma)))
    (vl-override-parameters (cdr x) valsigma typesigma ss warnings ctx)))



; Applying Substitutions, Unparameterizing an Instance ------------------------
;
; To review, we now have everything for
;   - lining up the actuals with the parameter declarations
;   - coercing types and turning parameters into value/type sigmas
;
; To expand out the parameters, then, we just need to give the module a new
; name and apply the desired substitutions.
;
; We want the new modules to have unique names.  We'll use the value/type
; sigmas to generate names.

(local (xdoc::set-default-parents vl-maybe-unparam-inst))

(define vl-unparam-valsigma-name ((sigma vl-sigma-p) &key (ps 'ps))
  :parents (vl-unparam-newname)
  :measure (vl-sigma-count sigma)
  :hooks ((:fix :hints (("goal" :expand ((vl-unparam-valsigma-name sigma)
                                         (vl-unparam-valsigma-name
                                          (vl-sigma-fix sigma)))
                         :induct (vl-unparam-valsigma-name sigma)
                         :in-theory (disable (:d vl-unparam-valsigma-name))))))
  (b* ((sigma (vl-sigma-fix sigma))
       ((when (atom sigma))
        ps)
       ((cons name expr) (car sigma))
       ((the string name-part)
        (acl2::substitute #\_ #\Space name))
       ((the string expr-part)
        (if (and (vl-expr-resolved-p expr)
                 (equal (vl-expr->finalwidth expr) 32)
                 (equal (vl-expr->finaltype expr) :vl-signed))
            ;; Special case to avoid things like size=32'sd5.
            (str::natstr (vl-resolved->val expr))
          (acl2::substitute #\_ #\Space (vl-pps-expr expr)))))
    (vl-ps-seq (vl-print "$")
               (vl-print-str name-part)
               (vl-print "=")
               (vl-print-str expr-part)
               (vl-unparam-valsigma-name (cdr sigma)))))

(define vl-unparam-typesigma-name ((sigma vl-typesigma-p) &key (ps 'ps))
  :parents (vl-unparam-newname)
  :measure (vl-typesigma-count sigma)
  :hooks ((:fix :hints (("goal" :expand ((vl-unparam-typesigma-name sigma)
                                         (vl-unparam-typesigma-name
                                          (vl-typesigma-fix sigma)))
                         :induct (vl-unparam-typesigma-name sigma)
                         :in-theory (disable (:d vl-unparam-typesigma-name))))))
  (b* ((sigma (vl-typesigma-fix sigma))
       ((when (atom sigma))
        ps)
       ((cons name type) (car sigma))
       ((the string name-part)
        (acl2::substitute #\_ #\Space name))
       ((the string type-part)
        (acl2::substitute #\_ #\Space (with-local-ps (vl-pp-datatype type)))))
    (vl-ps-seq (vl-print "$")
               (vl-print-str name-part)
               (vl-print "=")
               (vl-print-str type-part)
               (vl-unparam-typesigma-name (cdr sigma)))))

(define vl-unparam-newname
  :short "Generate a new name for an unparameterized module."
  ((origname  stringp        "Original name of the module, e.g., @('my_adder').")
   (valsigma  vl-sigma-p     "Binds value parameters to expressions, e.g., @('size <-- 5').")
   (typesigma vl-typesigma-p "Binds type parameters to types, e.g., @('foo_t <-- logic [3:0]')."))
  :returns (new-name stringp :rule-classes :type-prescription
                     "New, mangled name, e.g., @('my_adder$size=5').")
  :long "<p>This is a dumb but probably sufficient way to generate new names.
Note that we explicitly check (later on) that no name conflicts are
introduced.</p>"
  (hons-copy (with-local-ps (vl-ps-seq (vl-print-str origname)
                                       (vl-unparam-valsigma-name valsigma)
                                       (vl-unparam-typesigma-name typesigma)))))

(define vl-create-unparameterized-module
  :short "Apply substitutions to actually unparameterize a module. (memoized)"
  ((mod       vl-module-p)
   (valsigma  vl-sigma-p      "A <b>honsed</b> fast alist (for memoization).")
   (typesigma vl-typesigma-p  "A <b>honsed</b> fast alist (for memoization)."))
  :returns (mv (okp booleanp :rule-classes :type-prescription)
               (new-mod vl-module-p))
  (b* ((name (vl-unparam-newname (vl-module->name mod) valsigma typesigma))
       (mod  (change-vl-module mod :name name :paramdecls nil))
       ((with-fast valsigma typesigma))
       (mod  (vl-module-subst mod valsigma))
       ((mv okp mod) (vl-module-typesubst mod typesigma)))
    (mv okp mod)))


(defprod vl-unparam-signature
  :parents (unparameterization)
  :short "A unique object representing a complete assignment of parameters to a module."
  ((name      stringp)
   (valsigma  vl-sigma-p)
   (typesigma vl-typesigma-p))
  :layout :tree
  :hons t)

(fty::deflist vl-unparam-signaturelist :elt-type vl-unparam-signature
  :elementp-of-nil nil)





(define vl-unparam-inst
  :parents (unparameterization)
  :short "Try to unparameterize a single module instance."

  ((inst     vl-modinst-p
             "Instance of some module.  The module being instantiated may or
              may not have parameters.")
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p
             "Warnings accumulator for the submodule.")
   (modname  stringp "Containing module name, for context"))

  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (inst     vl-modinst-p
                "Updated module instance, perhaps instantiating a new module
                 like @('my_adder$width=5') instead of @('my_adder').")
      (needed-sigs (iff (vl-unparam-signature-p needed-sigs) needed-sigs)
                   "An unparam-signature for the instantiated module, if needed."))

  (b* (((vl-modinst inst) (vl-modinst-fix inst))

       (mod (vl-scopestack-find-definition inst.modname ss))
       ((unless (and mod (eq (tag mod) :vl-module)))
        (vl-unparam-debug "~a0: can't find module ~a1.~%" inst.modname)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: trying to instantiate undefined module ~s1."
                   :args (list inst inst.modname))
            inst nil))

       ((vl-module mod) mod)

       ((when (atom mod.paramdecls))
        ;; Optimization.  In the common case there are no parameter
        ;; declarations for the submodule.  In this case, all we need to do is
        ;; make sure the instance is also parameter-free.
        (if (vl-paramargs-empty-p inst.paramargs)
            (mv t (ok) inst 
                (make-vl-unparam-signature :name inst.modname))
          (mv nil
              (fatal :type :vl-bad-instance
                     :msg "~a0: parameter arguments given to ~s1, but ~s1 ~
                           does not take any parameters."
                     :args (list inst inst.modname))
              inst nil)))

       (ctx (make-vl-context :mod modname :elem inst))
       ;; Line up formals/actuals
       ((mv okp warnings overrides)
        (vl-make-paramdecloverrides mod.paramdecls inst.paramargs warnings ctx))
       ((unless okp)
        ;; Already warned.
        (vl-unparam-debug "~a0: failed to line up formals/actuals.~%" inst)
        (mv nil warnings inst nil))

       ;; Create sigmas
       (valsigma  nil)
       (typesigma nil)
       ((mv okp warnings valsigma typesigma)
        (vl-override-parameters overrides valsigma typesigma ss warnings ctx))
       ((acl2::free-on-exit valsigma typesigma))

       ((unless okp)
        ;; Already warned
        (vl-unparam-debug "~a0: failed to create sigmas.~%" inst)
        (mv nil warnings inst nil))

       (- (vl-unparam-debug "~a0: raw value sigma: ~x1~%raw type sigma: ~x2~%"
                            inst valsigma typesigma))

       (new-modname      (vl-unparam-newname inst.modname valsigma typesigma))

       (new-inst (change-vl-modinst inst
                                    :modname new-modname
                                    :paramargs (make-vl-paramargs-plain :args nil)))

       (unparam-signature (make-vl-unparam-signature
                           :name inst.modname
                           :valsigma valsigma
                           :typesigma typesigma)))

    (vl-unparam-debug "~a0: success, new instance is ~a1.~%" inst new-inst)
    (mv t warnings new-inst unparam-signature)))


; Unparameterizing throughout a module ----------------------------------------

(local (xdoc::set-default-parents vl-unparameterize-module))

(define vl-unparam-instlist
  :short "Extension of @(see vl-unparam-inst) to a list of instances."
  ((insts    vl-modinstlist-p "List of instances to unparameterize.")
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p)
   (modname  stringp "containing module, for context"))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (new-insts vl-modinstlist-p)
      (needed-sigs vl-unparam-signaturelist-p))
  :hooks ((:fix :hints (("goal" :induct (vl-unparam-instlist insts ss warnings modname)
                         :in-theory (disable (:d vl-unparam-instlist) cons-equal)
                         :expand ((:free (ss warnings modname)
                                   (vl-unparam-instlist insts ss warnings modname))
                                  (vl-unparam-instlist (vl-modinstlist-fix insts) ss warnings modname))))))
  (b* (((when (atom insts))
        (mv t (ok) nil nil))
       ((mv okp1 warnings car-prime car-neededsigs)
        (vl-unparam-inst (car insts) ss warnings modname))
       ((mv okp2 warnings cdr-prime cdr-neededsigs)
        (vl-unparam-instlist (cdr insts) ss warnings modname)))
    (mv (and okp1 okp2)
        warnings
        (cons car-prime cdr-prime)
        (if car-neededsigs (cons car-neededsigs cdr-neededsigs) cdr-neededsigs))))

(defines vl-unparameterize-main
  :prepwork ((local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (vl-module-p x)
                               (vl-scope-p x)))))
  (define vl-unparameterize-main ((sig vl-unparam-signature-p)
                                  (donelist "fast alist of previously-seen signatures")
                                  (depthlimit natp "termination counter")
                                  (ss vl-scopestack-p))
    :measure (two-nats-measure depthlimit 0)
    :verify-guards nil
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-mods vl-modulelist-p
                  :hints ('(:in-theory (disable vl-unparameterize-main-list
                                                vl-unparameterize-main)
                            :expand ((vl-unparameterize-main sig donelist depthlimit ss)))))
                 (donelist))
    (b* (((when (hons-get sig donelist)) (mv t nil nil donelist))
         (warnings nil)
         ((when (zp depthlimit))
          (mv nil
              (fatal :type :vl-unparameterize-loop
                     :msg "Recursion depth ran out in unparameterize -- loop in the hierarchy?") 
              nil donelist))

         (donelist (hons-acons sig t donelist))

         ((vl-unparam-signature sig))
         (mod (vl-scopestack-find-definition sig.name ss))
         ((unless (and mod (eq (tag mod) :vl-module)))
          (mv nil
              (fatal :type :vl-unparameterize-programming-error
                     :msg "Couldn't find module ~s0"
                     :args (list sig.name))
              nil donelist))

         ((mv mod-okp new-mod)
          (if (and (atom sig.valsigma) (atom sig.typesigma))
              ;; No unparameterization neede
              (mv t mod)
            (vl-create-unparameterized-module mod sig.valsigma sig.typesigma)))

         ((vl-module new-mod))
         (warnings new-mod.warnings)
         (warnings (if mod-okp
                       warnings
                     (fatal :type :vl-unparam-fail
                            :msg "Unparameterizing ~s0 failed; see ~s1 for details."
                            :args (list sig.name (vl-module->name new-mod)))))

         (internal-ss (vl-scopestack-push mod ss))

         ((mv insts-okp warnings new-insts need-sigs)
          (vl-unparam-instlist new-mod.modinsts internal-ss warnings sig.name))

         (new-mod (change-vl-module new-mod :warnings warnings :modinsts new-insts))

         ((mv unparams-okp warnings new-mods donelist)
          (vl-unparameterize-main-list need-sigs donelist (1- depthlimit) ss)))
      (mv (and mod-okp insts-okp unparams-okp)
          warnings (cons new-mod new-mods) donelist)))

  (define vl-unparameterize-main-list ((sigs vl-unparam-signaturelist-p)
                                       (donelist)
                                       (depthlimit natp)
                                       (ss vl-scopestack-p))
    :measure (two-nats-measure depthlimit (len sigs))
    :returns (mv (successp booleanp :rule-classes :type-prescription)
                 (warnings vl-warninglist-p)
                 (new-mods vl-modulelist-p
                  :hints ('(:in-theory (disable vl-unparameterize-main-list
                                                vl-unparameterize-main)
                            :expand ((vl-unparameterize-main-list sigs donelist depthlimit ss)))))
                 (donelist))
    (b* (((when (atom sigs)) (mv t nil nil donelist))
         ((mv ok1 warnings1 new-mods1 donelist)
          (vl-unparameterize-main (car sigs) donelist depthlimit ss))
         ((mv ok2 warnings2 new-mods2 donelist)
          (vl-unparameterize-main-list (cdr sigs) donelist depthlimit ss)))
      (mv (and ok1 ok2)
          (append warnings1 warnings2)
          (append new-mods1 new-mods2)
          donelist)))
  ///
  (local (in-theory (disable vl-unparameterize-main
                             vl-unparameterize-main-list)))
  (defthm-vl-unparameterize-main-flag
    (defthm true-listp-of-vl-unparameterize-main-warnings
      (true-listp (mv-nth 1 (vl-unparameterize-main sig donelist depthlimit ss)))
      :hints ('(:expand ((vl-unparameterize-main sig donelist depthlimit ss))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main)
    (defthm true-listp-of-vl-unparameterize-main-list-warnings
      (true-listp (mv-nth 1 (vl-unparameterize-main-list sigs donelist depthlimit ss)))
      :hints ('(:expand ((vl-unparameterize-main-list sigs donelist depthlimit ss))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main-list))

  (defthm-vl-unparameterize-main-flag
    (defthm true-listp-of-vl-unparameterize-main-mods
      (true-listp (mv-nth 2 (vl-unparameterize-main sig donelist depthlimit ss)))
      :hints ('(:expand ((vl-unparameterize-main sig donelist depthlimit ss))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main)
    (defthm true-listp-of-vl-unparameterize-main-list-mods
      (true-listp (mv-nth 2 (vl-unparameterize-main-list sigs donelist depthlimit ss)))
      :hints ('(:expand ((vl-unparameterize-main-list sigs donelist depthlimit ss))))
      :rule-classes :type-prescription
      :flag vl-unparameterize-main-list))

  (verify-guards vl-unparameterize-main))



(define vl-module-default-signature ((modname stringp)
                                     (ss       vl-scopestack-p)
                                     (warnings vl-warninglist-p))
  :returns (mv (sig vl-unparam-signature-p)
               (warnings vl-warninglist-p))
  (b* ((modname (string-fix modname))
       (x (vl-scopestack-find-definition modname ss))
       ((unless (and x (eq (tag x) :vl-module)))
        (mv (make-vl-unparam-signature :name modname)
            (fatal :type :vl-unparam-fail
                   :msg "Programming error: top-level module ~s0 not found"
                   :args (list modname))))
       ((vl-module x))
       (ctx (make-vl-context :mod x.name :elem (make-vl-modinst :instname "top-level"
                                                                :modname x.name
                                                                :paramargs (make-vl-paramargs-named)
                                                                :portargs (make-vl-arguments-named)
                                                                :loc *vl-fakeloc*)))
       ((mv ?ok warnings overrides)
        (vl-make-paramdecloverrides x.paramdecls (make-vl-paramargs-named)
                                    warnings ctx))
       (valsigma  nil)
       (typesigma nil)
       ((mv ?okp warnings valsigma typesigma)
        (vl-override-parameters overrides valsigma typesigma ss warnings ctx))
       ((acl2::free-on-exit valsigma typesigma)))
    (mv (make-vl-unparam-signature :name x.name :valsigma valsigma :typesigma typesigma)
        warnings)))

(define vl-modulelist-default-signatures ((names string-listp)
                                          (ss    vl-scopestack-p)
                                          (warnings vl-warninglist-p))
  :returns (mv (sigs vl-unparam-signaturelist-p)
               (warnings vl-warninglist-p))
  (if (atom names)
      (mv nil (vl-warninglist-fix warnings))
    (b* (((mv sig warnings) (vl-module-default-signature (car names) ss warnings))
         ((mv sigs warnings) (vl-modulelist-default-signatures (cdr names) ss warnings)))
      (mv (cons sig sigs) warnings))))
  


(define vl-design-unparameterize
  :short "Top-level @(see unparameterization) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (;; Throw out modules that have problems with shadowed parameters.
       ((vl-design x) (vl-design-unparam-check x))
       (ss (vl-scopestack-init x))
       (topmods (vl-modulelist-toplevel x.mods))
       ((mv top-sigs warnings) (vl-modulelist-default-signatures topmods ss x.warnings))

       ((mv ?ok warnings1 new-mods donelist)
        (vl-unparameterize-main-list top-sigs nil 1000 ss))

       (warnings (append warnings1 warnings)))
    (fast-alist-free donelist)
    (change-vl-design x :warnings warnings :mods new-mods)))
