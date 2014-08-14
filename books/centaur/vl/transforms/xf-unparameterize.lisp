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
(include-book "../mlib/writer")           ; BOZO necessary?
(include-book "../mlib/remove-bad")       ; BOZO necessary?
(include-book "../mlib/print-warnings")   ; BOZO necessary?
(include-book "../wf-ranges-resolved-p")  ; BOZO necessary?
(include-book "../util/cwtime")           ; BOZO necessary?
(local (include-book "../util/arithmetic"))
(local (include-book "../mlib/modname-sets"))
(local (include-book "../util/osets"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))  ; BOZO necessary?
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

(define vl-datatype-width ((x vl-datatype-p))
  ;; BOZO misplaced, eventually should be integrated into sizing, etc.
  :returns (width maybe-posp :rule-classes :type-prescription)
  ;; We don't try very hard yet.
  (vl-datatype-case x
    (:vl-coretype
     (case x.name
       ;; See SystemVerilog-2012 Section 6.11, Integer Data Types.

       ;; integer atom types -- these don't have any dimensions, they're just fixed sizes
       (:vl-byte     8)
       (:vl-shortint 16)
       (:vl-int      32)
       (:vl-longint  64)
       (:vl-integer  32)
       (:vl-time     64)

       ;; integer vector types -- these have arbitrary packed dimensions.
       ((:vl-bit :vl-logic :vl-reg)
        (cond ((atom x.dims)
               ;; No dimensions means it's just a scalar
               1)
              ((atom (cdr x.dims))
               ;; A single dimension, maybe we can figure out its size
               (b* ((dim (car x.dims))
                    ((when (eq dim :vl-unsized-dimension))
                     ;; ah, what a pity
                     nil)
                    ((unless (vl-range-resolved-p dim))
                     ;; well shucks
                     nil))
                 (vl-range-size dim)))
              (t
               ;; Multiple dimensions?  Good luck with that.
               nil)))

       (otherwise
        ;; (:vl-shortreal :vl-real :vl-realtime)
        ;; We arguably *could* handle things like shortreal/real/realtime and even perhaps string,
        ;; but that doesn't seem like anything we actually *should* do.
        nil)))

    (:vl-struct
     ;; Maybe some day support packed structure sizes
     nil)

    (:vl-union
     ;; Can these even be packed?
     nil)

    (:vl-usertype
     ;; BOZO maybe some day extend this to be able to do lookups
     nil)))

(define vl-datatype-exprtype ((x vl-datatype-p))
  ;; BOZO misplaced, eventually should be integrated into sizing, etc.
  :returns (type vl-maybe-exprtype-p)
  ;; We don't try very hard yet.
  (vl-datatype-case x
    (:vl-coretype
     (case x.name
       ;; integer atom types -- signedness is determined at parse time, so just
       ;; look at the signedp field.
       ((:vl-byte :vl-shortint :vl-int :vl-longint :vl-integer :vl-time)
        (if x.signedp :vl-signed :vl-unsigned))

       ;; integer vector types -- signedness is also determined at parse time
       ((:vl-bit :vl-logic :vl-reg)
        (if x.signedp :vl-signed :vl-unsigned))

       (otherwise
        nil)))

    (:vl-struct
     ;; Maybe packed structures should be viewed as unsigned?
     nil)

    (:vl-union
     nil)

    (:vl-usertype
     ;; BOZO maybe some day extend this to be able to do lookups
     nil)))

(define vl-override-parameter-with-type
  :short "Try to override a parameter with a new datatype."
  ((decl     vl-paramdecl-p        "Some parameter from the submodule.")
   (datatype vl-datatype-p         "A new datatype to override this parameter with.")
   (warnings vl-warninglist-p      "Warnings accumulator for the submodule.")
   (inst     vl-modinst-p          "Context for error messages."))
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (new-decl  vl-paramdecl-p
                          "Rewritten parameter declaration, overwritten as
                           specified by the submodule."))
  (b* ((decl     (vl-paramdecl-fix decl))
       (datatype (vl-datatype-fix datatype))
       (inst     (vl-modinst-fix inst))

       ((vl-paramdecl decl) decl)
       ((unless (eq (vl-paramtype-kind decl.type) :vl-typeparam))
        (vl-unparam-debug "~a0: trying to override value parameter ~a1 with datatype ~a2.~%"
                          inst decl datatype)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: can't override parameter ~s1 with datatype ~a2: ~
                         ~s1 is a value parameter, not a type parameter."
                   :args (list inst decl.name datatype))
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
    (vl-unparam-debug "~a0: parameter ~a1 becomes ~a2.~%" inst decl new-decl)
    (mv t (ok) new-decl)))

(define vl-convert-parameter-value-to-explicit-type
  :short "Alter the expression given to an explicitly typed parameter so that
          it has the correct type."
  ((type     vl-datatype-p    "The type of the parameter.")
   (expr     vl-expr-p        "The override expression given to this parameter.")
   (warnings vl-warninglist-p "Warnings accumulator for the submodule.")
   (inst     vl-modinst-p     "Context for error messages.")
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
       (inst      (vl-modinst-fix inst))
       (paramname (string-fix paramname))

       ((mv ok reduced-expr) (vl-consteval expr))
       ((unless ok)
        (vl-unparam-debug "~a0: only reduced ~a1 to ~a2 (not a constant).~%"
                          inst expr reduced-expr)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: can't override parameter ~s1: failed to reduce ~
                         expression ~a2 to a constant integer."
                   :args (list inst paramname expr))
            expr))

       ;; Otherwise, VAL is a resolved expression and we know its actual size
       ;; and type.  We want to convert it from whatever size/type it currently
       ;; happens to have into the type that is specified by this parameter.
       ;; That means getting the type and size from a datatype.
       (desired-width (vl-datatype-width type))
       (desired-type  (vl-datatype-exprtype type))
       ((unless (and desired-width desired-type))
        (vl-unparam-debug "~a0: can't override ~a1: width or type unknown: width ~a2, type ~a3."
                          inst paramname desired-width desired-type)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: can't override parameter ~s1: don't know the ~
                         correct width/signedness for type ~a2."
                   :args (list inst paramname type))
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
                :args (list inst paramname desired-width
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
                      inst paramname new-expr)
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
                       (x (mv-nth 1 (vl-consteval expr))))))))

(define vl-override-parameter-with-expr
  :short "Try to override a parameter with a new expression."
  ((decl     vl-paramdecl-p        "Some parameter from the submodule.")
   (expr     vl-expr-p             "The value expression to override this parameter with.")
   (warnings vl-warninglist-p      "Warnings accumulator for the submodule.")
   (inst     vl-modinst-p          "Context for error messages."))
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (new-decl  vl-paramdecl-p
                          "Rewritten parameter declaration, overwritten as
                           specified by the submodule."))

  (b* (((vl-paramdecl decl) (vl-paramdecl-fix decl))
       (expr (vl-expr-fix expr))
       (inst (vl-modinst-fix inst)))

    (vl-paramtype-case decl.type
      (:vl-typeparam
       (vl-unparam-debug "~a0: can't override type parameter ~a1 width expression ~a2.~%"
                         inst decl expr)
       (mv nil
           (fatal :type :vl-bad-instance
                  :msg "~a0: can't override parameter ~s1 with expression, ~
                        ~a2: ~s1 is a type parameter, not a value parameter."
                  :args (list inst decl.name expr))
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
             (vl-convert-parameter-value-to-explicit-type decl.type.type expr warnings inst decl.name))
            ((unless okp)
             ;; Already warned.
             (mv nil warnings decl))
            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            (new-type (change-vl-explicitvalueparam decl.type :default coerced-expr))
            (new-decl (change-vl-paramdecl decl :type new-type)))
         (vl-unparam-debug "~a0: successfully overriding value parameter ~a1 with ~a2.~%"
                           inst decl new-decl)
         (mv t (ok) new-decl)))

      (:vl-implicitvalueparam
       ;; See the rules in SystemVerilog-2012 Section 23.10.
       (b* (((mv ok reduced-expr) (vl-consteval expr))
            ((unless ok)
             (vl-unparam-debug "~a0: can't override ~a1, only reduced expr ~a2 to ~a3 (not a constant)."
                               inst decl expr reduced-expr)
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "~a0: can't override parameter ~s1: failed to ~
                              reduce expression ~a2 to a constant integer."
                        :args (list inst decl.name expr))
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
                                             :dims new-dims))
            ((mv okp warnings coerced-expr)
             ;; Do the conversion explicitly, which gives us all the nice warnings.
             (vl-convert-parameter-value-to-explicit-type explicit-type reduced-expr warnings inst decl.name))
            ((unless okp)
             ;; Already warned
             (mv nil warnings decl))
            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            (new-type (make-vl-explicitvalueparam :type explicit-type :default coerced-expr))
            (new-decl (change-vl-paramdecl decl :type new-type)))
         (vl-unparam-debug "~a0: successfully overriding ~a1 with ~a2.~%"
                           inst decl new-decl)
         (mv t (ok) new-decl))))))

(define vl-override-parameter-value
  :short "Try to override an arbitrary parameter with its final value."
  ((decl     vl-paramdecl-p     "Some parameter from the submodule.")
   (value    vl-paramvalue-p    "Final value to override the parameter with.")
   (warnings vl-warninglist-p   "Warnings accumulator for the submodule.")
   (inst     vl-modinst-p       "Context for error messages."))
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (new-decl  vl-paramdecl-p
                          "Rewritten parameter declaration, overwritten as
                           specified by the submodule."))
  :guard-hints(("Goal" :in-theory (enable vl-maybe-paramvalue-p)))
  (b* ((decl  (vl-paramdecl-fix decl))
       (value (vl-paramvalue-fix value))
       ((when (vl-paramvalue-datatype-p value))
        (vl-override-parameter-with-type decl value warnings inst)))
    (vl-override-parameter-with-expr decl value warnings inst)))


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
  :short "Line up parameter arguments with parameter declarations."
  ((formals  vl-paramdecllist-p "In proper order, from the submodule.")
   (actuals  vl-paramargs-p     "From the instance.")
   (warnings vl-warninglist-p   "Warnings accumulator for the superior module.")
   (inst     vl-modinst-p       "Context for error messages."))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (overrides vl-paramdecloverridelist-p))
  (b* (((vl-modinst inst) (vl-modinst-fix inst))
       (formals           (vl-paramdecllist-fix formals))

       ((unless (uniquep (vl-paramdecllist->names formals)))
        ;; Not a great place to check for this, but better safe than sorry.
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: parameters of ~a1 are not unique: ~&2."
                   :args (list inst inst.modname (duplicated-members (vl-paramdecllist->names formals))))
            nil)))

    (vl-paramargs-case actuals

      (:vl-paramargs-named
       (b* ((actual-names (vl-namedparamvaluelist->names actuals.args))
            (formal-names (vl-paramdecllist->names (vl-nonlocal-paramdecls formals)))

            ((unless (uniquep actual-names))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "~a0: multiple occurrences of parameter arguments: ~&1."
                        :args (list inst (duplicated-members actual-names)))
                 nil))

            (illegal-names
             ;; Actuals that are NOT actually declarations.
             (difference (mergesort actual-names) (mergesort formal-names)))
            ((when illegal-names)
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "~a0: parameter~s1 ~&2 ~s2."
                        :args (list (vl-modinst-fix inst)
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
                        :msg "~a0: too many parameter values: ~s1 has ~x2 (non-local) ~
                              parameter~s3, but is given ~x4 parameter argument~s5."
                        :args (list inst
                                    inst.modname
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
   (inst      vl-modinst-p      "Context for error messages."))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (new-x    vl-paramdecl-p))
  (b* ((inst (vl-modinst-fix inst))
       ((vl-paramdecl x) x)
       ;; BOZO can the order of the substitutions possibly matter?  I don't
       ;; think it should be able to, at least if parameters are always defined
       ;; before use, but I haven't really thought it through very clearly yet.
       (type x.type)
       (type                   (vl-paramtype-subst type valsigma))
       ((mv okp warnings type) (vl-paramtype-typesubst type typesigma inst warnings))
       (new-x (change-vl-paramdecl x :type type)))
    (mv okp warnings new-x)))

(define vl-override-parameter-1
  :short "Override a single parameter, extending the value and type sigmas."
  ((x         vl-paramdecloverride-p "Parameter and its final override to process.")
   (valsigma  vl-sigma-p             "Value substitution we're accumulating.")
   (typesigma vl-typesigma-p         "Type substitution we're accumulating.")
   (warnings  vl-warninglist-p       "Warnings accumulator for the submodule.")
   (inst      vl-modinst-p           "Context for error messages."))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (valsigma  vl-sigma-p        "Extended on success.")
      (typesigma vl-typesigma-p    "Extended on success."))
  (b* ((valsigma  (vl-sigma-fix valsigma))
       (typesigma (vl-typesigma-fix typesigma))
       (inst      (vl-modinst-fix inst))

       ;; Substitute the sigmas so far into the param decl, possibly fixing up
       ;; its datatype and default value.  Do NOT substitute them into the
       ;; override --- it comes from the submodule instance.
       ((mv okp warnings decl)
        (vl-pre-substitute-param (vl-paramdecloverride->decl x) valsigma typesigma warnings inst))
       ((unless okp)
        ;; Already warned.
        (vl-unparam-debug "~a0: failed to pre-substitute into ~a1.~%"
                          inst (vl-paramdecloverride->decl x))
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
        (vl-unparam-debug "~a0: no value for ~s1.~%" inst name)
        (mv nil
            (fatal :type :vl-bad-inst
                   :msg "~a0: no value for parameter ~s1."
                   :args (list inst name))
            valsigma
            typesigma))

       ;; Coerce the override value into the correct type.
       ((mv okp warnings decl)
        (vl-override-parameter-value decl override warnings inst))
       ((unless okp)
        (vl-unparam-debug "~a0: failed to override ~a1 with ~a2.~%" inst decl override)
        ;; Already warned.
        (mv nil warnings valsigma typesigma))

       ;; Extend the appropriate sigma.
       (final (vl-paramtype->default (vl-paramdecl->type decl)))
       ((unless final)
        (vl-unparam-debug "~a0: after overriding, no default value?? new, raw decl: ~x1" inst decl)
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: paramdecl ~x1 somehow has no value?"
                   :args (list inst name))
            valsigma typesigma))

       ((when (vl-paramvalue-expr-p final))
        (vl-unparam-debug "~a0: OK - extending valsigma: ~a1 --> ~a2.~%" inst name final)
        (mv t (ok) (hons-acons! name final valsigma) typesigma)))

    (vl-unparam-debug "~a0: OK - extending typesigma: ~a1 --> ~a2.~%" inst name final)
    (mv t (ok) valsigma (hons-acons! name final typesigma))))

(define vl-override-parameters
  :short "Override all parameters, creating value and type sigmas."
  ((x         vl-paramdecloverridelist-p "Overrides from @(see vl-make-paramdecloverrides).")
   (valsigma  vl-sigma-p                 "Value substitution we're accumulating.")
   (typesigma vl-typesigma-p             "Type substitution we're accumulating.")
   (warnings  vl-warninglist-p           "Warnings accumulator for the submodule.")
   (inst      vl-modinst-p               "Context for error messages."))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (valsigma  vl-sigma-p        "Extended on success.")
      (typesigma vl-typesigma-p    "Extended on success."))
  (b* (((when (atom x))
        (mv t (ok) (vl-sigma-fix valsigma) (vl-typesigma-fix typesigma)))

       ((mv okp warnings valsigma typesigma)
        (vl-override-parameter-1 (car x) valsigma typesigma warnings inst))
       ((unless okp)
        (mv nil warnings valsigma typesigma)))
    (vl-override-parameters (cdr x) valsigma typesigma warnings inst)))



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
       (mod  (vl-module-subst mod valsigma))
       ((mv okp mod) (vl-module-typesubst mod typesigma)))
    (mv okp mod))
  ///
  (memoize 'vl-create-unparameterized-module))

(define vl-maybe-unparam-inst
  :parents (unparameterization)
  :short "Try to unparameterize a single module instance."

  ((inst     vl-modinst-p
             "Instance of some module.  The module being instantiated may or
              may not have parameters.")
   (unsafe   alistp
             "Fast alist of modules we aren't to unparameterize.")
   (mods     vl-modulelist-p
             "List of all modules, for submodule lookups.")
   (modalist (equal modalist (vl-modalist mods))
             "For fast lookups.")
   (warnings vl-warninglist-p
             "Warnings accumulator for the submodule."))

  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (inst     vl-modinst-p
                "Updated module instance, perhaps instantiating a new module
                 like @('my_adder$width=5') instead of @('my_adder').")
      (new-mods vl-modulelist-p
                "Any new modules to add to the module list, e.g., it should
                 include definitions for modules like @('my_adder$width=5')."))

  (b* (((vl-modinst inst) (vl-modinst-fix inst))

       ((when (hons-get inst.modname unsafe))
        ;; Not safe to unparameterize this yet.  Don't do anything.
        (vl-unparam-debug "~a0: unsafe to unparameterize, skipping for now.~%" inst)
        (mv t (ok) inst nil))

       (mod (vl-fast-find-module inst.modname mods modalist))
       ((unless mod)
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
            (mv t (ok) inst nil)
          (mv nil
              (fatal :type :vl-bad-instance
                     :msg "~a0: parameter arguments given to ~s1, but ~s1 ~
                           does not take any parameters."
                     :args (list inst inst.modname))
              inst nil)))

       ;; Line up formals/actuals
       ((mv okp warnings overrides)
        (vl-make-paramdecloverrides mod.paramdecls inst.paramargs warnings inst))
       ((unless okp)
        ;; Already warned.
        (vl-unparam-debug "~a0: failed to line up formals/actuals.~%" inst)
        (mv nil warnings inst nil))

       ;; Create sigmas
       (valsigma  nil)
       (typesigma nil)
       ((mv okp warnings valsigma typesigma)
        (vl-override-parameters overrides valsigma typesigma warnings inst))
       ((acl2::free-on-exit valsigma typesigma))

       ((unless okp)
        ;; Already warned
        (vl-unparam-debug "~a0: failed to create sigmas.~%" inst)
        (mv nil warnings inst nil))

       (- (vl-unparam-debug "~a0: raw value sigma: ~x1~%raw type sigma: ~x2~%"
                            inst valsigma typesigma))

       ((mv okp new-mod) (vl-create-unparameterized-module mod valsigma typesigma))
       (new-modname      (vl-module->name new-mod))

       ;; The above can fail if there's a problem substituting the sigmas into
       ;; the module.  But even in that case, I'll still go ahead and change
       ;; the instance.  (I'll also make sure to add a fatal warning).

       ;; This seems nicer than not changing the instance, because we can at
       ;; least get to see the problematic module, and we sort of make more
       ;; progress, i.e., the superior module will be a zombie, but at least
       ;; its instances won't have parameters.
       (new-inst (change-vl-modinst inst
                                    :modname new-modname
                                    :paramargs (make-vl-paramargs-plain :args nil)))
       ((unless okp)
        (vl-unparam-debug "~a0: creating unparameterized module failed.~%" inst)
        (mv nil
            (fatal :type :vl-unparam-fail
                   :msg "~a0: unparameterizing ~s1 failed, see ~s2 for details."
                   :args (list inst inst.modname new-modname))
            new-inst
            (list new-mod))))

    (vl-unparam-debug "~a0: success, new instance is ~a1.~%" inst new-inst)
    (mv t warnings new-inst (list new-mod)))

  ///
  (more-returns
   (new-mods true-listp :rule-classes :type-prescription)))


; Unparameterizing throughout a module ----------------------------------------

(local (xdoc::set-default-parents vl-unparameterize-module))

(define vl-maybe-unparam-instlist
  :short "Extension of @(see vl-maybe-unparam-inst) to a list of instances."
  ((insts    vl-modinstlist-p "List of instances to unparameterize.")
   (unsafe   alistp           "Fast alist of modules we aren't to unparameterize.")
   (mods     vl-modulelist-p  "List of all modules, for submodule lookups.")
   (modalist (equal modalist (vl-modalist mods)) "For fast lookups.")
   (warnings vl-warninglist-p))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (new-insts vl-modinstlist-p)
      (new-mods  vl-modulelist-p))
  (b* (((when (atom insts))
        (mv t (ok) nil nil))
       ((mv okp1 warnings car-prime car-newmods)
        (vl-maybe-unparam-inst (car insts) unsafe mods modalist warnings))
       ((mv okp2 warnings cdr-prime cdr-newmods)
        (vl-maybe-unparam-instlist (cdr insts) unsafe mods modalist warnings)))
    (mv (and okp1 okp2)
        warnings
        (cons car-prime cdr-prime)
        (append car-newmods cdr-newmods)))
  ///
  (more-returns
   (new-mods true-listp :rule-classes :type-prescription)))

(define vl-unparameterize-module
  :parents (unparameterization)
  :short "Unparameterize module instances throughout a module."

  ((mod      vl-module-p     "Superior module, whose instances will be rewritten.")
   (unsafe   alistp          "Fast alist of modules we aren't to unparameterize.")
   (mods     vl-modulelist-p "All modules, for submodule lookups.")
   (modalist (equal modalist (vl-modalist mods)) "For fast lookups."))

  :returns (mv (successp booleanp :rule-classes :type-prescription
                         "<b>NOTE</b> Success does <b>NOT</b> mean that the instances
                          in new-mod are parameter-free.  It only says that there
                          were no errors during the course of unparameterization.
                          There can still be parameterized instances of the modules
                          listed in @('unsafe'), for instance.")
               (new-mod  vl-module-p)
               (new-mods vl-modulelist-p))

  (b* (((vl-module mod) mod)
       (- (vl-unparam-debug "Starting on module ~x0.~%" mod.name))

       ((mv successp warnings new-insts new-mods)
        (vl-maybe-unparam-instlist mod.modinsts unsafe mods modalist mod.warnings))

       (new-mod (change-vl-module mod
                                  :warnings warnings
                                  :modinsts new-insts)))
    (mv successp new-mod new-mods))
  ///
  (more-returns
   (new-mods true-listp :rule-classes :type-prescription)))


; Unparameterizing until a fixed point is reached -----------------------------

(local (xdoc::set-default-parents vl-modulelist-unparameterize))

(define vl-modules-with-params
  :short "Collect modules that have any parameters."
  ((mods vl-modulelist-p))
  :returns (mods-with-params vl-modulelist-p :hyp :fguard)
  :hooks nil
  (cond ((atom mods)
         nil)
        ((consp (vl-module->paramdecls (car mods)))
         (cons (car mods) (vl-modules-with-params (cdr mods))))
        (t
         (vl-modules-with-params (cdr mods))))
  ///
  (defthm subsetp-equal-of-vl-modules-with-params
    (subsetp-equal (vl-modules-with-params mods) mods))
  (defthm uniquep-of-vl-modulelist->names-of-vl-modules-with-params
    (implies (uniquep (vl-modulelist->names mods))
             (no-duplicatesp (vl-modulelist->names (vl-modules-with-params mods))))))

(define vl-delete-top-level-modules-with-params
  :short "Delete parameterized modules that are no longer used."
  ((mods vl-modulelist-p))
  :returns (new-mods vl-modulelist-p)
  :hooks nil
  :long "<p>Basic idea: once we've replaced all occurrences of @('plus') with
instances of replacement modules like @('plus$size=16'), we need to eliminate
the generic @('plus') from the list of modules in order to finally arrive at a
list of modules which are parameter-free.</p>"
  (b* ((topnames   (vl-modulelist-toplevel mods))
       (modalist   (vl-modalist mods))
       (topmods    (vl-fast-find-modules topnames mods modalist))
       (-          (fast-alist-free modalist))
       (withparams (vl-modules-with-params topmods))
       (delmods    (vl-modulelist->names withparams)))
    (vl-unparam-debug "Removing now-unnecessary modules: ~&0.~%" delmods)
    (vl-delete-modules delmods mods))

  :prepwork
  ((local (defthm l0
            (subsetp-equal (set-difference-equal x y) x)
            :hints((set-reasoning))))

   (local (defthm l1
            (subsetp-equal (vl-modulelist-toplevel mods)
                           (vl-modulelist->names mods))
            :hints(("Goal" :in-theory (enable vl-modulelist-toplevel)))))))


(define vl-unsafe-to-unparameterize-modules
  :short "Identify modules that might not be safe to unparameterize."
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods)))))
  :returns (unsafe string-listp)
  :hooks nil

  :long "<p>During unparameterization, we want to ensure that at no point are
conflicting versions of any module ever generated.  However, if in every pass
we blindly try to unparameterize every module instance whose parameters are
resolved, we can violate this property.</p>

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
After that, mid will become okay to unparameterize, etc.</p>

<p>This is also a convenient mechanism to prevent ourselves from trying to
unparameterize instances of any modules that have errors.</p>"

  (b* ((mods          (mergesort (vl-modulelist-fix mods)))
       (modalist      (vl-modalist mods))
       (parameterized (vl-modules-with-params mods))
       (instanced     (vl-modulelist-everinstanced parameterized))
       ;; It might be that instanced might be enough, but it seems
       ;; safer to also exclude all transitively instanced modules.
       (necessary     (vl-necessary-modules instanced mods modalist))
       ;; We will also exclude all modules that happen to be zombies.
       (zombies       (vl-modulelist-zombies mods)))
    (append zombies necessary)))

(define vl-unparameterize-pass-main
  :short "Main loop to unparameterize a list of modules."
  ((x        vl-modulelist-p "Modules to unparameterize, which are being recurred through.")
   (unsafe   alistp          "Fast alist of modules we aren't to unparameterize.")
   (mods     vl-modulelist-p "All modules, for submodule lookups.")
   (modalist (equal modalist (vl-modalist mods)) "For fast lookups."))
  :returns
  (new-x vl-modulelist-p "Contains rewritten modules from @('x') and also new
                          definitions of modules like @('myadder$size=5').")

  :long "<p>This is almost a full pass of unparameterization, except that it
doesn't do much in the way of error checking and throwing away bad modules.  We
try to apply @(see vl-unparameterize-module) to every module in the list.</p>"

  (b* (((when (atom x))
        nil)
       ((mv ?successp car-prime car-newmods)
        (vl-unparameterize-module (car x) unsafe mods modalist))
       (rest (vl-unparameterize-pass-main (cdr x) unsafe mods modalist)))
    (cons car-prime (append car-newmods rest)))
  ///
  (more-returns
   (new-x true-listp :rule-classes :type-prescription)))

(define vl-unparameterize-pass
  :short "One full pass of unparameterization over a module list."
  ((mods vl-modulelist-p))
  :guard (uniquep (vl-modulelist->names mods))
  :returns (new-mods vl-modulelist-p)
  (b* ((mods     (vl-modulelist-fix mods))
       (modalist (vl-modalist mods))

       ;; Figure out which modules can't be safely unparameterized because
       ;; they're zombies or are instanced by other modules that still have
       ;; parameters.
       (unsafe   (make-lookup-alist (vl-unsafe-to-unparameterize-modules mods)))
       (- (vl-unparam-debug "Currently unsafe to unparameterize: ~x0.~%" (alist-keys unsafe)))

       ;; Eliminate parameters everywhere that we can safely do so.
       (new-mods (vl-unparameterize-pass-main mods unsafe mods modalist))
       (- (fast-alist-free modalist))
       (- (fast-alist-free unsafe))

       ;; Make sure there are no name clashes.  It's okay to have true
       ;; duplicates since, e.g., separate occurrences of my_adder #(.size(4))
       ;; will produces duplicate modules like my_adder$size=4.  So, sort
       ;; first.
       (new-mods (mergesort new-mods))
       ((unless (uniquep (vl-modulelist->names new-mods)))
        (raise "Unparameterization caused a name conflict: ~x0."
               (duplicated-members (vl-modulelist->names new-mods))))

       ;; We may no longer need instances of, e.g., my_adder because we turned
       ;; them all into my_adder$width=5 and my_adder$width=10 and so forth.
       ;; So, delete top level modules (modules that are never instanced) that
       ;; still have parameters.
       (new-mods (vl-delete-top-level-modules-with-params new-mods))
       ((unless (uniquep (vl-modulelist->names new-mods)))
        (raise "Deleting top level mods with params caused a name conflict?"))

       ;; We may have failed to unparameterize some module instances due to
       ;; real errors.  So, propagate any errors.  This will turn the superior
       ;; modules into zombies, which will prevent us from trying to
       ;; unparameterize them later.
       ((mv survivors victims) (vl-modulelist-propagate-errors new-mods))
       (new-mods (append survivors victims)))
    new-mods)
  ///
  (defthm unique-names-after-vl-unparameterize-pass
    (implies (uniquep (vl-modulelist->names mods))
             (no-duplicatesp-equal (vl-modulelist->names (vl-unparameterize-pass mods))))))

(define vl-handle-unparam-fail-aux
  :short "Annotate each module in mods with a warning saying we failed to
          unparameterize it."
  ((mods      vl-modulelist-p)
   (bad-names string-listp))
  :returns (new-mods vl-modulelist-p)
  :hooks nil
  (b* (((when (atom mods))
        nil)
       (mod1 (vl-module-fix (car mods)))
       ((unless (member-equal (vl-module->name mod1) bad-names))
        (cons mod1 (vl-handle-unparam-fail-aux (cdr mods) bad-names)))
       (warnings (fatal :type :vl-unparameterize-fail
                        :msg "Unable to eliminate remaining parameters, ~&0."
                        :args (list (vl-paramdecllist->names (vl-module->paramdecls mod1)))
                        :acc (vl-module->warnings mod1))))
    (cons (change-vl-module mod1 :warnings warnings)
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
  :returns (new-mods vl-modulelist-p)
  (b* ((withparams (vl-modules-with-params mods))
       (bad-names  (vl-modulelist->names withparams))
       (mods       (vl-handle-unparam-fail-aux mods bad-names))
       ((mv survivors victims) (vl-remove-bad-modules bad-names mods)))
    (append survivors victims))
  ///
  (defthm vl-handle-unparam-fail-does-not-cause-name-conflict
    (implies (force (uniquep (vl-modulelist->names mods)))
             (no-duplicatesp-equal (vl-modulelist->names (vl-handle-unparam-fail mods))))))

(define vl-modulelist-unparameterize
  :parents (unparameterization)
  :short "Main unparamterization routine."
  ((mods vl-modulelist-p   "Modules to unparameterize.")
   (n    natp              "How many passes of unparameterization to try."))
  :guard
  (uniquep (vl-modulelist->names mods))
  :returns (new-mods vl-modulelist-p)
  :verify-guards nil
  :measure (nfix n)
  (b* ((mods       (vl-modulelist-fix mods))
       (withparams (mergesort (vl-modules-with-params mods)))
       (zombies    (mergesort (vl-modulelist-zombies mods)))
       (todo       (difference withparams zombies))

       ((when (atom todo))
        ;; Success, all modules are parameter-free.
        (cw "; unparameterize: all remaining modules are parameter-free.~%")
        mods)

       ((when (zp n))
        ;; Ran out of steps.  Throw away all modules with params and everything
        ;; that depends on them.
        (cw "; unparameterize: out of tries and modules still have parameters: ~&0"
            (vl-modulelist->names withparams))
        (vl-handle-unparam-fail mods))

       (- (cw "; unparameterize: starting round ~x0: ~x1 mods total, ~x2 to go.~%"
              n (len mods) (len todo)))

       (new-mods (vl-unparameterize-pass mods))

       ((when (equal (mergesort new-mods) (mergesort mods)))
        (cw "; unparameterize: no progress, but modules still have parameters: ~&1~%"
            n (vl-modulelist->names todo))
        (vl-handle-unparam-fail new-mods)))

    (vl-modulelist-unparameterize new-mods (- n 1)))
  ///
  (defthm no-duplicatesp-of-vl-modulelist->names-of-vl-modulelist-unparameterize
    (implies (uniquep (vl-modulelist->names mods))
             (no-duplicatesp (vl-modulelist->names (vl-modulelist-unparameterize mods n)))))
  (verify-guards vl-modulelist-unparameterize))

(define vl-design-unparameterize
  :short "Top-level @(see unparameterization) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (;; Throw out modules that have problems with shadowed parameters.
       ((vl-design x) (vl-design-unparam-check x))
       ((unless (uniquep (vl-modulelist->names x.mods)))
        (raise "Programming error: module names are not unique.")
        x)
       (new-mods (vl-modulelist-unparameterize x.mods 1000))

       ;; Just to be absolutely certain this can't happen:
       ((unless (mbt (uniquep (vl-modulelist->names new-mods))))
        (impossible)
        x))

    (clear-memoize-table 'vl-create-unparameterized-module)
    (cw "; unparameterize: ~x0 => ~x1 modules.~%" (len x.mods) (len new-mods))
    (change-vl-design x :mods new-mods)))
