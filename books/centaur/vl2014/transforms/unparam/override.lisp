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
(include-book "../../mlib/consteval")
(include-book "../../mlib/fmt") ;; blaaaaah bad deps
(local (include-book "../../util/arithmetic"))
;(local (include-book "../../mlib/modname-sets"))
;(local (include-book "../../util/osets"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))


(defconst *vl-unparam-debug* nil)

(defmacro vl-unparam-debug (&rest args)
  `(and *vl-unparam-debug*
        (progn$ (cw "; UNPARAM: ~s0: " __function__)
                (vl-cw-ps-seq (vl-cw . ,args)))))


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
               (new-type  vl-datatype-p "On success, the new replacement type."))
  (b* ((decl     (vl-paramdecl-fix decl))
       (datatype (vl-datatype-fix datatype))
       (ctx      (vl-context-fix ctx))

       ((vl-paramdecl decl) decl)
       ((unless (eq (vl-paramtype-kind decl.type) :vl-typeparam))
        (vl-unparam-debug "~a0: trying to override value parameter ~a1 with datatype ~a2.~%"
                          ctx decl datatype)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0: can't override parameter ~s1 with datatype ~a2: ~
                         ~s1 is a value parameter, not a type parameter."
                   :args (list ctx decl.name datatype))
            datatype))

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
       ;(new-type (change-vl-typeparam decl.type :default datatype))
       ;(new-decl (change-vl-paramdecl decl :type new-type))
       )
    (vl-unparam-debug "~a0: parameter ~a1 becomes ~a2.~%" ctx decl datatype)
    (mv t (ok) datatype)))

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
               (new-value vl-expr-p "On success, final (coerced) value to use
                                     for this parameter."))

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
           expr))

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
             (mv nil warnings expr))
            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            ;; (new-type (change-vl-explicitvalueparam decl.type :default coerced-expr))
            ;; (new-decl (change-vl-paramdecl decl :type new-type))
            )
         (vl-unparam-debug "~a0: successfully overriding value parameter ~a1 with ~a2.~%"
                           ctx decl coerced-expr)
         (mv t (ok) coerced-expr)))

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
                 expr))

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
             (mv nil warnings expr))
            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            ;(new-type (make-vl-explicitvalueparam :type explicit-type :default coerced-expr))
            ;(new-decl (change-vl-paramdecl decl :type new-type))
            )
         (vl-unparam-debug "~a0: successfully overriding ~a1 with ~a2.~%"
                           ctx decl coerced-expr)
         (mv t (ok) coerced-expr))))))

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
               (new-value vl-paramvalue-p
                          "On success, the new value to use for this parameter."))
  (b* ((decl  (vl-paramdecl-fix decl))
       (value (vl-paramvalue-fix value))
       ((when (vl-paramvalue-datatype-p value))
        (vl-override-parameter-with-type decl value warnings ctx)))
    (vl-override-parameter-with-expr decl value ss warnings ctx)))

(defconst *vl-fake-context*
  (make-vl-context :mod "fakemodule"
                   :elem *vl-fake-elem-for-vl-consteval*))

(define vl-paramdecl-final-value ((decl vl-paramdecl-p)
                                  (ss   vl-scopestack-p))
  :returns (val vl-maybe-paramvalue-p)
  :guard-debug t
  (b* (((vl-paramdecl decl))
       (default (vl-paramtype->default decl.type))
       ((unless default)
        nil)
       (ctx *vl-fake-context*)
       ((mv okp ?warnings new-value)
        (vl-override-parameter-value decl default ss nil ctx)))
    (and okp new-value)))


