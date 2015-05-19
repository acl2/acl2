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
(include-book "centaur/sv/vl/elaborate" :dir :system)
;; (include-book "../../mlib/fmt") ;; blaaaaah bad deps
(local (include-book "../../util/arithmetic"))
;(local (include-book "../../mlib/modname-sets"))
;(local (include-book "../../util/osets"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable (tau-system))))

(defconst *vl-unparam-debug* nil)

(encapsulate
  (((vl-unparam-debug-fn * *) => *
    :formals (function args) :guard t))
  (local (defun vl-unparam-debug-fn (function args)
           (Declare (xargs :guard t))
           (list function args))))

(defun vl-unparam-debug-silent (function args)
  (declare (xargs :guard t)
           (ignore function args))
  nil)

(defattach vl-unparam-debug-fn vl-unparam-debug-silent)

(defmacro vl-unparam-debug (&rest args)
  `(vl-unparam-debug-fn __function__ (list . ,args)))
;; (defmacro vl-unparam-debug (&rest args)
;;   `(and *vl-unparam-debug*
;;         (progn$ (cw "; UNPARAM: ~s0: " __function__)
;;                 (vl-cw-ps-seq (vl-cw . ,args)))))


(define vl-paramtype->default ((x vl-paramtype-p))
  :parents (vl-paramtype-p)
  :short "Get the default value from any @(see vl-paramtype-p)."
  :returns (value vl-maybe-paramvalue-p)
  (vl-paramtype-case x
    (:vl-implicitvalueparam (and x.default
                                 (vl-paramvalue-expr x.default)))
    (:vl-explicitvalueparam (and x.default
                                 (vl-paramvalue-expr x.default)))
    (:vl-typeparam          (and x.default
                                 (vl-paramvalue-type x.default))))
  :prepwork ((local (in-theory (enable vl-maybe-paramvalue-p)))))



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
   (datatype vl-datatype-p         "A new datatype to override this parameter with (resolved)")
   (warnings vl-warninglist-p      "Warnings accumulator for the submodule."))
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (new-param vl-paramdecl-p "The replacement parameter."))
  (b* ((decl     (vl-paramdecl-fix decl))
       (datatype (vl-datatype-fix datatype))

       ((vl-paramdecl decl) decl)
       ((unless (eq (vl-paramtype-kind decl.type) :vl-typeparam))
        (vl-unparam-debug "trying to override value parameter ~a1 with datatype ~a2.~%"
                          nil decl datatype)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "can't override parameter ~s1 with datatype ~a2: ~
                         ~s1 is a value parameter, not a type parameter."
                   :args (list nil decl.name datatype))
            decl))

       ((unless (vl-datatype-resolved-p datatype))
        (vl-unparam-debug "unresolved usertypes usertypes in override ~
                           datatype ~a1 for parameter ~a2~%"
                         nil datatype decl)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "unresolved usertypes in override datatype ~
                         ~a1 for parameter ~a2"
                   :args (list nil datatype decl))
            decl))

       (new-decl (change-vl-paramdecl
                  decl
                  :type (change-vl-typeparam decl.type :default datatype)))

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
    (vl-unparam-debug "parameter ~a1 becomes ~a2.~%" nil decl datatype)
    (mv t (ok) new-decl)))

(define vl-convert-parameter-value-to-explicit-type
  :short "Alter the expression given to an explicitly typed parameter so that
          it has the correct type."
  ((type     vl-datatype-p    "The type of the parameter.")
   (expr     vl-expr-p        "The override expression given to this parameter.")
   (conf     vl-svexconf-p    "Svexconf for the expr")
   (warnings vl-warninglist-p "Warnings accumulator for the submodule.")
   (paramname stringp         "More context for error messages."))

  :guard (vl-datatype-resolved-p type)
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
       (conf     (vl-svexconf-fix conf))
       (warnings (ok))
       (paramname (string-fix paramname))

       ((unless (vl-datatype-packedp type))
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "For now we can only assign to parameters of ~
                         packed type, unlike ~a1."
                   :args (list nil type))
            expr))

       ;; Assuming we can resolve VAL to a constant expression, we want to
       ;; evaluate it as something that fits in the width of this datatype.
       ;; That means getting the type and size from a datatype.
       ((mv err desired-width) (vl-datatype-size type))
       ((mv ?caveat desired-signedness)  (vl-datatype-signedness type))
       ((unless (and (not err) desired-width desired-signedness))
        (vl-unparam-debug "can't override ~a1: width or type unknown: ~
                           width ~a2, type ~a3; ~s4."
                          nil paramname desired-width desired-signedness
                          err)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "can't override parameter ~s1: don't know the ~
                         correct width/signedness for type ~a2; ~@3."
                   :args (list nil paramname type err))
            expr))

       ((wmv ok ?constp warnings reduced-expr ?svex)
        (vl-elaborated-expr-consteval expr conf :ctxsize desired-width))
       ((unless (and ok (vl-expr-case reduced-expr :vl-literal)))
        (vl-unparam-debug "only reduced ~a1 to ~a2 (not a constant).~%"
                          nil expr reduced-expr)
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "can't override parameter ~s1: failed to reduce ~
                         expression ~a2 to a constant integer."
                   :args (list nil paramname expr))
            expr)))

    (vl-unparam-debug "overriding parameter ~a1, new expr is ~a2: ~x2.~%"
                      nil paramname reduced-expr)
    (mv t warnings reduced-expr)))

;; (define vl-implicitvalueparam-final-type ((x vl-paramtype-p)
;;                                           (override vl-expr-p)
;;                                           (ss vl-scopestack-p
;;                                               "for override"))
;;   :guard (vl-paramtype-case x :vl-implicitvalueparam)
;;   :returns (mv (warnings vl-warninglist-p)
;;                (err (iff (vl-msg-p err) err))
;;                (type (implies (not err) (vl-datatype-p type))))
;;   (b* ((override (vl-expr-fix override))
;;        ((vl-implicitvalueparam x) (vl-paramtype-fix x))
;;        (warnings nil)
;;        ((when x.range)
;;         ;; BOZO When do we ensure that the range is resolved?  Presumably
;;         ;; parameters are allowed to use other parameters in defining their
;;         ;; datatypes.
;;         (if (vl-range-resolved-p x.range)
;;             (mv warnings nil
;;                 (make-vl-coretype :name :vl-logic
;;                                   :pdims (list (vl-range->packeddimension x.range))
;;                                   :signedp (eq x.sign :vl-signed)))
;;           (mv warnings (vmsg "Unresolved range") nil)))
;;        ((wmv warnings size) (vl-expr-selfsize override ss))
;;        ((unless (posp size))
;;         (mv warnings
;;             (vmsg "Unsized or zero-size parameter override: ~a0" override)
;;             nil))
;;        (dims (list (vl-range->packeddimension
;;                     (make-vl-range :msb (vl-make-index (1- size)) :lsb (vl-make-index 0)))))
;;        ((when x.sign)
;;         (mv warnings nil
;;             (make-vl-coretype :name :vl-logic :pdims dims :signedp (eq x.sign :vl-signed))))
;;        ((wmv warnings signedness) (vl-expr-typedecide override ss))
;;        ((unless signedness)
;;         (mv warnings
;;             (vmsg "Couldn't decide signedness of parameter override ~a0" override)
;;             nil)))
;;     (mv warnings nil
;;         (make-vl-coretype :name :vl-logic :pdims dims :signedp (eq signedness :vl-signed))))
;;   ///
;;   (defret vl-datatype-resolved-p-of-vl-implicitvalueparam-final-type
;;     (implies (not err)
;;              (vl-datatype-resolved-p type))))
    

#|
(trace$ #!vl (Vl-override-parameter
              :entry (list 'vl-override-parameter
                           (with-local-ps (vl-pp-paramdecl decl)))
              :exit (list 'vl-override-parameter
                          (with-local-ps (vl-pp-paramdecl (nth 2 values)))
                          (with-local-ps (vl-print-warnings
                                          (butlast (nth 1 values) (len warnings)))))))

(trace$ #!vl (vl-paramtype-elaborate-fn
              :entry (list 'paramtype-elaborate
                           (with-local-ps (vl-pp-paramdecl
                                           (make-vl-paramdecl
                                            :name "xxx"
                                            :type x
                                            :loc *vl-fakeloc*))))
              :exit (list 'paramtype-elaborate
                          (with-local-ps (vl-pp-paramdecl
                                           (make-vl-paramdecl
                                            :name "xxx"
                                            :type (nth 2 values)
                                            :loc *vl-fakeloc*)))
                          (and (not (car values))
                               (with-local-ps
                                 (vl-print-warnings (nth 1 values)))))))

(trace$ #!vl (vl-datatype-elaborate-fn
              :entry (list 'datatype-elaborate
                           (with-local-ps (vl-pp-datatype x)))
              :exit (list 'datatype-elaborate
                          (with-local-ps (vl-pp-datatype (nth 2 values)))
                          (and (not (car values))
                               (with-local-ps
                                 (vl-print-warnings (nth 1 values)))))))

(trace$ #!vl (vl-expr-elaborate-fn
              :entry (list 'expr-elaborate
                           (with-local-ps (vl-pp-expr x)))
              :exit (list 'expr-elaborate
                          (with-local-ps (vl-pp-expr (nth 2 values)))
                          (and (not (car values))
                               (with-local-ps
                                 (vl-print-warnings (nth 1 values)))))))

(trace$ #!vl (vl-assign-elaborate-fn
              :entry (list 'assign-elaborate
                           (with-local-ps (vl-pp-assign x)))
              :exit (list 'assign-elaborate
                          (with-local-ps (vl-pp-assign (nth 2 values)))
                          (and (not (car values))
                               (with-local-ps
                                 (vl-print-warnings (nth 1 values)))))))

(trace$ #!vl (vl-fundecl-elaborate-aux-fn
              :entry (list 'fundecl-elaborate-aux
                           (with-local-ps (vl-pp-fundecl x)))
              :exit (list 'fundecl-elaborate-aux
                          (with-local-ps (vl-pp-fundecl (nth 2 values)))
                          (and (not (car values))
                               (with-local-ps
                                 (vl-print-warnings (nth 1 values))))
                          (strip-cars (vl-svexconf->fns (nth 3 values))))))

(trace$ #!vl (vl-fundecl-elaborate-fn
              :entry (list 'fundecl-elaborate
                           (with-local-ps (vl-pp-fundecl x)))
              :exit (list 'fundecl-elaborate
                          (with-local-ps (vl-pp-fundecl (nth 2 values)))
                          (and (not (car values))
                               (with-local-ps
                                 (vl-print-warnings (nth 1 values))))
                          (strip-cars (vl-svexconf->fns (nth 3 values))))))

(trace$ #!vl (vl-index-resolve-if-constant-fn
              :entry (list 'index-resolve-if-constant
                           (with-local-ps (vl-pp-expr x)))
              :exit (list 'index-resolve-if-constant
                          (with-local-ps (vl-pp-expr (nth 2 values)))
                          (and (not (car values))
                               (with-local-ps
                                 (vl-print-warnings (nth 1 values)))))))

(trace$ #!vl (vl-expr-maybe-resolve-to-constant-fn
              :entry (list 'expr-maybe-resolve-to-constant
                           (with-local-ps (vl-pp-expr x)))
              :exit (list 'expr-maybe-resolve-to-constant
                          (with-local-ps (vl-pp-expr (nth 3 values)))
                          (and (not (car values))
                               (with-local-ps
                                 (vl-print-warnings (nth 1 values))))
                          (and (not (nth 1 values)) (nth 4 values))
                          (and (not (nth 1 values))
                               (change-vl-svexconf (nth 5 values)
                                                   :ss nil)))))



(trace$ #!vl (vl-elaborated-expr-consteval-fn
              :entry (list 'vl-elaborated-expr-consteval
                           (with-local-ps (vl-pp-expr x)))
              :exit (list 'vl-elaborated-expr-consteval
                          (with-local-ps (vl-pp-expr (nth 3 values))))))

|#

(define vl-override-parameter
  :short "Try to override a parameter with a new expression."
  ((decl       vl-paramdecl-p      "Some parameter from the submodule.")
   (decl-conf  vl-svexconf-p       "Svexconf for parameter declaration context")
   (override   vl-maybe-paramvalue-p "The value to override this parameter with,
                                      if any -- should be elaborated already")
   (conf     vl-svexconf-p         "Svexconf for the override context")
   (warnings vl-warninglist-p      "Warnings accumulator for the submodule."))
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (new-param vl-paramdecl-p "On success, final (coerced) value to
                                          use for this parameter.")
               (new-decl-conf vl-svexconf-p "updated svexconf for paramdecl context"))

  (b* (((vl-paramdecl decl) (vl-paramdecl-fix decl))
       ;; ((vl-svexconf conf))
       (decl-conf (vl-svexconf-fix decl-conf))
       (warnings (ok))
       ((wmv ok warnings decl.type decl-conf)
        (vl-paramtype-elaborate decl.type decl-conf))
       ;; (- (cw "decl-conf: ~x0~%" decl-conf))
       ((unless ok)
        (mv nil warnings decl decl-conf)))

    (vl-paramtype-case decl.type
      (:vl-typeparam
       (b* (((unless override)
             (b* (((unless decl.type.default)
                   (mv nil
                       (fatal :type :vl-bad-instance
                              :msg "Can't instantiate without assignment ~
                                    for type parameter ~a1."
                              :msg (list nil decl))
                       decl decl-conf))
                  ((unless (vl-datatype-resolved-p decl.type.default))
                   (mv nil
                       (fatal :type :vl-bad-instance
                              :msg "Default type for parameter ~a1 not resolved."
                              :msg (list nil decl))
                       decl decl-conf)))
               (mv t (ok) (change-vl-paramdecl decl :type decl.type) decl-conf)))
            ((when (vl-paramvalue-case override :expr))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "Overriding type parameter ~a1 with expression ~a2."
                        :msg (list nil decl (vl-paramvalue-expr->expr override)))
                 decl decl-conf))
            (type (vl-paramvalue-type->type override))
            ((unless (vl-datatype-resolved-p type))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "Override type ~a1 for parameter ~a2 not resolved."
                        :msg (list nil type decl))
                 decl decl-conf)))
         (mv t warnings (change-vl-paramdecl
                         decl :type (change-vl-typeparam decl.type :default type))
             decl-conf)))


      (:vl-explicitvalueparam
       ;; See the rules in SystemVerilog 23.10.  I think we should regard this
       ;; case as having an "explicit type and range specification", even
       ;; though that's pretty vague.  (We might not *really* have an explicit
       ;; range, but might have a datatype like "integer", which sort of
       ;; implicitly has a range.) If this is right, then we are supposed to
       ;; convert the override value (expr) so that it has the type and range
       ;; of this parameter.
       (b* (((when (and override (vl-paramvalue-case override :type)))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "Overriding value parameter ~a1 with type ~a2."
                        :args (list nil decl (vl-paramvalue-type->type override)))
                 decl decl-conf))
            ((mv expr expr-conf)
             (if override
                 (mv (vl-paramvalue-expr->expr override) conf)
               (mv decl.type.default decl-conf)))
            ((unless expr)
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "Can't instantiate without assignment for ~
                              value parameter ~a1."
                        :args (list nil decl))
                 decl decl-conf))
            ((unless (vl-datatype-resolved-p decl.type.type))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "Failed to resolve datatype ~a1 for parameter ~a2"
                        :args (list nil decl.type.type decl))
                 decl decl-conf))
            ((mv okp warnings coerced-expr)
             (vl-convert-parameter-value-to-explicit-type
              decl.type.type expr expr-conf warnings decl.name))
            ((unless okp)
             ;; Already warned.
             (mv nil warnings decl decl-conf))
            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            ;; (new-type (change-vl-explicitvalueparam decl.type :default coerced-expr))
            ;; (new-decl (change-vl-paramdecl decl :type new-type))
            (new-decl (change-vl-paramdecl
                       decl :type (change-vl-explicitvalueparam
                                   decl.type
                                   :default coerced-expr)))
            )
         (vl-unparam-debug "successfully overriding value parameter ~a1 with ~a2.~%"
                           nil decl coerced-expr)
         (mv t (ok) new-decl decl-conf)))

      (:vl-implicitvalueparam
       ;; See the rules in SystemVerilog-2012 Section 23.10 and 6.20.2.
       (b* (((when (and override (vl-paramvalue-case override :type)))
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "Overriding value parameter ~a1 with type ~a2."
                        :args (list nil decl (vl-paramvalue-type->type override)))
                 decl decl-conf))
            ((mv expr expr-conf)
             (if override
                 (mv (vl-paramvalue-expr->expr override) conf)
               (mv decl.type.default decl-conf)))
            ((unless expr)
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "Can't instantiate without assignment for ~
                              value parameter ~a1."
                        :args (list nil decl))
                 decl decl-conf))
            ((wmv warnings err datatype)
             (vl-implicitvalueparam-final-type decl.type expr expr-conf))
            ((when err)
             (mv nil
                 (fatal :type :vl-bad-instance
                        :msg "Failed to determine datatype for parameter ~
                              ~a1 overridden with ~a2: ~@3"
                        :args (list nil decl expr err))
                 decl decl-conf))

            ((mv okp warnings coerced-expr)
             ;; Do the conversion explicitly, which gives us all the nice warnings.
             (vl-convert-parameter-value-to-explicit-type datatype expr expr-conf warnings decl.name))
            ((unless okp)
             ;; Already warned
             (mv nil warnings decl decl-conf))

            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            (new-decl (change-vl-paramdecl
                       decl :type (make-vl-explicitvalueparam :type datatype :default coerced-expr))))
         (vl-unparam-debug "successfully overriding ~a1 with ~a2.~%"
                           nil decl coerced-expr)
         (mv t (ok) new-decl decl-conf))))))

;; (define vl-override-parameter-value
;;   :parents (unparameterization)
;;   :short "Try to override an arbitrary parameter with its final value."
;;   ((decl      vl-paramdecl-p     "Some parameter from the submodule.")
;;    (decl-conf vl-svexconf-p      "svexconf from the submodule")
;;    (value    vl-paramvalue-p    "Final value to override the parameter with.")
;;    (conf     vl-svexconf-p      "Svexconf for the parameter value")
;;    (warnings vl-warninglist-p   "Warnings accumulator for the submodule.")
;;    (ctx      vl-context-p       "Context for error messages."))
;;   :returns (mv (okp       booleanp :rule-classes :type-prescription)
;;                (warnings  vl-warninglist-p)
;;                (new-decl vl-paramdecl-p
;;                           "On success, the parameter declaration with new value
;;                            installed as default.")
;;                (new-decl-conf vl-svexconf-p)
;;                (new-conf      vl-svexconf-p))
;;   (b* ((decl  (vl-paramdecl-fix decl)))
;;     (vl-paramvalue-case value
;;       :expr (vl-override-parameter-with-expr decl decl-conf value.expr ss warnings ctx)
;;       :type (vl-override-parameter-with-type decl value.type ss warnings ctx))))

;; (define vl-paramdecl-finalize ((decl vl-paramdecl-p)
;;                                (decl-ss vl-scopestack-p
;;                                         "Scopestack from the submodule where
;;                                             the parameter is defined")
;;                                (ss   vl-scopestack-p))
;;   :prepwork ((local (defthm override-parameter-value-hack
;;                       (mv-nth 2 (vl-override-parameter-value
;;                                  decl decl-ss value ss warnings ctx))
;;                       :hints (("goal" :use VL-PARAMDECL-P-OF-VL-OVERRIDE-PARAMETER-VALUE.NEW-DECL



;;                                :in-theory (disable VL-PARAMDECL-P-OF-VL-OVERRIDE-PARAMETER-VALUE.NEW-DECL))))))
;;   :returns (new-decl (iff (vl-paramdecl-p new-decl) new-decl))
;;   :guard-debug t
;;   (b* (((vl-paramdecl decl) (vl-paramdecl-fix decl))
;;        (default (vl-paramtype->default decl.type))
;;        ((unless default)
;;         nil)
;;        (ctx (vl-context-fix decl))
;;        ((mv okp ?warnings new-value)
;;         (vl-override-parameter-value decl decl-ss default ss nil ctx)))
;;     (and okp new-value)))


