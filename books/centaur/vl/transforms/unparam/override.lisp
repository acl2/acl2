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
; We now develop vl-override-parameter, which, we think, correctly implements
; these rules and allows us to correctly override a single parameter with the
; value supplied by the module instance.

(local (xdoc::set-default-parents vl-override-parameter))

;; [Jared] BOZO where is this done now?

;; (define vl-override-parameter-with-type
;;   :short "Try to override a parameter with a new datatype."
;;   ((decl     vl-paramdecl-p        "Some parameter from the submodule.")
;;    (datatype vl-datatype-p         "A new datatype to override this parameter with (resolved)")
;;    (warnings vl-warninglist-p      "Warnings accumulator for the submodule."))
;;   :returns (mv (okp       booleanp :rule-classes :type-prescription)
;;                (warnings  vl-warninglist-p)
;;                (new-param vl-paramdecl-p "The replacement parameter."))
;;   (b* ((decl     (vl-paramdecl-fix decl))
;;        (datatype (vl-datatype-fix datatype))

;;        ((vl-paramdecl decl) decl)
;;        ((unless (eq (vl-paramtype-kind decl.type) :vl-typeparam))
;;         (vl-unparam-debug "trying to override value parameter ~a1 with datatype ~a2.~%"
;;                           nil decl datatype)
;;         (mv nil
;;             (fatal :type :vl-bad-parameter-override
;;                    :msg "can't override parameter ~s1 with datatype ~a2: ~
;;                          ~s1 is a value parameter, not a type parameter."
;;                    :args (list nil decl.name datatype))
;;             decl))

;;        ((unless (vl-datatype-resolved-p datatype))
;;         (vl-unparam-debug "unresolved usertypes usertypes in override ~
;;                            datatype ~a1 for parameter ~a2~%"
;;                          nil datatype decl)
;;         (mv nil
;;             (fatal :type :vl-bad-parameter-override
;;                    :msg "unresolved usertypes in override datatype ~
;;                          ~a1 for parameter ~a2"
;;                    :args (list nil datatype decl))
;;             decl))

;;        (new-decl (change-vl-paramdecl
;;                   decl
;;                   :type (change-vl-typeparam decl.type :default datatype)))

;;        ;; It seems like we might want to do some other kinds of sanity/error
;;        ;; checking here, but I'm not sure what that would look like.  Well
;;        ;; maybe we don't?  After all, this is basically just setting up a type
;;        ;; alias.  What kinds of things could go wrong?
;;        ;;
;;        ;;   - The type might be sort of malformed or non-existent, e.g., the
;;        ;;     instance could say use foo_t but this might not be a defined
;;        ;;     type, or could say to use a struct { foo_t a; int b; } when foo_t
;;        ;;     doesn't exist, or something like that.
;;        ;;
;;        ;;   - The type might not make sense in a context where it's used.  For
;;        ;;     instance, suppose that somewhere in the module we try to add one
;;        ;;     to a variable of this type.  That won't make sense if the
;;        ;;     instance overrides this type with, say, an unpacked struct.
;;        ;;
;;        ;;   - Probably other things I haven't thought through very well yet.
;;        ;;
;;        ;; Well, so what?  I think all of these could also be problems with the
;;        ;; parameter's default type.  So, it seems like probably we don't have
;;        ;; to be especially worried with sanity checking this kind of stuff at
;;        ;; override time.
;;        ;(new-type (change-vl-typeparam decl.type :default datatype))
;;        ;(new-decl (change-vl-paramdecl decl :type new-type))
;;        )
;;     (vl-unparam-debug "parameter ~a1 becomes ~a2.~%" nil decl datatype)
;;     (mv t (ok) new-decl)))

#||
(trace$ #!vl
        (vl-convert-parameter-value-to-explicit-type
         :entry (list 'vl-convert-parameter-value-to-explicit-type
                      (with-local-ps (vl-pp-vardecl (make-vl-vardecl :name paramname :type type
                                                                     :loc *vl-fakeloc*)))
                      (with-local-ps (vl-pp-expr expr))
                      paramname)
         :exit (b* (((list okp warnings-out new-expr) values))
                 (list 'vl-convert-parameter-value-to-explicit-type
                       okp
                       (with-local-ps
                         (vl-print-warnings (take (- (len warnings-out) (len warnings)) warnings-out)))
                       (with-local-ps (vl-pp-expr new-expr))))))

||#

(define vl-convert-parameter-value-to-explicit-type
  :short "Alter the expression given to an explicitly typed parameter so that
          it has the correct type."
  ((type     vl-datatype-p    "The type of the parameter.")
   (expr     vl-expr-p        "The override expression given to this parameter.")
   (ss       vl-scopestack-p)
   (scopes   vl-elabscopes-p "Scoped at the override expression.")
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
       (warnings (ok))
       (paramname (string-fix paramname))

       ;; ((unless (vl-datatype-packedp type))
       ;;  (mv nil
       ;;      (fatal :type :vl-bad-parameter-override
       ;;             :msg "For now we can only assign to parameters of ~
       ;;                   packed type, unlike ~a1."
       ;;             :args (list nil type))
       ;;      expr))

       ;; Assuming we can resolve VAL to a constant expression, we want to
       ;; evaluate it as something that fits in the width of this datatype.
       ;; That means getting the type and size from a datatype.
       ;; ((mv err desired-width) (vl-datatype-size type))
       ;; ((mv ?caveat desired-arithclass)  (vl-datatype-arithclass type))
       ;; ((unless (and (not err)
       ;;               desired-width
       ;;               (vl-integer-arithclass-p desired-arithclass)))
       ;;  (vl-unparam-debug "can't override ~a1: width or type unknown: ~
       ;;                     width ~a2, type ~a3; ~s4."
       ;;                    nil paramname desired-width desired-arithclass err)
       ;;  (mv nil
       ;;      (fatal :type :vl-bad-parameter-override
       ;;             :msg "can't override parameter ~s1: don't know the ~
       ;;                   correct width/signedness for type ~a2; ~@3."
       ;;             :args (list nil paramname type err))
       ;;      expr))

       ((wmv ok ?constp warnings reduced-expr ?svex)
        (vl-elaborated-expr-consteval expr ss scopes :type type))
       ((unless ok)
        (vl-unparam-debug "only reduced ~a1 to ~a2 (not a constant).~%"
                          nil expr reduced-expr)
        (mv nil
            (fatal :type :vl-bad-parameter-override
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


(define vl-override-parameter
  :parents (elaborate)
  :short "Try to override a parameter with a new expression."
  ((decl       vl-paramdecl-p      "Some parameter from the submodule.")
   (elabindex  "In the declaration scope")
   (override   vl-maybe-paramvalue-p "The value to override this parameter with,
                                      if any -- should be elaborated already")
   (ov-ss         vl-scopestack-p     "Scopestack for the override context")
   (ov-scope-path vl-elabtraversal-p "How to get to the scopes for the override context")
   (warnings vl-warninglist-p      "Warnings accumulator for the submodule.")
   &key
   ((config vl-simpconfig-p) 'config))
  :returns (mv (okp       booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (new-param vl-paramdecl-p "On success, final (coerced) value to
                                          use for this parameter.")
               (new-elabindex "updated svexconf for paramdecl context"))

  (b* (((vl-paramdecl decl) (vl-paramdecl-fix decl))
       (warnings (ok))
       ((vl-simpconfig config))
       ((wmv ok warnings decl.type elabindex)
        (vl-paramtype-elaborate decl.type elabindex
                                :reclimit config.elab-limit))

       ;; To get the override scopes, temporarily traverse to that path.
       (elabindex (vl-elabindex-sync-scopes))
       (scopes1 (vl-elabindex->scopes))
       ;; (- (set-fal-debug (list (vl-elabscope->members (vl-elabscopes->top-scope scopes1))
       ;;                         (vl-elabscope->subscopes (vl-elabscopes->top-scope scopes1)))))
       (ov-scopes (vl-elabscopes-traverse ov-scope-path scopes1))
       ;; (- (add-fal-debug (list (vl-elabscope->members (vl-elabscopes->top-scope ov-scopes))
       ;;                         (vl-elabscope->subscopes (vl-elabscopes->top-scope ov-scopes))))
       

       ;; (- (cw "decl-conf: ~x0~%" decl-conf))
       ((unless ok)
        (mv nil warnings decl elabindex)))
    ;; ((mv ok warnings new-param elabindex)
    (vl-paramtype-case decl.type
      (:vl-typeparam
       (b* (((unless override)
             (b* (((unless decl.type.default)
                   (mv nil
                       (fatal :type :vl-bad-parameter-override
                              :msg "Can't instantiate without assignment ~
                                    for type parameter ~a1."
                              :args (list nil decl))
                       decl elabindex))
                  ((unless (vl-datatype-resolved-p decl.type.default))
                   (mv nil
                       (fatal :type :vl-bad-parameter-override
                              :msg "Default type for parameter ~a1 not resolved."
                              :args (list nil decl))
                       decl elabindex)))
               (mv t (ok) (change-vl-paramdecl decl :type decl.type) elabindex)))
            ((when (vl-paramvalue-case override :expr))
             (mv nil
                 (fatal :type :vl-bad-parameter-override
                        :msg "Overriding type parameter ~a1 with expression ~a2."
                        :args (list nil decl (vl-paramvalue-expr->expr override)))
                 decl elabindex))
            (type (vl-paramvalue-type->type override))
            ((unless (vl-datatype-resolved-p type))
             (mv nil
                 (fatal :type :vl-bad-parameter-override
                        :msg "Override type ~a1 for parameter ~a2 not resolved."
                        :args (list nil type decl))
                 decl elabindex)))
         (mv t warnings (change-vl-paramdecl
                         decl
                         :type (change-vl-typeparam decl.type :default type)
                         :overriddenp t)
             elabindex)))


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
                 (fatal :type :vl-bad-parameter-override
                        :msg "Overriding value parameter ~a1 with type ~a2."
                        :args (list nil decl (vl-paramvalue-type->type override)))
                 decl elabindex))
            ((mv expr expr-ss expr-scopes)
             (if override
                 (mv (vl-paramvalue-expr->expr override) ov-ss ov-scopes)
               (mv decl.type.default (vl-elabindex->ss) (vl-elabindex->scopes))))
            ((unless expr)
             (mv nil
                 (fatal :type :vl-bad-parameter-override
                        :msg "Can't instantiate without assignment for ~
                              value parameter ~a1."
                        :args (list nil decl))
                 decl elabindex))
            ((unless (vl-datatype-resolved-p decl.type.type))
             (mv nil
                 (fatal :type :vl-bad-parameter-override
                        :msg "Failed to resolve datatype ~a1 for parameter ~a2"
                        :args (list nil decl.type.type decl))
                 decl elabindex))
            ((mv okp warnings coerced-expr)
             (vl-convert-parameter-value-to-explicit-type
              decl.type.type expr expr-ss expr-scopes warnings decl.name))
            ((unless okp)
             ;; Already warned.
             (mv nil warnings decl elabindex))
            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            ;; (new-type (change-vl-explicitvalueparam decl.type :default coerced-expr))
            ;; (new-decl (change-vl-paramdecl decl :type new-type))
            (new-decl (change-vl-paramdecl
                       decl
                       :type (change-vl-explicitvalueparam
                              decl.type
                              :default coerced-expr)
                       :overriddenp (and override t)))
            )
         (vl-unparam-debug "successfully overriding value parameter ~a1 with ~a2.~%"
                           nil decl coerced-expr)
         (mv t (ok) new-decl elabindex)))

      (:vl-implicitvalueparam
       ;; See the rules in SystemVerilog-2012 Section 23.10 and 6.20.2.
       (b* (((when (and override (vl-paramvalue-case override :type)))
             (mv nil
                 (fatal :type :vl-bad-parameter-override
                        :msg "Overriding value parameter ~a1 with type ~a2."
                        :args (list nil decl (vl-paramvalue-type->type override)))
                 decl elabindex))
            ((mv expr expr-ss expr-scopes)
             (if override
                 (mv (vl-paramvalue-expr->expr override) ov-ss ov-scopes)
               (mv decl.type.default (vl-elabindex->ss) (vl-elabindex->scopes))))
            ((unless expr)
             (mv nil
                 (fatal :type :vl-bad-parameter-override
                        :msg "Can't instantiate without assignment for ~
                              value parameter ~a1."
                        :args (list nil decl))
                 decl elabindex))
            ((wmv warnings err datatype)
             (vl-implicitvalueparam-final-type decl.type expr expr-ss expr-scopes))
            ((when err)
             (mv nil
                 (fatal :type :vl-bad-parameter-override
                        :msg "Failed to determine datatype for parameter ~
                              ~a1 overridden with ~a2: ~@3"
                        :args (list nil decl expr err))
                 decl elabindex))

            ((mv okp warnings coerced-expr)
             ;; Do the conversion explicitly, which gives us all the nice warnings.
             (vl-convert-parameter-value-to-explicit-type datatype expr expr-ss expr-scopes warnings decl.name))
            ((unless okp)
             ;; Already warned
             (mv nil warnings decl elabindex))

            ;; Else, we successfully converted the overwriting expr to have the
            ;; right type.  So, rewrite the parameter declaration to install
            ;; the right value.
            (new-decl (change-vl-paramdecl
                       decl
                       :type (make-vl-explicitvalueparam :type datatype :default coerced-expr)
                       :overriddenp (and override t))))
         (vl-unparam-debug "successfully overriding ~a1 with ~a2.~%"
                           nil decl coerced-expr)
         (mv t (ok) new-decl elabindex))));; ))
    ;; (set-fal-debug nil)
    ;; (mv ok warnings new-param elabindex)
    ))

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


