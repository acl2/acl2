; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SOFT")

(include-book "core")

(include-book "kestrel/event-macros/make-event-terse" :dir :system)
(include-book "kestrel/event-macros/restore-output" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ defthm-inst-implementation
  :parents (soft-implementation defthm-inst)
  :short "Implementation of @(tsee defthm-inst)."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-sothm-inst (sothm-inst (wrld plist-worldp))
  :returns (yes/no "A @(tsee booleanp).")
  :mode :program
  :short "Recognize designations of instances of second-order theorems."
  :long
  (xdoc::topstring-p
   "A designation of an instance of a second-order theorem has the form
    @('(sothm (f1 . g1) ... (fM . gM))'),
    where @('sothm') is a second-order theorem
    and @('((f1 . g1) ... (fM . gM))') is an instantiation.
    These designations are used in @(tsee defthm-inst).")
  (and (true-listp sothm-inst)
       (>= (len sothm-inst) 2)
       (sothmp (car sothm-inst) wrld)
       (funvar-instp (cdr sothm-inst) wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define defthm-inst-fn (thm
                        sothm-inst
                        options
                        (ctx "Context for errors.")
                        state)
  :returns (mv (erp "@(tsee booleanp) flag of the
                     <see topic='@(url acl2::error-triple)'>error
                     triple</see>.")
               (event "A @(tsee maybe-pseudo-event-formp).")
               state)
  :mode :program
  :short "Validate some of the inputs to @(tsee defthm-inst)
          and generate the event form to submit."
  :long
  (xdoc::topstring-p
   "We directly check all the inputs except for the @(':rule-classes') option,
    relying on @(tsee defthm) to check it.")
  (b* ((wrld (w state))
       ((unless (symbolp thm))
        (er-soft+ ctx t nil
                  "The first input must be a symbol, but ~x0 is not."
                  thm))
       ((unless (check-sothm-inst sothm-inst wrld))
        (er-soft+ ctx t nil
                  "The second input must be ~
                   the name of a second-order theorem ~
                   followed by the pairs of an instantiation, ~
                   but ~x0 is not."
                  sothm-inst))
       (sothm (car sothm-inst))
       (inst (cdr sothm-inst))
       ((unless (subsetp (alist-keys inst) (funvars-of-thm sothm wrld)))
        (er-soft+ ctx t nil
                  "Each function variable key of ~x0 must be ~
                   among function variable that ~x1 depends on."
                  inst sothm))
       ((unless (keyword-value-listp options))
        (er-soft+ ctx t nil
                  "The inputs after the second input ~
                   must be a keyword-value list, ~
                   but ~x0 is not."
                  options))
       (keywords (evens options))
       ((unless (no-duplicatesp keywords))
        (er-soft+ ctx t nil
                  "The inputs keywords must be unique."))
       ((unless (subsetp keywords '(:rule-classes :enable :print)))
        (er-soft+ ctx t nil
                  "Only the input keywords ~
                   :RULE-CLASSES, :ENABLE, and :PRINT are allowed."))
       (print-pair (assoc-keyword :print options))
       (print (if print-pair
                  (cadr print-pair)
                :result))
       ((unless (member-eq print '(nil :all :result)))
        (er-soft+ ctx t nil
                  "The :PRINT input must be NIL, :ALL, or :RESULT, ~
                   but ~x0 is not."
                  print))
       (options (remove-keyword :print options))
       (enable-pair (assoc-keyword :enable options))
       (enable (if enable-pair
                   (cadr enable-pair)
                 t))
       ((unless (booleanp enable))
        (er-soft+ ctx t nil
                  "The :ENABLE input must be T or NIL, ~
                   but it is ~x0 instead."
                  enable))
       (options (remove-keyword :enable options))
       (sothm-formula (formula sothm nil wrld))
       (thm-formula (fun-subst-term inst sothm-formula wrld))
       (thm-formula (untranslate thm-formula t wrld))
       (fsbs (ext-fun-subst-term sothm-formula inst wrld))
       (thm-proof (sothm-inst-proof sothm fsbs wrld))
       (macro (if enable 'defthm 'defthmd))
       (defthm-event `(,macro ,thm ,thm-formula ,@thm-proof ,@options))
       (defthm-event-without-proof `(,macro ,thm ,thm-formula ,@options))
       (return-value-event `(value-triple ',thm))
       (event (cond ((eq print nil)
                     `(progn
                        ,defthm-event
                        ,return-value-event))
                    ((eq print :all)
                     (restore-output
                      `(progn
                         ,defthm-event
                         ,return-value-event)))
                    ((eq print :result)
                     `(progn
                        ,defthm-event
                        (cw-event "~x0~|" ',defthm-event-without-proof)
                        ,return-value-event))
                    (t (impossible)))))
    (value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection defthm-inst-macro-definition
  :short "Definition of the @(tsee defthm-inst) macro."
  :long
  "@(def defthm-inst)
   @(def acl2::defthm-inst)"

  (defmacro defthm-inst (thm sothminst &rest options)
    `(make-event-terse (defthm-inst-fn
                         ',thm
                         ',sothminst
                         ',options
                         (cons 'defthm-inst ',thm)
                         state)))

  (defmacro acl2::defthm-inst (&rest args)
    `(defthm-inst ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection show-defthm-inst
  :short "Show the event form generated by @(tsee defthm-inst),
          without submitting them."
  :long
  "@(def show-defthm-inst)
   @(def acl2::show-defthm-inst)"

  (defmacro show-defthm-inst (thm sothminst &rest options)
    `(defthm-inst-fn
       ',thm
       ',sothminst
       ',options
       (cons 'defthm-inst ',thm)
       state))

  (defmacro acl2::show-defthm-inst (&rest args)
    `(show-defthm-inst ,@args)))
