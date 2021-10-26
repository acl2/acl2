; Syntheto Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SYNTHETO")

(include-book "language/static-semantics")
(include-book "language/deep-to-shallow")
(include-book "shallow/top")

(include-book "kestrel/std/util/defmacro-plus" :dir :system)
(include-book "system/pseudo-event-formp" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ translation
  :parents (syntheto)
  :short "Translation between Syntheto and ACL2."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since Syntheto is a front-end language for ACL2 (and APT),
     there is a mapping between the two.
     We are developing a bidirectional translation between the two.")
   (xdoc::p
    "The translation is more than turning constructs in one language
     into corresponding constructs of the other language.
     In particular, when translating Syntheto to ACL2,
     we also need to submit and keep track of
     the ACL2 events corresponding to the Syntheto constructs."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod trans-state
  :short "Fixtype of translation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "The translation between Syntheto and ACL2 is stateful.
     Syntheto top-level constructs are incrementally translated to ACL2.
     Since new top-level constructs may depend on old ones,
     we keep track of the Syntheto top-level constructs
     translated to ACL2 so far.")
   (xdoc::p
    "These are stored as deeply embedded Syntheto ASTs,
     ordered as a sequence according to how they are introduced.
     (This suggests that we may want to use the term `Syntheto events'
     for what we now call `Syntheto top-level constructs',
     and abolish the notion of Syntheto program altogether.)")
   (xdoc::p
    "The sequence is initially empty.
     It grows as new Syntheto top-level constructs are translated to ACL2
     (these ultimately come from the Syntheto IDE).
     It shrinks (as ultimately directed by the Syntheto IDE)
     in a similar way to ACL2's undo history commands.
     We represent the sequence as a list in reverse chronological order,
     i.e. the @(tsee car) is the most recent top-level construct:
     this makes the extension of the sequence more efficient.")
   (xdoc::p
    "For now these ASTs are the only information in the translation state.
     We may extend the translation state to hold additional information.")
   (xdoc::p
    "We store the curent translation state in an ACL2 table with a single key.
     We provide operations to initialize and extend tha translation state,
     and to retrieve it from the table.
     We also provide event macros to update it in the table.
     We do not provide operations to shrink the translation state:
     this can be achieved via ACL2's undo history commands,
     which also retract the ACL2 events generated
     from the Syntheto top-level constructs stored in the translation state."))
  ((tops toplevel-list))
  :pred trans-statep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-trans-state ()
  :returns (tstate trans-statep)
  :short "Initial translation state."
  (make-trans-state :tops nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define extend-trans-state ((top toplevelp) (tstate trans-statep))
  :returns (new-tstate trans-statep)
  :short "Extend the translation state with a Syntheto top-level construct."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is @(tsee cons)ed to the list,
     which is in reverse chronological order."))
  (change-trans-state tstate :tops (cons top (trans-state->tops tstate)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;

(define extend-trans-state-list ((tops toplevel-listp) (tstate trans-statep))
  :returns (new-tstate trans-statep)
  :short "Lift @(tsee extend-trans-state) to lists."
  (cond ((endp tops) (trans-state-fix tstate))
        (t (extend-trans-state-list (cdr tops)
                                    (extend-trans-state (car tops) tstate))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection trans-state-table
  :short "Table of translation states."

  (table trans-state-table nil nil
    :guard (and (eq acl2::key :state)
                (trans-statep acl2::val)))

  (table trans-state-table :state (init-trans-state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define get-trans-state ((wrld plist-worldp))
  :returns (tstate trans-statep)
  :short "Get the translation state from the table."
  (b* ((table (table-alist 'trans-state-table wrld))
       ((unless (alistp table))
        (raise "Internal error: ~
                the translation state table ~x0 is not an alist."
               table)
        (init-trans-state))
       (tstate (cdr (assoc-eq :state table)))
       ((unless (trans-statep tstate))
        (raise "Internal error: ~
                the translation state ~x0 is malformed."
               tstate)
        (init-trans-state)))
    tstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ set-trans-state (tstate)
  (declare (xargs :guard (trans-statep tstate)))
  `(table trans-state-table :state ',tstate))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ translate-to-acl2 (top/tops)
  :short "Translate to ACL2 a Syntheto top-level construct or a list of them."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the entry point of the translation from Syntheto to ACL2.
     The argument is evaluated, and it must evaluate to
     a Syntheto top-level construct or to a list of them;
     this is checked by the function called by this macro.
     The function returns events that are submitted to ACL2 by this macro.
     The events update the translation state table
     and generate ACL2 counterparts of the Syntheto construct(s)."))
  `(make-event (translate-to-acl2-fn ,top/tops
                                     'translate-to-acl2
                                     state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define translate-to-acl2-fn (top/tops ctx state)
  :returns (mv erp (event "A @(tsee pseudo-event-formp).") state)
  :mode :program
  :short "Translate a Syntheto top-level construct, or a list of them,
          into corresponding ACL2 events."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is called by @(tsee translate-to-acl2),
     which is the entry point of the translation from Syntheto to ACL2.")
   (xdoc::p
    "We ensure that the input is a top-level construct or a list of them.")
   (xdoc::p
    "We retrieve the existing (i.e. old) top-level constructs
     from the current translation state.
     We wrap them into a context and we check that
     the input satisfies the static semantics
     (this wrapping is a bit awkward, and we will eliminate it
     after we make some planned improvements to the static semnantics).
     If the static semantic checks succeed,
     we generate an event to extend the translation state with the input.")
   (xdoc::p
    "This is just a start: there is, of course, much more to do here.
     In particular, we need to generate ACL2 events
     corresponding to the input Syntheto top-level constructs.
     We are also curently ignoring the type obligations
     generated by the static semantics checks:
     these should be turned into ACL2 theorems,
     and used to generate proofs for the other events
     (e.g. guard proofs for function definitions)."))
  (b* (((er tops)
        (cond ((toplevelp top/tops) (value (list top/tops)))
              ((toplevel-listp top/tops) (value top/tops))
              (t (er soft ctx
                     "The input must be ~
                            a Syntheto top-level construct ~
                            or a list of them, ~
                            but it is ~x0 instead."
                     top/tops))))
       (tstate (get-trans-state (w state)))
       (old-tops (trans-state->tops tstate))
       (ctxt (make-context :tops old-tops))
       ((mv err? obligs) (check-toplevel-list tops ctxt))
       ((when err?) (er soft ctx "Static semantic failure:~%~x0" err?))
       (- (cw "Proof obligations:~%~x0~%" obligs))
       (tstate (extend-trans-state-list tops tstate))
       (table-event `(set-trans-state ,tstate))
       (logical-events (d-->s-toplevel-list tops)))
    (value `(progn
              ,table-event
              ,@logical-events))))
