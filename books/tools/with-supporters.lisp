; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date March, 2014)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This utility provides necessary function definitions, but not macro
; definitions.

; Possible future enhancements include the following.

; - Collect up function symbols from keyword arguments of defattach.

; - Consider trying to ensure that the defattach events go through -- could be
;   very difficult since we would need to re-create the theory in which they
;   were processed, and some rules might have been local -- or at least improve
;   the error message when they fail.

; - Perhaps support keyword arguments in with-supporters-after that are
;   supported in with-supporters.

; - Potential loose ends include loop$ expressions, picking up symbols inside
;   quoted lambdas and lambda$ objects, flet calls (in
;   collect-constants-and-macros-1), guards for non-trivial encapsulates
;   when signatures length exceeds 1 (see supporters-of-1), and handling of
;   ruler-extenders in locally included book (not sure how to do that).

; - Not much explicit attention has been paid to default hints and
;   override-hints.  Handling of tables might cover them, but these haven't
;   been tested in with-supporters-test-{sub|top}.lisp.

; - Perhaps improve defattach-event-lst, as indicated in its comment about the
;   "seen" argument.

(in-package "ACL2")

(program)
(set-state-ok t)

(defun fns-with-abs-ev-between (names min max wrld acc)

; Return a list of all symbols in names whose absolute-event-number property
; has value greater than min and at most max.

  (cond
   ((endp names) acc)
   (t (fns-with-abs-ev-between
       (cdr names)
       min max
       wrld
       (let ((k (getpropc (car names) 'absolute-event-number 0 wrld)))
         (cond ((and (< min k)
                     (<= k max))
                (cons (car names) acc))
               (t acc)))))))

(defun instantiable-ancestors-with-guards/measures (fns wrld ans)

; See ACL2 source function instantiable-ancestors, from which this is derived.
; However, in this case we also include function symbols from guards in the
; result.

  (cond
   ((null fns) ans)
   ((member-eq (car fns) ans)
    (instantiable-ancestors-with-guards/measures (cdr fns) wrld ans))
   (t
    (let* ((ans1 (cons (car fns) ans))
           (imm (immediate-instantiable-ancestors (car fns) wrld ans1))
           (guard (getpropc (car fns) 'guard nil wrld))
           (just (getpropc (car fns) 'justification nil wrld))
           (measure (and just (access justification just :measure)))
           (imm1 (if guard
                     (all-fnnames1 nil guard imm)
                   imm))
           (imm2 (if measure
                     (all-fnnames1 nil measure imm1)
                   imm1))
           (ans2 (instantiable-ancestors-with-guards/measures imm2 wrld ans1)))
      (instantiable-ancestors-with-guards/measures (cdr fns) wrld ans2)))))

(defun macro-names-from-aliases (names macro-aliases acc)
  (cond ((endp names) acc)
        (t (macro-names-from-aliases
            (cdr names)
            macro-aliases
            (let ((pair (rassoc (car names) macro-aliases)))
              (cond (pair (cons (car pair) acc))
                    (t acc)))))))

(defun get-event+ (name wrld)

; This variant of get-event (defined in the ACL2 sources) returns (mv n ev)
; where ev is the event and n is its absolute-event-number, and returns (mv nil
; nil) if the event is not found.

  (let ((index (getpropc name 'absolute-event-number nil wrld)))
    (cond (index (mv index
                     (access-event-tuple-form
                      (cddr (car (lookup-world-index 'event index wrld))))))
          (t (mv nil nil)))))

(mutual-recursion

(defun collect-constants-and-macros-1 (form acc wrld state-vars)

; We make a reasonable effort to accumulate into acc all macros called and
; constants encountered in the expansion of form.

  (cond
   ((booleanp form) acc)
   ((defined-constant form wrld) (cons form acc))
   ((not (true-listp form)) acc)
   ((member-eq (car form) '(quote lambda$)) acc)
   ((eq (car form) 'let)
    (let ((bindings (cadr form)))
      (collect-constants-and-macros-lst
       (and (doublet-listp bindings) ; could fail if under macro call
            (strip-cadrs bindings))
       (collect-constants-and-macros-1 (car (last form)) acc wrld state-vars)
       wrld state-vars)))
   ((eq (car form) 'stobj-let)
    (collect-constants-and-macros-lst (cdddr form) acc wrld state-vars))
   ((and (consp (car form))
         (eq (caar form) 'lambda)
         (true-listp (car form)))
    (collect-constants-and-macros-1
     (car (last (car form))) ; lambda-body
     (collect-constants-and-macros-lst (cdr form) acc wrld state-vars)
     wrld state-vars))
   ((getpropc (car form) 'macro-body nil wrld)
    (mv-let (erp expansion)
      (macroexpand1-cmp form 'some-ctx wrld state-vars)
      (cond
       (erp acc) ; impossible?
       (t (collect-constants-and-macros-1 expansion (cons (car form) acc)
                                          wrld state-vars)))))
   (t (collect-constants-and-macros-lst (cdr form) acc wrld state-vars))))

(defun collect-constants-and-macros-lst (lst acc wrld state-vars)
  (cond ((endp lst) acc)
        (t (collect-constants-and-macros-1
            (car lst)
            (collect-constants-and-macros-lst (cdr lst) acc wrld state-vars)
            wrld state-vars))))
)

(defun guard-from-event (ev wrld)

; This is based on source function guard-raw.  But here we pass in the event,
; which could be a defmacro call, not just a defun[x] call.  The result is the
; original, untranslated guard if one is supplied, else nil.

  (mv-let
    (dcls guard)
    (dcls-guard-raw-from-def (cdr ev) wrld)
    (declare (ignore dcls))
    guard))

(mutual-recursion

(defun collect-constants-and-macros-ev (ev acc wrld state-vars)

; Ev is an embedded event form stored in an event-tuple of wrld.  This function
; attempts to collect all names occurring during the expansion of ev as
; constants or macros.  It may collect too few or too many, and it can surely
; be improved (e.g., by looking inside :corollary fields of rule-classes).  But
; it's something.

; We skip encapsulate, since our overarching algorithm already picks up its
; subsidiary events.

  (assert$
   (true-listp ev)
   (case (car ev)
     ((defun defund defun-nx defund-nx ; variants of defun in mutual-recursion
             defmacro)
      (let* ((guard (guard-from-event ev wrld))
             (acc
              (if guard
                  (collect-constants-and-macros-1 guard acc wrld state-vars)
                acc)))
        (collect-constants-and-macros-1 (car (last ev)) acc wrld state-vars)))
     (defchoose
      (collect-constants-and-macros-1 (car (last ev)) acc wrld state-vars))
     (mutual-recursion
      (collect-constants-and-macros-ev-lst (cdr ev) acc wrld state-vars))
     ((defthm defaxiom defconst deftheory)
      (collect-constants-and-macros-1 (caddr ev) acc wrld state-vars))
     (defchoose
       (collect-constants-and-macros-1 (nth 4 ev) acc wrld state-vars))
     (table (collect-constants-and-macros-lst (cddr ev) acc wrld state-vars))
     (otherwise acc))))

(defun collect-constants-and-macros-ev-lst (ev-lst acc wrld state-vars)
  (cond
   ((endp ev-lst) acc)
   (t (collect-constants-and-macros-ev
       (car ev-lst)
       (collect-constants-and-macros-ev-lst (cdr ev-lst) acc wrld state-vars)
       wrld state-vars))))
)

(mutual-recursion

(defun supporters-of-1-lst (defs min max macro-aliases wrld state-vars)
  (cond ((endp defs) nil)
        (t (append (supporters-of-1 (car defs) min max macro-aliases wrld
                                    state-vars)
                   (supporters-of-1-lst (cdr defs) min max macro-aliases wrld
                                        state-vars)))))

(defun supporters-of-1 (ev min max macro-aliases wrld state-vars)

 ; Make a reasonable attempt to return all function, macro, and constant
 ; symbols that support ev.

  (cond
   ((and (consp ev) ; always true?
         (eq (car ev) 'mutual-recursion))
    (supporters-of-1-lst (cdr ev) min max macro-aliases wrld state-vars))
   (t
    (let* ((non-trivial-encapsulate-p

; In this case, the non-local events inside the encapsulate get their own
; event-landmarks so we don't need to handle them here.

            (and (consp ev) ; always true?
                 (eq (car ev) 'encapsulate)
                 (cadr ev)))
           (name (if non-trivial-encapsulate-p
                     (let ((sig (car (cadr ev))))
                       (if (symbolp (car sig)) ; old-style signature
                           (car sig)
                         (caar sig)))
                   (and (consp ev)          ; always true?
                        (consp (cdr ev))    ; always true?
                        (symbolp (cadr ev))
                        (cadr ev)))))
      (and name
           (let* ((formula
                   (if non-trivial-encapsulate-p
                       (mv-let (name2 x)
                         (constraint-info name wrld)
                         (cond
                          ((unknown-constraints-p x) *t*) ; incomplete!
                          (name2 (conjoin x))
                          (t x)))
                     (or (getpropc name 'macro-body nil wrld)
                         (formula name nil wrld))))
                  (guard ; incomplete for encapsulate if more than 1 signature
                   (getpropc name 'guard nil wrld))
                  (attachment-prop (attachment-alist name wrld))
                  (attachment-alist (and (not (eq (car attachment-prop)
                                                  :attachment-disallowed))
                                         attachment-prop))
                  (new-fns
                   (and (or formula ; non-nil if guard is non-nil
                            attachment-alist)
                        (fns-with-abs-ev-between
                         (instantiable-ancestors-with-guards/measures
                          (fns-with-abs-ev-between
                           (all-fnnames1
                            nil
                            formula ; OK even if formula=nil (treated as var)
                            (and (or guard attachment-alist)
                                 (all-fnnames1
                                  nil
                                  guard
                                  (append (strip-cars attachment-alist)
                                          (strip-cdrs attachment-alist)))))
                           min max wrld nil)
                          wrld
                          nil)
                         min max wrld nil)))
                  (new-names
                   (if non-trivial-encapsulate-p
                       (collect-constants-and-macros-1 formula new-fns wrld
                                                       state-vars)
                     (collect-constants-and-macros-ev
                      ev new-fns wrld state-vars))))
             (macro-names-from-aliases new-fns macro-aliases new-names)))))))
)

(defun supporters-of-rec (lst fal min max macro-aliases ctx wrld state-vars)

; Each element of lst is either a symbol or a pair (n . ev) where ev is an
; event and n is its absolute-event-number.  Fal is a fast-alist that is nil at
; the top level.  We extend fal with triples (n ev . fns) where ev is an event
; with absolute event number n and fns is a list of function symbols introduced
; by ev.  We do this for each event ev that supports events based on lst
; (either events in lst or definitions of names in lst).

  (cond
   ((endp lst) fal)
   (t
    (let ((constraint-lst
           (and (symbolp (car lst))
                (getpropc (car lst) 'constraint-lst nil wrld))))
      (cond
       ((and constraint-lst
             (symbolp constraint-lst))

; We are looking at a defun in an encapsulate that is not one that
; (conceptually) can be moved before or after that encapsulate (as described in
; the "Structured Theory" paper).  We leave it to the encapsulate to deal with
; it, since that defun might reference functions constrained in the encapsulate
; that have a later absolute-event-number.  So, we simply replace the current
; function symbol with the one it references.

        (supporters-of-rec (cons constraint-lst (cdr lst))
                           fal min max macro-aliases ctx wrld
                           state-vars))
       (t
        (mv-let (n ev)
          (if (symbolp (car lst))
              (get-event+ (car lst) wrld)
            (mv (caar lst) (cdar lst)))
          (cond
           ((null n) ; hence (symbolp (car lst))
            (er hard ctx
                "The name ~x0 is not defined, yet it was expected to be."
                (car lst)))
           ((hons-get n fal)
            (supporters-of-rec (cdr lst)
                               fal min max macro-aliases ctx wrld state-vars))
           (t
            (let ((fns (supporters-of-1 ev min max macro-aliases wrld
                                        state-vars)))
              (supporters-of-rec (append fns (cdr lst))
                                 (hons-acons n (cons ev fns) fal)
                                 min max macro-aliases ctx wrld
                                 state-vars)))))))))))

(defun adjust-defun-for-symbol-class (ev wrld)

; See adjust-ev-for-symbol-class.  This is the special case when ev is a defun
; event (or defund etc.).

  (flet ((add-dcl-to-defun
          (dcl ev)                           ; ev is (defun ...)
          `(,(car ev) ,(cadr ev) ,(caddr ev) ; defun[d][nx] name formals
            (declare ,dcl)
            ,@(cdddr ev))))
    (case (symbol-class (cadr ev) wrld)
      (:program
; Avoid sensitivity to default-defun-mode.
       (add-dcl-to-defun '(xargs :mode :program) ev))
      (:ideal
; Avoid sensitivity to default-defun-mode and verify-guards-eagerness.
       (add-dcl-to-defun '(xargs :mode :logic :verify-guards nil) ev))
      (otherwise ; :common-lisp-compliant

; This case is a bit tricky.  Suppose we are defining f and that before
; including the book at issue, f was defined simply as (defun f (x) x).  Now
; suppose the book contains the form (verify-guards f).  Then we need that
; verify-guards form here, rather than simply adding declaring :verify-guards
; t, which ACL2 would not accept.  It seems simplest just to include a
; verify-guards event.

       `(progn ,ev
               (verify-guards ,(cadr ev)))))))

(defun adjust-encapsulate-for-symbol-class (ev wrld)

; See adjust-ev-for-symbol-class.  This is the special case when ev is a
; non-trivial encapsulate event.

  (let ((name (case-match ev
                (('encapsulate (((name . &) . &) . &) . &)
                 name)
                (('encapsulate ((name . &) . &) . &)
                 name)
                (& nil))))
    (cond
     (name
      (let* ((wrld-tail (lookup-world-index
                         'event
                         (getpropc name 'absolute-event-number 0 wrld)
                         wrld))
             (old-vge (default-verify-guards-eagerness wrld-tail))
             (new-vge (default-verify-guards-eagerness wrld)))
        (cond ((eql old-vge new-vge) ev)
              (t `(encapsulate
                    ()
; The following setting of the acl2-defaults-table is local to the surrounding
; encapsulate.
                    (set-verify-guards-eagerness ,old-vge)
                    ,ev)))))
     (t ev))))

(defun adjust-ev-for-symbol-class (ev wrld)

; Ev is an event, as returned by get-event, that comes from a locally-included
; book.  We will be evaluating ev without including that book, after evaluating
; events that support ev.  We want to ensure that its symbol-class in that
; future state will be the same as it was when we locally included the book.
; We return a possibly modified event that provides that guarantee.  So we
; return an event that is a version of ev with that property.

  (case (car ev)
    (defchoose

; Defchoose is skipped in :program mode.  So the original event was executed in
; ;logic mode and we want that to happen here, too.

      `(encapsulate () (logic) ,ev))
    ((defun defund defun-nx defund-nx) ; variants of defun in mutual-recursion
     (adjust-defun-for-symbol-class ev wrld))
    (mutual-recursion
     (let ((def1 (adjust-defun-for-symbol-class (cadr ev) wrld)))
       (if (eq (car def1) 'progn) ; (progn & (verify-guards &))
           `(progn ,ev ,(caddr def1))
         `(mutual-recursion
           ,def1
           ,@(cddr ev)))))
    (encapsulate
     (adjust-encapsulate-for-symbol-class ev wrld))
    (otherwise ev)))

(defun events-from-supporters-fal (pairs min max wrld acc)

; Each element of pairs is of the form (n ev . &) where ev is an event, and
; pairs is sorted by car in increasing order.  We collect suitably-adjusted
; cadrs from pairs until a car exceeds max.

  (cond
   ((or (endp pairs)
        (< max (caar pairs)))
    (reverse acc))
   ((<= (car (car pairs)) min)
    (events-from-supporters-fal (cdr pairs) min max wrld acc))
   (t
    (events-from-supporters-fal
     (cdr pairs) min max wrld
     (cons (adjust-ev-for-symbol-class (cadr (car pairs)) wrld)
           acc)))))

(defun get-defattach-event-fn (ev)

; Ev is a defattach event.  Return (mv fs gs), where fs is lists the functions
; attached in ev and gs lists the functions to which the fs are attached.

  (case-match ev
    (('defattach (f . &) . &)
     f)
    (('defattach f &)
     f)
    (& nil)))

(defun defattach-event-lst (wrld fns min max acc seen)

; Wrld is a list of triples, most recent first.  Fns is a list of function
; symbols.  Accumulate into acc every defattach event with
; absolute-event-number in the half-open interval (min,max] that attaches to
; any function symbol in fns.  At the top level, acc is nil; the events are
; returned with the oldest first (reverse order from wrld).  Seen accumulates
; the "key" (first) function symbol from each set of defattach events -- this
; may not be perfect since a later defattach event may have a different key
; but still attach to the same function.

  (let ((trip (car wrld)))
    (cond
     ((and (eq (car trip) 'event-landmark)
           (eq (cadr trip) 'global-value))
      (cond
       ((<= (access-event-tuple-number (cddr trip)) min)
        acc)
       ((or (> (access-event-tuple-number (cddr trip)) max)
            (not (eq (car (access-event-tuple-form (cddr trip))) 'defattach)))
        (defattach-event-lst (cdr wrld) fns min max acc seen))
       (t
        (let* ((ev (access-event-tuple-form (cddr trip)))
               (fn (get-defattach-event-fn ev)))
          (cond
           ((and fn
                 (not (member-eq fn seen))
                 (member-eq fn fns))
            (defattach-event-lst (cdr wrld) fns min max
              (cons ev acc)
              (cons fn seen)))
           (t (defattach-event-lst (cdr wrld) fns min max acc seen)))))))
     (t (defattach-event-lst (cdr wrld) fns min max acc seen)))))

(defun supporters-of (lst min max ctx wrld state-vars)

; Each element of lst is either a symbol or a pair (n . ev) where ev is an
; event and n is its absolute-event-number.  We return a pair (evs . fns) where
; evs contains all such events except that some are suitably adjusted (see
; adjust-ev-for-symbol-class), and fns lists of names supporting these events
; including function symbols, constant symbols, and macro names.

  (let* ((fal (supporters-of-rec lst nil min max
                                 (macro-aliases wrld)
                                 ctx wrld state-vars))
         (x (merge-sort-car-< (fast-alist-free fal)))
         (fns (append-lst (strip-cddrs x))))
    (cons (append? (events-from-supporters-fal x min max wrld nil)
                   (defattach-event-lst wrld fns min max nil nil))
          fns)))

(defun table-info-after-k (names wrld k evs table-guard-fns)

; Accumulate into evs the most recent table event for each name in names (or
; all names other than the two skipped, as mentioned below, if names is :all)
; having absolute-event-number property greater than k.  Except, the "most
; recent" restriction does not apply to table guard events.  Also, accumulate
; into table-guard-fns all function symbols occurring in those table guards.

; We skip the acl2-defaults-table, as we should for our purposes since that
; table's events are local to a book.

; We also skip the xdoc table, since it may be awkward to maintain invariants.
; Without that exception, we saw an error, "HARD ACL2 ERROR in XDOC-EXTEND:
; Topic FAST-<< wasn't found."

  (let ((trip (car wrld)))
    (cond
     ((and (eq (car trip) 'event-landmark)
           (eq (cadr trip) 'global-value))
      (cond
       ((<= (access-event-tuple-number (cddr trip)) k)
        (mv evs table-guard-fns))
       (t (let* ((ev (access-event-tuple-form (cddr trip)))
                 (evs (case-match ev
                        (('table name nil nil :guard &)
                         (cond
                          ((eq name 'pe-table)

; The extend-pe-table event generates a call of (table pe-table ...) that
; causes an error if the name doesn't have an absolute-event-number.  This can
; heppen if that name isn't among the supporters.  Our solution here is to skip
; pe-table events.  If this is a problem we can perhaps pass in all supporters
; and make sure the name is among them.

                           evs)
                          ((or (eq names :all)
                               (member-eq name names))
                           (cons ev evs))
                          (t evs)))
                        (('table name . &)
                         (cond
                          ((eq name 'pe-table) ; see comment on pe-table above
                           evs)
                          ((and (not (member-eq name ; see comment above
                                                '(acl2-defaults-table
                                                  xdoc)))
                                (or (eq names :all)
                                    (member-eq name names))
                                (not (assoc-eq-cadr name evs)))
                           (cons ev evs))
                          (t evs)))
                        (& evs))))
            (table-info-after-k names (cdr wrld) k evs table-guard-fns)))))
     ((and (eq (cadr trip) 'table-guard)
           (not (eq (cddr trip) *acl2-property-unbound*)))
      (table-info-after-k names (cdr wrld) k evs
                          (all-fnnames1 nil (cddr trip) table-guard-fns)))
     (t (table-info-after-k names (cdr wrld) k evs table-guard-fns)))))

(defun supporters-in-theory-event (fns ens wrld disables)
  (cond ((endp fns)
         (and disables
              `(in-theory (disable ,@disables))))
        (t (supporters-in-theory-event (cdr fns) ens wrld
                                       (append
                                        (disabledp-fn (car fns) ens wrld)
                                        disables)))))

(defmacro wsa-er (str &rest args)
  `(mv (er hard 'with-supporters ,str ,@args)
       nil nil nil nil))

(defconst *with-supporters-with-output-default*
  '(:off :all :on (error)))

(defun with-supporters-args (events names tables show with-output
                                    with-output-p)

; We return (mv names tables events), where the input events optionally starts
; with :names and/or :tables.  An error occurs if this parse fails.

  (cond ((null events)
         (mv names
             tables
             show
             (if with-output-p
                 with-output
               '(:off :all :on error))
             nil))
        ((eq (car events) :names)
         (cond ((null (cdr events))
                (wsa-er "No argument was supplied for :NAMES."))
               ((not (symbol-listp (cadr events)))
                (wsa-er "The value of :NAMES must be a list of symbols, which ~
                         ~x0 is not."
                        (cadr events)))
               (t (with-supporters-args (cddr events)
                                        (cadr events)
                                        tables show with-output
                                        with-output-p))))
        ((eq (car events) :tables)
         (cond ((null (cdr events))
                (wsa-er "No argument was supplied for :TABLES."))
               ((not (or (eq (cadr events) :all)
                         (symbol-listp (cadr events))))
                (wsa-er "The value of :TABLES must be :ALL or a list of ~
                         symbols, but ~x0 is neither."
                        (cadr events)))
               (t (with-supporters-args (cddr events)
                                        names
                                        (cadr events)
                                        show with-output with-output-p))))
        ((eq (car events) :show)
         (cond ((null (cdr events))
                (wsa-er "No argument was supplied for :SHOW."))
               ((not (member-eq (cadr events) '(t nil :only)))
                (wsa-er "The value of :SHOW must be Boolean or :ONLY, but ~
                         ~x0 is not."
                        (cadr events)))
               (t (with-supporters-args (cddr events)
                                        names tables
                                        (cadr events)
                                        with-output with-output-p))))
        ((eq (car events) :with-output)
         (cond ((null (cdr events))
                (wsa-er "No argument was supplied for :WITH-OUTPUT."))
               ((not (keyword-value-listp (cadr events)))
                (wsa-er "The value of :WITH-OUTPUT must satisfy ~x0, but ~x1 ~
                         does not."
                        'keyword-value-listp
                        (cadr events)))
               (t (with-supporters-args (cddr events)
                                        names tables show
                                        (cadr events) t))))
        ((atom (car events))
         (wsa-er "An event must be a cons, but your first event was ~x0. ~
                  Perhaps you intended to use :NAMES."
                 (car events)))
        ((or (member-eq :names events)
             (member-eq :tables events)
             (member-eq :show events)
             (member-eq :with-output events))
         (wsa-er "The :NAMES, and :TABLES keywords of WITH-SUPPORTERS must ~
                  appear immediately after the (initial) LOCAL event."))
        (t (mv names tables show
               (if with-output-p
                   with-output
                 '(:off :all :on error))
               events))))

(defun event-pairs-after (k wrld acc)

; Accumulate into acc all pairs (n . ev) for events ev stored in wrld with
; absolute-event-number n exceeding k.  The extended acc is returned, which
; puts the accumulated pairs in ascending order by car.

  (let ((trip (car wrld)))
    (cond ((and (eq (car trip) 'event-landmark)
                (eq (cadr trip) 'global-value))
           (let ((n (access-event-tuple-number (cddr trip))))
             (cond ((<= n k) acc)
                   (t (event-pairs-after k
                                         (cdr wrld)
                                         (cons (cons n (access-event-tuple-form
                                                        (cddr trip)))
                                               acc))))))
          (t (event-pairs-after k (cdr wrld) acc)))))

(defun with-supporters-fn (local-event rest)
  (cond
   ((not (and (true-listp local-event)
              (eq (car local-event) 'local)
              (consp (cdr local-event))
              (null (cddr local-event))))
    (er hard 'with-supporters
        "The first argument of ~x0 should be of the form (LOCAL ...), but ~
         that argument is ~x1."
        'with-supporters local-event))
   ((member-eq :names (cdr (member-eq :names rest)))
    (er hard 'with-supporters
        "A :NAMES argument may not occur more than once in a call of ~x0."
        'with-supporters))
   (t
    (mv-let (names tables show with-output events)
      (with-supporters-args rest nil nil nil nil nil)
      (let* ((form
              `(let ((min (max-absolute-event-number (w state)))
                     (ctx 'with-supporters))
                 (er-progn
                  ,(cadr local-event)
                  (let* ((wrld (w state))
                         (max (max-absolute-event-number wrld)))
                    (mv-let (table-evs fns1)
                      (table-info-after-k ',tables wrld min nil nil)
                      (er-progn
                       (progn ,@events)
                       (let* ((wrld (w state))
                              (event-pairs

; Since events might include macro calls, calls of progn, etc., we seed our
; call of supporters-of using events taken directly from the world.  An
; alternate approach would be to call macroexpand1-cmp repeatedly until
; reaching an event, but note that this way we also have the corresponding
; absolute event numbers in hand.

                               (event-pairs-after max wrld nil))
                              (extras/fns
                               (supporters-of (append fns1
                                                      ',names
                                                      event-pairs)
                                              min max ctx wrld
                                              (default-state-vars t)))
                              (extras (car extras/fns))
                              (fns (cdr extras/fns))
                              (in-theory-event
                               (supporters-in-theory-event
                                fns (ens state) wrld nil))
                              (ev
                               (list*
                                'encapsulate
                                ()
                                ',local-event
                                '(set-enforce-redundancy t)
                                '(SET-BOGUS-DEFUN-HINTS-OK T)
                                '(SET-BOGUS-MUTUAL-RECURSION-OK T)
                                '(SET-IRRELEVANT-FORMALS-OK T)
                                '(SET-IGNORE-OK T)
                                '(SET-STATE-OK T)
                                (append extras
                                        table-evs
                                        (and in-theory-event
                                             (list in-theory-event))
                                        (cons '(set-enforce-redundancy nil)
                                              ',events))))
                              ,@(and with-output
                                     `((ev (cons 'with-output
                                                 (append ',with-output
                                                         (list ev)))))))
                         ,(case show
                            (:only
                             '(value (list 'value-triple (list 'quote ev))))
                            ((t)
                             '(pprogn
                               (fms "Expansion of with-supporters call:~|~x0~|"
                                    (list (cons #\0 ev))
                                    (standard-co state) state nil)
                               (value ev)))
                            ((nil) '(value ev))
                            (otherwise (er hard 'with-supporters
                                           "Illegal value of :show, ~x0"
                                           show)))))))))))
        (if with-output
            `(make-event (with-output! ,@with-output ,form))
          `(make-event ,form)))))))

(defmacro with-supporters (local-event &rest rest)
  (with-supporters-fn local-event rest))

(defun with-supporters-after-fn (name events)
  `(make-event
    (let ((min (getprop ',name 'absolute-event-number nil
                        'current-acl2-world (w state)))
          (max (max-absolute-event-number (w state))))
      (cond
       ((null min)
        (er soft 'with-supporters
            "The symbol ~x0 does not seem to be the name of an event."
            ',name))
       (t (er-progn
           (progn ,@events)
           (let* ((wrld (w state))
                  (event-pairs (event-pairs-after max wrld nil))
                  (extras/fns
                   (supporters-of event-pairs min max 'with-supporters-after
                                  wrld (default-state-vars t)))
                  (extras (car extras/fns))
                  (fns (cdr extras/fns))
                  (in-theory-event
                   (supporters-in-theory-event
                    fns (ens state) (w state) nil)))
             (value (list* 'progn
                           '(set-enforce-redundancy t)
                           '(SET-BOGUS-DEFUN-HINTS-OK T)
                           '(SET-BOGUS-MUTUAL-RECURSION-OK T)
                           '(SET-IRRELEVANT-FORMALS-OK T)
                           '(SET-IGNORE-OK T)
                           (append extras
                                   (and in-theory-event
                                        (list in-theory-event))
                                   (cons '(set-enforce-redundancy nil)
                                         ',events)))))))))))

(defmacro with-supporters-after (name &rest events)
  (declare (xargs :guard (symbolp name)))
  (with-supporters-after-fn name events))
