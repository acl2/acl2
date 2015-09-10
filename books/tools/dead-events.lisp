; Copyright (C) 2013, Regents of the University of Texas
; Written by Shilpi Goel and Matt Kaufmann (original date January, 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Dead events (dead code and theorems) analysis tool

; For some relevant background, see :DOC dead-events in the ACL2
; documentation.

; Example use:
; cd ../workshops/1999/compiler/
; [Start ACL2]
; (ld "proof.lisp")
; (include-book "misc/dead-events" :dir :system)
; (dead-events '(compiler-correctness-for-programs) :start 'function-callp)
; Result:
;  (BINARY-FOR-ARGS BINARY-FOR-ARGSEVLIST-APPEND
;                   BINARY-FOR-OPERATORS
;                   TLP-REV NATP1+ EVLIST-ON-NON-INTEGERS
;                   COMPILE-DEFS-TRUE-LISTS
;                   DEFINITION-LISTS-ARE-TRUE-LISTS
;                   WF-DEFS-ARE-TRUE-LISTS)
; After commenting out all events in proof.lisp with names in the list returned
; by the above call of dead-events, the resulting book was still certifiable.

; Example invocations:

; (dead-events '(foo bar))
; - Find the names of all function symbols and theorems that do not participate
;   in the proofs of admission of foo and bar.  Even "syntactic supporters" are
;   considered to "participate": function symbols f that occur in the formulas
;   of foo or bar, function symbols that occur in the formulas of all such f,
;   and so on.

; (dead-events '(foo bar baz) :syntaxp nil)
; - Find all user events that do not support any of the proofs done when
;   admitting events foo, bar, and baz.

; (dead-events '(foo bar baz) :syntaxp t) ; default for :syntaxp
; - As just above, except that the notion of "support" is extended to include
;   syntactic supporters.

; (dead-events '(foo bar) :start 'start-of-events-label)
; - With the above :start argument, the events returned are restricted to those
;   that are as recent as the event named start-of-events-label.

; General specification:

; The macro (dead-events lst) is defined near the end of this book, where lst
; should evaluate to a non-empty list of event names, and the result is a list
; of event names for dead code and dead theorems: names of function and
; theorems that do not support the proof of any event in lst, even though they
; are admitted before some event in lst.

; By default, or if keyword :syntaxp t is provided, "support the proof of event
; E" is interpreted broadly: it includes not only the names of rules and hinted
; events (from :use, :by, or :clause-processor hints) that are used by the
; prover when admitting E, but also function symbols ancestral in the formula
; of event E.  However, if keyword argument :syntaxp nil is provided, then only
; the former are included, not the ancestral function symbols.

; It may be useful to provide a value for the keyword argument, :start.  When
; that argument is evaluated, its value should be the name E of an event, and
; only events at least as recent as E will be returned.

; The summary that is printed at the end of the admission of an event is
; basically a courtesy to the user.  The tools provided here are only as good
; as that summary, which may not be complete since it does not mention, for
; example, congruence rules.  Still, we expect the summary to be adequate in
; most cases.  Other possible weaknesses of these tools are outlined in the
; section labeled "TO DO" below.

; NOTES:

; - Please feel free to extend or otherwise improve this book!

; - This tool is to be run in a world that was created without skipping proofs.
;   Note that names of macros and :program mode functions are never considered
;   to be dead.  More complete documentation will likely come later.

; - This code may not work as expected if there has been redefinition.  Indeed,
;   the macro dead-events requires keyword parameter :redef-ok t in that case.
;   Search for "redefinition" below for at least a few places where
;   redefinition presents problems.  But those comments are probably far from
;   exhaustive; redefinition is tricky.  It may be difficult to give a sensible
;   answer to the following question: What does it even mean for A to be a
;   proof-supporter of B if we have redefined one of these events?

; - If you want to read the code below, it may be helpful to go top-down.  Some
;   key data structures passed around are as follows.

;   supp-ar: an array whose keys are absolute-event-numbers.  Each key is
;   mapped to the list of names of events that support a proof for the event
;   whose absolute-event-number is the given key.

;   live-names-ar: an array whose keys are absolute-event-numbers.  All keys
;   are initially mapped to nil, but as we see that a key k is the
;   absolute-event-number of a non-dead event, we map k to t.

; TO DO:

; - Improve documentation, e.g., clarifying that (and how) proof-supporters
;   tracking and summaries aren't perfect (for example, ignoring
;   verify-guards).

; - (ACL2 sources change) Save the proof-supporters-alist produced by
;   certify-book, so that we can run dead-events after certify-book.

; - Save info in proof-supporters-alist for events without names whose
;   admissibility depends on proofs, such as verify-guards.

; - Consider extending the notion of ancestors to include the function
;   symbols from the 'classes property.  To see that property try this, for
;   example:
;     (defthm foo (equal x x)
;       :rule-classes ((:rewrite :corollary (equal (car (cons 3 b)) 3))))
;     :props foo
;   By the way, notice that source function immediate-canonical-ancestors
;   considers the guard of the canonical function but, sadly I think, not the
;   guard of its siblings.

; - Generalize notion of "syntactic supporter"; see the WARNING in
;   immediate-syntactic-supporters-lst.

; - Improve efficiency by using "start" argument of dead-events-fn to limit
;   building of the transitive closure.

; - Arrange that for each macro, or at least each macro called in the formula
;   of an input event name, all of its supporters are considered not dead.

; - Put the events below into :logic mode.

; - Add syntactic support to event-supports.

(in-package "ACL2")

(program)

(defun absolute-event-number (namex wrld quietp)

; If quietp is nil then we insist on an absolute event number; otherwise we are
; allowed to return nil.

  (let ((name (if (consp namex) (car namex) namex)))
    (cond ((getprop name 'absolute-event-number nil 'current-acl2-world wrld))
          (quietp nil)
          (t (er hard 'absolute-event-number
                 "There is no event in the current ACL2 world that ~
                  corresponds to the name ~x0."
                 name)))))

(defconst *supp-ar-name* 'supp-ar)

(defun make-supp-ar-1 (supp-alist supp-ar wrld)

; The proof-supporters-alist of wrld is an alist with entries of the form
; (namex . supps), where namex is a symbol or list of symbols and supps is a
; list of symbols.  Supp-alist is a tail of (global-val 'proof-supporters-alist
; wrld).  Supp-ar is initially an empty array, built in make-supp-ar.  We
; extend supp-ar so that for each pair (namex . supps) in supp-alist, the
; absolute event number for namex is an index associated with supps.

  (cond ((endp supp-alist) supp-ar)
        (t
         (let* ((n (absolute-event-number (caar supp-alist) wrld nil))
                (supps (cdar supp-alist))
                (supp-ar (assert$ (null (aref1 *supp-ar-name* supp-ar n))
                                  (aset1 *supp-ar-name* supp-ar n supps))))
           (make-supp-ar-1 (cdr supp-alist) supp-ar wrld)))))

(defun make-supp-ar (wrld)

; We return an array corresponding to the proof-supporters-alist of wrld, as
; described in make-supp-ar-1.

  (let ((size (next-absolute-event-number wrld))
        (supp-alist (global-val 'proof-supporters-alist wrld)))
    (make-supp-ar-1 supp-alist
                    (compress1 *supp-ar-name*
                               (list (list :HEADER
                                           :DIMENSIONS (list size)
                                           :MAXIMUM-LENGTH
; Why is the max length 1 more than size?  See :doc arrays.
                                           (1+ size)
                                           :DEFAULT nil
                                           :NAME *supp-ar-name*)))
                    wrld)))

(defconst *live-names-ar-name* 'live-names-ar)

(defun make-live-names-ar-nil (names supp-ar live-names-ar wrld)

; Return an extension of live-names-ar that associates each name in names with
; its supporters, according to supp-ar (which associates the proof-supporters
; for each event with its absolute-event-numbers).  Note that the resulting
; array is transitively closed: a supporter of a supporter is a supporter.

; Keep this in sync with make-live-names-ar-t, as these functions are different
; only on whether they include syntactic ancestors.  (This one does not.)

  (cond ((endp names) live-names-ar)
        (t (let ((n (absolute-event-number (car names) wrld nil)))
             (cond
              ((aref1 *live-names-ar-name* live-names-ar n)
               (make-live-names-ar-nil (cdr names) supp-ar live-names-ar wrld))
              (t (let ((live-names-ar
                        (aset1 *live-names-ar-name* live-names-ar n t))
                       (supps (aref1 *supp-ar-name* supp-ar n)))
                   (make-live-names-ar-nil

; Make sure that each supporter (and all their supporters, etc.) is ultimately
; marked.

                    (append supps (cdr names))
                    supp-ar live-names-ar wrld))))))))

(defun immediate-syntactic-supporters (name wrld)

; WARNING: This function is incomplete.  To be really complete, it ought also
; to account for siblings and for the 'classes property for theorems.

  (cond
   ((function-symbolp name wrld)
    (let ((guard (guard name t wrld))
          (anc (immediate-instantiable-ancestors name wrld nil)))
      (cond ((equal guard *t*) ; rather common case
             anc)
            (t (all-ffn-symbs (guard name t wrld)
                              anc)))))
   (t (let ((thm (getprop name 'theorem nil 'current-acl2-world wrld)))
        (if thm (all-ffn-symbs thm nil) nil)))))

(defun make-live-names-ar-t (names supp-ar live-names-ar wrld)

; Return an extension of live-names-ar that associates each name in names with
; its supporters: not only supporters according to supp-ar (which associates
; the proof-supporters for each event with its absolute-event-numbers), but
; also syntactic supporters.  Note that the resulting array is transitively
; closed: a supporter of a supporter is a supporter.

; Keep this in sync with make-live-names-ar-nil, as these functions are
; different only on whether they include syntactic ancestors.  (This one does.)

  (cond ((endp names) live-names-ar)
        (t (let ((n (absolute-event-number (car names) wrld nil)))
             (cond
              ((aref1 *live-names-ar-name* live-names-ar n)
               (make-live-names-ar-t (cdr names) supp-ar live-names-ar wrld))
              (t (let ((live-names-ar
                        (aset1 *live-names-ar-name* live-names-ar n t))
                       (supps (aref1 *supp-ar-name* supp-ar n))
                       (supps-syn (immediate-syntactic-supporters (car names)
                                                                  wrld)))
                   (make-live-names-ar-t

; Make sure that each supporter (and all their supporters, etc.) is ultimately
; marked.
                    (append supps-syn supps (cdr names))
                    supp-ar live-names-ar wrld))))))))

(defun make-live-names-ar (syntaxp names supp-ar wrld)

; Note that dimensions and maximum-length can in general be reduced with a bit
; of effort, based on the maximum absolute event number for members of names.
; But that seems like an unimportant optimization.

  (let* ((dimensions (dimensions *supp-ar-name* supp-ar))
         (maximum-length (maximum-length *supp-ar-name* supp-ar))
         (live-names-ar (compress1 *live-names-ar-name*
                                   (list (list :HEADER
                                               :DIMENSIONS dimensions
                                               :MAXIMUM-LENGTH maximum-length
                                               :DEFAULT nil
                                               :NAME *live-names-ar-name*)))))
    (if syntaxp
        (make-live-names-ar-t names supp-ar live-names-ar wrld)
      (make-live-names-ar-nil names supp-ar live-names-ar wrld))))

(defun dead-events-1 (start live-names-ar trips wrld acc)

; Trips is a tail of the current logical world, wrld.  We walk through trips,
; collecting suitably dead event names into acc.  Live-names-ar is an array
; that maps live event names (only) to t.  Since we are assuming that there has
; been no redefinition, we do not have to concern ourselves with properties
; that have been erased, i.e., we do not have to handle
; *acl2-property-unbound*.

  (cond ((null trips)
         (er hard 'dead-events-1
             "Implementation error!  Somehow missed event landmark for ~x0."
             start))
        (t (let ((trip (car trips)))
             (case-match trip
               (('event-landmark 'global-value . rest)
                (cond
                 ((eql (access-event-tuple-number rest) start)
                  acc)
                 (t (dead-events-1 start live-names-ar (cdr trips) wrld acc))))
               ((name prop . &)
                (dead-events-1
                 start live-names-ar (cdr trips) wrld
                 (if (and (or (eq prop 'theorem)
                              (and (eq prop 'formals)
                                   (not (eq (symbol-class name wrld)
                                            :PROGRAM))))
                          (let ((n (absolute-event-number name wrld t)))
                            (and n
                                 (not (aref1 *live-names-ar-name* live-names-ar
                                             n)))))
                     (cons name acc)
                   acc)))
               (& (er hard 'dead-events-1
                      "Implementation error: Found non-triple in world!")))))))

(defun max-live-names-ar-number (live-names-ar acc)

; We accumulate into acc, and ultimately return, the maximum absolute event
; number from live-names-ar.

  (cond ((endp live-names-ar) acc)
        (t (max-live-names-ar-number
            (cdr live-names-ar)
            (if (eq (caar live-names-ar) :HEADER)
                acc
              (max acc
                   (caar live-names-ar)))))))

(defun return-tail-of-world (max-live-event-number wrld)

; Return-tail-of-world returns the tail of the world beginning from this
; number.

  (cond ((endp wrld)
         (er hard 'return-tail-of-world
             "Implementation error: Reached the end of the world!"))
        (t
         (let ((trip (car wrld)))
           (case-match trip
               (('event-landmark 'global-value . rest)
                (cond
                  ((eql (access-event-tuple-number rest)
                        max-live-event-number)
                   wrld)
                  (t
                   (return-tail-of-world max-live-event-number (cdr wrld)))))
             ((& & . &)
              (return-tail-of-world max-live-event-number (cdr wrld)))
             (& (er hard 'return-tail-of-world
                    "Implementation error: Found non-triple in world!")))))))

(defun dead-events-fn (names syntaxp start redef-ok wrld)
  (let ((ctx 'dead-events))
    (cond
     ((null names)
      (er hard ctx
          "At least one name must be supplied to DEAD-EVENTS."))
     ((not (symbol-listp names))
      (er hard ctx
          "The argument of DEAD-EVENTS must evaluate to a true list of ~
           symbols, but instead it evaluates to ~x0."
          names))
     ((and (not redef-ok)
           (global-val 'redef-seen wrld))
      (er hard ctx
          "Redefinition has taken place in the current ACL2 world.  However, ~
           the DEAD-EVENTS utility has been designed under the assumption ~
           that there has not been any redefinition.  If you wish to risk ~
           hard errors and surprising results, use keyword parameter ~
           :REDEF-OK T."))
     (t
      (let* ((supp-ar (make-supp-ar wrld))
             (live-names-ar (make-live-names-ar syntaxp names supp-ar wrld))
             (start (cond ((symbolp start)
                           (if start

; We subtract 1 here because we need to continue past the event-landmark for
; start (which is laid down last, towards the top of the world) up to the
; preceding event-landmark.

                               (1- (absolute-event-number start wrld nil))
                             (absolute-event-number 'end-of-pass-2 wrld nil)))
                          ((posp start) (1- start))
                          (t (er hard ctx
                                 "The first argument of dead-events must ~
                                  evaluate to a positive integer or a symbol, ~
                                  but ~x0 is neither."
                                 start))))
             (max (max-live-names-ar-number live-names-ar -1))
             (trips (return-tail-of-world max wrld)))
        (dead-events-1 start live-names-ar trips wrld nil))))))

(defmacro dead-events (names &key (syntaxp 't) start redef-ok)
  `(dead-events-fn ,names ,syntaxp ,start ,redef-ok (w state)))

; Start code for event-supports.  For now, it does not use syntactic supporters.

(defun event-supports-fn (name supp-alist events-acc)
  (let ((supporters (cdar supp-alist)))
    (if (endp supp-alist)
        events-acc
      (event-supports-fn name
                         (cdr supp-alist)
                         (if (member-eq name supporters)
                             (cons (caar supp-alist) events-acc)
                           events-acc)))))

(defun event-supports-fn-lst (names supp-alist acc)
  (cond ((endp names) acc)
        (t
         (event-supports-fn-lst (cdr names)
                                supp-alist
                                (cons (cons (car names)
                                            (event-supports-fn
                                             (car names)
                                             supp-alist
                                             nil))
                                      acc)))))

(defmacro event-supports (namex)

; event-supports macro takes a list of events --- namex --- and for every event
; name in namex, prints out a list of events that are supported by name. The
; event-supports macro uses the proof-supporters-alist and hence, for now, does
; not return the events for which name is a syntactic supporter (for example,
; the events whose guard proofs need name).

; TO-DO:

; A way in which syntactic supporters can be listed in the output of
; event-supports is by writing a function that returns the name of the event
; when given the absolute-event-number and using it on the output of
; make-supp-ar.  The resulting list can be provided in place of
; proof-supporters-alist. (Else modify live-names-ar to map
; absolute-event-numbers to the names of the event, etc).

  `(event-supports-fn-lst ,namex
                          (global-val 'proof-supporters-alist (w state))
                          nil))

(logic)

