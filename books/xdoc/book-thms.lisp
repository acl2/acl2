; Utility for finding theorems defined non-redundantly in a book or encapsulate

; Copyright (C) 2014, Regents of the University of Texas
; Written by Matt Kaufmann (original date October, 2007; augmented January, 2011)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Modified by Jared Davis, October 2014, to add support for raw documentation
; strings in defsections.

; This file first introduces two utilities, which require that the indicated
; book already be included when running them.

;   (theorems-introduced-in "book-name" state)
;   returns a list of names of all the theorems (i.e. defthm event names) and
;   axioms (i.e., defaxiom event names) introduced in the book or its
;   certifification world (portcullis), not including those introduced in
;   sub-books.

;   (book-thms "book-name" translated-p)
;   is similar to the above, but returns an alist associating names with their
;   formulas (in translated form if translated-p is t, but untranslated if
;   translated-p is nil).

; Then, this file introduces utilities for collecting and displaying formulas
; introduced by a sequence of events.  The main macro at the user level is
; encapsulate-then-new-info, but users may want something different, and the
; underlying utility new-formula-info suggests how to build other such macros.

; Thanks to Jared Davis for requesting and trying out this book.

; See book-thms-example.lisp for an example of the usage of these utilities.

(in-package "ACL2")

(program)

(defun newly-defined-top-level-thms-rec (trips collect-p full-book-name acc
                                               translated-p)

; See newly-defined-top-level-fns-rec in the sources.  Translated-p is true if
; we want translated theorems, else is false.

  (cond ((endp trips)
         acc)
        ((and (eq (caar trips) 'include-book-path)
              (eq (cadar trips) 'global-value))
         (newly-defined-top-level-thms-rec (cdr trips)
                                           (equal (car (cddar trips))
                                                  full-book-name)
                                           full-book-name
                                           acc
                                           translated-p))
        ((not collect-p)
         (newly-defined-top-level-thms-rec (cdr trips) nil full-book-name acc
                                           translated-p))
        ((eq (cadar trips) (if translated-p 'theorem 'untranslated-theorem))
         (newly-defined-top-level-thms-rec
          (cdr trips)
          collect-p
          full-book-name
          (acons (caar trips) (cddar trips) acc)
          translated-p))
        (t
         (newly-defined-top-level-thms-rec (cdr trips) collect-p full-book-name
                                          acc translated-p))))

(defun reversed-world-since-event (wrld ev acc)
  (cond ((or (endp wrld)
             (let ((trip (car wrld)))
               (and (eq (car trip) 'event-landmark)
                    (eq (cadr trip) 'global-value)
                    (equal (access-event-tuple-form (cddr trip)) ev))))
         acc)
        (t (reversed-world-since-event (cdr wrld)
                                       ev
                                       (cons (car wrld) acc)))))

(defun reversed-world-since-boot-strap (wrld)
  (reversed-world-since-event wrld '(exit-boot-strap-mode) nil))

(defun book-thms-fn (book-name translated-p state)

; This function assumes that book-name has already been included.  Translated-p
; is true if we want translated theorems, else is false.

  (declare (xargs :stobjs state))
  (mv-let
    (full-book-name directory-name familiar-name)
    (parse-book-name (cbd) book-name ".lisp" 'book-thms state)
    (declare (ignore directory-name familiar-name))
    (newly-defined-top-level-thms-rec
     (reversed-world-since-boot-strap (w state))
      nil
      full-book-name
      nil
      translated-p)))

(defmacro book-thms (book-name translated-p)

; This macro assumes that book-name has already been included.  Translated-p is
; true if we want translated theorems, else is false.

  `(book-thms-fn ,book-name ,translated-p state))

(defun theorems-introduced-in (book-name state)

; This function assumes that book-name has already been included.  Translated-p
; is true if we want translated theorems, else is false.

  (declare (xargs :stobjs state))
  (strip-cars (book-thms-fn book-name t state)))

;;; Section: New axioms and theorems after executing events, e.g., an
;;; encapsulate

; Below we collect up the new formulas introduced by a sequence of events.  We
; do not include information on events that don't introduce formulas, such as
; table events or deflabel events.  That wouldn't be difficult to do, but the
; current view is formula-based rather than event-based, so presentation might
; be an issue.

(table acl2-xdoc)

(defmacro acl2-xdoc-fragment (msg)
  `(progn
     ;; Originally I didn't have this extra setting of :fragment to NIL, but
     ;; that can lead to doc fragments being redundant with one another.  This
     ;; was really confusing when dong the bitops/merge documentation where the
     ;; fragments were copied and pasted from one function to the next.
     ;; Anyway, setting the fragment to NIL makes sure that the next message
     ;; won't be redundant.
     (table acl2-xdoc :fragment nil)
     (table acl2-xdoc :fragment ,msg)))



; We collect into acc entries of the following forms, using untranslated
; (user-level) syntax for formulas.

; - (name :theorem thm)
;     for (defthm name thm ...)
; - (name :def (equal (name . formals) body))
;     for (defun name formals ... body)
; - ((name1 ... namek) :constraint formula)
;     for names (name1 ... namek) introduced with the indicated constraint
;     formula
; - (name :defchoose formula)
;     for name introduced by defchoose with the indicated constraint
; - "blah"
;     for calls of (acl2-xdoc-fragment "blah")

; Remarks:

; (1) Definitions in a mutual-recursion are listed separately.

; (2) We don't check for which may leave properties *acl2-property-unbound*, so
; we are not handling redefinition,

; (3) Defun-sk is implemented with encapsulate and a local defchoose, so one
; will see a :constrain tuple rather than :defchoose tuple in this case.

; (4) Unlike the function newly-defined-top-level-fns-rec, we give no special
; treatment for include-book.  Events from a subsidiary book that are
; represented in trips will be considered.  However, typically trips may come
; from (pass 2 of) an encapsulate event, in which case there are no
; include-book events represented (since any such are local to the
; encapsulate).

(defun new-formula-info1 (trip wrld acc)
  (let ((name (car trip))
        (prop (cddr trip)))
    (case (cadr trip)
      (theorem
       (cons (list name :theorem prop) acc))
      (unnormalized-body
       (cond ((eq (getprop name 'constraint-lst t 'current-acl2-world wrld) t)
              (cons (list name
                          :def
                          `(equal (,name ,@(formals name wrld))
                                  ,(untranslate prop nil wrld)))
                    acc))
             (t ; function is really constrained
              acc)))
      (constraint-lst
       (cond ((and prop (symbolp prop))
              acc)
             (t
              (cons (list (getprop name 'siblings nil 'current-acl2-world wrld)
                          :constraint
                          (untranslate (cons 'and prop) t wrld))
                    acc))))
      (defchoose-axiom
        (cons (list name :defchoose (untranslate prop t wrld))
              acc))
      (global-value
       (if (and (eq name 'event-landmark)
                (eq (access-event-tuple-type prop) 'table))
           (let ((form (access-event-tuple-form prop)))
             (if (and (eq (first form) 'table)
                      (eq (second form) 'acl2-xdoc)
                      (eq (third form) :fragment)
                      (stringp (fourth form)))
                 (cons (fourth form) acc)
               acc))
         acc))
      (t acc))))

(defun new-formula-info (trips wrld acc)
  (if (endp trips)
      acc
    (let ((acc (new-formula-info1 (car trips) wrld acc)))
      (new-formula-info (cdr trips) wrld acc))))

(defmacro with-intro-table (&rest events)

; Events is a list of events.  We wrap events in a progn that concludes with an
; additional event, a table mapping :info to the information collected by
; new-formula-info (see the comments there) for the indicated events.

  (let ((marker ; lay down a non-redundant marker
         '(table intro-table :mark world)))
    `(progn
       ,marker
       ,@events
       (make-event
        (let* ((wrld (w state))
               (trips (reversed-world-since-event wrld ',marker nil))
               (info (reverse (new-formula-info trips wrld nil))))
          `(table intro-table :info ',info))))))

(defmacro encapsulate-then-new-info (name &rest events)

; Events is a list of events.  We wrap events into an (encapsulate () ...) and
; follow that with a zero-ary definition of name, which returns information of
; the sort discussed above (see comments in new-formula-info).

  (declare (xargs :guard (and name (symbolp name))))
  `(progn (with-intro-table
           (encapsulate
            ()
            ,@events))
          (make-event
           (let ((wrld (w state)))
             (list 'defun ',name nil
                   (list 'quote
                         (cdr (assoc-eq :info (table-alist 'intro-table
                                                           wrld)))))))))

#||
;; for testing:
(encapsulate-then-new-info foo
  (defun f (x) x)
  (acl2-xdoc-fragment "Hello")
  (defun f2 (x) x)
  (acl2-xdoc-fragment "World")
  (defun f3 (x) x))
||#
