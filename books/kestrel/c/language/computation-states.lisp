; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "array-operations")
(include-book "structure-operations")

(include-book "kestrel/fty/defomap" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ computation-states
  :parents (language)
  :short "A model of C computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide a model of the states of computation of an executing C program,
     along with operations to manipulate these computation states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap scope
  :short "Fixtype of variable scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "A variable scope is a finite map from identifiers to values.
     It represents the contents of the variables in a scope.
     This may be a block scope or a file scope."))
  :key-type ident
  :val-type value
  :pred scopep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist scope-list
  :short "Fixtype of lists of variable scopes."
  :elt-type scope
  :true-listp t
  :elementp-of-nil t
  :pred scope-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult scope "scopes")

(defruled not-errorp-when-scopep
  (implies (scopep x)
           (not (errorp x)))
  :enable errorp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult scope-list "lists of scopes")

;;;;;;;;;;;;;;;;;;;;

(defruled errorp-when-scope-list-resultp
  (implies (scope-list-resultp x)
           (equal (errorp x)
                  (not (scope-listp x))))
  :enable (errorp scope-list-resultp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod frame
  :short "Fixtype of frames."
  :long
  (xdoc::topstring
   (xdoc::p
    "Every time a function is called, a frame is created,
     which contains information about
     the function and its variables' values.")
   (xdoc::p
    "The variables are organized into a stack (i.e. list) of scopes,
     which grows leftward and shrinks rightward
     (i.e. scopes are added via @(tsee cons) and removed via @(tsee cdr).
     There is always at least one scope,
     i.e. the one for the function body's block.")
   (xdoc::p
    "As defined later, the call stack is represented as
     a stack (i.e. list) of frames."))
  ((function ident)
   (scopes scope-list :reqfix (if (consp scopes) scopes (list nil))))
  :require (consp scopes)
  :pred framep
  ///

  (defrule len-of-frame->scopes-lower-bound
    (> (len (frame->scopes frame)) 0)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist frame-list
  :short "Fixtype of lists of frames."
  :elt-type frame
  :true-listp t
  :elementp-of-nil nil
  :pred frame-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap heap
  :short "Fixtype of heaps."
  :long
  (xdoc::topstring
   (xdoc::p
    "The heap is the memory area manipulated by @('malloc') and @('free').
     [C] does not actually use the term `heap';
     in fact, [C] does not appear to use a specific term for this memory area.
     However, `heap' is sufficiently commonly used
     that it seems adequate to use it here.")
   (xdoc::p
    "For now we model the heap just as a finite map from addresses to values."))
  :key-type address
  :val-type value
  :pred heapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod compustate
  :short "Fixtype of computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "A computation state consists of:")
   (xdoc::ul
    (xdoc::li
     "A scope for static storage [C:6.2.4].
      Our current C subset only has one translation unit (i.e. file),
      so the static storage corresponds to
      the variables declared at the top-level in the file,
      which form a scope.")
    (xdoc::li
     "A stack of frames.
      The variables there are in automatic storage [C:6.2.4].")
    (xdoc::li
     "A heap.
      This is allocated storage [C:6.2.4]."))
   (xdoc::p
    "More components may be added,
     and some components may be refined,
     as our modeling coverage of C increases.")
   (xdoc::p
    "The stack grows leftward and shrinks rightward,
     i.e. push is @(tsee cons), pop is @(tsee cdr), and top is @(tsee car)."))
  ((static scope)
   (frames frame-list)
   (heap heap))
  :pred compustatep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption compustate-option
  compustate
  :short "Fixtype of optional computation states."
  :pred compustate-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult compustate "computation states")

;;;;;;;;;;;;;;;;;;;;

(defrule not-compustatep-of-error
  (not (compustatep (error x)))
  :enable (compustatep error))

;;;;;;;;;;;;;;;;;;;;

(defruled not-errorp-when-compustatep
  (implies (compustatep x)
           (not (errorp x)))
  :enable (errorp compustatep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult compustate-option "optional computation states"
  :enable (compustatep compustate-optionp errorp))

(defruled compustate-resultp-when-compustate-option-result-and-not-nil
  (implies (and (compustate-option-resultp x)
                x)
           (compustate-resultp x))
  :enable (compustate-resultp compustate-option-resultp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compustate-frames-number ((compst compustatep))
  :returns (n natp)
  :short "Number of frames in the call stack of a computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "The theorem @('compustate-frames-number-of-compustate-same-frames')
     is useful to show that @(tsee change-compustate)
     for a component other than @(':frames')
     preserves the number of frames."))
  (len (compustate->frames compst))
  :hooks (:fix)
  ///

  (defrule compustate-frames-number-of-compustate-same-frames
    (equal (compustate-frames-number
            (compustate static
                        (compustate->frames compst)
                        heap))
           (compustate-frames-number compst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define push-frame ((frame framep) (compst compustatep))
  :returns (new-compst compustatep)
  :short "Push a frame onto a computation state's call stack."
  (b* ((stack (compustate->frames compst))
       (new-stack (cons (frame-fix frame) stack)))
    (change-compustate compst :frames new-stack))
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-push-frame
    (equal (compustate-frames-number new-compst)
           (1+ (compustate-frames-number compst)))
    :hints (("Goal" :in-theory (enable compustate-frames-number)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define top-frame ((compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (frame framep)
  :short "Top frame of a computation state's call stack."
  (frame-fix (car (compustate->frames compst)))
  :guard-hints (("Goal" :in-theory (enable compustate-frames-number)))
  :hooks (:fix)
  ///

  (defrule top-frame-of-push-frame
    (equal (top-frame (push-frame frame compst))
           (frame-fix frame))
    :enable push-frame))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define pop-frame ((compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (new-compst compustatep)
  :short "Pop a frame from a computation state's non-empty call stack."
  (b* ((stack (compustate->frames compst))
       (new-stack (cdr stack)))
    (change-compustate compst :frames new-stack))
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-pop-frame
    (equal (compustate-frames-number new-compst)
           (1- (compustate-frames-number compst)))
    :hyp (> (compustate-frames-number compst) 0)
    :hints (("Goal" :in-theory (enable compustate-frames-number))))

  (defrule pop-frame-of-push-frame
    (equal (pop-frame (push-frame frame compst))
           (compustate-fix compst))
    :enable push-frame))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compustate-scopes-numbers ((compst compustatep))
  :returns (ns pos-listp)
  :short "Ordered list of the numbers of scopes in the call stack frames."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each frame in the call stack has a number of scopes.
     This function returns these numbers,
     in the same order as the frames in the stack."))
  (compustate-scopes-numbers-aux (compustate->frames compst))

  :prepwork
  ((define compustate-scopes-numbers-aux ((frames frame-listp))
     :returns (ns pos-listp)
     (cond ((endp frames) nil)
           (t (cons (len (frame->scopes (car frames)))
                    (compustate-scopes-numbers-aux (cdr frames)))))
     :hooks (:fix)
     ///
     (defret len-of-compustate-scopes-numbers-aux
       (equal (len ns)
              (len frames)))
     (defret consp-of-compustate-scopes-numbers-aux
       (equal (consp ns)
              (consp frames)))
     (defret car-of-compustate-scopes-numbers-aux
       (implies (> (len frames) 0)
                (equal (car ns)
                       (len (frame->scopes (car frames))))))))

  :hooks (:fix)

  ///

  (defret len-of-compustate-scopes-numbers
    (equal (len ns)
           (len (compustate->frames compst))))
  (in-theory (disable len-of-compustate-scopes-numbers))

  (defret consp-of-compustate-scopes-numbers
    (consp ns)
    :hyp (> (compustate-frames-number compst) 0)
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable compustate-frames-number))))

  (defret posp-of-car-of-compustate-scopes-numbers
    (posp (car ns))
    :hyp (> (compustate-frames-number compst) 0)
    :rule-classes :type-prescription
    :hints (("Goal" :in-theory (enable compustate-frames-number))))

  (defret car-of-compustate-scopes-numbers-lower-bound
    (> (car ns) 0)
    :hyp (> (compustate-frames-number compst) 0)
    :rule-classes :linear
    :hints (("Goal" :in-theory (enable compustate-frames-number))))

  (defret car-of-compustate-scopes-numbers
    (implies (> (compustate-frames-number compst) 0)
             (equal (car ns)
                    (len (frame->scopes (car (compustate->frames compst))))))
    :hints (("Goal" :in-theory (enable compustate-frames-number))))
  (in-theory (disable car-of-compustate-scopes-numbers))

  (defrule compustate-scopes-numbers-of-push-frame
    (equal (compustate-scopes-numbers (push-frame frame compst))
           (cons (len (frame->scopes frame))
                 (compustate-scopes-numbers compst)))
    :enable (push-frame compustate-scopes-numbers-aux))

  (defrule compustate-scopes-numbers-of-pop-frame
    (equal (compustate-scopes-numbers (pop-frame compst))
           (cdr (compustate-scopes-numbers compst)))
    :enable (pop-frame compustate-scopes-numbers-aux)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compustate-top-frame-scopes-number ((compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (n posp
              :hyp (> (compustate-frames-number compst) 0)
              :rule-classes :type-prescription)
  :short "Number of scopes in the top frame of
          a computation state with a non-empty call stack."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use this as an enabled abbreviation."))
  (car (compustate-scopes-numbers compst))
  :enabled t
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define enter-scope ((compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (new-compst compustatep)
  :short "Enter a scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "We push an empty scope onto the scope stack of the top frame."))
  (b* ((frame (top-frame compst))
       (scopes (frame->scopes frame))
       (new-scopes (cons nil scopes))
       (new-frame (change-frame frame :scopes new-scopes))
       (new-compst (push-frame new-frame (pop-frame compst))))
    new-compst)
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-enter-scope
    (equal (compustate-frames-number new-compst)
           (compustate-frames-number compst))
    :hyp (> (compustate-frames-number compst) 0))

  (defret compustate-scopes-numbers-of-enter-scope
    (equal (compustate-scopes-numbers new-compst)
           (cons (1+ (car (compustate-scopes-numbers compst)))
                 (cdr (compustate-scopes-numbers compst))))
    :hyp (> (compustate-frames-number compst) 0)
    :hints (("Goal" :in-theory (enable top-frame
                                       car-of-compustate-scopes-numbers)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define exit-scope ((compst compustatep))
  :guard (and (> (compustate-frames-number compst) 0)
              (> (compustate-top-frame-scopes-number compst) 1))
  :returns (new-compst compustatep)
  :short "Exit a scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pop the scope stack of the top frame."))
  (b* ((frame (top-frame compst))
       (scopes (frame->scopes frame))
       (new-scopes (cdr scopes))
       (new-frame (change-frame frame :scopes new-scopes))
       (new-compst (push-frame new-frame (pop-frame compst))))
    new-compst)
  :guard-hints (("Goal" :in-theory (enable car-of-compustate-scopes-numbers
                                           top-frame)))
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-exit-scope
    (equal (compustate-frames-number (exit-scope compst))
           (compustate-frames-number compst))
    :hyp (> (compustate-frames-number compst) 0))

  (defret compustate-scopes-numbers-of-exit-scope
    (equal (compustate-scopes-numbers new-compst)
           (cons (1- (car (compustate-scopes-numbers compst)))
                 (cdr (compustate-scopes-numbers compst))))
    :hyp (and (> (compustate-frames-number compst) 0)
              (> (compustate-top-frame-scopes-number compst) 1))
    :hints (("Goal" :in-theory (enable car-of-compustate-scopes-numbers
                                       top-frame)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define create-var ((var identp) (val valuep) (compst compustatep))
  :returns (result compustate-resultp)
  :short "Create a variable in a computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are no frames, we add the variable to the static storage;
     otherwise, we add the variable to the top scope of the top frame.
     The variable comes with a value.
     If there is already a variable with the same name
     (in the static storage or in the top scope of the top frame),
     we return an error: C disallows variable redefinition.
     However, there may well be a variable with the same in a different scope:
     in this case, the new variable hides the other one."))
  (b* ((var (ident-fix var))
       ((when (equal (compustate-frames-number compst) 0))
        (b* ((static (compustate->static compst))
             (pair (omap::in var static))
             ((when (consp pair)) (error (list :var-redefinition var)))
             (new-static (omap::update var (value-fix val) static))
             (new-compst (change-compustate compst :static new-static)))
          new-compst))
       (frame (top-frame compst))
       (scopes (frame->scopes frame))
       (scope (car scopes))
       (pair (omap::in var scope))
       ((when (consp pair)) (error (list :var-redefinition var)))
       (new-scope (omap::update var (value-fix val) scope))
       (new-scopes (cons new-scope (cdr scopes)))
       (new-frame (change-frame frame :scopes new-scopes))
       (new-compst (push-frame new-frame (pop-frame compst))))
    new-compst)
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-create-var
    (implies (compustatep result)
             (equal (compustate-frames-number result)
                    (compustate-frames-number compst))))

  (defret compustate-scopes-numbers-of-create-var
    (implies (compustatep result)
             (equal (compustate-scopes-numbers result)
                    (compustate-scopes-numbers compst)))
    :hyp (> (compustate-frames-number compst) 0)
    :hints (("Goal" :in-theory (enable top-frame
                                       push-frame
                                       pop-frame
                                       compustate-scopes-numbers
                                       compustate-scopes-numbers-aux
                                       compustate-frames-number)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-auto-var ((var identp) (compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (val value-optionp)
  :short "Read a variable in automatic storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, read the variable in the scopes in the top frame.
     We search the scopes from innermost (leftmost) to outermost (rightmost),
     according to the scoping rules for variables,
     where variables in inner scopes may hide variables in outer scopes.")
   (xdoc::p
    "If the variable is not found, we return @('nil'), not an error.
     The reason is that this ACL2 function is used
     as a subroutine of @(tsee read-var),
     where if a variable is not found in automatic storage,
     it is looked up in static storage.
     Thus, not finding a variable in automatic storage,
     in this ACL2 function, is not necessarily an error.")
   (xdoc::p
    "We do not look at other frames,
     because the variables in other frames are not in scope
     when running in the top frame."))
  (read-auto-var-aux var (frame->scopes (top-frame compst)))
  :hooks (:fix)

  :prepwork
  ((define read-auto-var-aux ((var identp) (scopes scope-listp))
     :returns (val value-optionp)
     :parents nil
     (b* (((when (endp scopes)) nil)
          (scope (car scopes))
          (pair (omap::in (ident-fix var) (scope-fix scope)))
          ((when (not pair)) (read-auto-var-aux var (cdr scopes))))
       (cdr pair))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-static-var ((var identp) (compst compustatep))
  :returns (val value-resultp)
  :short "Read a variable in static storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the variable is not found, we return an error."))
  (b* ((pair (omap::in (ident-fix var) (compustate->static compst)))
       ((when (not pair)) (error (list :var-not-found (ident-fix var)))))
    (cdr pair))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-var ((var identp) (compst compustatep))
  :returns (val value-resultp)
  :short "Read a variable in a computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we ignore static storage.
     We will extend this function to deal with static storage soon.
     If there are no frames, or the variable is not found in automatic storage,
     we return an error."))
  (if (> (compustate-frames-number compst) 0)
      (b* ((val (read-auto-var var compst)))
        (or val
            (error (list :var-not-found (ident-fix var)))))
    (error (list :read-var-empty-frame-stack (ident-fix var))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-auto-var ((var identp) (val valuep) (compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (new-compst compustate-option-resultp)
  :short "Write a variable in automatic storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is, write the variable in the scopes of the top frame.
     The scopes are searched in the same way as @(tsee read-auto-var).
     The variable must exist in order to write to it, i.e. it is not created;
     variables are created only via @(tsee create-var).
     The new value must have the same type as the old value;
     note that, in our restricted dynamic semantics of C,
     variables always have values, they are never uninitialized.")
   (xdoc::p
    "If the variable is not found, we return @('nil'), not an error.
     The reason is that this ACL2 function is used
     as a subroutine of @(tsee write-var),
     where if a variable is not found in automatic storage,
     it is looked up in static storage.
     Thus, not finding a variable in automatic storage,
     in this ACL2 function, is not necessarily an error.
     If the auxiliary recursive function returns @('nil'),
     it means that the variable was not found:
     since a frame always has at least one scope (see @(tsee frame)),
     this cannot be confused with a result where
     the variable was just not found in the scopes.")
   (xdoc::p
    "We do not look at other frames,
     because the variables in other frames are not in scope
     when running in the top frame."))
  (b* ((frame (top-frame compst))
       (new-scopes (write-auto-var-aux var val (frame->scopes frame)))
       ((when (errorp new-scopes)) new-scopes)
       ((when (endp new-scopes)) nil)
       (new-frame (change-frame frame :scopes new-scopes)))
    (push-frame new-frame (pop-frame compst)))
  :hooks (:fix)

  :prepwork
  ((define write-auto-var-aux ((var identp) (val valuep) (scopes scope-listp))
     :returns (new-scopes
               scope-list-resultp
               :hints (("Goal"
                        :in-theory
                        (enable
                         scope-listp-when-scope-list-resultp-and-not-errorp))))
     :parents nil
     (b* (((when (endp scopes)) nil)
          (scope (scope-fix (car scopes)))
          (pair (omap::in (ident-fix var) scope))
          ((when (consp pair))
           (if (equal (type-of-value (cdr pair))
                      (type-of-value val))
               (cons (omap::update (ident-fix var) (value-fix val) scope)
                     (scope-list-fix (cdr scopes)))
             (error (list :write-auto-var-mistype (ident-fix var)
                          :required (type-of-value (cdr pair))
                          :supplied (type-of-value val)))))
          (new-cdr-scopes (write-auto-var-aux var val (cdr scopes)))
          ((when (errorp new-cdr-scopes)) new-cdr-scopes)
          ((when (endp new-cdr-scopes)) nil))
       (cons scope new-cdr-scopes))
     :hooks (:fix)

     ///

     (defret consp-of-write-auto-var-aux
       (implies (and (scope-listp new-scopes)
                     (consp new-scopes))
                (equal (consp new-scopes)
                       (consp scopes)))
       :hints (("Goal" :in-theory (enable error))))

     (defret len-of-write-auto-var-aux
       (implies (and (scope-listp new-scopes)
                     (consp new-scopes))
                (equal (len new-scopes)
                       (len scopes)))
       :hints (("Goal" :in-theory (enable error errorp))))))

  ///

  (defret compustate-frames-number-of-write-auto-var
    (implies (and (> (compustate-frames-number compst) 0)
                  (compustatep new-compst))
             (equal (compustate-frames-number new-compst)
                    (compustate-frames-number compst)))
    :hints (("Goal" :in-theory (enable not-errorp-when-compustatep))))

  (defret compustate-scopes-numbers-of-write-auto-var
    (implies (and (> (compustate-frames-number compst) 0)
                  (compustatep new-compst))
             (equal (compustate-scopes-numbers new-compst)
                    (compustate-scopes-numbers compst)))
    :hints (("Goal" :in-theory (enable top-frame
                                       push-frame
                                       pop-frame
                                       compustate-frames-number
                                       compustate-scopes-numbers
                                       compustate-scopes-numbers-aux
                                       errorp-when-scope-list-resultp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-static-var ((var identp) (val valuep) (compst compustatep))
  :returns (new-compst compustate-resultp)
  :short "Write a varible in static storage."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the variable is not found, we return an error.
     If the variable is found but its current value
     has a different type from the one of the new value,
     we return an error.
     Otherwise, we overwrite the old value with the new one."))
  (b* ((static (compustate->static compst))
       (pair (omap::in (ident-fix var) static))
       ((when (not pair)) (error (list :var-not-found (ident-fix var))))
       ((unless (equal (type-of-value (cdr pair))
                       (type-of-value val)))
        (error (list :write-static-var-mistype (ident-fix var)
                     :required (type-of-value (cdr pair))
                     :supplied (type-of-value val))))
       (new-static (omap::update (ident-fix var) (value-fix val) static))
       (new-compst (change-compustate compst :static new-static)))
    new-compst)
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-write-static-var
    (implies (compustatep new-compst)
             (equal (compustate-frames-number new-compst)
                    (compustate-frames-number compst)))
    :hints (("Goal" :in-theory (enable compustate-frames-number))))

  (defret compustate-scopes-numbers-of-write-static-var
    (implies (compustatep new-compst)
             (equal (compustate-scopes-numbers new-compst)
                    (compustate-scopes-numbers compst)))
    :hints (("Goal" :in-theory (enable compustate-scopes-numbers)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-var ((var identp) (val valuep) (compst compustatep))
  :returns (new-compst
            compustate-resultp
            :hints
            (("Goal"
              :in-theory
              (enable
               compustate-resultp-when-compustate-option-result-and-not-nil))))
  :short "Write a variable in the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we ignore static storage.
     We will extend this function to deal with static storage soon.
     If there are no frames,
     or the variable is not found in automatic storage,
     or the variable is found but has a value of inconsistent type,
     we return an error."))
  (if (> (compustate-frames-number compst) 0)
      (b* ((new-compst (write-auto-var var val compst))
           ((when (errorp new-compst)) new-compst))
        (or new-compst
            (error (list :var-not-found (ident-fix var)))))
    (error (list :write-var-empty-frame-stack (ident-fix var))))
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-write-var
    (implies (compustatep new-compst)
             (equal (compustate-frames-number new-compst)
                    (compustate-frames-number compst))))

  (defret compustate-scopes-numbers-of-write-var
    (implies (compustatep new-compst)
             (equal (compustate-scopes-numbers new-compst)
                    (compustate-scopes-numbers compst)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-object ((objdes objdesignp) (compst compustatep))
  :returns (obj value-resultp)
  :short "Read an object in the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the object designator is a variable,
     we look it up in static storage.
     If the object designator is an address,
     we look up the object in the heap.
     Otherwise, first we recursively read the super-object,
     then we access the sub-object,
     ensuring that the super-object is of the appropriate kind
     for the object designator."))
  (objdesign-case
   objdes
   :variable (read-static-var objdes.get compst)
   :address
   (b* ((addr objdes.get)
        (heap (compustate->heap compst))
        (addr+obj (omap::in addr heap))
        ((unless (consp addr+obj))
         (error (list :address-not-found addr)))
        (obj (cdr addr+obj)))
     obj)
   :element
   (b* ((obj (read-object objdes.super compst))
        ((when (errorp obj)) obj)
        ((unless (value-case obj :array))
         (error (list :objdesign-mismatch (objdesign-fix objdes)
                      :required :array
                      :supplied obj))))
     (value-array-read objdes.index obj))
   :member
   (b* ((obj (read-object objdes.super compst))
        ((when (errorp obj)) obj)
        ((unless (value-case obj :struct))
         (error (list :objdesign-mismatch (objdesign-fix objdes)
                      :required :struct
                      :supplied obj))))
     (value-struct-read objdes.name obj)))
  :measure (objdesign-count objdes)
  :verify-guards :after-returns
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-object ((objdes objdesignp) (val valuep) (compst compustatep))
  :returns (new-compst compustate-resultp)
  :short "Write an object in the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the object designator is a variable,
     we write it in static storage.
     If the object designator is an address,
     we check whether the heap has an object at the address,
     of the same type as the new object
     (note that, for arrays, the type includes the number of elements).
     If this checks succeed, we overwrite the object in the heap.")
   (xdoc::p
    "Otherwise,
     we retrieve the super-object,
     and we update its element or member,
     provided that the super-object is of the right kind.
     Then we recursively write the updated super-object."))
  (objdesign-case
   objdes
   :variable (write-static-var objdes.get val compst)
   :address
   (b* ((addr objdes.get)
        (heap (compustate->heap compst))
        (addr+obj (omap::in addr heap))
        ((unless (consp addr+obj))
         (error (list :address-not-found addr)))
        (obj (cdr addr+obj))
        ((unless (equal (type-of-value val)
                        (type-of-value obj)))
         (error (list :write-object-mistype
                      :old (type-of-value obj)
                      :new (type-of-value val))))
        (new-heap (omap::update addr (value-fix val) heap))
        (new-compst (change-compustate compst :heap new-heap)))
     new-compst)
   :element
   (b* ((super (read-object objdes.super compst))
        ((when (errorp super)) super)
        ((unless (value-case super :array))
         (error (list :objdesign-mismatch (objdesign-fix objdes)
                      :required :array
                      :supplied super)))
        (new-super (value-array-write objdes.index val super))
        ((when (errorp new-super)) new-super))
     (write-object objdes.super new-super compst))
   :member
   (b* ((super (read-object objdes.super compst))
        ((when (errorp super)) super)
        ((unless (value-case super :struct))
         (error (list :objdesign-mismatch (objdesign-fix objdes)
                      :required :struct
                      :supplied super)))
        (new-super (value-struct-write objdes.name val super))
        ((when (errorp new-super)) new-super))
     (write-object objdes.super new-super compst)))
  :measure (objdesign-count objdes)
  :hooks (:fix)
  ///

  (defret compustate-frames-number-of-write-object
    (implies (compustatep new-compst)
             (equal (compustate-frames-number new-compst)
                    (compustate-frames-number compst)))
    :hints (("Goal"
             :in-theory (e/d (compustate-frames-number)
                             (compustate-frames-number-of-write-static-var)))
            '(:use (:instance compustate-frames-number-of-write-static-var
                              (var (objdesign-variable->get objdes))))))

  (defret compustate-scopes-numbers-of-write-object
    (implies (compustatep new-compst)
             (equal (compustate-scopes-numbers new-compst)
                    (compustate-scopes-numbers compst)))
    :hints (("Goal"
             :in-theory (e/d (compustate-scopes-numbers)
                             (compustate-scopes-numbers-of-write-static-var)))
            '(:use (:instance compustate-scopes-numbers-of-write-static-var
                              (var (objdesign-variable->get objdes)))))))
