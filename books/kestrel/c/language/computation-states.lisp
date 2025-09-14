; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2025 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "array-operations")
(include-book "structure-operations")

(include-book "kestrel/fty/defomap" :dir :system)

(local (include-book "arithmetic/top" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruledl update-nth-of-rev
  (implies (and (< (nfix i) (len x)))
           (equal (update-nth i a (rev x))
                  (rev (update-nth (- (1- (len x)) (nfix i)) a x))))
  :enable (update-nth len rev fix nfix))

(defruledl nth-of-minus1-and-cdr
  (implies (and (natp i)
                (< 0 i)
                (< i (len x)))
           (equal (nth (1- i) (cdr x))
                  (nth i x)))
  :enable nth)

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
  :pred scopep

  ///

  (defruled cdr-of-assoc-when-scopep
    (implies (scopep scope)
             (iff (cdr (omap::assoc id scope))
                  (omap::assoc id scope)))
    :induct t
    :enable omap::assoc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist scope-list
  :short "Fixtype of lists of variable scopes."
  :elt-type scope
  :true-listp t
  :elementp-of-nil t
  :pred scope-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult scope "scopes")

;;;;;;;;;;;;;;;;;;;;

(defruled not-errorp-when-scopep
  (implies (scopep x)
           (not (errorp x)))
  :enable (errorp scopep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult scope-list "lists of scopes")

;;;;;;;;;;;;;;;;;;;;

(defruled errorp-when-scope-list-resultp
  (implies (scope-list-resultp x)
           (equal (errorp x)
                  (not (scope-listp x))))
  :enable (errorp scope-list-resultp))

;;;;;;;;;;;;;;;;;;;;

(defruled not-errorp-when-scope-listp
  (implies (scope-listp x)
           (not (errorp x)))
  :enable errorp)

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
     (i.e. scopes are added via @(tsee cons) and removed via @(tsee cdr)).
     There is always at least one scope,
     i.e. the one for the function body's block.")
   (xdoc::p
    "As defined later, the call stack is also represented as
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
     [C17] does not actually use the term `heap';
     in fact, [C17] does not appear to use a specific term for this memory area.
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
     "A scope for static storage [C17:6.2.4].
      Our current C subset only has one translation unit
      (i.e. a single @('.c') file, with an optional @('.h') file;
      together they form a single translation unit, see @(tsee preprocess)),
      so the static storage corresponds to
      the variables declared at the top-level in the translation unit,
      which form a scope.")
    (xdoc::li
     "A stack of frames.
      The variables there are in automatic storage [C17:6.2.4].")
    (xdoc::li
     "A heap.
      This is allocated storage [C17:6.2.4]."))
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
  :enable (compustatep error strip-cars))

;;;;;;;;;;;;;;;;;;;;

(defruled not-errorp-when-compustatep
  (implies (compustatep x)
           (not (errorp x)))
  :enable (errorp compustatep strip-cars))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult compustate-option "optional computation states"
  :enable (compustatep compustate-optionp errorp alistp))

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
    :hints (("Goal" :in-theory (enable compustate-frames-number len))))

  (defret compustate->static-of-push-frame
    (equal (compustate->static new-compst)
           (compustate->static compst)))

  (defret compustate->heap-of-push-frame
    (equal (compustate->heap new-compst)
           (compustate->heap compst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
    :hints (("Goal" :in-theory (enable compustate-frames-number len fix))))

  (defret compustate->static-of-pop-frame
    (equal (compustate->static new-compst)
           (compustate->static compst)))

  (defret compustate->heap-of-pop-frame
    (equal (compustate->heap new-compst)
           (compustate->heap compst))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define top-frame ((compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (frame framep)
  :short "Top frame of a computation state's call stack."
  (frame-fix (car (compustate->frames compst)))
  :guard-hints (("Goal" :in-theory (enable compustate-frames-number)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection push/pop/top-frame-theorems
  :short "Theorems relating
          @(tsee push-frame), @(tsee pop-frame), and @(tsee top-frame)."

  (defrule top-frame-of-push-frame
    (equal (top-frame (push-frame frame compst))
           (frame-fix frame))
    :enable (top-frame push-frame))

  (defrule pop-frame-of-push-frame
    (equal (pop-frame (push-frame frame compst))
           (compustate-fix compst))
    :enable (pop-frame push-frame))

  (defrule push-frame-of-top-frame-and-pop-frame
    (implies (> (compustate-frames-number compst) 0)
             (equal (push-frame (top-frame compst)
                                (pop-frame compst))
                    (compustate-fix compst)))
    :cases ((consp (compustate->frames compst)))
    :enable (push-frame
             top-frame
             pop-frame
             compustate-frames-number)))

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
     :returns (ns pos-listp
                  :hints (("Goal" :in-theory (enable posp pos-listp))))
     (cond ((endp frames) nil)
           (t (cons (len (frame->scopes (car frames)))
                    (compustate-scopes-numbers-aux (cdr frames)))))
     :hooks (:fix)

     ///

     (defret len-of-compustate-scopes-numbers-aux
       (equal (len ns)
              (len frames))
       :hints (("Goal" :in-theory (enable len))))

     (defret consp-of-compustate-scopes-numbers-aux
       (equal (consp ns)
              (consp frames)))

     (defret car-of-compustate-scopes-numbers-aux
       (implies (> (len frames) 0)
                (equal (car ns)
                       (len (frame->scopes (car frames)))))
       :hints (("Goal" :in-theory (enable len))))

     (defrule compustate-scopes-numbers-aux-of-append
       (equal (compustate-scopes-numbers-aux (append frames1 frames2))
              (append (compustate-scopes-numbers-aux frames1)
                      (compustate-scopes-numbers-aux frames2))))

     (defrule compustate-scopes-numbers-aux-of-rev
       (equal (compustate-scopes-numbers-aux (rev frames))
              (rev (compustate-scopes-numbers-aux frames))))

     (defrule compustate-scopes-numbers-aux-of-update-nth
       (implies (< (nfix i) (len frames))
                (equal (compustate-scopes-numbers-aux
                        (update-nth i frame frames))
                       (update-nth i
                                   (len (frame->scopes frame))
                                   (compustate-scopes-numbers-aux frames))))
       :enable (update-nth len))

     (defrule update-nth-of-nth-and-compustate-scopes-numbers-aux
       (implies (< (nfix i) (len (compustate->frames compst)))
                (equal
                 (update-nth i
                             (len (frame->scopes
                                   (nth i (compustate->frames compst))))
                             (compustate-scopes-numbers-aux
                              (compustate->frames compst)))
                 (compustate-scopes-numbers-aux (compustate->frames compst))))
       :use (:instance compustate-scopes-numbers-aux-of-update-nth
                       (frame (nth i (compustate->frames compst)))
                       (frames (compustate->frames compst)))
       :disable compustate-scopes-numbers-aux-of-update-nth)))

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
    :hints (("Goal" :in-theory (enable compustate-frames-number posp))))

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
    :hyp (> (compustate-frames-number compst) 0)
    :hints (("Goal" :in-theory (enable fix))))

  (defret compustate-scopes-numbers-of-enter-scope
    (equal (compustate-scopes-numbers new-compst)
           (cons (1+ (car (compustate-scopes-numbers compst)))
                 (cdr (compustate-scopes-numbers compst))))
    :hyp (> (compustate-frames-number compst) 0)
    :hints (("Goal" :in-theory (enable top-frame
                                       car-of-compustate-scopes-numbers
                                       len))))

  (defret compustate->static-of-enter-scope
    (equal (compustate->static new-compst)
           (compustate->static compst)))

  (defret compustate->heap-of-enter-scope
    (equal (compustate->heap new-compst)
           (compustate->heap compst)))

  (defruled pop-frame-of-enter-scope
    (equal (pop-frame (enter-scope compst))
           (pop-frame compst))
    :enable (pop-frame
             push-frame)))

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
                                           top-frame
                                           len)))
  :hooks (:fix)

  ///

  (defret compustate-frames-number-of-exit-scope
    (equal (compustate-frames-number (exit-scope compst))
           (compustate-frames-number compst))
    :hyp (> (compustate-frames-number compst) 0)
    :hints (("Goal" :in-theory (enable fix))))

  (defret compustate-scopes-numbers-of-exit-scope
    (equal (compustate-scopes-numbers new-compst)
           (cons (1- (car (compustate-scopes-numbers compst)))
                 (cdr (compustate-scopes-numbers compst))))
    :hyp (and (> (compustate-frames-number compst) 0)
              (> (compustate-top-frame-scopes-number compst) 1))
    :hints (("Goal" :in-theory (enable car-of-compustate-scopes-numbers
                                       top-frame
                                       fix
                                       len))))

  (defret compustate->static-of-exit-scope
    (equal (compustate->static new-compst)
           (compustate->static compst)))

  (defret compustate->heap-of-exit-scope
    (equal (compustate->heap new-compst)
           (compustate->heap compst)))

  (defruled pop-frame-of-exit-scope
    (equal (pop-frame (exit-scope compst))
           (pop-frame compst))
    :enable (pop-frame
             push-frame)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection entr/exit-scope-theorems
  :short "Theorems relating @(tsee enter-scope) and @(tsee exit-scope)."

  (defruled exit-scope-of-enter-scope
    (implies (> (compustate-frames-number compst) 0)
             (equal (exit-scope (enter-scope compst))
                    (compustate-fix compst)))
    :enable (exit-scope
             enter-scope
             push-frame-of-top-frame-and-pop-frame)))

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
     in this case, the new variable hides the other one.")
   (xdoc::p
    "Prior to storing the value, we remove its flexible array member, if any.
     See @(tsee remove-flexible-array-member)."))
  (b* ((var (ident-fix var))
       ((when (equal (compustate-frames-number compst) 0))
        (b* ((static (compustate->static compst))
             (pair (omap::assoc var static))
             ((when (consp pair)) (error (list :var-redefinition var)))
             (new-static (omap::update var
                                       (remove-flexible-array-member val)
                                       static))
             (new-compst (change-compustate compst :static new-static)))
          new-compst))
       (frame (top-frame compst))
       (scopes (frame->scopes frame))
       (scope (car scopes))
       (pair (omap::assoc var scope))
       ((when (consp pair)) (error (list :var-redefinition var)))
       (new-scope (omap::update var
                                (remove-flexible-array-member val)
                                scope))
       (new-scopes (cons new-scope (cdr scopes)))
       (new-frame (change-frame frame :scopes new-scopes))
       (new-compst (push-frame new-frame (pop-frame compst))))
    new-compst)
  :hooks (:fix)

  ///

  (defret compustate-frames-number-of-create-var
    (implies (compustatep result)
             (equal (compustate-frames-number result)
                    (compustate-frames-number compst)))
    :hints (("Goal" :in-theory (enable fix))))

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
                                       compustate-frames-number
                                       len))))

  (defruled assoc-of-compustate-static-of-create-var
    (b* ((compst1 (create-var var val compst)))
      (implies (and (not (errorp compst1))
                    (identp var))
               (equal (omap::assoc var1 (compustate->static compst1))
                      (if (and (equal var1 var)
                               (equal (compustate-frames-number compst) 0))
                          (cons var (remove-flexible-array-member val))
                        (omap::assoc var1 (compustate->static compst))))))
    :enable (push-frame
             pop-frame))

  (defrule compustate->static-of-create-var-when-frames
    (b* ((compst1 (create-var var val compst)))
      (implies (and (not (errorp compst1))
                    (> (compustate-frames-number compst) 0))
               (equal (compustate->static compst1)
                      (compustate->static compst))))
    :enable (push-frame
             pop-frame))

  (defruled exit-scope-of-create-var
    (implies (and (> (compustate-frames-number compst) 0)
                  (> (compustate-top-frame-scopes-number compst) 1)
                  (not (errorp (create-var var val compst))))
             (equal (exit-scope (create-var var val compst))
                    (exit-scope compst)))
    :enable (exit-scope
             push-frame
             pop-frame
             top-frame)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define objdesign-of-var ((var identp) (compst compustatep))
  :returns (objdes? objdesign-optionp)
  :short "Object designator of a variable."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given the name of a variable in scope,
     there is an object designator for the variable,
     which can be found by looking up the variable in the computation states,
     according to the scoping rules of C.")
   (xdoc::p
    "If there are frames in the computation state,
     we look in the scopes of the top frame,
     from innermost (leftmost) scope to outermost (rightmost) scope;
     note that we pass the index of the top frame to the recursive function,
     so it can be put into the object designator.
     We do not look at other frames,
     because the variables in other frames are not in scope
     when running in the top frame.
     If the variable is not found in the top frame,
     we look for it in static storage.")
   (xdoc::p
    "If there are no frames in the computation state,
     we look in static storage.")
   (xdoc::p
    "If the variable is not found anywhere, we return @('nil'),
     which means that the variable is not in scope."))
  (b* ((objdes?
        (and (> (compustate-frames-number compst) 0)
             (objdesign-of-var-aux var
                                   (1- (compustate-frames-number compst))
                                   (frame->scopes (top-frame compst)))))
       ((when objdes?) objdes?)
       (var+val? (omap::assoc (ident-fix var) (compustate->static compst))))
    (and (consp var+val?)
         (objdesign-static var)))
  :guard-hints (("Goal" :in-theory (enable natp compustate-frames-number)))
  :hooks (:fix)

  :prepwork
  ((define objdesign-of-var-aux ((var identp) (frame natp) (scopes scope-listp))
     :returns (objdes? objdesign-optionp)
     :parents nil
     (b* (((when (endp scopes)) nil)
          (scope (car scopes))
          (var+val? (omap::assoc (ident-fix var) (scope-fix scope)))
          ((when (consp var+val?))
           (make-objdesign-auto :name var
                                :frame frame
                                :scope (1- (len scopes)))))
       (objdesign-of-var-aux var frame (cdr scopes)))
     :guard-hints (("Goal" :in-theory (enable natp len)))

     ///

     (fty::deffixequiv objdesign-of-var-aux
       :hints
       (("Goal"
         :expand (objdesign-of-var-aux var frame (scope-list-fix scopes)))))

     (defrule objdesign-kind-of-objdesign-of-var-aux
       (b* ((objdes (objdesign-of-var-aux var frame scopes)))
         (implies objdes
                  (equal (objdesign-kind objdes) :auto))))

     (defrule objdesign-auto->name-of-objdesign-of-var-aux
       (b* ((objdes (objdesign-of-var-aux var frame scopes)))
         (implies objdes
                  (equal (objdesign-auto->name objdes)
                         (ident-fix var))))
       :induct t)

     (defrule objdesign-auto->scope-of-objdesign-of-var-aux-upper-bound
       (b* ((objdes (objdesign-of-var-aux var frame scopes)))
         (implies objdes
                  (< (objdesign-auto->scope objdes) (len scopes))))
       :rule-classes :linear
       :induct t
       :enable (len nfix))

     (defruled objdesign-of-var-aux-lemma
       (b* ((objdes (objdesign-of-var-aux var frame scopes))
            (pair (omap::assoc (objdesign-auto->name objdes)
                               (scope-fix
                                (nth (- (1- (len scopes))
                                        (objdesign-auto->scope objdes))
                                     scopes)))))
         (implies objdes
                  (and (objdesign-case objdes :auto)
                       (equal (objdesign-auto->name objdes)
                              (ident-fix var))
                       (equal (objdesign-auto->frame objdes)
                              (nfix frame))
                       (< (objdesign-auto->scope objdes)
                          (len scopes))
                       (< (- (1- (len scopes))
                             (objdesign-auto->scope objdes))
                          (len scopes))
                       (consp pair)
                       (valuep (cdr pair)))))
       :induct t
       :enable (len
                fix
                nth-of-minus1-and-cdr))

     (defruled objdesign-of-var-aux-of-update-nth
       (implies (and (scope-listp scopes)
                     (< i (len scopes))
                     (identp var0)
                     (valuep val)
                     (omap::assoc var0 (nth i scopes)))
                (b* ((scope (omap::update var0 val (nth i scopes))))
                  (equal (objdesign-of-var-aux
                          var frame (update-nth i scope scopes))
                         (objdesign-of-var-aux var frame scopes))))
       :induct t
       :enable (update-nth
                nth
                len
                fix
                nfix
                max))

     (defruled objdesign-of-var-aux-of-cons-of-cdr
       (implies (and (scope-listp scopes)
                     (consp scopes)
                     (identp var)
                     (identp var1)
                     (valuep val))
                (b* ((scope (omap::update var val (car scopes))))
                  (equal (objdesign-of-var-aux
                          var1 frame (cons scope (cdr scopes)))
                         (if (equal var1 var)
                             (objdesign-auto var frame (1- (len scopes)))
                           (objdesign-of-var-aux var1 frame scopes)))))
       :enable len)))

  ///

  (defrule objdesign-kind-of-objdesign-of-var
    (b* ((objdes (objdesign-of-var var compst)))
      (implies objdes
               (member-equal (objdesign-kind objdes) '(:auto :static)))))

  (defruled objdesign-static->name-of-objdesign-of-var
    (b* ((objdes (objdesign-of-var var compst)))
      (implies (and objdes
                    (equal (objdesign-kind objdes) :static))
               (equal (objdesign-static->name objdes)
                      (ident-fix var)))))

  (defruled objdesign-auto->name-of-objdesign-of-var
    (b* ((objdes (objdesign-of-var var compst)))
      (implies (and objdes
                    (equal (objdesign-kind objdes) :auto))
               (equal (objdesign-auto->name objdes)
                      (ident-fix var))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-object ((objdes objdesignp) (compst compustatep))
  :returns (obj value-resultp)
  :short "Read an object in the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the object designator is a static variable,
     we look it up in static storage.
     If the object designator is an automatic variable,
     we index the frame stack,
     we index the scope stack,
     and we find the variable by name;
     note that, as explained in @(tsee objdesign),
     the indices start at the bottom, i.e. the end of the lists,
     so we reverse the lists before indexing them.
     If the object designator is for allocated storage,
     we look up the object in the heap by address.
     Otherwise, first we recursively read the super-object,
     then we access the sub-object (array element or structure member),
     ensuring that the super-object is of the appropriate kind
     for the object designator."))
  (objdesign-case
   objdes
   :static
   (b* ((var+val (omap::assoc objdes.name (compustate->static compst)))
        ((when (not var+val))
         (error (list :static-var-not-found objdes.name))))
     (cdr var+val))
   :auto
   (b* ((rev-frames (rev (compustate->frames compst)))
        ((unless (< objdes.frame (len rev-frames)))
         (error (list :frame-index-out-of-range objdes.frame)))
        (frame (nth objdes.frame rev-frames))
        (rev-scopes (rev (frame->scopes frame)))
        ((unless (< objdes.scope (len rev-scopes)))
         (error (list :scope-index-out-of-range objdes.scope)))
        (scope (nth objdes.scope rev-scopes))
        (var+val (omap::assoc objdes.name scope))
        ((unless (consp var+val))
         (error (list :name-not-found objdes.name)))
        (val (cdr var+val)))
     val)
   :alloc
   (b* ((addr objdes.get)
        (heap (compustate->heap compst))
        (addr+obj (omap::assoc addr heap))
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
  :hints (("Goal" :in-theory (enable o< o-p o-finp)))
  :verify-guards :after-returns
  :hooks (:fix)

  ///

  (defruled read-object-top-static/alloc-of-pop-frame
    (implies (and (member-equal (objdesign-kind (objdesign-top objdes))
                                '(:static :alloc))
                  (not (errorp (read-object objdes compst))))
             (equal (read-object objdes (pop-frame compst))
                    (read-object objdes compst)))
    :induct t
    :enable (objdesign-top
             read-object))

  (defruled read-object-top-auto-of-pop-frame
    (implies (and (equal (objdesign-kind (objdesign-top objdes)) :auto)
                  (not (errorp (read-object objdes compst)))
                  (not (equal (objdesign-auto->frame (objdesign-top objdes))
                              (1- (compustate-frames-number compst)))))
             (equal (read-object objdes (pop-frame compst))
                    (read-object objdes compst)))
    :induct t
    :enable (objdesign-top
             read-object
             pop-frame
             compustate-frames-number
             len
             nfix
             fix
             nth))

  (defruled read-object-of-pop-frame
    (implies (and (not (errorp (read-object objdes compst)))
                  (or (member-equal (objdesign-kind (objdesign-top objdes))
                                    '(:static :alloc))
                      (not (equal
                            (objdesign-auto->frame (objdesign-top objdes))
                            (1- (compustate-frames-number compst))))))
             (equal (read-object objdes (pop-frame compst))
                    (read-object objdes compst)))
    :enable (read-object-top-static/alloc-of-pop-frame
             read-object-top-auto-of-pop-frame)
    :use objdesign-kind-of-objdesign-top
    :disable objdesign-kind-of-objdesign-top)

  (defruled read-object-top-static/alloc-of-exit-scope
    (implies (and (member-equal (objdesign-kind (objdesign-top objdes))
                                '(:static :alloc))
                  (not (errorp (read-object objdes compst))))
             (equal (read-object objdes (exit-scope compst))
                    (read-object objdes compst)))
    :induct t
    :enable (objdesign-top
             read-object))

  (defruled read-object-top-auto-of-exit-scope
    (implies (and (equal (objdesign-kind (objdesign-top objdes)) :auto)
                  (not (errorp (read-object objdes compst)))
                  (or (not (equal
                            (objdesign-auto->frame (objdesign-top objdes))
                            (1- (compustate-frames-number compst))))
                      (not (equal
                            (objdesign-auto->scope (objdesign-top objdes))
                            (1- (compustate-top-frame-scopes-number compst))))))
             (equal (read-object objdes (exit-scope compst))
                    (read-object objdes compst)))
    :induct t
    :enable (objdesign-top
             read-object
             exit-scope
             push-frame
             pop-frame
             top-frame
             compustate-frames-number
             compustate-scopes-numbers
             len
             nfix
             fix
             nth))

  (defruled read-object-of-exit-scope
    (implies (and (not (errorp (read-object objdes compst)))
                  (or (member-equal (objdesign-kind (objdesign-top objdes))
                                    '(:static :alloc))
                      (not (equal
                            (objdesign-auto->frame (objdesign-top objdes))
                            (1- (compustate-frames-number compst))))
                      (not (equal
                            (objdesign-auto->scope (objdesign-top objdes))
                            (1- (compustate-top-frame-scopes-number compst))))))
             (equal (read-object objdes (exit-scope compst))
                    (read-object objdes compst)))
    :enable (read-object-top-static/alloc-of-exit-scope
             read-object-top-auto-of-exit-scope)
    :use objdesign-kind-of-objdesign-top
    :disable objdesign-kind-of-objdesign-top))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-object ((objdes objdesignp) (val valuep) (compst compustatep))
  :returns (new-compst compustate-resultp)
  :short "Write an object in the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the object designator is a static variable,
     we write it in static storage.
     If the object designator is an automatic variable,
     we index the frame stack,
     we index the scope stack,
     and we find the variable by name,
     writing the new value there,
     provided it has the same type as the existing value;
     note that, as explained in @(tsee objdesign),
     the indices start at the bottom, i.e. the end of the lists,
     so we reverse the lists before indexing them.
     If the object designator is for allocated storage,
     we check whether the heap has an object at the address,
     of the same type as the new object
     (note that, for arrays, the type includes the number of elements).
     If this checks succeed, we overwrite the object in the heap.")
   (xdoc::p
    "Otherwise,
     we retrieve the super-object,
     and we update its element or member,
     provided that the super-object is of the right kind.
     Then we recursively write the updated super-object.")
   (xdoc::p
    "If the object designator is an address,
     we store the value without removing the flexible array member
     (see @(tsee remove-flexible-array-member)).
     In all other cases, we remove it."))
  (objdesign-case
   objdes
   :static
   (b* ((static (compustate->static compst))
        (var+val (omap::assoc objdes.name static))
        ((when (not var+val))
         (error (list :static-var-not-found objdes.name)))
        ((unless (equal (type-of-value (cdr var+val))
                        (type-of-value val)))
         (error (list :static-var-mistype objdes.name
                      :required (type-of-value (cdr var+val))
                      :supplied (type-of-value val))))
        (new-static (omap::update objdes.name
                                  (remove-flexible-array-member val)
                                  static))
        (new-compst (change-compustate compst :static new-static)))
     new-compst)
   :auto
   (b* ((rev-frames (rev (compustate->frames compst)))
        ((unless (< objdes.frame (len rev-frames)))
         (error (list :frame-index-out-of-range objdes.frame)))
        (frame (nth objdes.frame rev-frames))
        (rev-scopes (rev (frame->scopes frame)))
        ((unless (< objdes.scope (len rev-scopes)))
         (error (list :scope-index-out-of-range objdes.scope)))
        (scope (nth objdes.scope rev-scopes))
        (var+val (omap::assoc objdes.name scope))
        ((unless (consp var+val))
         (error (list :name-not-found objdes.name)))
        (oldval (cdr var+val))
        (newval val)
        ((unless (equal (type-of-value newval)
                        (type-of-value oldval)))
         (error (list :write-auto-object-mistype objdes.name
                      :old (type-of-value oldval)
                      :new (type-of-value newval))))
        (new-scope (omap::update objdes.name
                                 (remove-flexible-array-member newval)
                                 scope))
        (rev-new-scopes (update-nth objdes.scope new-scope rev-scopes))
        (new-frame (change-frame frame :scopes (rev rev-new-scopes)))
        (rev-new-frames (update-nth objdes.frame new-frame rev-frames))
        (new-compst (change-compustate compst :frames (rev rev-new-frames))))
     new-compst)
   :alloc
   (b* ((addr objdes.get)
        (heap (compustate->heap compst))
        (addr+obj (omap::assoc addr heap))
        ((unless (consp addr+obj))
         (error (list :address-not-found addr)))
        (obj (cdr addr+obj))
        ((unless (equal (type-of-value val)
                        (type-of-value obj)))
         (error (list :write-alloc-object-mistype
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
  :hints (("Goal" :in-theory (enable o< o-p o-finp)))
  :hooks (:fix)

  ///

  (defret compustate-frames-number-of-write-object
    (implies (compustatep new-compst)
             (equal (compustate-frames-number new-compst)
                    (compustate-frames-number compst)))
    :hints (("Goal"
             :in-theory (enable compustate-frames-number nfix max))))

  (defret compustate-scopes-numbers-of-write-object
    (implies (compustatep new-compst)
             (equal (compustate-scopes-numbers new-compst)
                    (compustate-scopes-numbers compst)))
    :hints (("Goal"
             :in-theory (enable compustate-scopes-numbers
                                fix
                                max
                                acl2::nth-of-rev
                                update-nth-of-rev))))

  (defruled assoc-of-compustate-static-of-write-object
    (b* ((compst1 (write-object objdes val compst)))
      (implies (not (errorp compst1))
               (iff (omap::assoc var (compustate->static compst1))
                    (omap::assoc var (compustate->static compst)))))
    :induct t)

  (defruled not-errorp-of-read-object-when-not-write-error
    (implies (not (errorp (write-object objdes val compst)))
             (not (errorp (read-object objdes compst))))
    :induct t
    :enable (read-object
             not-errorp-of-value-struct-read-when-not-write-error
             not-errorp-of-value-array-read-when-not-write-error
             not-errorp-when-valuep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled valuep-of-read-object-of-objdesign-of-var
  :short "If @(tsee objdesign-of-var) succeeds,
          @(tsee read-object) returns a value (not an error)."
  (b* ((objdes (objdesign-of-var var compst)))
    (implies objdes
             (valuep (read-object objdes compst))))
  :enable (objdesign-of-var
           read-object
           fix
           compustate-frames-number
           top-frame)
  :use
  (:instance objdesign-of-var-aux-lemma
             (frame (+ -1 (len (compustate->frames compst))))
             (scopes (frame->scopes (car (compustate->frames compst))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled compustatep-of-write-object-of-objdesign-of-var
  :short "If @(tsee objdesign-of-var) succeeds,
          @(tsee write-object) returns a computation state (not an error)."
  (b* ((objdes (objdesign-of-var var compst)))
    (implies objdes
             (equal (compustatep (write-object objdes val compst))
                    (equal (type-of-value (read-object objdes compst))
                           (type-of-value val)))))
  :enable (objdesign-of-var
           write-object
           read-object
           top-frame
           compustate-frames-number)
  :use
  (valuep-of-read-object-of-objdesign-of-var
   (:instance objdesign-of-var-aux-lemma
              (frame (+ -1 (len (compustate->frames compst))))
              (scopes (frame->scopes (car (compustate->frames compst)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection objdesign-of-var-of-create-var
  :short "How @(tsee objdesign-of-var) changes under @(tsee create-var)."

  (defruled objdesign-of-var-aux-of-create-var
    (b* ((compst1 (create-var var val compst))
         (scopes (frame->scopes (top-frame compst)))
         (scopes1 (frame->scopes (top-frame compst1))))
      (implies (and (not (errorp compst1))
                    (identp var)
                    (identp var1))
               (equal (objdesign-of-var-aux var1 frame scopes1)
                      (if (and (equal var1 var)
                               (> (compustate-frames-number compst) 0))
                          (objdesign-auto var frame (1- (len scopes)))
                        (objdesign-of-var-aux var1 frame scopes)))))
    :enable (create-var
             nfix
             max
             objdesign-of-var-aux-of-cons-of-cdr
             push-frame
             pop-frame
             top-frame))

  (defruled objdesign-of-var-of-create-var
    (b* ((compst1 (create-var var val compst)))
      (implies (and (not (errorp compst1))
                    (identp var)
                    (identp var1))
               (equal (objdesign-of-var var1 compst1)
                      (if (equal var1 var)
                          (if (equal (compustate-frames-number compst) 0)
                              (objdesign-static var)
                            (objdesign-auto var
                                            (1- (compustate-frames-number
                                                 compst))
                                            (1- (len (frame->scopes
                                                      (top-frame compst))))))
                        (objdesign-of-var var1 compst)))))
    :enable (objdesign-of-var
             objdesign-of-var-aux-of-create-var
             assoc-of-compustate-static-of-create-var
             compustatep-when-compustate-resultp-and-not-errorp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection objdesign-of-var-of-write-object
  :short "How @(tsee objdesign-of-var) changes under @(tsee write-object)."

  (defruled objdesign-of-var-aux-of-write-object
    (b* ((compst1 (write-object objdes val compst))
         (scopes (frame->scopes (nth i (compustate->frames compst))))
         (scopes1 (frame->scopes (nth i (compustate->frames compst1)))))
      (implies (not (errorp compst1))
               (equal (objdesign-of-var-aux var frame scopes1)
                      (objdesign-of-var-aux var frame scopes))))
    :induct t
    :enable (write-object
             update-nth-of-rev
             nfix
             max
             objdesign-of-var-aux-of-update-nth))

  (defruled objdesign-of-var-of-write-object
    (b* ((compst1 (write-object objdes val compst)))
      (implies (not (errorp compst1))
               (equal (objdesign-of-var var compst1)
                      (objdesign-of-var var compst))))
    :enable (objdesign-of-var
             compustatep-when-compustate-resultp-and-not-errorp
             top-frame
             nth)
    :use ((:instance objdesign-of-var-aux-of-write-object
                     (i 0)
                     (frame (1- (compustate-frames-number compst))))
          (:instance assoc-of-compustate-static-of-write-object
                     (var (ident-fix var))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection read-object-of-create-var
  :short "How @(tsee read-object) changes under @(tsee create-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now this is limited to automatic and static storage.
     Handling other kinds of object designators is more complicated,
     due to the possibility of partial overlap of objects;
     we plan to tackle these eventually."))

  (defruled read-object-of-create-var-when-static
    (implies (and (equal (objdesign-kind objdes) :static)
                  (not (errorp (create-var var val compst)))
                  (identp var))
             (equal (read-object objdes (create-var var val compst))
                    (if (and (equal (compustate-frames-number compst) 0)
                             (equal (objdesign-static->name objdes) var))
                        (remove-flexible-array-member val)
                      (read-object objdes compst))))
    :enable (read-object
             assoc-of-compustate-static-of-create-var))

  (defruled read-object-of-create-var-when-auto
    (implies (and (equal (objdesign-kind objdes) :auto)
                  (not (errorp (create-var var val compst)))
                  (identp var))
             (equal (read-object objdes (create-var var val compst))
                    (if (and (> (compustate-frames-number compst) 0)
                             (equal (objdesign-auto->name objdes)
                                    var)
                             (equal (objdesign-auto->frame objdes)
                                    (1- (compustate-frames-number compst)))
                             (equal (objdesign-auto->scope objdes)
                                    (1- (len (frame->scopes
                                              (top-frame compst))))))
                        (remove-flexible-array-member val)
                      (read-object objdes compst))))
    :enable (read-object
             create-var
             top-frame
             push-frame
             pop-frame
             compustate-frames-number
             nfix
             fix
             len
             nth)
    :prep-lemmas
    ((defrule lemma
       (equal (nth i (cons a (cdr x)))
              (if (zp i)
                  a
                (nth i x)))
       :induct t
       :enable nth)))

  (defruled read-object-of-create-var-when-auto-or-static
    (implies (and (member-equal (objdesign-kind objdes) '(:auto :static))
                  (not (errorp (create-var var val compst)))
                  (identp var))
             (equal (read-object objdes (create-var var val compst))
                    (if (or (and (equal (objdesign-kind objdes) :static)
                                 (equal (compustate-frames-number compst) 0)
                                 (equal (objdesign-static->name objdes)
                                        var))
                            (and (equal (objdesign-kind objdes) :auto)
                                 (> (compustate-frames-number compst) 0)
                                 (equal (objdesign-auto->name objdes)
                                        var)
                                 (equal (objdesign-auto->frame objdes)
                                        (1- (compustate-frames-number compst)))
                                 (equal (objdesign-auto->scope objdes)
                                        (1- (len (frame->scopes
                                                  (top-frame compst)))))))
                        (remove-flexible-array-member val)
                      (read-object objdes compst))))
    :enable (read-object-of-create-var-when-static
             read-object-of-create-var-when-auto)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled read-object-of-write-object-when-auto-or-static
  :short "How @(tsee read-object) changes under @(tsee write-object)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is a read-over-write theorem.")
   (xdoc::p
    "For now this is limited to automatic and static storage.
     Handling other kinds of object designators is more complicated,
     due to the possibility of partial overlap of objects;
     we plan to tackle these eventually."))
  (implies (and (member-equal (objdesign-kind objdes) '(:auto :static))
                (member-equal (objdesign-kind objdes1) '(:auto :static))
                (not (errorp (write-object objdes val compst))))
           (equal (read-object objdes1 (write-object objdes val compst))
                  (if (equal (objdesign-fix objdes1)
                             (objdesign-fix objdes))
                      (remove-flexible-array-member val)
                    (read-object objdes1 compst))))
  :enable (read-object
           write-object
           fix
           nfix
           max
           equal-of-objdesign-auto-fix
           equal-of-objdesign-static-fix))
