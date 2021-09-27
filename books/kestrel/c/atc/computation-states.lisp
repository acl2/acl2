; C Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2021 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "arrays")
(include-book "values")

(include-book "kestrel/fty/defomap" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-computation-states
  :parents (atc-dynamic-semantics)
  :short "A model of C computation states for ATC."
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
     It represents the contents of the variables in a scope;
     currently this is always a block scope,
     because we do not model variables with file scope
     (i.e. variables declared at the top level)."))
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

(fty::defflatsum array
  :short "Fixtype of arrays."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only support arrays of the supported integer types."))
  (:uchar uchar-array)
  (:schar schar-array)
  (:ushort ushort-array)
  (:sshort sshort-array)
  (:uint uint-array)
  (:sint sint-array)
  (:ulong ulong-array)
  (:slong slong-array)
  (:ullong ullong-array)
  (:sllong sllong-array)
  :pred arrayp
  :prepwork ((defthm-disjoint *array-disjoint-rules*
               uchar-arrayp
               schar-arrayp
               ushort-arrayp
               sshort-arrayp
               uint-arrayp
               sint-arrayp
               ulong-arrayp
               slong-arrayp
               ullong-arrayp
               sllong-arrayp)))

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
    "For now we model the heap just as a finite map from addresses to arrays.
     That is, we only really consider arrays initially."))
  :key-type address
  :val-type array
  :pred heapp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defresult array "arrays"
  :enable (errorp
           arrayp
           uchar-arrayp
           schar-arrayp
           ushort-arrayp
           sshort-arrayp
           uint-arrayp
           sint-arrayp
           ulong-arrayp
           slong-arrayp
           ullong-arrayp
           sllong-arrayp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define deref ((ptr pointerp) (heap heapp))
  :returns (array array-resultp)
  :short "Dereference a pointer."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the pointer is null, we return an error:
     a null pointer cannot be dereferenced.
     Otherwise, we check whether the heap has an array at the pointer's address,
     which we return if it does (otherwise we return an error).
     We also ensure that the pointer's type matches the array."))
  (b* ((reftype (pointer->reftype ptr))
       ((unless (or (type-signed-integerp reftype)
                    (type-unsigned-integerp reftype)))
        (error (list :mistype-pointer-dereference
                     :required :array
                     :supplied reftype)))
       (address (pointer->address? ptr)))
    (if address
        (b* ((pair (omap::in address (heap-fix heap))))
          (if pair
              (cdr pair)
            (error (list :address-not-found address
                         :heap (heap-fix heap)))))
      (error :null-pointer-dereference)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod compustate
  :short "Fixtype of computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "A computation state consists of a stack of frames and a heap.
     More components may be added
     as our modeling coverage of C increases.")
   (xdoc::p
    "The stack grows leftward and shrinks rightward,
     i.e. push is @(tsee cons), pop is @(tsee cdr), and top is @(tsee car)."))
  ((frames frame-list)
   (heap heap))
  :pred compustatep)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compustate-frames-number ((compst compustatep))
  :returns (n natp)
  :short "Number of frames in the call stack of a computation state."
  (len (compustate->frames compst))
  :hooks (:fix))

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
  :guard (> (compustate-frames-number compst) 0)
  :returns (result compustate-resultp)
  :short "Create a variable in a computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add the variable to the top scope of the top frame;
     the variable comes with a value.
     If there is already a variable with the same name in the top scope,
     we return an error: C disallows variable redefinition.
     However, there may well be a variable with the same in a different scope:
     in this case, the new variable hides the other one."))
  (b* ((frame (top-frame compst))
       (scopes (frame->scopes frame))
       (scope (car scopes))
       (pair (omap::in (ident-fix var) scope))
       ((when (consp pair)) (error (list :var-redefinition (ident-fix var))))
       (new-scope (omap::update (ident-fix var) (value-fix val) scope))
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
    :hyp (> (compustate-frames-number compst) 0))

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

(define read-var ((var identp) (compst compustatep))
  :returns (result value-resultp)
  :short "Read a variable in a computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "If there are no frames, we return an error:
     the variable is not found.
     In the future, the computation state may be extended
     with file-scope (i.e. global) variables, which are not in frames;
     when that happens, variables will be looked up there,
     if they are not found in the top frame.")
   (xdoc::p
    "It should be the case that variables are looked up
     only when executing code in function bodies,
     and therefore when the frame stack is not empty.
     Thus, it could make sense for this ACL2 function
     to require the non-emptiness of the frame stack in the guard.
     However, that would require @(tsee exec-expr-pure) to have that guard,
     but in the future we may want to use @(tsee exec-expr-pure)
     to evaluate constant expressions used as initializers
     in external object definitions,
     which happens with an empty frame stack.
     So we avoid that guard here.")
   (xdoc::p
    "If the frame stack is not empty,
     we look in the scopes of the top frame from left to right,
     i.e. from innermost to outermost.
     If we find a variable with that name, we return its value.
     Otherwise we return an error.")
   (xdoc::p
    "We do not look at other frames,
     because the variables in other frames are not in scope
     for the C function in the top frame."))
  (if (> (compustate-frames-number compst) 0)
      (read-var-aux var (frame->scopes (top-frame compst)))
    (error (list :read-var-empty-frame-stack (ident-fix var))))
  :hooks (:fix)

  :prepwork
  ((define read-var-aux ((var identp) (scopes scope-listp))
     :returns (result value-resultp)
     (b* (((when (endp scopes))
           (error (list :read-var-not-found (ident-fix var))))
          (scope (car scopes))
          (pair (omap::in (ident-fix var) (scope-fix scope)))
          ((when (not pair)) (read-var-aux var (cdr scopes))))
       (cdr pair))
     :hooks (:fix))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-var ((var identp) (val valuep) (compst compustatep))
  :returns (new-compst compustate-resultp)
  :short "Write a variable in the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "We look for the variable in the same way as in @(tsee read-var),
     i.e. in the top frame's scopes from innermost to outermost.
     The variable must exist, it is not created;
     variables are created only via @(tsee create-var).
     The new value must have the same type as the old value;
     note that, in our restricted dynamic semantics of C,
     variables always have values, they are never uninitialized."))
  (b* (((unless (> (compustate-frames-number compst) 0))
        (error (list :write-var-empty-frame-stack (ident-fix var))))
       (frame (top-frame compst))
       (new-scopes (write-var-aux var val (frame->scopes frame)))
       ((when (errorp new-scopes)) new-scopes)
       (new-frame (change-frame frame :scopes new-scopes)))
    (push-frame new-frame (pop-frame compst)))
  :hooks (:fix)

  :prepwork
  ((define write-var-aux ((var identp) (val valuep) (scopes scope-listp))
     :returns (new-scopes
               scope-list-resultp
               :hints (("Goal"
                        :in-theory
                        (enable
                         scope-listp-when-scope-list-resultp-and-not-errorp))))
     (b* (((when (endp scopes))
           (error (list :write-var-not-found (ident-fix var))))
          (scope (scope-fix (car scopes)))
          (pair (omap::in (ident-fix var) scope))
          ((when (consp pair))
           (if (equal (type-of-value (cdr pair))
                      (type-of-value val))
               (cons (omap::update (ident-fix var) (value-fix val) scope)
                     (scope-list-fix (cdr scopes)))
             (error (list :write-var-mistype (ident-fix var)
                          :required (type-of-value (cdr pair))
                          :supplied (type-of-value val)))))
          (new-cdr-scopes (write-var-aux var val (cdr scopes)))
          ((when (errorp new-cdr-scopes)) new-cdr-scopes))
       (cons scope new-cdr-scopes))
     :hooks (:fix)

     ///

     (defret consp-of-write-var-aux
       (implies (scope-listp new-scopes)
                (equal (consp new-scopes)
                       (consp scopes)))
       :hints (("Goal" :in-theory (enable error))))

     (defret len-of-write-var-aux
       (implies (scope-listp new-scopes)
                (equal (len new-scopes)
                       (len scopes)))
       :hints (("Goal" :in-theory (enable error errorp))))))

  ///

  (defret compustate-frames-number-of-write-var
    (implies (compustatep new-compst)
             (equal (compustate-frames-number new-compst)
                    (compustate-frames-number compst)))
    :hints (("Goal" :in-theory (enable not-errorp-when-compustatep))))

  (defret compustate-scopes-numbers-of-write-var
    (implies (compustatep new-compst)
             (equal (compustate-scopes-numbers new-compst)
                    (compustate-scopes-numbers compst)))
    :hints (("Goal" :in-theory (enable top-frame
                                       push-frame
                                       pop-frame
                                       compustate-frames-number
                                       compustate-scopes-numbers
                                       compustate-scopes-numbers-aux
                                       errorp-when-scope-list-resultp)))))
