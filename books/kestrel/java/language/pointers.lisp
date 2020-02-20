; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/std/util/deffixer" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ pointers
  :parents (semantics)
  :short "Java pointers [JLS:4.3.1]."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize pointers to Java objects as opaque entities.
     Recall that there is no pointer arithmetic in Java.")
   (xdoc::p
    "We model an infinite supply of pointers,
     i.e. the ability to obtain a new pointer
     that is distinct from any given finite collection of pointers.")
   (xdoc::p
    "This does not necessarily mean that we model infinite memory,
     i.e. that it is always possible to allocate new objects.
     Finite-memory constraints can be captured separately,
     but in the absence of those constraints,
     we want the ability to model infinite memory
     (which is adequate for many purposes,
     and what all or most existing formalizations do).")
   (xdoc::p
    "The opacity of our pointers does not mean that
     we cannot model the fact that some Java implementations
     return an object's pointer (address) as default hash code.
     We can (optionally) model these hash codes
     separately from the pointers formalized here:
     we use these pointers just to identify objects,
     consistently with [JLS].")
   (xdoc::p
    "We could use natural numbers to model Java pointers,
     but we prefer this more abstract model,
     because it avoids any ``accidental'' properties of pointers
     entailed by the natural numbers
     (e.g. one pointer being greater than another one)."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pointerp
  :parents (pointer pointers)
  :short "Recognizer for @(tsee pointer)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Since our pointers are opaque,
     we introduce their recognizer as a constrained function.")
   (xdoc::p
    "We constrain the recognizer to return a boolean.
     We also indirectly constrain it
     to hold over an infinite number of values,
     by simultaneously introducing a constrained function
     that, given any list as input, returns a pointer that is not in the list.
     The list may include non-ponters, which are ignored.")
   (xdoc::p
    "This new-pointer function implies the infinity of pointers because
     starting from the empty list @('nil')
     we can obtain an initial pointer @('p0'),
     then given the singleton list @('(p0)')
     we can obtain a different pointer @('p1'),
     then given the list @('(p0 p1)')
     we can obtain yet a different pointer @('p2'),
     and so on.
     In other words, we can ``count'' pointers.")
   (xdoc::p
    "The @('-raw') suffix in the name of the constrained new-pointer function
     is because the rest of our formalization
     actually uses a wrapper function (without the suffix),
     defined later with a @(tsee pointer-listp) guard,
     where the latter recognizer is not yet available here.")
   (xdoc::p
    "We use natural numbers as witnesses for pointers.
     The new-pointer function returns a natural number
     larger than all the ones that occur in the argument list.")
   (xdoc::@def "pointerp"))

  (encapsulate
    (((pointerp *) => *)
     ((new-pointer-raw *) => *))

    (local
     (defun pointerp (x)
       (natp x)))

    (defrule booleanp-of-pointerp
      (booleanp (pointerp x))
      :rule-classes (:rewrite :type-prescription))

    (local
     (defun new-pointer-raw (list)
       (cond ((atom list) 0)
             ((natp (car list)) (1+ (max (car list)
                                         (new-pointer-raw (cdr list)))))
             (t (new-pointer-raw (cdr list))))))

    (defrule pointerp-of-new-pointer-raw
      (pointerp (new-pointer-raw list)))

    (defrule new-pointer-raw-is-new
      (not (member-equal (new-pointer-raw list) list))
      :use (:instance lemma (elem (new-pointer-raw list)))
      :prep-lemmas
      ((defruled lemma
         (implies (and (natp elem)
                       (member-equal elem list))
                  (> (new-pointer-raw list) elem)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection pointer
  :short "Fixtype of Java pointers."
  :long
  (xdoc::topstring-p
   "See @(tsee pointerp) for details.")

  (std::deffixer pointer-fix
    :parents (pointer)
    :short "Fixer for @(tsee pointer)."
    :pred pointerp
    :body-fix (new-pointer-raw nil))

  (fty::deffixtype pointer
    :pred pointerp
    :fix pointer-fix
    :equiv pointer-equiv
    :define t
    :forward t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist pointer-list
  :short "Fixtype of true lists of Java pointers."
  :elt-type pointer
  :true-listp t
  :pred pointer-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define new-pointer ((pointers pointer-listp))
  :returns (pointer pointerp)
  :short "Obtain a new Java pointer."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(tsee pointerp) for details on how new pointers are obtained.
     This function is a guarded wrapper
     of the constrained function @('new-pointer-raw')
     introduced with @(tsee pointerp)."))
  (new-pointer-raw pointers)
  ///

  (defrule new-pointer-is-new
    (not (member-equal (new-pointer pointers) pointers))))
