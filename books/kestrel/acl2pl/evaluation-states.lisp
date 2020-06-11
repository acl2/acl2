; ACL2 Programming Language Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2PL")

(include-book "translated-terms")

(include-book "kestrel/fty/defomap" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ evaluation-states
  :parents (acl2-programming-language)
  :short "Evaluation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation semantics of ACL2 can be described
     in terms of a succession of evaluation states.
     Here we formalize these evaluation states."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defomap binding
  :short "Fixtype of bindings."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize a binding of variables to values
     as an omap from symbols to values.
     In our formalization of "
    (xdoc::seetopic "translated-terms" "translated terms")
    ", variables are identified by symbol values;
     so we use symbol values as the keys of the omaps
     that formalize bindings."))
  :key-type symbol-value
  :val-type value
  :pred bindingp)

(defsection binding-ext
  :extension binding
  (defrule bindingp-of-from-lists
    (implies (and (symbol-value-listp variables)
                  (value-listp values)
                  (equal (len variables) (len values)))
             (bindingp (omap::from-lists variables values)))
    :enable omap::from-lists))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod frame
  :short "Fixtype of frames."
  :long
  (xdoc::topstring
   (xdoc::p
    "The evaluation of ACL2 terms is naturally described via a stack.
     Here we formalize the frames (i.e. elements) of this stack.")
   (xdoc::p
    "A frame consists of a term under evaluation
     and a binding for (normally) at least the variables in the term."))
  ((term tterm)
   (binding binding))
  :layout :list
  :tag :frame
  :pred framep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist stack
  :short "Fixtype of stacks."
  :long
  (xdoc::topstring
   (xdoc::p
    "We formalize a stack as a list of frames."))
  :elt-type frame
  :true-listp t
  :elementp-of-nil nil
  :pred stackp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum eval-state
  :short "Fixtype of evaluation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "In our current formalization,
     the execution of an ACL2 program starts with
     a call of a (named) function on some argument values.
     For every choice of function and arguments,
     there is one possible initial state.
     This is captured by the @(':init') summand of this fixtype.")
   (xdoc::p
    "As formalized elsewhere, the execution from an initial state
     proceeds by looking up the function's definition,
     binding the argument values to the function's parameters,
     and then executing the function's body,
     which is put in a frame together with the binding.
     As also formalized elsewhere, a frame is executed stepwise,
     and may result in new frames being pushed onto the stack.
     Thus, a transitional execution state,
     i.e. one that is neither initial nor final,
     consists of a stack of frames.
     This is captured by the @(':trans') summand of this fixtype.")
   (xdoc::p
    "Frames are pushed and popped during execution.
     When the last frame is popped,
     there is no longer a stack,
     but there is a value,
     which is the result of the original function call (in the initial state)
     that started the whole execution.
     The final state thus consists of a single value.
     This is captured by the @(':final') summand of this fixtype.")
   (xdoc::p
    "During execution, certain kinds of errors may occur.
     For example, a function definition may not be found.
     There are well-formedness conditions on programs
     that ensure, via invariants on evaluation states,
     the absence of such errors.
     This will be formalized as
     the static semantics of the ACL2 programming language.
     However, as is common in programing language research,
     we define the dynamic semantics of the ACL2 programing language
     without assumng any static well-formedness,
     and therefore we must allow for the occurrence of errors,
     which lead to error states.
     This is captured by the @(':error') summand of this fixtype.
     These values currently carry no information,
     but we may refine them with fields that convey information about
     the nature and details of errors.
     In the future we may also want to prove formally
     that constraints from the static semantics
     ensure the absence of errors in the dynamic semantics."))
  (:init ((function symbol-value) (arguments value-list)))
  (:trans ((stack stack)))
  (:final ((result value)))
  (:error ()))
