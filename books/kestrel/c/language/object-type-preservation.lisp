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

(include-book "frame-and-scope-peeling")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ object-type-preservation
  :parents (dynamic-semantics)
  :short "Preservation of object types under execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove theorems saying that,
     in our dynamic semantics of C,
     if an object has a value of a certain type
     in the computation state before an execution function,
     then the object has a value of the same type
     in the computation state after an execution function;
     the two values may differ
     (if the execution function changes the content of the object),
     but they always have the same type.")
   (xdoc::p
    "We prove an inductively stronger property, involving "
    (xdoc::seetopic "frame-and-scope-peeling"
                    "the peeling of frames and scopes")
    ", from which the desired theorems follow as corollaries.")
   (xdoc::p
    "For now we limit the property to top-level object designators.
     We plan to generalize this to all designators."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk object-type-preservep ((compst compustatep)
                                  (compst1 compustatep))
  :returns (yes/no booleanp)
  :short "Check if all objects in a computation state
          are also present in another computation state,
          with values of the same types,
          for any number of peeled frames and scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This expresses the property that we want to prove by induction."))
  (forall
   (objdes n m)
   (implies (and (objdesignp objdes)
                 (member-equal (objdesign-kind objdes) '(:auto :static :alloc))
                 (natp n)
                 (natp m))
            (b* ((peeled-compst (peel-scopes m (peel-frames n compst)))
                 (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
              (implies (not (errorp (read-object objdes peeled-compst)))
                       (and (not (errorp (read-object objdes peeled-compst1)))
                            (equal (type-of-value
                                    (read-object objdes peeled-compst1))
                                   (type-of-value
                                    (read-object objdes peeled-compst))))))))
  :prepwork ((local (in-theory (disable acl2::member-of-cons)))) ; for speed

  ///

  (fty::deffixequiv-sk object-type-preservep
    :args ((compst compustatep) (compst1 compustatep)))

  (defrule object-type-preservep-reflexive
    (object-type-preservep compst compst))

  (defrule object-type-preservep-transitive
    (implies (and (object-type-preservep compst compst1)
                  (object-type-preservep compst1 compst2))
             (object-type-preservep compst compst2))
    :expand (object-type-preservep compst compst2)
    :disable object-type-preservep
    :enable object-type-preservep-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled object-type-preservep-of-create-var
  :short "Preservation of object types under @(tsee create-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee object-type-preservep)
     holds between a computation state
     and the one obtained from it via @(tsee create-var).")
   (xdoc::p
    "This theorem is used, in @(tsee object-type-preservep-of-exec),
     to handle the execution of object declarations."))
  (b* ((compst1 (create-var var val compst)))
    (implies (not (errorp compst1))
             (object-type-preservep compst compst1)))
  :enable (object-type-preservep
           lemma8)

  :prep-lemmas

  ((defruled lemma1
     (b* ((compst1 (create-var var val compst))
          (peeled-compst (peel-scopes m (peel-frames n compst)))
          (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
       (implies (and (zp n)
                     (zp m)
                     (not (errorp compst1))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :enable (peel-frames
              peel-scopes
              read-object-of-create-var-when-existing))

   (defruled lemma2
     (b* ((compst1 (create-var var val compst))
          (peeled-compst (peel-scopes m (peel-frames n compst)))
          (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
       (implies (and (zp n)
                     (not (zp m))
                     (= (compustate-frames-number compst) 0)
                     (not (errorp compst1))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :enable (peel-frames
              peel-scopes
              compustatep-when-compustate-resultp-and-not-errorp
              read-object-of-create-var-when-existing))

   (defruled lemma3
     (b* ((compst1 (create-var var val compst))
          (peeled-compst (peel-scopes m (peel-frames n compst)))
          (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
       (implies (and (zp n)
                     (not (zp m))
                     (> (compustate-frames-number compst) 0)
                     (= (compustate-top-frame-scopes-number compst) 1)
                     (not (errorp compst1))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :enable (peel-frames
              peel-scopes
              compustatep-when-compustate-resultp-and-not-errorp
              read-object-of-create-var-when-existing))

   (defruled lemma4
     (b* ((compst1 (create-var var val compst))
          (peeled-compst (peel-scopes m (peel-frames n compst)))
          (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
       (implies (and (zp n)
                     (not (zp m))
                     (> (compustate-frames-number compst) 0)
                     (> (compustate-top-frame-scopes-number compst) 1)
                     (not (errorp compst1))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :enable (peel-frames
              peel-scopes-of-create-var))

   (defruled lemma5
     (b* ((compst1 (create-var var val compst))
          (peeled-compst (peel-scopes m (peel-frames n compst)))
          (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
       (implies (and (zp n)
                     (not (errorp compst1))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :use (lemma1 lemma2 lemma3 lemma4))

   (defruled lemma6
     (b* ((compst1 (create-var var val compst))
          (peeled-compst (peel-scopes m (peel-frames n compst)))
          (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
       (implies (and (not (zp n))
                     (= (compustate-frames-number compst) 0)
                     (not (errorp compst1))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :enable (peel-frames
              peel-scopes
              compustatep-when-compustate-resultp-and-not-errorp
              read-object-of-create-var-when-existing))

   (defruled lemma7
     (b* ((compst1 (create-var var val compst))
          (peeled-compst (peel-scopes m (peel-frames n compst)))
          (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
       (implies (and (not (zp n))
                     (> (compustate-frames-number compst) 0)
                     (not (errorp compst1))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :enable peel-frames-of-create-var)

   (defruled lemma8
     (b* ((compst1 (create-var var val compst))
          (peeled-compst (peel-scopes m (peel-frames n compst)))
          (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
       (implies (and (not (errorp compst1))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :use (lemma5 lemma6 lemma7))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled object-type-preservep-of-write-object
  :short "Preservation of object types under @(tsee write-object)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee object-type-preservep)
     holds between a computation state
     and the one obtained from it via @(tsee write-object).")
   (xdoc::p
    "This theorem is used, in @(tsee object-type-preservep-of-exec),
     to handle the execution of assignments."))
  (b* ((compst1 (write-object objdes val compst)))
    (implies (not (errorp compst1))
             (object-type-preservep compst compst1)))
  :enable object-type-preservep

  :prep-lemmas

  ((defrule lemma
     (b* ((compst1 (write-object objdes1 val compst))
          (peeled-compst (peel-scopes m (peel-frames n compst)))
          (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
       (implies (and (not (errorp compst1))
                     (member-equal (objdesign-kind objdes)
                                   '(:auto :static :alloc))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :enable (peel-frames
              peel-frames-of-write-object
              peel-scopes-of-write-object
              not-errorp-of-write-object-of-peel-frames
              not-errorp-of-write-object-of-peel-scopes
              read-object-of-write-object-when-auto/static/alloc-existing)
     :disable objdesign-kind-of-objdesign-top
     ::use (:instance objdesign-kind-of-objdesign-top (objdes objdes1)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled object-type-preservep-of-exit-scope-and-exit-scope
  :short "Preservation of object types is invariant
          under exiting a scope in both computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take two computation states
     with the same non-zero number of frames
     and with the same numbers od scopes in each frame,
     and more than one scope in the top frame.
     If @(tsee object-type-preservep) holds on the two computation states,
     it also holds on the ones obtained by
     applying @(tsee exit-scope) to both;
     the hypotheses guarantee that this operation can be applied.")
   (xdoc::p
    "This theorem serves to prove
     @(tsee object-type-preservep-of-exit-scope-when-enter-scope)."))
  (implies (and (object-type-preservep compst compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (equal (compustate-scopes-numbers compst1)
                       (compustate-scopes-numbers compst))
                (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 1))
           (object-type-preservep (exit-scope compst) (exit-scope compst1)))
  :expand (object-type-preservep (exit-scope compst) (exit-scope compst1))
  :enable lemma3

  :prep-lemmas

  ((defruled lemma1
     (b* ((peeled-compst (peel-scopes m (peel-frames n (exit-scope compst))))
          (peeled-compst1 (peel-scopes m (peel-frames n (exit-scope compst1)))))
       (implies (and (object-type-preservep compst compst1)
                     (equal (compustate-frames-number compst1)
                            (compustate-frames-number compst))
                     (equal (compustate-scopes-numbers compst1)
                            (compustate-scopes-numbers compst))
                     (> (compustate-frames-number compst) 0)
                     (> (compustate-top-frame-scopes-number compst) 1)
                     (zp n)
                     (natp m)
                     (objdesignp objdes)
                     (member-equal (objdesign-kind objdes)
                                   '(:auto :static :alloc))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :enable (peel-frames
              peel-scopes-of-exit-scope-fold
              nfix)
     :use (:instance object-type-preservep-necc (n 0) (m (1+ m))))

   (defruled lemma2
     (b* ((peeled-compst (peel-scopes m (peel-frames n (exit-scope compst))))
          (peeled-compst1 (peel-scopes m (peel-frames n (exit-scope compst1)))))
       (implies (and (object-type-preservep compst compst1)
                     (equal (compustate-frames-number compst1)
                            (compustate-frames-number compst))
                     (equal (compustate-scopes-numbers compst1)
                            (compustate-scopes-numbers compst))
                     (> (compustate-frames-number compst) 0)
                     (> (compustate-top-frame-scopes-number compst) 1)
                     (not (zp n))
                     (natp m)
                     (objdesignp objdes)
                     (member-equal (objdesign-kind objdes)
                                   '(:auto :static :alloc))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :expand ((peel-frames n (exit-scope compst))
              (peel-frames n (exit-scope compst1)))
     :enable (peel-frames
              pop-frame-of-exit-scope
              peel-frames-of-pop-frame-fold
              nfix
              fix
              object-type-preservep-necc))

   (defruled lemma3
     (b* ((peeled-compst (peel-scopes m (peel-frames n (exit-scope compst))))
          (peeled-compst1 (peel-scopes m (peel-frames n (exit-scope compst1)))))
       (implies (and (object-type-preservep compst compst1)
                     (equal (compustate-frames-number compst1)
                            (compustate-frames-number compst))
                     (equal (compustate-scopes-numbers compst1)
                            (compustate-scopes-numbers compst))
                     (> (compustate-frames-number compst) 0)
                     (> (compustate-top-frame-scopes-number compst) 1)
                     (natp m)
                     (objdesignp objdes)
                     (member-equal (objdesign-kind objdes)
                                   '(:auto :static :alloc))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :cases ((zp n))
     :enable (lemma1 lemma2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled object-type-preservep-of-exit-scope-when-enter-scope
  :short "If object types are preserved between
          a computation state just after entering a scope
          and another computation state,
          they are preserved also between
          the first computation state before entering the scope
          and the second computation state after exiting a scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note the ``cross-symmetry''
     between the two computation states in the hypothesis and conclusion,
     and between entering and exiting scopes.")
   (xdoc::p
    "This theorem is proved from
     @(tsee object-type-preservep-of-exit-scope-and-exit-scope),
     by suitably instantiating the computation states there.")
   (xdoc::p
    "This theorem is used, in @(tsee object-type-preservep-of-exec),
     to handle the execution of compound statements."))
  (implies (and (object-type-preservep (enter-scope compst) compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (equal (compustate-scopes-numbers compst1)
                       (compustate-scopes-numbers (enter-scope compst)))
                (> (compustate-frames-number compst) 0))
           (object-type-preservep compst (exit-scope compst1)))
  :use (:instance object-type-preservep-of-exit-scope-and-exit-scope
                  (compst (enter-scope compst))
                  (compst1 compst1))
  :enable exit-scope-of-enter-scope)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled object-type-preservep-of-pop-frame-and-pop-frame
  :short "Preservation of object types is invariant
          under popping a frame in both computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take two computation states
     with the same non-zero number of frames.
     If @(tsee object-type-preservep) holds on the two computation states,
     it also holds on the ones obtained by
     applying @(tsee pop-frame) to both;
     the hypotheses guarantee that this operation can be applied.")
   (xdoc::p
    "This theorem serves to prove
     @(tsee object-type-preservep-of-pop-frame-when-push-frame)."))
  (implies (and (object-type-preservep compst compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (> (compustate-frames-number compst) 0))
           (object-type-preservep (pop-frame compst) (pop-frame compst1)))
  :expand (object-type-preservep (pop-frame compst) (pop-frame compst1))
  :enable lemma

  :prep-lemmas

  ((defruled lemma
     (b* ((peeled-compst
           (peel-scopes m (peel-frames n (pop-frame compst))))
          (peeled-compst1
           (peel-scopes m (peel-frames n (pop-frame compst1)))))
       (implies (and (object-type-preservep compst compst1)
                     (equal (compustate-frames-number compst1)
                            (compustate-frames-number compst))
                     (> (compustate-frames-number compst) 0)
                     (natp n)
                     (natp m)
                     (objdesignp objdes)
                     (member-equal (objdesign-kind objdes)
                                   '(:auto :static :alloc))
                     (not (errorp (read-object objdes peeled-compst))))
                (and (not (errorp (read-object objdes peeled-compst1)))
                     (equal (type-of-value
                             (read-object objdes peeled-compst1))
                            (type-of-value
                             (read-object objdes peeled-compst))))))
     :enable (peel-frames-of-pop-frame-fold
              nfix
              object-type-preservep-necc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled object-type-preservep-of-pop-frame-when-push-frame
  :short "If object types are preserved between
          a computation state just after pushing a frame
          and another computation state,
          they are preserved also between
          the first computation state before pushing the frame
          and the second computation state after popping a frame."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note the ``cross-symmetry''
     between the two computation states in the hypothesis and conclusion,
     and between pushing and popping frames.")
   (xdoc::p
    "This theorem is proved from
     @(tsee object-type-preservep-of-pop-frame-and-pop-frame),
     by suitably instantiating the computation states there.")
   (xdoc::p
    "This theorem is used, in @(tsee object-type-preservep-of-exec),
     to handle the execution of functions calls."))
  (implies (and (object-type-preservep (push-frame frame compst) compst1)
                (equal (compustate-frames-number (push-frame frame compst))
                       (compustate-frames-number compst1)))
           (object-type-preservep compst (pop-frame compst1)))
  :use (:instance object-type-preservep-of-pop-frame-and-pop-frame
                  (compst (push-frame frame compst))
                  (compst1 compst1))
  :enable pop-frame-of-push-frame)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection object-type-preservep-of-exec
  :short "Preservation of object types under execution,
          for any number of peeled frames and scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove by induction that @(tsee object-type-preservep) holds
     between each computation state before execution
     and the computation state after execution."))

  (defthm-exec-flag
    (defthm object-type-preservep-of-exec-expr-call
      (b* (((mv result compst1) (exec-expr-call fun args compst fenv limit)))
        (implies (not (errorp result))
                 (object-type-preservep compst compst1)))
      :flag exec-expr-call)
    (defthm object-type-preservep-of-exec-expr-call-or-pure
      (b* (((mv result compst1) (exec-expr-call-or-pure e compst fenv limit)))
        (implies (not (errorp result))
                 (object-type-preservep compst compst1)))
      :flag exec-expr-call-or-pure)
    (defthm object-type-preservep-of-exec-expr-asg
      (b* ((compst1 (exec-expr-asg e compst fenv limit)))
        (implies (not (errorp compst1))
                 (object-type-preservep compst compst1)))
      :flag exec-expr-asg)
    (defthm object-type-preservep-of-exec-expr-call-or-asg
      (b* ((compst1 (exec-expr-call-or-asg e compst fenv limit)))
        (implies (not (errorp compst1))
                 (object-type-preservep compst compst1)))
      :flag exec-expr-call-or-asg)
    (defthm object-type-preservep-of-exec-fun
      (b* (((mv result compst1) (exec-fun fun args compst fenv limit)))
        (implies (not (errorp result))
                 (object-type-preservep compst compst1)))
      :flag exec-fun)
    (defthm object-type-preservep-of-exec-stmt
      (b* (((mv result compst1) (exec-stmt s compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (object-type-preservep compst compst1)))
      :flag exec-stmt)
    (defthm object-type-preservep-of-exec-stmt-while
      (b* (((mv result compst1) (exec-stmt-while test body compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (object-type-preservep compst compst1)))
      :flag exec-stmt-while)
    (defthm object-type-preservep-of-exec-initer
      (b* (((mv result compst1) (exec-initer initer compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (object-type-preservep compst compst1)))
      :flag exec-initer)
    (defthm object-type-preservep-of-exec-obj-declon
      (b* ((compst1 (exec-obj-declon declon compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp compst1)))
                 (object-type-preservep compst compst1)))
      :flag exec-obj-declon)
    (defthm object-type-preservep-of-exec-block-item
      (b* (((mv result compst1) (exec-block-item item compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (object-type-preservep compst compst1)))
      :flag exec-block-item)
    (defthm object-type-preservep-of-exec-block-item-list
      (b* (((mv result compst1) (exec-block-item-list items compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (object-type-preservep compst compst1)))
      :flag exec-block-item-list)
    :hints (("Goal"
             :in-theory
             (enable
              exec-expr-call
              exec-expr-call-or-pure
              exec-expr-asg
              exec-expr-call-or-asg
              exec-fun
              exec-stmt
              exec-stmt-while
              exec-initer
              exec-obj-declon
              exec-block-item
              exec-block-item-list
              object-type-preservep-of-create-var
              object-type-preservep-of-exit-scope-when-enter-scope
              object-type-preservep-of-pop-frame-when-push-frame
              object-type-preservep-of-write-object
              len))))

  (in-theory (disable object-type-preservep-of-exec-expr-call
                      object-type-preservep-of-exec-expr-call-or-pure
                      object-type-preservep-of-exec-expr-asg
                      object-type-preservep-of-exec-expr-call-or-asg
                      object-type-preservep-of-exec-fun
                      object-type-preservep-of-exec-stmt
                      object-type-preservep-of-exec-stmt-while
                      object-type-preservep-of-exec-initer
                      object-type-preservep-of-exec-obj-declon
                      object-type-preservep-of-exec-block-item
                      object-type-preservep-of-exec-block-item-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection object-type-of-exec
  :short "Preservation of object types under execution."

  (defruled object-type-of-exec-expr-call
    (b* (((mv result compst1) (exec-expr-call fun args compst fenv limit)))
      (implies (and (not (errorp result))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-expr-call
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1
                      (mv-nth 1 (exec-expr-call fun args compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-expr-call-or-pure
    (b* (((mv result compst1) (exec-expr-call-or-pure e compst fenv limit)))
      (implies (and (not (errorp result))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-expr-call-or-pure
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1
                      (mv-nth 1 (exec-expr-call-or-pure e compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-expr-asg
    (b* ((compst1 (exec-expr-asg e compst fenv limit)))
      (implies (and (not (errorp compst1))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-expr-asg
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1 (exec-expr-asg e compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-call-or-asg
    (b* ((compst1 (exec-expr-call-or-asg e compst fenv limit)))
      (implies (and (not (errorp compst1))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-expr-call-or-asg
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1 (exec-expr-call-or-asg e compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-fun
    (b* (((mv result compst1) (exec-fun fun args compst fenv limit)))
      (implies (and (not (errorp result))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-fun
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1 (mv-nth 1 (exec-fun fun args compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-stmt
    (b* (((mv result compst1) (exec-stmt s compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-stmt
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1 (mv-nth 1 (exec-stmt s compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-stmt-while
    (b* (((mv result compst1) (exec-stmt-while test body compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-stmt-while
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1
                      (mv-nth 1 (exec-stmt-while test body compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-initer
    (b* (((mv result compst1) (exec-initer initer compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-initer
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1
                      (mv-nth 1 (exec-initer initer compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-obj-declon
    (b* ((compst1 (exec-obj-declon declon compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp compst1))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-obj-declon
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1 (exec-obj-declon declon compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-block-item
    (b* (((mv result compst1) (exec-block-item item compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-block-item
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1
                      (mv-nth 1 (exec-block-item item compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled object-type-of-exec-block-item-list
    (b* (((mv result compst1) (exec-block-item-list items compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (member-equal (objdesign-kind objdes)
                                  '(:auto :static :alloc))
                    (not (errorp (read-object objdes compst))))
               (and (not (errorp (read-object objdes compst1)))
                    (equal (type-of-value (read-object objdes compst1))
                           (type-of-value (read-object objdes compst))))))
    :use (object-type-preservep-of-exec-block-item-list
          (:instance object-type-preservep-necc
                     (objdes (objdesign-fix objdes))
                     (compst1
                      (mv-nth 1 (exec-block-item-list items compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes)))
