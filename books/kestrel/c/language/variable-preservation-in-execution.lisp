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

(include-book "dynamic-semantics")

(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "std/util/define-sk" :dir :system)

(local (include-book "std/basic/inductions" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ variable-preservation-in-execution
  :parents (language)
  :short "Preservation of variables under execution"
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove theorems about the fact that,
     in our dynamic semantics of C,
     the execution functions preserve the variables in the computation state:
     for each execution function,
     if a variable exists before execution,
     then it also exists after execution.
     This preservation is critically dependent on
     the big-step nature of our execution functions:
     clearly, in a small-step execution, variables may disappear
     as scopes are exited and frames are popped;
     but in a big-step execution,
     frames are popped and scopes are exited only after
     pushing frames and entering scopes.")
   (xdoc::p
    "we prove these properties by induction,
     but we need a sufficiently strong induction hypothesis to handle
     the pushing/popping of frames and the entering/exiting of scopes.
     So we introduce functions to peel off any number of frames and scopes,
     and we prove inductive properties about them,
     from which the desired properties, not involving the peeling functions,
     are then easily proved."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peel-frames ((n natp) (compst compustatep))
  :returns (new-compst compustatep)
  :short "Peel frames from the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "We pop @('n') frames, but we stop earlier if we run out of frames.")
   (xdoc::p
    "We prove theorems about how this function interacts
     with creating variables and with writing objects.
     Some of these theorems generalize similar ones for @(tsee pop-frame)."))
  (cond ((zp n) (compustate-fix compst))
        ((= (compustate-frames-number compst) 0) (compustate-fix compst))
        (t (peel-frames (1- n) (pop-frame compst))))
  :prepwork ((local (in-theory (enable nfix))))
  :hooks (:fix)

  ///

  (defruled peel-frames-of-create-var
    (b* ((compst1 (create-var var val compst)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp compst1))
                    (not (zp n)))
               (equal (peel-frames n compst1)
                      (peel-frames n compst))))
    :induct  (acl2::dec-induct n)
    :enable (create-var
             fix))

  (defruled peel-frames-of-pop-frame-fold
    (implies (> (compustate-frames-number compst) 0)
             (equal (peel-frames n (pop-frame compst))
                    (peel-frames (1+ (nfix n)) compst)))
    :enable fix)

  (defruled peel-frames-of-write-object
    (implies (not (errorp (write-object objdes val compst)))
             (equal (peel-frames n (write-object objdes val compst))
                    (if (and (objdesign-case (objdesign-top objdes) :auto)
                             (>= (objdesign-auto->frame (objdesign-top objdes))
                                 (if (< (nfix n)
                                        (compustate-frames-number compst))
                                     (- (compustate-frames-number compst)
                                        (nfix n))
                                   0)))
                        (peel-frames n compst)
                      (write-object objdes val (peel-frames n compst)))))
    :induct t
    :enable (pop-frame-of-write-object
             not-errorp-of-write-object-of-pop-frame
             compustatep-when-compustate-resultp-and-not-errorp
             nfix
             fix)
    :disable objdesign-kind-of-objdesign-top
    :hints ('(:use
              (objdesign-kind-of-objdesign-top
               objdesign-top-auto-frame-bound-when-write-object-not-error))))

  (defruled not-errorp-of-write-object-of-peel-frames
    (implies (and (or (member-equal (objdesign-kind (objdesign-top objdes))
                                    '(:static :alloc))
                      (< (objdesign-auto->frame (objdesign-top objdes))
                         (if (< (nfix n)
                                (compustate-frames-number compst))
                             (- (compustate-frames-number compst)
                                (nfix n))
                           0)))
                  (not (errorp (write-object objdes val compst))))
             (not (errorp (write-object objdes val (peel-frames n compst)))))
    :induct t
    :enable (not-errorp-of-write-object-of-pop-frame
             fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define peel-scopes ((m natp) (compst compustatep))
  :returns (new-compst compustatep)
  :short "Peel scopes from the computation state."
  :long
  (xdoc::topstring
   (xdoc::p
    "We exit @('m') scopes, but we stop earlier if we run out of scopes;
     note that a frame must always contain at least one scope,
     so we stop when one scope is left.
     The scopes are in the top frame;
     if there are no frames, this function does nothing.")
   (xdoc::p
    "We prove theorems about how this function interacts
     with creating variables and with writing objects.
     Some of these theorems generalize similar ones for @(tsee exit-frame)."))
  (cond ((zp m) (compustate-fix compst))
        ((= (compustate-frames-number compst) 0) (compustate-fix compst))
        ((= (compustate-top-frame-scopes-number compst) 1)
         (compustate-fix compst))
        (t (peel-scopes (1- m) (exit-scope compst))))
  :prepwork ((local (in-theory (enable nfix))))
  :hooks (:fix)

  ///

  (defruled peel-scopes-of-not-zp-unfold
    (implies (and (> (compustate-frames-number compst) 0)
                  (> (compustate-top-frame-scopes-number compst) 1)
                  (not (zp m)))
             (equal (peel-scopes m compst)
                    (peel-scopes (1- m) (exit-scope compst)))))

  (defruled peel-scopes-of-create-var
    (b* ((compst1 (create-var var val compst)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (> (compustate-top-frame-scopes-number compst) 1)
                    (not (errorp compst1))
                    (not (zp m)))
               (equal (peel-scopes m compst1)
                      (peel-scopes m compst))))
    :enable (peel-scopes-of-not-zp-unfold
             exit-scope-of-create-var
             compustatep-when-compustate-resultp-and-not-errorp)
    :disable peel-scopes)

  (defruled peel-scopes-one-scope-unfold
    (implies (and (not (zp m))
                  (equal (compustate-top-frame-scopes-number compst) 1))
             (equal (peel-scopes m compst)
                    (compustate-fix compst))))

  (defruled peel-scopes-of-exit-scope-fold
    (implies (and (> (compustate-frames-number compst) 0)
                  (> (compustate-top-frame-scopes-number compst) 1))
             (equal (peel-scopes m (exit-scope compst))
                    (peel-scopes (1+ (nfix m)) compst)))
    :enable fix)

  (defruled peel-scopes-of-write-object
    (implies (not (errorp (write-object objdes val compst)))
             (equal (peel-scopes m (write-object objdes val compst))
                    (if (and (objdesign-case (objdesign-top objdes) :auto)
                             (equal (objdesign-auto->frame (objdesign-top objdes))
                                    (1- (compustate-frames-number compst)))
                             (>= (objdesign-auto->scope (objdesign-top objdes))
                                 (if (< (nfix m)
                                        (compustate-top-frame-scopes-number
                                         compst))
                                     (- (compustate-top-frame-scopes-number
                                         compst)
                                        (nfix m))
                                   1)))
                        (peel-scopes m compst)
                      (write-object objdes val (peel-scopes m compst)))))
    :induct t
    :enable (exit-scope-of-write-object
             not-errorp-of-write-object-of-exit-scope
             compustatep-when-compustate-resultp-and-not-errorp
             fix)
    :disable objdesign-kind-of-objdesign-top
    :hints ('(:use (objdesign-kind-of-objdesign-top
                    objdesign-top-auto-scope-bound-when-write-object-not-error))))

  (defruled not-errorp-of-write-object-of-peel-scopes
    (implies (and (or (member-equal (objdesign-kind (objdesign-top objdes))
                                    '(:static :alloc))
                      (not (equal (objdesign-auto->frame (objdesign-top objdes))
                                  (1- (compustate-frames-number compst))))
                      (< (objdesign-auto->scope (objdesign-top objdes))
                         (if (< (nfix m)
                                (compustate-top-frame-scopes-number
                                 compst))
                             (- (compustate-top-frame-scopes-number
                                 compst)
                                (nfix m))
                           1)))
                  (not (errorp (write-object objdes val compst))))
             (not (errorp (write-object objdes val (peel-scopes m compst)))))
    :induct t
    :enable (not-errorp-of-write-object-of-exit-scope
             fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk objdesign-of-var-preservep ((compst compustatep)
                                       (compst1 compustatep))
  :returns (yes/no booleanp)
  :short "Check if all variables in a computation state
          are also in another computation state,
          for any number of peeled frames and scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This expressed the property that we want to prove by induction."))
  (forall (var n m)
          (implies (and (identp var)
                        (natp n)
                        (natp m)
                        (objdesign-of-var
                         var (peel-scopes m (peel-frames n compst))))
                   (objdesign-of-var
                    var (peel-scopes m (peel-frames n compst1)))))

  ///

  (fty::deffixequiv-sk objdesign-of-var-preservep
    :args ((compst compustatep) (compst1 compustatep)))

  (defrule objdesign-of-var-preservep-reflexive
    (objdesign-of-var-preservep compst compst))

  (defrule objdesign-of-var-preservep-transitive
    (implies (and (objdesign-of-var-preservep compst compst1)
                  (objdesign-of-var-preservep compst1 compst2))
             (objdesign-of-var-preservep compst compst2))
    :expand (objdesign-of-var-preservep compst compst2)
    :disable objdesign-of-var-preservep
    :enable objdesign-of-var-preservep-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled objdesign-of-var-preservep-of-create-var
  :short "Preservation of variables under @(tsee create-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicates @(tsee objdesign-of-var-preservep)
     holds between a computation state
     and the one obtained from it via @(tsee create-var).")
   (xdoc::p
    "This theorem is used, in @(tsee objdesign-of-var-preservep-of-exec),
     to handle the execution of object declarations."))
  (b* ((compst1 (create-var var val compst)))
    (implies (and (> (compustate-frames-number compst) 0)
                  (not (errorp compst1))
                  (identp var))
             (objdesign-of-var-preservep compst compst1)))
  :enable (objdesign-of-var-preservep lemma4)

  :prep-lemmas

  ((defruled lemma1
     (b* ((compst1 (create-var var val compst)))
       (implies (and (> (compustate-frames-number compst) 0)
                     (not (errorp compst1))
                     (identp var)
                     (zp n)
                     (zp m)
                     (identp var1)
                     (objdesign-of-var
                      var1 (peel-scopes m (peel-frames n compst))))
                (objdesign-of-var
                 var1 (peel-scopes m (peel-frames n compst1)))))
     :enable (peel-frames
              peel-scopes
              objdesign-of-var-of-create-var))

   (defruled lemma2
     (b* ((compst1 (create-var var val compst)))
       (implies (and (> (compustate-frames-number compst) 0)
                     (not (errorp compst1))
                     (identp var)
                     (zp n)
                     (not (zp m))
                     (identp var1)
                     (objdesign-of-var
                      var1 (peel-scopes m (peel-frames n compst))))
                (objdesign-of-var
                 var1 (peel-scopes m (peel-frames n compst1)))))
     :cases ((equal (compustate-top-frame-scopes-number compst) 1))
     :enable (peel-frames
              peel-scopes-one-scope-unfold
              peel-scopes-of-create-var
              objdesign-of-var-of-create-var
              compustatep-when-compustate-resultp-and-not-errorp))

   (defruled lemma3
     (b* ((compst1 (create-var var val compst)))
       (implies (and (> (compustate-frames-number compst) 0)
                     (not (errorp compst1))
                     (identp var)
                     (not (zp n))
                     (identp var1)
                     (objdesign-of-var
                      var1 (peel-scopes m (peel-frames n compst))))
                (objdesign-of-var
                 var1 (peel-scopes m (peel-frames n compst1)))))
     :enable peel-frames-of-create-var)

   (defruled lemma4
     (b* ((compst1 (create-var var val compst)))
       (implies (and (> (compustate-frames-number compst) 0)
                     (not (errorp compst1))
                     (identp var)
                     (natp n)
                     (natp m)
                     (identp var1)
                     (objdesign-of-var
                      var1 (peel-scopes m (peel-frames n compst))))
                (objdesign-of-var
                 var1 (peel-scopes m (peel-frames n compst1)))))
     :use (lemma1 lemma2 lemma3))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled objdesign-of-var-preservep-of-exit-scope-and-exit-scope
  :short "Preservation of variables is invariant
          under exiting a scope in both computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take two computation states
     with the same non-zero number of frames
     and with the same numbers od scopes in each frame,
     and more than one scope in the top frame.
     If @(tsee objdesign-of-var-preservep) holds on the two computation states,
     it also holds on the ones obtained by
     applying @(tsee exit-scope) to both;
     the hypotheses guarantee that this operation can be applied.")
   (xdoc::p
    "This theorem serves to prove
     @(tsee objdesign-of-var-preservep-of-exit-scope-when-enter-scope)."))
  (implies (and (objdesign-of-var-preservep compst compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (equal (compustate-scopes-numbers compst1)
                       (compustate-scopes-numbers compst))
                (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 1))
           (objdesign-of-var-preservep (exit-scope compst) (exit-scope compst1)))
  :expand (objdesign-of-var-preservep (exit-scope compst) (exit-scope compst1))
  :enable lemma

  :prep-lemmas

  ((defruled lemma1
     (implies (and (objdesign-of-var-preservep compst compst1)
                   (equal (compustate-frames-number compst1)
                          (compustate-frames-number compst))
                   (equal (compustate-scopes-numbers compst1)
                          (compustate-scopes-numbers compst))
                   (> (compustate-frames-number compst) 0)
                   (> (compustate-top-frame-scopes-number compst) 1)
                   (zp n)
                   (natp m)
                   (identp var)
                   (objdesign-of-var
                    var (peel-scopes m (peel-frames n (exit-scope compst)))))
              (objdesign-of-var
               var (peel-scopes m (peel-frames n (exit-scope compst1)))))
     :enable (peel-frames
              peel-scopes-of-exit-scope-fold
              nfix)
     :use (:instance objdesign-of-var-preservep-necc (n 0) (m (1+ m))))

   (defruled lemma2
     (implies (and (objdesign-of-var-preservep compst compst1)
                   (equal (compustate-frames-number compst1)
                          (compustate-frames-number compst))
                   (equal (compustate-scopes-numbers compst1)
                          (compustate-scopes-numbers compst))
                   (> (compustate-frames-number compst) 0)
                   (> (compustate-top-frame-scopes-number compst) 1)
                   (not (zp n))
                   (natp m)
                   (identp var)
                   (objdesign-of-var
                    var (peel-scopes m (peel-frames n (exit-scope compst)))))
              (objdesign-of-var
               var (peel-scopes m (peel-frames n (exit-scope compst1)))))
     :expand ((peel-frames n (exit-scope compst))
              (peel-frames n (exit-scope compst1)))
     :enable (peel-frames
              pop-frame-of-exit-scope
              peel-frames-of-pop-frame-fold
              nfix
              fix
              objdesign-of-var-preservep-necc))

   (defruled lemma
     (implies (and (objdesign-of-var-preservep compst compst1)
                   (equal (compustate-frames-number compst1)
                          (compustate-frames-number compst))
                   (equal (compustate-scopes-numbers compst1)
                          (compustate-scopes-numbers compst))
                   (> (compustate-frames-number compst) 0)
                   (> (compustate-top-frame-scopes-number compst) 1)
                   (natp m)
                   (identp var)
                   (objdesign-of-var
                    var (peel-scopes m (peel-frames n (exit-scope compst)))))
              (objdesign-of-var
               var (peel-scopes m (peel-frames n (exit-scope compst1)))))
     :cases ((zp n))
     :enable (lemma1 lemma2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled objdesign-of-var-preservep-of-exit-scope-when-enter-scope
  :short "If variables are preserved between
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
     @(tsee objdesign-of-var-preservep-of-exit-scope-and-exit-scope),
     by suitably instantiating the computation states there.")
   (xdoc::p
    "This theorem is used, in @(tsee objdesign-of-var-preservep-of-exec),
     to handle the execution of compound statements."))
  (implies (and (objdesign-of-var-preservep (enter-scope compst) compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (equal (compustate-scopes-numbers compst1)
                       (compustate-scopes-numbers (enter-scope compst)))
                (> (compustate-frames-number compst) 0))
           (objdesign-of-var-preservep compst (exit-scope compst1)))
  :use (:instance objdesign-of-var-preservep-of-exit-scope-and-exit-scope
                  (compst (enter-scope compst))
                  (compst1 compst1))
  :enable exit-scope-of-enter-scope)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled objdesign-of-var-preservep-of-pop-frame-and-pop-frame
  :short "Preservation of variables is invariant
          under popping a frame in both computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take two computation states
     with the same non-zero number of frames.
     If @(tsee objdesign-of-var-preservep) holds on the two computation states,
     it also holds on the ones obtained by
     applying @(tsee pop-frame) to both;
     the hypotheses guarantee that this operation can be applied.")
   (xdoc::p
    "This theorem serves to prove
     @(tsee objdesign-of-var-preservep-of-pop-frame-when-push-frame)."))
  (implies (and (objdesign-of-var-preservep compst compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (> (compustate-frames-number compst) 0))
           (objdesign-of-var-preservep (pop-frame compst) (pop-frame compst1)))
  :expand (objdesign-of-var-preservep (pop-frame compst) (pop-frame compst1))
  :enable lemma

  :prep-lemmas

  ((defruled lemma
     (implies (and (objdesign-of-var-preservep compst compst1)
                   (equal (compustate-frames-number compst1)
                          (compustate-frames-number compst))
                   (> (compustate-frames-number compst) 0)
                   (natp n)
                   (natp m)
                   (identp var)
                   (objdesign-of-var
                    var (peel-scopes m (peel-frames n (pop-frame compst)))))
              (objdesign-of-var
               var (peel-scopes m (peel-frames n (pop-frame compst1)))))
     :enable (peel-frames-of-pop-frame-fold
              nfix
              objdesign-of-var-preservep-necc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled objdesign-of-var-preservep-of-pop-frame-when-push-frame
  :short "If variables are preserved between
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
     @(tsee objdesign-of-var-preservep-of-pop-frame-and-pop-frame),
     by suitably instantiating the computation states there.")
   (xdoc::p
    "This theorem is used, in @(tsee objdesign-of-var-preservep-of-exec),
     to handle the execution of functions calls."))
  (implies (and (objdesign-of-var-preservep (push-frame frame compst) compst1)
                (equal (compustate-frames-number (push-frame frame compst))
                       (compustate-frames-number compst1)))
           (objdesign-of-var-preservep compst (pop-frame compst1)))
  :use (:instance objdesign-of-var-preservep-of-pop-frame-and-pop-frame
                  (compst (push-frame frame compst))
                  (compst1 compst1))
  :enable pop-frame-of-push-frame)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled objdesign-of-var-preservep-of-write-object
  :short "Preservation of variables under @(tsee write-object)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicates @(tsee objdesign-of-var-preservep)
     holds between a computation state
     and the one obtained from it via @(tsee write-object).")
   (xdoc::p
    "This theorem is used, in @(tsee objdesign-of-var-preservep-of-exec),
     to handle the execution of assignments."))
  (b* ((compst1 (write-object objdes val compst)))
    (implies (not (errorp compst1))
             (objdesign-of-var-preservep compst compst1)))
  :enable objdesign-of-var-preservep

  :prep-lemmas

  ((defrule lemma
     (b* ((compst1 (write-object objdes val compst)))
       (implies (and (not (errorp compst1))
                     (objdesign-of-var
                      var1 (peel-scopes m (peel-frames n compst))))
                (objdesign-of-var
                 var1 (peel-scopes m (peel-frames n compst1)))))
     :enable (peel-frames
              peel-frames-of-write-object
              peel-scopes-of-write-object
              not-errorp-of-write-object-of-peel-frames
              not-errorp-of-write-object-of-peel-scopes
              objdesign-of-var-of-write-object)
     :disable objdesign-kind-of-objdesign-top
     ::use objdesign-kind-of-objdesign-top)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection objdesign-of-var-preservep-of-exec
  :short "Preservation of variables under execution,
          for any number of peeled frames and scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove by induction that @(tsee objdesign-of-var-preservep) holds
     between each computation state before execution
     and the computation state after execution."))

  (defthm-exec-flag
    (defthm objdesign-of-var-preservep-of-exec-expr-call
      (b* (((mv result compst1) (exec-expr-call fun args compst fenv limit)))
        (implies (not (errorp result))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-expr-call)
    (defthm objdesign-of-var-preservep-of-exec-expr-call-or-pure
      (b* (((mv result compst1) (exec-expr-call-or-pure e compst fenv limit)))
        (implies (not (errorp result))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-expr-call-or-pure)
    (defthm objdesign-of-var-preservep-of-exec-expr-asg
      (b* ((compst1 (exec-expr-asg e compst fenv limit)))
        (implies (not (errorp compst1))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-expr-asg)
    (defthm objdesign-of-var-preservep-of-exec-expr-call-or-asg
      (b* ((compst1 (exec-expr-call-or-asg e compst fenv limit)))
        (implies (not (errorp compst1))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-expr-call-or-asg)
    (defthm objdesign-of-var-preservep-of-exec-fun
      (b* (((mv result compst1) (exec-fun fun args compst fenv limit)))
        (implies (not (errorp result))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-fun)
    (defthm objdesign-of-var-preservep-of-exec-stmt
      (b* (((mv result compst1) (exec-stmt s compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-stmt)
    (defthm objdesign-of-var-preservep-of-exec-stmt-while
      (b* (((mv result compst1) (exec-stmt-while test body compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-stmt-while)
    (defthm objdesign-of-var-preservep-of-exec-initer
      (b* (((mv result compst1) (exec-initer initer compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-initer)
    (defthm objdesign-of-var-preservep-of-exec-obj-declon
      (b* ((compst1 (exec-obj-declon declon compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (> (compustate-top-frame-scopes-number compst) 0)
                      (not (errorp compst1)))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-obj-declon)
    (defthm objdesign-of-var-preservep-of-exec-block-item
      (b* (((mv result compst1) (exec-block-item item compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (> (compustate-top-frame-scopes-number compst) 0)
                      (not (errorp result)))
                 (objdesign-of-var-preservep compst compst1)))
      :flag exec-block-item)
    (defthm objdesign-of-var-preservep-of-exec-block-item-list
      (b* (((mv result compst1) (exec-block-item-list items compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (> (compustate-top-frame-scopes-number compst) 0)
                      (not (errorp result)))
                 (objdesign-of-var-preservep compst compst1)))
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
              objdesign-of-var-preservep-of-create-var
              objdesign-of-var-preservep-of-exit-scope-when-enter-scope
              objdesign-of-var-preservep-of-pop-frame-when-push-frame
              objdesign-of-var-preservep-of-write-object
              len))))

  (in-theory (disable objdesign-of-var-preservep-of-exec-expr-call
                      objdesign-of-var-preservep-of-exec-expr-call-or-pure
                      objdesign-of-var-preservep-of-exec-expr-asg
                      objdesign-of-var-preservep-of-exec-expr-call-or-asg
                      objdesign-of-var-preservep-of-exec-fun
                      objdesign-of-var-preservep-of-exec-stmt
                      objdesign-of-var-preservep-of-exec-stmt-while
                      objdesign-of-var-preservep-of-exec-initer
                      objdesign-of-var-preservep-of-exec-obj-declon
                      objdesign-of-var-preservep-of-exec-block-item
                      objdesign-of-var-preservep-of-exec-block-item-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection objdesign-of-var-of-exec
  :short "Preservation of variables under execution."

  (defruled objdesign-of-var-of-exec-expr-call
    (b* (((mv result compst1) (exec-expr-call fun args compst fenv limit)))
      (implies (and (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-expr-call
          (:instance objdesign-of-var-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-expr-call fun args compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-expr-call-or-pure
    (b* (((mv result compst1) (exec-expr-call-or-pure e compst fenv limit)))
      (implies (and (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-expr-call-or-pure
          (:instance objdesign-of-var-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-expr-call-or-pure e compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-expr-asg
    (b* ((compst1 (exec-expr-asg e compst fenv limit)))
      (implies (and (not (errorp compst1))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-expr-asg
          (:instance objdesign-of-var-preservep-necc
                     (compst1 (exec-expr-asg e compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-call-or-asg
    (b* ((compst1 (exec-expr-call-or-asg e compst fenv limit)))
      (implies (and (not (errorp compst1))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-expr-call-or-asg
          (:instance objdesign-of-var-preservep-necc
                     (compst1 (exec-expr-call-or-asg e compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-fun
    (b* (((mv result compst1) (exec-fun fun args compst fenv limit)))
      (implies (and (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-fun
          (:instance objdesign-of-var-preservep-necc
                     (compst1 (mv-nth 1 (exec-fun fun args compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-stmt
    (b* (((mv result compst1) (exec-stmt s compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-stmt
          (:instance objdesign-of-var-preservep-necc
                     (compst1 (mv-nth 1 (exec-stmt s compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-stmt-while
    (b* (((mv result compst1) (exec-stmt-while test body compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-stmt-while
          (:instance objdesign-of-var-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-stmt-while test body compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-initer
    (b* (((mv result compst1) (exec-initer initer compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-initer
          (:instance objdesign-of-var-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-initer initer compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-obj-declon
    (b* ((compst1 (exec-obj-declon declon compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (> (compustate-top-frame-scopes-number compst) 0)
                    (not (errorp compst1))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-obj-declon
          (:instance objdesign-of-var-preservep-necc
                     (compst1 (exec-obj-declon declon compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-block-item
    (b* (((mv result compst1) (exec-block-item item compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (> (compustate-top-frame-scopes-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-block-item
          (:instance objdesign-of-var-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-block-item item compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled objdesign-of-var-of-exec-block-item-list
    (b* (((mv result compst1) (exec-block-item-list items compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (> (compustate-top-frame-scopes-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (objdesign-of-var-preservep-of-exec-block-item-list
          (:instance objdesign-of-var-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-block-item-list items compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes)))
