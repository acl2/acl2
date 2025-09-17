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

(local (include-book "std/basic/inductions" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ variable-visibility-preservation
  :parents (dynamic-semantics)
  :short "Preservation of variable visibility under execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove theorems saying that,
     in our dynamic semantics of C,
     if a variable with a certain name
     is visible in the computation state before an execution function,
     then a variable with the same name
     is visible in the computation state after the execution function.
     The variable may be the same or a different one,
     e.g. after executing a block item declaration
     that introduces a variable that hides one in an outer scope.")
   (xdoc::p
    "The visibility is expressed via @(tsee objdesign-of-var).
     We prove an inductively stronger property, involving "
    (xdoc::seetopic "frame-and-scope-peeling"
                    "the peeling of frames and scopes")
    ", from which the desired theorems follow as corollaries."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk var-visible-preservep ((compst compustatep)
                                  (compst1 compustatep))
  :returns (yes/no booleanp)
  :short "Check if all variable names visible in a computation state
          are also visible in another computation state,
          for any number of peeled frames and scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This expresses the property that we want to prove by induction."))
  (forall (var n m)
          (implies (and (identp var)
                        (natp n)
                        (natp m)
                        (objdesign-of-var
                         var (peel-scopes m (peel-frames n compst))))
                   (objdesign-of-var
                    var (peel-scopes m (peel-frames n compst1)))))

  ///

  (fty::deffixequiv-sk var-visible-preservep
    :args ((compst compustatep) (compst1 compustatep)))

  (defrule var-visible-preservep-reflexive
    (var-visible-preservep compst compst))

  (defrule var-visible-preservep-transitive
    (implies (and (var-visible-preservep compst compst1)
                  (var-visible-preservep compst1 compst2))
             (var-visible-preservep compst compst2))
    :expand (var-visible-preservep compst compst2)
    :disable var-visible-preservep
    :enable var-visible-preservep-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-visible-preservep-of-create-var
  :short "Preservation of variable visibility under @(tsee create-var)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee var-visible-preservep)
     holds between a computation state
     and the one obtained from it via @(tsee create-var).")
   (xdoc::p
    "This theorem is used, in @(tsee var-visible-preservep-of-exec),
     to handle the execution of object declarations."))
  (b* ((compst1 (create-var var val compst)))
    (implies (and (> (compustate-frames-number compst) 0)
                  (not (errorp compst1))
                  (identp var))
             (var-visible-preservep compst compst1)))
  :enable (var-visible-preservep lemma4)

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-visible-preservep-of-exit-scope-and-exit-scope
  :short "Preservation of variable visibility is invariant
          under exiting a scope in both computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take two computation states
     with the same non-zero number of frames
     and with the same numbers od scopes in each frame,
     and more than one scope in the top frame.
     If @(tsee var-visible-preservep) holds on the two computation states,
     it also holds on the ones obtained by
     applying @(tsee exit-scope) to both;
     the hypotheses guarantee that this operation can be applied.")
   (xdoc::p
    "This theorem serves to prove
     @(tsee var-visible-preservep-of-exit-scope-when-enter-scope)."))
  (implies (and (var-visible-preservep compst compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (equal (compustate-scopes-numbers compst1)
                       (compustate-scopes-numbers compst))
                (> (compustate-frames-number compst) 0)
                (> (compustate-top-frame-scopes-number compst) 1))
           (var-visible-preservep (exit-scope compst) (exit-scope compst1)))
  :expand (var-visible-preservep (exit-scope compst) (exit-scope compst1))
  :enable lemma

  :prep-lemmas

  ((defruled lemma1
     (implies (and (var-visible-preservep compst compst1)
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
     :use (:instance var-visible-preservep-necc (n 0) (m (1+ m))))

   (defruled lemma2
     (implies (and (var-visible-preservep compst compst1)
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
              var-visible-preservep-necc))

   (defruled lemma
     (implies (and (var-visible-preservep compst compst1)
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

(defruled var-visible-preservep-of-exit-scope-when-enter-scope
  :short "If variable visibility is preserved between
          a computation state just after entering a scope
          and another computation state,
          it is preserved also between
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
     @(tsee var-visible-preservep-of-exit-scope-and-exit-scope),
     by suitably instantiating the computation states there.")
   (xdoc::p
    "This theorem is used, in @(tsee var-visible-preservep-of-exec),
     to handle the execution of compound statements."))
  (implies (and (var-visible-preservep (enter-scope compst) compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (equal (compustate-scopes-numbers compst1)
                       (compustate-scopes-numbers (enter-scope compst)))
                (> (compustate-frames-number compst) 0))
           (var-visible-preservep compst (exit-scope compst1)))
  :use (:instance var-visible-preservep-of-exit-scope-and-exit-scope
                  (compst (enter-scope compst))
                  (compst1 compst1))
  :enable exit-scope-of-enter-scope)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-visible-preservep-of-pop-frame-and-pop-frame
  :short "Preservation of variable visibility is invariant
          under popping a frame in both computation states."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take two computation states
     with the same non-zero number of frames.
     If @(tsee var-visible-preservep) holds on the two computation states,
     it also holds on the ones obtained by
     applying @(tsee pop-frame) to both;
     the hypotheses guarantee that this operation can be applied.")
   (xdoc::p
    "This theorem serves to prove
     @(tsee var-visible-preservep-of-pop-frame-when-push-frame)."))
  (implies (and (var-visible-preservep compst compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (> (compustate-frames-number compst) 0))
           (var-visible-preservep (pop-frame compst) (pop-frame compst1)))
  :expand (var-visible-preservep (pop-frame compst) (pop-frame compst1))
  :enable lemma

  :prep-lemmas

  ((defruled lemma
     (implies (and (var-visible-preservep compst compst1)
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
              var-visible-preservep-necc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-visible-preservep-of-pop-frame-when-push-frame
  :short "If variable visibility is preserved between
          a computation state just after pushing a frame
          and another computation state,
          it is preserved also between
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
     @(tsee var-visible-preservep-of-pop-frame-and-pop-frame),
     by suitably instantiating the computation states there.")
   (xdoc::p
    "This theorem is used, in @(tsee var-visible-preservep-of-exec),
     to handle the execution of functions calls."))
  (implies (and (var-visible-preservep (push-frame frame compst) compst1)
                (equal (compustate-frames-number (push-frame frame compst))
                       (compustate-frames-number compst1)))
           (var-visible-preservep compst (pop-frame compst1)))
  :use (:instance var-visible-preservep-of-pop-frame-and-pop-frame
                  (compst (push-frame frame compst))
                  (compst1 compst1))
  :enable pop-frame-of-push-frame)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-visible-preservep-of-write-object
  :short "Preservation of variable visbility under @(tsee write-object)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee var-visible-preservep)
     holds between a computation state
     and the one obtained from it via @(tsee write-object).")
   (xdoc::p
    "This theorem is used, in @(tsee var-visible-preservep-of-exec),
     to handle the execution of assignments."))
  (b* ((compst1 (write-object objdes val compst)))
    (implies (not (errorp compst1))
             (var-visible-preservep compst compst1)))
  :enable var-visible-preservep

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection var-visible-preservep-of-exec
  :short "Preservation of variable visibility under execution,
          for any number of peeled frames and scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove by induction that @(tsee var-visible-preservep) holds
     between each computation state before execution
     and the computation state after execution."))

  (defthm-exec-flag
    (defthm var-visible-preservep-of-exec-expr-call
      (b* (((mv result compst1) (exec-expr-call fun args compst fenv limit)))
        (implies (not (errorp result))
                 (var-visible-preservep compst compst1)))
      :flag exec-expr-call)
    (defthm var-visible-preservep-of-exec-expr-call-or-pure
      (b* (((mv result compst1) (exec-expr-call-or-pure e compst fenv limit)))
        (implies (not (errorp result))
                 (var-visible-preservep compst compst1)))
      :flag exec-expr-call-or-pure)
    (defthm var-visible-preservep-of-exec-expr-asg
      (b* ((compst1 (exec-expr-asg e compst fenv limit)))
        (implies (not (errorp compst1))
                 (var-visible-preservep compst compst1)))
      :flag exec-expr-asg)
    (defthm var-visible-preservep-of-exec-expr-call-or-asg
      (b* ((compst1 (exec-expr-call-or-asg e compst fenv limit)))
        (implies (not (errorp compst1))
                 (var-visible-preservep compst compst1)))
      :flag exec-expr-call-or-asg)
    (defthm var-visible-preservep-of-exec-fun
      (b* (((mv result compst1) (exec-fun fun args compst fenv limit)))
        (implies (not (errorp result))
                 (var-visible-preservep compst compst1)))
      :flag exec-fun)
    (defthm var-visible-preservep-of-exec-stmt
      (b* (((mv result compst1) (exec-stmt s compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-visible-preservep compst compst1)))
      :flag exec-stmt)
    (defthm var-visible-preservep-of-exec-stmt-while
      (b* (((mv result compst1) (exec-stmt-while test body compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-visible-preservep compst compst1)))
      :flag exec-stmt-while)
    (defthm var-visible-preservep-of-exec-initer
      (b* (((mv result compst1) (exec-initer initer compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-visible-preservep compst compst1)))
      :flag exec-initer)
    (defthm var-visible-preservep-of-exec-obj-declon
      (b* ((compst1 (exec-obj-declon declon compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp compst1)))
                 (var-visible-preservep compst compst1)))
      :flag exec-obj-declon)
    (defthm var-visible-preservep-of-exec-block-item
      (b* (((mv result compst1) (exec-block-item item compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-visible-preservep compst compst1)))
      :flag exec-block-item)
    (defthm var-visible-preservep-of-exec-block-item-list
      (b* (((mv result compst1) (exec-block-item-list items compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-visible-preservep compst compst1)))
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
              var-visible-preservep-of-create-var
              var-visible-preservep-of-exit-scope-when-enter-scope
              var-visible-preservep-of-pop-frame-when-push-frame
              var-visible-preservep-of-write-object
              len))))

  (in-theory (disable var-visible-preservep-of-exec-expr-call
                      var-visible-preservep-of-exec-expr-call-or-pure
                      var-visible-preservep-of-exec-expr-asg
                      var-visible-preservep-of-exec-expr-call-or-asg
                      var-visible-preservep-of-exec-fun
                      var-visible-preservep-of-exec-stmt
                      var-visible-preservep-of-exec-stmt-while
                      var-visible-preservep-of-exec-initer
                      var-visible-preservep-of-exec-obj-declon
                      var-visible-preservep-of-exec-block-item
                      var-visible-preservep-of-exec-block-item-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection var-visible-of-exec
  :short "Preservation of variable visibility under execution."

  (defruled var-visible-of-exec-expr-call
    (b* (((mv result compst1) (exec-expr-call fun args compst fenv limit)))
      (implies (and (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-expr-call
          (:instance var-visible-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-expr-call fun args compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-expr-call-or-pure
    (b* (((mv result compst1) (exec-expr-call-or-pure e compst fenv limit)))
      (implies (and (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-expr-call-or-pure
          (:instance var-visible-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-expr-call-or-pure e compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-expr-asg
    (b* ((compst1 (exec-expr-asg e compst fenv limit)))
      (implies (and (not (errorp compst1))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-expr-asg
          (:instance var-visible-preservep-necc
                     (compst1 (exec-expr-asg e compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-call-or-asg
    (b* ((compst1 (exec-expr-call-or-asg e compst fenv limit)))
      (implies (and (not (errorp compst1))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-expr-call-or-asg
          (:instance var-visible-preservep-necc
                     (compst1 (exec-expr-call-or-asg e compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-fun
    (b* (((mv result compst1) (exec-fun fun args compst fenv limit)))
      (implies (and (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-fun
          (:instance var-visible-preservep-necc
                     (compst1 (mv-nth 1 (exec-fun fun args compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-stmt
    (b* (((mv result compst1) (exec-stmt s compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-stmt
          (:instance var-visible-preservep-necc
                     (compst1 (mv-nth 1 (exec-stmt s compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-stmt-while
    (b* (((mv result compst1) (exec-stmt-while test body compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-stmt-while
          (:instance var-visible-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-stmt-while test body compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-initer
    (b* (((mv result compst1) (exec-initer initer compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-initer
          (:instance var-visible-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-initer initer compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-obj-declon
    (b* ((compst1 (exec-obj-declon declon compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp compst1))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-obj-declon
          (:instance var-visible-preservep-necc
                     (compst1 (exec-obj-declon declon compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-block-item
    (b* (((mv result compst1) (exec-block-item item compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-block-item
          (:instance var-visible-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-block-item item compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-visible-of-exec-block-item-list
    (b* (((mv result compst1) (exec-block-item-list items compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (objdesign-of-var var compst1)))
    :use (var-visible-preservep-of-exec-block-item-list
          (:instance var-visible-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-block-item-list items compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes)))
