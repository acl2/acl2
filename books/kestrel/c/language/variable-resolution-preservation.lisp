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

(defsection variable-resolution-preservation
  :parents (dynamic-semantics)
  :short "Preservation of variable resolution under execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove theorems saying that,
     in our dynamic semantics of C,
     if a variable with a certain name
     is visible in the computation state before an execution function,
     then the same variable is also visible
     in the computation state after the execution function,
     with a slight exception explained shortly.
     Here visibility is expressed via @(tsee objdesign-of-var);
     the fact that the same variable is visible
     (as opposed to a possibly different one with the same name)
     is expressed via the equality of @(tsee objdesign-of-var)
     before and after the execution.
     Compare this notion with
     the one in @(see variable-visibiliy-preservation).
     The exception mentioned above applied to
     the execution of
     object declarations,
     block items,
     and lists of block items:
     since those may introduce any number of new variables,
     which may hides ones with the same names in outer scopes,
     @(tsee objdesign-of-var) may not resolve to the same variable,
     i.e. to the same object designator.
     Here the term `resolution' refers to
     the object designator returned by @(tsee objdesign-of-var).")
   (xdoc::p
    "We prove an inductively stronger property, involving "
    (xdoc::seetopic "frame-and-scope-peeling"
                    "the peeling of frames and scopes")
    ", from which the desired theorems follow as corollaries."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define prev-scope/frame ((compst compustatep))
  :guard (> (compustate-frames-number compst) 0)
  :returns (compst1 compustatep)
  :short "Go to the previous scope or frame."
  :long
  (xdoc::topstring
   (xdoc::p
    "That is,
     exit a scope if the top frame has more than one,
     otherwise pop a frame.")
   (xdoc::p
    "This function is used to express the exception,
     noted in @(see variable-resolution-preservation),
     for the execution of
     object declarations,
     block items,
     and lists of block items.
     Those block items always execute in a frame
     (which justifies the guard of this function),
     but that frame may have one or more scopes,
     with the object declarations or block items executing in the top scope;
     thus, in order to always exclude the scope
     in which the object declarations or block items are executing,
     we need to pop frame if that is the only scope.
     Note that just using @(tsee exit-scope),
     or just using @(tsee peel-scopes) with argument 1,
     would not work, and so we need to introduce this function here."))
  (if (> (compustate-top-frame-scopes-number compst) 1)
      (exit-scope compst)
    (pop-frame compst))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sk var-resolve-preservep ((compst compustatep) (compst1 compustatep))
  :returns (yes/no booleanp)
  :short "Check if all the variable names visible in a computation state
          are also visible in another computation state
          and they resolve to the same variables,
          for any number of peeled frames and scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "This expresses the property that we want to prove by induction."))
  (forall
   (var n m)
   (implies (and (identp var)
                 (natp n)
                 (natp m))
            (b* ((peeled-compst (peel-scopes m (peel-frames n compst)))
                 (peeled-compst1 (peel-scopes m (peel-frames n compst1))))
              (implies (objdesign-of-var var peeled-compst)
                       (equal (objdesign-of-var var peeled-compst1)
                              (objdesign-of-var var peeled-compst))))))

  ///

  (fty::deffixequiv-sk var-resolve-preservep
    :args ((compst compustatep) (compst1 compustatep)))

  (defrule var-resolve-preservep-reflexive
    (var-resolve-preservep compst compst))

  (defrule var-resolve-preservep-transitive
    (implies (and (var-resolve-preservep compst compst1)
                  (var-resolve-preservep compst1 compst2))
             (var-resolve-preservep compst compst2))
    :expand (var-resolve-preservep compst compst2)
    :disable var-resolve-preservep
    :enable var-resolve-preservep-necc))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-resolve-preservep-of-prev-scope/frame-of-create-var
  :short "Preservation of variable resolution under @(tsee create-var),
          for the previous scope or frame."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee var-resolve-preservep)
     holds between a computation state
     and the one obtained from it via @(tsee create-var),
     after going to the previous scope or frame in both computation states.
     The use of @(tsee prev-scope/frame) is critical,
     because clearly @(tsee create-var) may add a variable
     that hides another one with the same name.")
   (xdoc::p
    "This theorem is used to prove
     @(tsee var-resolve-preservep-of-prev-scope/frame-and-create-var)."))
  (b* ((compst1 (create-var var val compst)))
    (implies (and (not (errorp compst1))
                  (> (compustate-frames-number compst) 0))
             (var-resolve-preservep (prev-scope/frame compst)
                                    (prev-scope/frame compst1))))
  :enable var-resolve-preservep

  :prep-lemmas

  ((defrule lemma
     (b* ((compst1 (create-var var1 val compst))
          (peeled-compst
           (peel-scopes m (peel-frames n (prev-scope/frame compst))))
          (peeled-compst1
           (peel-scopes m (peel-frames n (prev-scope/frame compst1)))))
       (implies (and (not (errorp compst1))
                     (> (compustate-frames-number compst) 0))
                (implies (objdesign-of-var var peeled-compst)
                         (equal (objdesign-of-var var peeled-compst1)
                                (objdesign-of-var var peeled-compst)))))
     :enable (peel-frames
              prev-scope/frame
              exit-scope-of-create-var
              pop-frame-of-create-var
              compustatep-when-compustate-resultp-and-not-errorp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-resolve-preservep-of-write-object
  :short "Preservation of variable resolution under @(tsee write-object)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The predicate @(tsee var-resolve-preservep)
     holds between a computation state
     and the one obtained from it via @(tsee write-object).")
   (xdoc::p
    "This theorem is used, in @(tsee var-resolve-preservep-of-exec),
     to handle the execution of assignments."))
  (b* ((compst1 (write-object objdes val compst)))
    (implies (not (errorp compst1))
             (var-resolve-preservep compst compst1)))
  :expand (var-resolve-preservep compst (write-object objdes val compst))
  :enable (objdesign-of-var-of-write-object
           peel-frames
           peel-frames-of-write-object
           peel-scopes-of-write-object
           not-errorp-of-write-object-of-peel-frames
           not-errorp-of-write-object-of-peel-scopes
           objdesign-of-var-of-write-object)
  :disable objdesign-kind-of-objdesign-top
  ::use objdesign-kind-of-objdesign-top)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-resolve-preservep-of-prev-scope/frame-and-prev-scope/frame
  :short "Preservation of variable resolution
          when going back to the previous scope or frame."
  :long
  (xdoc::topstring
   (xdoc::p
    "We take two computation states
     with the same non-zero number of frames
     and with the same numbers od scopes in each frame.
     If @(tsee var-resolve-preservep) holds on the two computation states,
     it also holds on the ones obtained by
     applying @(tsee prev-scope/frame) to both.")
   (xdoc::p
    "This theorem is used, in @(tsee var-resolve-preservep-of-exec),
     to handle the execution of block items.
     It is also used to prove
     @(tsee var-resolve-preservep-of-prev-scope/frame-and-create-var)."))
  (implies (and (var-resolve-preservep compst compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (equal (compustate-scopes-numbers compst1)
                       (compustate-scopes-numbers compst))
                (> (compustate-frames-number compst) 0))
           (var-resolve-preservep (prev-scope/frame compst)
                                  (prev-scope/frame compst1)))
  :expand (var-resolve-preservep (prev-scope/frame compst)
                                 (prev-scope/frame compst1))

  :prep-lemmas

  ((defrule lemma
     (implies (and (var-resolve-preservep compst compst1)
                   (equal (compustate-frames-number compst1)
                          (compustate-frames-number compst))
                   (equal (compustate-scopes-numbers compst1)
                          (compustate-scopes-numbers compst))
                   (> (compustate-frames-number compst) 0)
                   (identp var)
                   (natp n)
                   (natp m))
              (b* ((peeled-compst
                    (peel-scopes m (peel-frames n (prev-scope/frame
                                                   compst))))
                   (peeled-compst1
                    (peel-scopes m (peel-frames n (prev-scope/frame
                                                   compst1)))))
                (implies (objdesign-of-var var peeled-compst)
                         (equal (objdesign-of-var var peeled-compst1)
                                (objdesign-of-var var peeled-compst)))))
     :use (lemma1 lemma2)

     :prep-lemmas

     ((defruled lemma1
        (implies (and (var-resolve-preservep compst compst1)
                      (equal (compustate-frames-number compst1)
                             (compustate-frames-number compst))
                      (equal (compustate-scopes-numbers compst1)
                             (compustate-scopes-numbers compst))
                      (> (compustate-frames-number compst) 0)
                      (identp var)
                      (zp n))
                 (b* ((peeled-compst
                       (peel-scopes m (peel-frames n (prev-scope/frame
                                                      compst))))
                      (peeled-compst1
                       (peel-scopes m (peel-frames n (prev-scope/frame
                                                      compst1)))))
                   (implies (objdesign-of-var var peeled-compst)
                            (equal (objdesign-of-var var peeled-compst1)
                                   (objdesign-of-var var peeled-compst)))))
        :cases ((zp m))
        :enable (peel-frames
                 peel-scopes
                 prev-scope/frame
                 peel-scopes-of-exit-scope-fold
                 nfix)
        :use ((:instance var-resolve-preservep-necc (n 0) (m 1))
              (:instance var-resolve-preservep-necc (n 1) (m 0))
              (:instance var-resolve-preservep-necc (n 0) (m (1+ m)))
              (:instance var-resolve-preservep-necc (n 1))))

      (defruled lemma2
        (implies (and (var-resolve-preservep compst compst1)
                      (equal (compustate-frames-number compst1)
                             (compustate-frames-number compst))
                      (equal (compustate-scopes-numbers compst1)
                             (compustate-scopes-numbers compst))
                      (> (compustate-frames-number compst) 0)
                      (identp var)
                      (not (zp n)))
                 (b* ((peeled-compst
                       (peel-scopes m (peel-frames n (prev-scope/frame
                                                      compst))))
                      (peeled-compst1
                       (peel-scopes m (peel-frames n (prev-scope/frame
                                                      compst1)))))
                   (implies (objdesign-of-var var peeled-compst)
                            (equal (objdesign-of-var var peeled-compst1)
                                   (objdesign-of-var var peeled-compst)))))
        :cases ((zp m))
        :enable (peel-scopes
                 prev-scope/frame
                 peel-frames-of-exit-scope
                 peel-frames-of-pop-frame-fold
                 nfix)
        :use ((:instance var-resolve-preservep-necc (m 0))
              (:instance var-resolve-preservep-necc (n (1+ n)) (m 0))
              var-resolve-preservep-necc
              (:instance var-resolve-preservep-necc (n (1+ n)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-resolve-preservep-of-prev-scope/frame-and-create-var
  :short "Combination of preservation of variable resolution
          under @(tsee create-var)
          and going back to the previous scope or frame."
  :long
  (xdoc::topstring
   (xdoc::p
    "This combines
     @(tsee var-resolve-preservep-of-prev-scope/frame-of-create-var)
     and
     @(tsee var-resolve-preservep-of-prev-scope/frame-and-prev-scope/frame),
     into a theorem that is used,
     in @(tsee var-resolve-preservep-of-exec),
     to handle the execution of object declarations."))
  (implies (and (var-resolve-preservep compst compst1)
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (equal (compustate-scopes-numbers compst1)
                       (compustate-scopes-numbers compst))
                (> (compustate-frames-number compst) 0)
                (not (errorp (create-var var val compst1))))
           (var-resolve-preservep (prev-scope/frame compst)
                                  (prev-scope/frame
                                   (create-var var val compst1))))
  :use ((:instance var-resolve-preservep-of-prev-scope/frame-of-create-var
                   (compst compst1))
        var-resolve-preservep-of-prev-scope/frame-and-prev-scope/frame
        (:instance
         var-resolve-preservep-of-prev-scope/frame-and-prev-scope/frame
         (compst compst1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-resolve-preservep-of-exit-scope-when-enter-scope
  :short "If variables resolution is preserved between
          a computation state just after entering a scope
          and another computation state,
          by going to the previous scope or frame,
          then variable resolution is also preserved between
          the first computation state before entering the scope
          and the second computation state after exiting a scope,
          and without going to the previous scope or frame."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note the ``cross-symmetry''
     between the two computation states in the hypothesis and conclusion,
     and between entering and exiting scopes.")
   (xdoc::p
    "This theorem is proved easily,
     given the use of @(tsee prev-scope/frame).")
   (xdoc::p
    "This theorem is used, in @(tsee var-resolve-preservep-of-exec),
     to handle the execution of compound statements."))
  (implies (and (var-resolve-preservep (prev-scope/frame (enter-scope compst))
                                       (prev-scope/frame compst1))
                (equal (compustate-frames-number compst1)
                       (compustate-frames-number compst))
                (equal (compustate-scopes-numbers compst1)
                       (compustate-scopes-numbers (enter-scope compst)))
                (> (compustate-frames-number compst) 0))
           (var-resolve-preservep compst (exit-scope compst1)))
  :enable (prev-scope/frame
           exit-scope-of-enter-scope))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled var-resolve-preservep-of-pop-frame-when-push-frame
  :short "If variables resolution is preserved between
          a computation state just after pushing a frame
          and another computation state,
          by going to the previous scope or frame,
          then variable resolution is also preserved between
          the first computation state before pushing the frame
          and the second computation state after popping a frane,
          and without going to the previous scope or frame."
  :long
  (xdoc::topstring
   (xdoc::p
    "Note the ``cross-symmetry''
     between the two computation states in the hypothesis and conclusion,
     and between pushing and popping frames.")
   (xdoc::p
    "This theorem is proved easily,
     given the use of @(tsee prev-scope/frame).")
   (xdoc::p
    "This theorem is used, in @(tsee var-visible-preservep-of-exec),
     to handle the execution of functions calls."))
  (implies (and (var-resolve-preservep
                 (prev-scope/frame (push-frame frame compst))
                 (prev-scope/frame compst1))
                (equal (compustate-frames-number (push-frame frame compst))
                       (compustate-frames-number compst1))
                (equal (len (frame->scopes frame)) 1)
                (equal (compustate-top-frame-scopes-number compst1) 1))
           (var-resolve-preservep compst (pop-frame compst1)))
  :enable prev-scope/frame)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection var-resolve-preservep-of-exec
  :short "Preservation of variable resolution under execution,
          for any number of peeled frames and scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We prove by induction that @(tsee var-resolve-preservep) holds
     between each computation state before execution
     and the computation state after execution.
     As explained in @(see variable-resolution-preservation),
     the theorems are weakened for
     object declarations,
     block items,
     and lists of block items,
     by going back to the previous scope or frame."))

  (defthm-exec-flag
    (defthm var-resolve-preservep-of-exec-expr-call
      (b* (((mv result compst1) (exec-expr-call fun args compst fenv limit)))
        (implies (not (errorp result))
                 (var-resolve-preservep compst compst1)))
      :flag exec-expr-call)
    (defthm var-resolve-preservep-of-exec-expr-call-or-pure
      (b* (((mv result compst1) (exec-expr-call-or-pure e compst fenv limit)))
        (implies (not (errorp result))
                 (var-resolve-preservep compst compst1)))
      :flag exec-expr-call-or-pure)
    (defthm var-resolve-preservep-of-exec-expr-asg
      (b* ((compst1 (exec-expr-asg e compst fenv limit)))
        (implies (not (errorp compst1))
                 (var-resolve-preservep compst compst1)))
      :flag exec-expr-asg)
    (defthm var-resolve-preservep-of-exec-expr-call-or-asg
      (b* ((compst1 (exec-expr-call-or-asg e compst fenv limit)))
        (implies (not (errorp compst1))
                 (var-resolve-preservep compst compst1)))
      :flag exec-expr-call-or-asg)
    (defthm var-resolve-preservep-of-exec-fun
      (b* (((mv result compst1) (exec-fun fun args compst fenv limit)))
        (implies (not (errorp result))
                 (var-resolve-preservep compst compst1)))
      :flag exec-fun)
    (defthm var-resolve-preservep-of-exec-stmt
      (b* (((mv result compst1) (exec-stmt s compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-resolve-preservep compst compst1)))
      :flag exec-stmt)
    (defthm var-resolve-preservep-of-exec-stmt-while
      (b* (((mv result compst1) (exec-stmt-while test body compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-resolve-preservep compst compst1)))
      :flag exec-stmt-while)
    (defthm var-resolve-preservep-of-exec-initer
      (b* (((mv result compst1) (exec-initer initer compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-resolve-preservep compst compst1)))
      :flag exec-initer)
    (defthm var-resolve-preservep-of-exec-obj-declon
      (b* ((compst1 (exec-obj-declon declon compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp compst1)))
                 (var-resolve-preservep (prev-scope/frame compst)
                                        (prev-scope/frame compst1))))
      :flag exec-obj-declon)
    (defthm var-resolve-preservep-of-exec-block-item
      (b* (((mv result compst1) (exec-block-item item compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-resolve-preservep (prev-scope/frame compst)
                                        (prev-scope/frame compst1))))
      :flag exec-block-item)
    (defthm var-resolve-preservep-of-exec-block-item-list
      (b* (((mv result compst1) (exec-block-item-list items compst fenv limit)))
        (implies (and (> (compustate-frames-number compst) 0)
                      (not (errorp result)))
                 (var-resolve-preservep (prev-scope/frame compst)
                                        (prev-scope/frame compst1))))
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
              var-resolve-preservep-of-prev-scope/frame-and-prev-scope/frame
              var-resolve-preservep-of-prev-scope/frame-and-create-var
              var-resolve-preservep-of-exit-scope-when-enter-scope
              var-resolve-preservep-of-pop-frame-when-push-frame
              var-resolve-preservep-of-write-object
              len))))

  (in-theory (disable var-resolve-preservep-of-exec-expr-call
                      var-resolve-preservep-of-exec-expr-call-or-pure
                      var-resolve-preservep-of-exec-expr-asg
                      var-resolve-preservep-of-exec-expr-call-or-asg
                      var-resolve-preservep-of-exec-fun
                      var-resolve-preservep-of-exec-stmt
                      var-resolve-preservep-of-exec-stmt-while
                      var-resolve-preservep-of-exec-initer
                      var-resolve-preservep-of-exec-obj-declon
                      var-resolve-preservep-of-exec-block-item
                      var-resolve-preservep-of-exec-block-item-list)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection var-resolve-of-exec
  :short "Preservation of variable visibility under execution."

  (defruled var-resolve-of-exec-expr-call
    (b* (((mv result compst1) (exec-expr-call fun args compst fenv limit)))
      (implies (and (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (equal (objdesign-of-var var compst1)
                      (objdesign-of-var var compst))))
    :use (var-resolve-preservep-of-exec-expr-call
          (:instance var-resolve-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-expr-call fun args compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-expr-call-or-pure
    (b* (((mv result compst1) (exec-expr-call-or-pure e compst fenv limit)))
      (implies (and (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (equal (objdesign-of-var var compst1)
                      (objdesign-of-var var compst))))
    :use (var-resolve-preservep-of-exec-expr-call-or-pure
          (:instance var-resolve-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-expr-call-or-pure e compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-expr-asg
    (b* ((compst1 (exec-expr-asg e compst fenv limit)))
      (implies (and (not (errorp compst1))
                    (identp var)
                    (objdesign-of-var var compst))
               (equal (objdesign-of-var var compst1)
                      (objdesign-of-var var compst))))
    :use (var-resolve-preservep-of-exec-expr-asg
          (:instance var-resolve-preservep-necc
                     (compst1 (exec-expr-asg e compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-call-or-asg
    (b* ((compst1 (exec-expr-call-or-asg e compst fenv limit)))
      (implies (and (not (errorp compst1))
                    (identp var)
                    (objdesign-of-var var compst))
               (equal (objdesign-of-var var compst1)
                      (objdesign-of-var var compst))))
    :use (var-resolve-preservep-of-exec-expr-call-or-asg
          (:instance var-resolve-preservep-necc
                     (compst1 (exec-expr-call-or-asg e compst fenv limit))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-fun
    (b* (((mv result compst1) (exec-fun fun args compst fenv limit)))
      (implies (and (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (equal (objdesign-of-var var compst1)
                      (objdesign-of-var var compst))))
    :use (var-resolve-preservep-of-exec-fun
          (:instance var-resolve-preservep-necc
                     (compst1 (mv-nth 1 (exec-fun fun args compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-stmt
    (b* (((mv result compst1) (exec-stmt s compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (equal (objdesign-of-var var compst1)
                      (objdesign-of-var var compst))))
    :use (var-resolve-preservep-of-exec-stmt
          (:instance var-resolve-preservep-necc
                     (compst1 (mv-nth 1 (exec-stmt s compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-stmt-while
    (b* (((mv result compst1) (exec-stmt-while test body compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (equal (objdesign-of-var var compst1)
                      (objdesign-of-var var compst))))
    :use (var-resolve-preservep-of-exec-stmt-while
          (:instance var-resolve-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-stmt-while test body compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-initer
    (b* (((mv result compst1) (exec-initer initer compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var compst))
               (equal (objdesign-of-var var compst1)
                      (objdesign-of-var var compst))))
    :use (var-resolve-preservep-of-exec-initer
          (:instance var-resolve-preservep-necc
                     (compst1
                      (mv-nth 1 (exec-initer initer compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-obj-declon
    (b* ((compst1 (exec-obj-declon declon compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp compst1))
                    (identp var)
                    (objdesign-of-var var (prev-scope/frame compst)))
               (equal (objdesign-of-var var (prev-scope/frame compst1))
                      (objdesign-of-var var (prev-scope/frame compst)))))
    :use (var-resolve-preservep-of-exec-obj-declon
          (:instance var-resolve-preservep-necc
                     (compst (prev-scope/frame compst))
                     (compst1 (prev-scope/frame
                               (exec-obj-declon declon compst fenv limit)))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-block-item
    (b* (((mv result compst1) (exec-block-item item compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var (prev-scope/frame compst)))
               (equal (objdesign-of-var var (prev-scope/frame compst1))
                      (objdesign-of-var var (prev-scope/frame compst)))))
    :use (var-resolve-preservep-of-exec-block-item
          (:instance var-resolve-preservep-necc
                     (compst (prev-scope/frame compst))
                     (compst1 (prev-scope/frame
                               (mv-nth 1 (exec-block-item
                                          item compst fenv limit))))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes))

  (defruled var-resolve-of-exec-block-item-list
    (b* (((mv result compst1) (exec-block-item-list items compst fenv limit)))
      (implies (and (> (compustate-frames-number compst) 0)
                    (not (errorp result))
                    (identp var)
                    (objdesign-of-var var (prev-scope/frame compst)))
               (equal (objdesign-of-var var (prev-scope/frame compst1))
                      (objdesign-of-var var (prev-scope/frame compst)))))
    :use (var-resolve-preservep-of-exec-block-item-list
          (:instance var-resolve-preservep-necc
                     (compst (prev-scope/frame compst))
                     (compst1 (prev-scope/frame
                               (mv-nth 1 (exec-block-item-list
                                          items compst fenv limit))))
                     (n 0)
                     (m 0)))
    :enable (peel-frames
             peel-scopes)))
