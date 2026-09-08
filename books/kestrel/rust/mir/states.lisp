; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "values")

; These allow the fixtype definitions below to prove
; their internal theorems under the controlled configuration,
; as in ../syntax/token-trees.lisp.
(local (include-book "kestrel/arithmetic-light/fix" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/update-nth" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ mir-states
  :parents (mir)
  :short "States of the MIR interpreter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The machine state is a stack of frames, one per active call.
     A frame records which function it is executing,
     the values of that function's locals
     (indexed by local number; possibly uninitialized),
     and the current position in the body:
     the index of the current basic block and
     the index of the next statement within it
     (equal to the number of statements when
     the block's terminator is next).")
   (xdoc::p
    "A non-bottom frame also records where its caller continues:
     the place (in the caller's frame) that receives the return value
     and the caller's target block.
     For the bottom frame these two components are not used
     (the return value of the bottom frame's function is
     the result of the whole execution).")
   (xdoc::p
    "The function bodies themselves are not part of the state:
     the program is a separate, unchanging input of the interpreter,
     and frames refer to their function by name."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod frame
  :short "Fixtype of frames."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see mir-states).
     The @('dest') and @('target') components are
     the caller-continuation information,
     unused (and irrelevant) in the bottom frame."))
  ((fn acl2::string)
   (locals value-option-list)
   (cur-block acl2::nat)
   (cur-stmt acl2::nat)
   (dest place)
   (target acl2::nat))
  :pred framep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-frame
  :short "A frame witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see irr-edition) for
     the purpose of these witnesses."))
  :type framep
  :body (make-frame :fn ""
                    :locals nil
                    :cur-block 0
                    :cur-stmt 0
                    :dest (irr-place)
                    :target 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist frame-list
  :short "Fixtype of lists of frames."
  :elt-type frame
  :true-listp t
  :elementp-of-nil nil
  :pred frame-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod mstate
  :short "Fixtype of machine states."
  :long
  (xdoc::topstring
   (xdoc::p
    "The stack of frames, topmost (innermost call) first.
     An empty stack does not occur during execution:
     the step function that receives a state with an empty stack
     reports it as a stuck state."))
  ((frames frame-list))
  :pred mstatep)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-mstate
  :short "A machine state witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see irr-edition) for
     the purpose of these witnesses."))
  :type mstatep
  :body (make-mstate :frames nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The locals of a frame are read and written by position.
; The fixtype machinery does not provide nth/update-nth rules
; for its list types, so we prove the two we need here.

(local
 (defthm value-optionp-of-nth-when-value-option-listp
   (implies (and (value-option-listp l)
                 (< (nfix i) (len l)))
            (value-optionp (nth i l)))
   :hints (("Goal" :induct (nth i l)
                   :in-theory (e/d (nth nfix) (acl2::nth-of-cdr))))))

(local
 (defthm value-option-listp-of-update-nth-when-value-option-listp
   (implies (and (value-option-listp l)
                 (value-optionp v)
                 (< (nfix i) (len l)))
            (value-option-listp (update-nth i v l)))
   :hints (("Goal" :induct (update-nth i v l)
                   :in-theory (enable update-nth nfix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define read-local ((local acl2::natp) (frame framep))
  :returns (value value-optionp)
  :short "Read a local of a frame."
  :long
  (xdoc::topstring
   (xdoc::p
    "The result is @('nil') if the local is uninitialized
     or its index is out of range;
     the interpreter treats both as errors at its level,
     where it can also distinguish them
     (an out-of-range local is an ill-formed body,
     while reading an uninitialized local is
     undefined behavior of the program)."))
  (b* ((local (acl2::nfix local))
       (locals (frame->locals frame)))
    (if (< local (len locals))
        (value-option-fix (nth local locals))
      nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define write-local ((local acl2::natp) (value value-optionp) (frame framep))
  :returns (new-frame framep)
  :short "Write a local of a frame (or mark it uninitialized)."
  :long
  (xdoc::topstring
   (xdoc::p
    "Writing @('nil') marks the local uninitialized,
     which is how the storage markers reset locals.
     Writing to an out-of-range local index
     leaves the frame unchanged;
     the interpreter checks the range before writing,
     so this case does not arise from it."))
  (b* ((local (acl2::nfix local))
       (locals (frame->locals frame)))
    (if (< local (len locals))
        (change-frame frame
                      :locals (update-nth local
                                          (value-option-fix value)
                                          locals))
      (frame-fix frame))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define local-in-range-p ((local acl2::natp) (frame framep))
  :returns (yes/no booleanp)
  :short "Check if a local index is in range for a frame."
  (< (acl2::nfix local)
     (len (frame->locals frame))))
