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

(local (include-book "std/basic/inductions" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ frame-and-scope-peeling
  :parents (dynamic-semantics)
  :short "Functions and theorems about peeling frames and scopes."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce functions to peel off
     any number of frames and scopes from a computation state,
     and we prove properties of these functions.
     These functions are not used in the definition of the dynamic semantics,
     but they are useful to express and prove inductive properties
     of the dynamic semantics.
     Since the execution functions of the dynamic semantics
     push/pop frames and enter/exit scopes,
     some desired properties of the execution functions
     need to be first proved in a more general way
     on computation states obtained by peeling frames and scopes,
     so that the properties are inductively sufficiently strong;
     then the desired properties, not involving peeling frames and scopes,
     follow as special cases of peeling no frames and no scopes."))
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

  (defruled peel-frames-of-exit-scope
    (implies (and (not (zp n))
                  (> (compustate-frames-number compst) 0))
             (equal (peel-frames n (exit-scope compst))
                    (peel-frames n compst)))
    :enable (exit-scope
             push-frame
             pop-frame
             top-frame
             compustate-frames-number
             len)
    :expand (peel-frames n compst))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
     Some of these theorems generalize similar ones for @(tsee exit-scope)."))
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
