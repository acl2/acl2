; A generic pattern for proving things about a tail-recursive function
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Postulate the existence of functions to:
;; - test whether we should exit the recursion
;; - update the params one step
;; - measure the params, for termination
(encapsulate (((generic-tail-exitp *) => *)
              ((generic-tail-update *) => *)
              ((generic-tail-measure *) => *))

  (local (defun generic-tail-exitp (params) (zp params)))
  (local (defun generic-tail-update (params) (+ -1 params)))
  (local (defun generic-tail-measure (params) (nfix params)))

  ;; The measure must always be an ordinal:
  (defthm o-p-of-generic-tail-measure
    (o-p (generic-tail-measure x)))

  ;; The measure must decrease when we update the params, assuming we do not
  ;; exit:
  (defthm generic-tail-rec-termination
    (implies (not (generic-tail-exitp params))
             (o< (generic-tail-measure (generic-tail-update params))
                 (generic-tail-measure params)))))

;; Postulate the existence of a function that computes a return value from the
;; params, in the base case.
(defstub generic-tail-base (params) t)

;; A generic tail recursive function:
(defun generic-tail (params)
  (declare (xargs :measure (generic-tail-measure params)))
  (if (generic-tail-exitp params)
      (generic-tail-base params)
    (generic-tail (generic-tail-update params))))

;; TODO: Make post take the params too. also the inv?

;; Postulate the existence of some postcondition and invariant:
(encapsulate (((generic-tail-inv *)=> *)
              ((generic-tail-post *)=> *))

  (local (defun generic-tail-inv (params) (declare (ignore params)) t))
  (local (defun generic-tail-post (params) (declare (ignore params)) t))

  ;;the update function must preserve the invariant, assuming we don't exit:
  (defthm generic-tail-inv-of-generic-tail-update
    (implies (and (generic-tail-inv params)
                  (not (generic-tail-exitp params)) ;we get to assume we are not exiting
                  )
             (generic-tail-inv (generic-tail-update params))))

  ;;the invariant must impliy the postcondition after we do the base case work,
  ;;assuming we exit:
  (defthm generic-tail-post-of-generic-tail-base
    (implies (and (generic-tail-inv params)
                  (generic-tail-exitp params) ;we get to assume we are exiting
                  )
             (generic-tail-post (generic-tail-base params)))))

;; If the invariant is true of the initial params, then the postcondition is
;; true of the final value returned.  Proved by induction.
(defthm main
  (implies (generic-tail-inv params)
           (generic-tail-post (generic-tail params))))
