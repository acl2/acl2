; A tool to avoid expensive calls of expt
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A tool to avoid evaluation of calls to EXPT when the exponent is huge (TODO:
;; Didn't I do this somewhere else?):

;; To turn on limiting, do (limit-expt)

;; TODO: What about calls to EXPT that get evaluated in :type-prescription
;; and/or :forward-chaining, etc.?  I think that can cause some proofs to break
;; when this is turned on.  Otherwise, we could consider turning this on by
;; default.

;TODO: Consider raising this, or making it changeable by the user (perhaps
;using a table).
(defconst *max-exponent-to-evaluate* 1000)

;; An alias of EXPT whose :executable-counterpart will remain enabled.  The
;; :definition rule should remain disabled.
(defund expt-limited (r i)
  (expt r i))

;; Turn calls of EXPT that can be safely evaluated into calls of EXPT-LIMITED,
;; which then get evaluated. This is disabled until the user does (limit-expt).
(defthmd expt-becomes-expt-limited
  (implies (and (syntaxp (and (quotep r)
                              (quotep i)))
                (or (<= i *max-exponent-to-evaluate*)
                    ;; These bases seem quick to evaluate:
                    (equal r 0)
                    (equal r 1)
                    (equal r -1)))
           (equal (expt r i)
                  (expt-limited r i)))
  :hints (("Goal" :in-theory (enable expt-limited))))

(defmacro limit-expt ()
  '(progn (in-theory (disable (:executable-counterpart expt)))
          (in-theory (enable expt-becomes-expt-limited))))

(defmacro unlimit-expt ()
  '(progn (in-theory (enable (:executable-counterpart expt)))
          (in-theory (disable expt-becomes-expt-limited))))
