; A very simple utility to negate a term
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/forms" :dir :system)

;; Negate TERM by adding or removing a call of not (avoids double negation)
;; See also dumb-negate-lit.
(defund negate-term (term)
  (declare (xargs :guard t ;(pseudo-termp term)
                  ))
  (if (and (call-of 'not term)
           (consp (cdr term)) ;for guards
           )
      (farg1 term) ;negation of (not x) is just x
    `(not ,term)))

(defthm pseudo-termp-of-negate-term
  (implies (pseudo-termp term)
           (pseudo-termp (negate-term term)))
  :hints (("Goal" :in-theory (enable negate-term))))
