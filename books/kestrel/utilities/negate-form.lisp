; A very simple utility to negate a form (not necessarily a term)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also negate-term, for a variant of this which does have a pseudo-termp guard.

(include-book "forms")

;; Negate FORM by adding or removing a call of not (avoids double negation)
;; See also dumb-negate-lit.
(defund negate-form (form)
  (declare (xargs :guard t))
  (if (and (call-of 'not form)
           (consp (cdr form)) ;for guards
           )
      (farg1 form) ;negation of (not x) is just x
    `(not ,form)))

;; (defthm pseudo-formp-of-negate-form
;;   (implies (pseudo-formp form)
;;            (pseudo-formp (negate-form form)))
;;   :hints (("Goal" :in-theory (enable negate-form))))

;; (defthm logic-formp-of-negate-form
;;   (implies (and (logic-formp form w)
;;                 (arities-okp '((not . 1)) w))
;;            (logic-formp (negate-form form) w))
;;   :hints (("Goal" :in-theory (enable negate-form))))
