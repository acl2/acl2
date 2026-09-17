; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.

(in-package "ACL2")

; The redundancy check for NON-EXECUTABLE defuns never compares :MEASURE.
; The local definition is admitted with the (true) measure (ACL2-COUNT Y);
; the non-local one claims the (false) measure (ACL2-COUNT X) and is accepted
; as redundant.  Pass 2 of the ENCAPSULATE then installs the claimed
; justification with no proof.

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  ()
  (local (defun-nx f (x y)
           (declare (xargs :measure (acl2-count y)))
           (if (and (consp x) (consp y))
               (f (cons 1 x) (cdr y))
             (list x y))))
; The must-fail wrapper below was added by Matt Kaufmann, as the following
; definition of f is no longer redundant as of mid-September, 2026.
  (must-fail
  (defun-nx f (x y)
    (declare (xargs :measure (acl2-count x)))
    (if (and (consp x) (consp y))
        (f (cons 1 x) (cdr y))
      (list x y)))))

; Commented out by Matt Kaufmann:
#|
(defthm bad
  (not (and (consp x) (consp y)))
  :rule-classes nil
  :hints (("Goal" :use (:termination-theorem f))))

(defthm nil-proved
  nil
  :rule-classes nil
  :hints (("Goal" :use (:instance bad (x '(1)) (y '(2))))))
|#
