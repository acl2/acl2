; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.  The bug was in oneify, case (eq (car x) 'stobj-let), where the
; prog2$ form in dups-check finished with "temp" rather than the correct
; ",temp".

(in-package "ACL2") ; Added by Matt K. to make this into a book

(defstobj kid (kf :type integer :initially 0))
(defstobj kid2 (kf2 :type integer :initially 0) :congruent-to kid)
(defstobj par (kids :type (array kid (3))))
(defun two (i j par)
  (declare (xargs :stobjs par
                  :guard (and (natp i) (natp j) (< i 3) (< j 3) (not (equal i j)))
                  :verify-guards nil))
  (stobj-let ((kid (kidsi i par) update-kidsi) (kid2 (kidsi j par) update-kidsi))
             (kid kid2)
             (let* ((kid (update-kf 10 kid)) (kid2 (update-kf2 20 kid2))) (mv kid kid2))
             par))
(defun rd (i par) (declare (xargs :stobjs par :guard (and (natp i) (< i 3))))
  (stobj-let ((kid (kidsi i par))) (v) (kf kid) v))
(defthm is-10 (equal (rd 0 (two 0 1 (create-par))) 10)          ; by the definitions
  :rule-classes nil :hints (("Goal" :in-theory (disable (:e two)))))

; Added by Matt Kaufmann:
(include-book "std/testing/must-fail" :dir :system)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm is-not-10 (not (equal (rd 0 (two 0 1 (create-par))) 10)) ; by (:e two): garbage
  :rule-classes nil)
)

(must-fail ; The must-fail wrapper was added by Matt Kaufmann:
(defthm contradiction nil :rule-classes nil :hints (("Goal" :use (is-10 is-not-10))))
)
