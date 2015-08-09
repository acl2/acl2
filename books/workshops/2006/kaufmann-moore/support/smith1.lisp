; An example from :doc note-2-9, based on events from Eric Smith.

(in-package "ACL2")

(encapsulate
 (((foo *) => *)
  ((bar *) => *))

 (local (defun foo (x) (declare (ignore x)) t))
 (local (defun bar (x) (declare (ignore x)) t))

 (defthm foo-holds
   (implies x
            (equal (foo x) t)))
 (defthm bar-holds-propositionally
   (iff (bar x) t)))

; The following proves fine.  Note that foo-holds does not produce a
; double-rewrite warning even though x occurs in a non-IFF context where it is
; bound on the left-hand side of the conclusion of foo-holds, because we have
; special handling for this sort of case (which is why the following proves).

(defthm foo-bar
  (foo (bar y)))
