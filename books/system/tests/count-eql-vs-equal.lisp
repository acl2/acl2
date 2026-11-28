; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug fixed before ACL2 Version 8.8.

; Logically, (count item lst) is the number of members of the list lst that
; are EQUAL to item.  But guard-verified code calling count runs the Common
; Lisp function COUNT, which compares with EQL.  The guard of count did not
; account for that, so the function count-a-b below was guard-verified and its
; execution returned 0, although logically it returns 2.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(must-fail
 (encapsulate
   ()
   (defun count-a-b (x)
     (declare (xargs :guard (true-listp x)))
     (count '(a b) x))
   (defthm count-a-b-is-2
     (equal (count-a-b '(17 (a b) 23 (a b) (c d))) 2)
     :hints (("Goal" :in-theory (disable (:e count-a-b))))
     :rule-classes nil)
   (defthm nil-proved
     nil
     :hints (("Goal" :use count-a-b-is-2))
     :rule-classes nil)))

; Guards are still verified when item or every member of the list is suitable
; for EQL (see eqlablep), and for strings.

(defun count-a (x)
  (declare (xargs :guard (true-listp x)))
  (count 'a x))

(assert-event (equal (count-a '(17 a 23 a (c d))) 2))

(defun count-in-eqlable-list (item x)
  (declare (xargs :guard (eqlable-listp x)))
  (count item x :start 1))

(assert-event (equal (count-in-eqlable-list '(a b) '(17 a 23)) 0))
(assert-event (equal (count-in-eqlable-list 'a '(a 17 a 23 a)) 2))

(defun count-char (c s)
  (declare (xargs :guard (stringp s)))
  (count c s))

(assert-event (equal (count-char #\D "DabcDefcDe") 3))
