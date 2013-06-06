; A double-rewrite example based on events from Dave Greve.

(in-package "ACL2")

(encapsulate
 ((perm (x y) nil)
  (unique (x) nil)
  (disjoint (x y) nil)
  (flat (x) nil)
  (goo (x) nil)
  (hoo (x) nil)
  (boo (x) nil)
  (red (x y) nil))


 (set-ignore-ok t)
 (set-irrelevant-formals-ok t)
 (local (defun perm (x y) (equal x y)))
 (local (defun unique (x) nil))
 (local (defun disjoint (x y) nil))
 (local (defun flat (x) nil))
 (local (defun goo (x) nil))
 (local (defun hoo (x) nil))
 (local (defun boo (x) nil))
 (local (defun red (x y) nil))

 (defequiv perm)

 (defcong perm iff (unique x) 1)
 (defcong perm equal (disjoint x y) 2)
 (defcong perm equal (disjoint x y) 2)
 (defcong perm equal (disjoint y x) 1)
 (defcong perm perm (append x y) 1)
 (defcong perm perm (append x y) 2)
 (defcong perm perm (flat x) 1)

 (defthm flat-append
   (equal (flat (append x y))
          (append (flat x) (flat y))))

 (defthm unique-disjoint
   (implies (unique (append x y z))
            (and (disjoint x (append y z))
                 (disjoint (append y z) x))))


 (defthm goo-perm
   (perm (goo x) (append (hoo x) (boo x))))

 (defthm red-disjoint
   (implies (disjoint (flat (double-rewrite x))
                      (flat (double-rewrite y)))
            (red x y))))

(defthm unique-disjoint-test
  (implies (unique (append (flat y)
                           (flat (hoo x))
                           (flat (boo x))))
           (and (disjoint (flat y)
                          (flat (goo x)))
                (disjoint (flat (goo x))
                          (flat y))))
  :rule-classes nil)

(defthm tis-so
  (implies (unique (append (flat y)
			   (flat (hoo x))
			   (flat (boo x))))
	   (red y (goo x)))
  :instructions
  (:pro (:rewrite red-disjoint) :prove)
  :rule-classes nil)

(defthm whynot
  (implies (unique (append (flat y)
                           (flat (hoo x))
                           (flat (boo x))))
           (red y (goo x)))
  :rule-classes nil)

(defthm red-disjoint-bad
  (implies (disjoint (flat x)
                     (flat y)) ; Double-rewrite warnings for x and y
           (red x y)))

(in-theory (disable red-disjoint))

; The following fails because the double-rewrite calls are missing in
; red-disjoint-bad (compare with red-disjoint).  Notice the warnings for
; red-disjoint-bad above.

; (defthm whynot-fails
;   (implies (unique (append (flat y)
;                            (flat (hoo x))
;                            (flat (boo x))))
;            (red y (goo x))))
