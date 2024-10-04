(in-package "HANOI")
(include-book "misc/records" :dir :system)
(include-book "basic")
(include-book "stack")

(acl2::set-verify-guards-eagerness 2)

(defund new-state ()
  (s 'A nil (s 'B nil (s 'C nil nil))))

(defund statep (st)
  (and (stackp (g 'A st))
       (stackp (g 'B st))
       (stackp (g 'C st))))

(defund pegp (p)
  (or (equal p 'A)
      (equal p 'B)
      (equal p 'C)))

(defun set-peg (peg stk st)
  (declare (xargs :guard (and (pegp peg)
                              (statep st)
                              (stackp stk))))
  (s peg stk st))


(defun get-peg (peg st)
  (declare (xargs :guard (and (pegp peg)
                              (statep st))))
  (g peg st))

;----------------------------------------------------------------------

(defthm new-state-statep
  (statep (new-state))
  :hints (("Goal" :in-theory (enable new-state statep))))


(defthm statep-g-peg
  (implies (and (statep st)
                (pegp p))
           (stackp (g p st)))
  :hints (("Goal" :in-theory (enable pegp stackp statep))))

(defthm statep-s-peg-stackp
  (implies (and (statep st)
                (pegp p)
                (stackp stk))
           (statep (s p stk st)))
  :hints (("Goal" :in-theory (enable pegp stackp statep))))

;----------------------------------------------------------------------
