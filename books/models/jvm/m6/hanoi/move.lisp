(in-package "HANOI")
(include-book "misc/records" :dir :system)
(include-book "state")

(acl2::set-verify-guards-eagerness 2)

(local (in-theory (enable pegp)))

(defund new-move (from to)
  (declare (xargs :guard (and (pegp from)
                              (pegp to))))
  (s 'FROM from (s 'TO to nil)))

(defund movep (m)
  (and (pegp (g 'FROM m))
       (pegp (g 'TO m))))


(defun src (m)
  (declare (xargs :guard (movep m)))
  (g 'FROM m))


(defun dest (m)
  (declare (xargs :guard (movep m)))
  (g 'TO m))

;----------------------------------------------------------------------
(defthm g-src-move-peg
  (implies (movep m)
           (pegp (g 'FROM m)))
  :hints (("Goal" :in-theory (enable movep))))

(defthm g-dest-move-peg
  (implies (movep m)
           (pegp (g 'TO m)))
  :hints (("Goal" :in-theory (enable movep))))

;----------------------------------------------------------------------
