
(in-package "ACL2")


;; "logical nfix"
(defmacro lnfix (x)
  `(mbe :logic (nfix ,x) :exec ,x))

;; This function crops up all over the place.

(defun numlist (start by n)
  (declare (xargs :guard (and (acl2-numberp start)
                              (acl2-numberp by)
                              (natp n))))
  (if (mbe :logic (zp n) :exec (= n 0))
      nil
    (cons start (numlist (+ start by) by (1- (lnfix n))))))


(defthm len-numlist
  (equal (len (numlist start by n))
         (nfix n)))

