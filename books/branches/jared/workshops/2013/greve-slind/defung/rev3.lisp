(in-package "ACL2")

(include-book "defung")

(def::ung rev3 (x)
  (declare (xargs :signature ((true-listp) true-listp)
		  :default-value x))
  (cond
   ((endp x) nil)
   ((endp (cdr x)) (list (car x)))
   (t
    ;; a.b*.c
    (let* ((b.c       (cdr x))
	   (c.rev-b   (rev3 b.c))
	   (rev-b     (cdr c.rev-b))
	   (b         (rev3 rev-b))
	   (a         (car x))
	   (a.b       (cons a b))
	   (rev-b.a   (rev3 a.b))
	   (c         (car c.rev-b))
	   (c.rev-b.a (cons c rev-b.a)))
      c.rev-b.a))))

(defthm len-rev3
  (equal (len (rev3 x))
	 (len x))
  :otf-flg t
  :hints (("Goal" :in-theory (enable use-rev3-total-induction))))

(defthm consp-rev3
  (equal (consp (rev3 x))
	 (consp x))
  :otf-flg t
  :hints (("Goal" :in-theory (enable use-rev3-total-induction))))

(def::total rev3 (x)
  (declare (xargs :measure (len x)))
  t)

;; This is probably true w/out the termination proof ..
;; but it is easier here.
(def::signature rev3 (t) true-listp)

(def::un rev (x)
  (declare (xargs :signature ((true-listp) true-listp)))
  (if (endp x) nil
    (append (rev (cdr x)) (list (car x)))))

(def::signature rev (t) true-listp)

(defun list-fix (x)
  (if (atom x) nil
    (cons (car x) (list-fix (cdr x)))))

(defthm list-fix-of-true-listp
  (implies
   (true-listp x)
   (equal (list-fix x) x)))

(defthm rev-rev
  (equal (rev (rev x)) 
	 (list-fix x)))

(defthm consp-rev
  (equal (consp (rev x))
	 (consp x)))

(def::signature cdr (true-listp) true-listp)

(defthm rev3-reduction
  (equal (rev3 x) (rev x))
  :hints (("Goal" :induct (rev3 x))))
