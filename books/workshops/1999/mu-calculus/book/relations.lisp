(in-package "RELATIONS")
(include-book "fast-sets")

(defun relationp (r)
  (cond ((atom r) (eq r nil))
        (t (and (consp (car r))
                (true-listp (cdar r))
                (relationp (cdr r))))))

(defun value-of (x alist)
  (cdr (assoc-equal x alist)))

(defun image-aux (X r tmp)
  (if (endp X)
      tmp
    (image-aux (cdr X) r
               (set-union (value-of (car X) r) tmp))))

(defun image (X r)
  (image-aux X r nil))

(defun range-aux (r tmp)
  (if (consp r)
      (range-aux (cdr r) (set-union (cdar r) tmp))
    tmp))

(defun range (r)
  (range-aux r nil))

(defun inverse-step-aux (st r tmp)
  (if (endp r)
      tmp
    (inverse-step-aux st (cdr r)
                      (if (in st (cdar r))
                          (add (caar r) tmp)
                        tmp))))

(defun inverse-step (st r)
  (inverse-step-aux st r nil))

(defun inverse-aux (r ran tmp)
  (if (endp ran)
      tmp
    (inverse-aux r (cdr ran)
        (acons (car ran) (inverse-step (car ran) r) tmp))))

(defun inverse (r)
  (inverse-aux r (range r) nil))

(defun rel-range-subset (r X)
  (cond ((endp r) t)
	(t (and (=< (cdar r) X)
		(rel-range-subset (cdr r) X)))))
