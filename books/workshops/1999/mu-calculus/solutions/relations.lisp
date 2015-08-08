(in-package "RELATIONS")

(include-book "fast-sets")

(defun relationp (r)
  (declare (xargs :guard t))
  (cond ((atom r) (eq r nil))
        (t (and (consp (car r))
                (true-listp (cdar r))
                (relationp (cdr r))))))

(defthm relationp->alistp
  (implies (relationp x)
           (alistp x))
  :rule-classes :forward-chaining)

(defthm true-list-relation-cdr
  (implies (relationp alist)
           (true-listp (cdr (assoc-equal x alist)))))

(defthm relation-put-assoc-equal
  (implies (and (relationp val)
                (true-listp s))
          (relationp (put-assoc-equal v s val))))

(defun value-of (x alist)
  (declare (xargs :guard (alistp alist)))
  (cdr (assoc-equal x alist)))

(defung image-aux (X r tmp)
  "The image of set X under relation r (if tmp=nil)"
  (declare (xargs :guard (and (relationp r) (true-listp X)
                              (true-listp tmp))))
  ((implies (true-listp tmp) (true-listp (image-aux X r tmp))))
  (if (endp X)
      tmp
    (image-aux (cdr X) r
               (set-union (value-of (car X) r) tmp))))

(defung image (X r)
  "The image of set X under relation r"
  (declare (xargs :guard (and (relationp r) (true-listp X))))
  ((true-listp (image X r)))
  (image-aux X r nil))

(defung range-aux (r tmp)
  "The range of relation r"
  (declare (xargs :guard (and (relationp r) (true-listp tmp))))
  ((implies (true-listp tmp) (true-listp (range-aux r tmp))))
  (if (consp r)
      (range-aux (cdr r) (set-union (cdar r) tmp))
    tmp))

; Exercise 14
(defung range (r)
  "The range of relation r"
  (declare (xargs :guard (relationp r)))
  ((true-listp (range r)))
  (range-aux r nil))

(defung inverse-step-aux (st r tmp)
"Creates a list of all the states from which st is reachable
in one step."
  (declare (xargs :guard (and (relationp r) (true-listp tmp))))
  ((implies (true-listp tmp) (true-listp (inverse-step-aux st r tmp))))
  (if (endp r)
      tmp
    (inverse-step-aux st (cdr r)
                      (if (in st (cdar r))
                          (add (caar r) tmp)
                        tmp))))

(defung inverse-step (st r)
"Creates a list of all the states from which st is reachable
in one step."
  (declare (xargs :guard (relationp r)))
  ((true-listp (inverse-step st r)))
  (inverse-step-aux st r nil))

(defung inverse-aux (r ran tmp)
  "Creates the converse relation of r."
  (declare (xargs :guard (and (relationp r) (true-listp ran) (relationp tmp))))
  ((implies (relationp tmp) (relationp (inverse-aux r ran tmp))))
  (if (endp ran)
      tmp
    (inverse-aux r (cdr ran)
        (acons (car ran) (inverse-step (car ran) r) tmp))))

; Exercise 15
(defung inverse (r)
  "r^{-1}, the inverse of relation r"
  (declare (xargs :guard (relationp r)))
  ((relationp (inverse r)))
  (inverse-aux r (range r) nil))

(in-theory (disable image))

(defthm assoc-equal-put-assoc-equal
 (equal (assoc-equal x (put-assoc-equal z y val))
        (if (equal x z)
            (cons x y)
          (assoc-equal x val))))

(defthm put-assoc-equal-twice
  (equal (put-assoc-equal x z (put-assoc-equal x y val))
         (put-assoc-equal x z val)))

(defun rel-range-subset (r X)
  (cond ((endp r) t)
	(t (and (=< (cdar r) X)
		(rel-range-subset (cdr r) X)))))


(defthm expand-relation-ok
  (implies (and (rel-range-subset r st)
                (=< y st))
           (rel-range-subset (put-assoc-equal b y r) st)))

(defthm check-relation-ok-ok
  (implies (rel-range-subset r st)
           (=< (cdr (assoc-equal x r)) st)))

(defthm =<-image-aux-rel-ok
  (implies (and (rel-range-subset r st)
                (=< x st))
           (=< (relations::image-aux y r x) st)))

; Exercise 16, part 1
(defthm =<-image-rel-ok
  (implies (rel-range-subset r X)
           (=< (image Y r) X))
  :hints (("Goal" :in-theory (enable image))))

; Exercise 16, part 2
(defthm =<-image-rel-ok2
  (implies (and (rel-range-subset r X)
                (=< X Y))
           (rel-range-subset r Y)))

