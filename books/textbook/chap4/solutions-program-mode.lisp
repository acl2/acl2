(in-package "ACL2")

; ============================================================

; Exercise 4.1

(defun from-end (n lst)
  (nth n (reverse lst)))

; ============================================================

; Exercise 4.2

(defun update-alist (key val alist)
  (cons (cons key val) alist))

; ============================================================

; Exercise 4.3

(defun next-k (k)
  (if (evenp k)
      (/ k 2)
    (1+ (* 3 k))))

; ============================================================

; Exercise 4.4

; Here is the function mem defined earlier in the text.

(defun mem (e x)
  (if (endp x)
      nil
    (if (equal e (car x))
        t
      (mem e (cdr x)))))

(defun no-dupls-p (lst)
  (if (endp lst)
      t
    (if (mem (car lst) (cdr lst))
        nil
      (no-dupls-p (cdr lst)))))

; ============================================================

; Exercise 4.5

(defun get-keys (alist)
  (if (endp alist)
      nil
    (cons (caar alist)
          (get-keys (cdr alist)))))

; ============================================================

; Exercise 4.6

(defun del (elt lst)
  (cond ((endp lst) nil)
	((equal elt (car lst))
	 (cdr lst))
	(t (cons (car lst) (del elt (cdr lst))))))

(defun perm (x y)
  (cond ((endp x) (endp y))
        (t (and (mem (car x) y)
                (perm (cdr x) (del (car x) y))))))

; ============================================================

; Exercise 4.7

(defun update-alist-rec (key val alist)
  (cond
   ((endp alist)
    (list (cons key val)))
   ((equal key (caar alist))
    (cons (cons key val) (cdr alist)))
   (t
    (cons (car alist)
          (update-alist-rec key val (cdr alist))))))

; ============================================================

; Exercise 4.8

(defun next-k-iter-list (k)
  (declare (xargs :mode :program))
  (if (equal k 1) ; or use int= for efficiency
      '(1)
    (cons k (next-k-iter-list (next-k k)))))

(defun next-k-iter (k)
  (declare (xargs :mode :program))
  (if (equal k 1) ; or use int= for efficiency
      0
    (1+ (next-k-iter (next-k k)))))

#|

We ask that you state a relationship between these two functions.
Here is one:

(implies (and (integerp k)
	      (< 0 k))
	 (equal (len (next-k-iter-list k))
		(1+ (next-k-iter k))))
|#

; ============================================================

; Exercise 4.9

(defun next-k-max-iterations (n)
  (declare (xargs :mode :program))
  (if (equal n 1) ; or use int= for efficiency
      0
    (max (next-k-iter n)
         (next-k-max-iterations (1- n)))))

; ============================================================

; Exercise 4.10

(defun sum-base-10-digits (n)
  (declare (xargs :mode :program))
  (cond ((zp n) 0)
	((< n 10) n)
	(t (+ (mod n 10)
	      (sum-base-10-digits (floor n 10))))))

(defun cast-out-nines (n)
  (declare (xargs :mode :program))
  (cond ((equal n 9) t)
	((< n 9) nil)
	(t (cast-out-nines (sum-base-10-digits n)))))


#|

The definition of cast-out-nines is a reasonable definition when n is
assumed to be a positive integer (this is what we ask you to assume in
the problem statement).  We could have defined cast-out-nines
differently, e.g.:

(defun cast-out-nines (n)
  (declare (xargs :mode :program))
  (if (or (zp n)
          (< n 10))
      (or (equal n 0) (equal n 9))
    (cast-out-nines (sum-base-10-digits n))))

but this does not seem as clear.

|#

; ============================================================

; Exercise 4.11

; Here is the definition of fact, as given in the book.
(defun fact (n)
  (if (zp n)
      1
    (* n (fact (- n 1)))))

(defun fact-tailrec (n acc)
  (if (zp n)
      acc
    (fact-tailrec (- n 1) (* n acc))))

(defun fact1 (n)
  (fact-tailrec n 1))

; ============================================================

; Exercise 4.12

;;; Tail recursion for Exercise 4.5:

(defun get-keys-tail-rec (alist acc)
  (if (endp alist)
      (reverse acc)
    (get-keys-tail-rec (cdr alist) (cons (caar alist) acc))))

(defun get-keys1 (alist)
  (get-keys-tail-rec alist nil))

;;; Tail recursion for Exercise 4.7

(defun update-alist-tail-rec (key val alist acc)
  (cond
   ((endp alist)
    (reverse (cons (cons key val) acc)))
   ((equal key (caar alist))
    (revappend acc (cons (cons key val) (cdr alist))))
   (t (update-alist-tail-rec key val (cdr alist) (cons (car alist) acc)))))

(defun update-alist-rec1 (key val alist)
  (update-alist-tail-rec key val alist nil))

;;; Tail recursion for Exercise 4.8

(defun next-k-iter-list-tail-rec (k acc)
  (declare (xargs :mode :program))
  (if (int= k 1)
      (reverse (cons 1 acc))
    (next-k-iter-list-tail-rec (next-k k) (cons k acc))))

(defun next-k-iter-list1 (k)
  (declare (xargs :mode :program))
  (next-k-iter-list-tail-rec k nil))

(defun next-k-iter-tail-rec (k acc)
  (declare (xargs :mode :program))
  (if (equal k 1) ; or use int= for efficiency
      acc
    (next-k-iter-tail-rec (next-k k) (1+ acc))))

(defun next-k-iter1 (k)
  (declare (xargs :mode :program))
  (next-k-iter-tail-rec k 0))

;;; Tail recursion for Exercise 4.9

(defun next-k-max-iterations-tail-rec (n acc)
  (declare (xargs :mode :program))
  (if (int= n 1)
      acc
    (next-k-max-iterations-tail-rec
     (1- n)
     (max acc (next-k-iter1 n)))))

(defun next-k-max-iterations1 (n)
  (declare (xargs :mode :program))
  (next-k-max-iterations-tail-rec n 0))

; ============================================================

; Exercise 4.13

(defun split-list (x)
  (cond
   ((endp x)
    (mv nil nil))
   (t (mv-let (evens odds)
	      (split-list (cdr x))
	      (mv (cons (car x) odds) evens)))))

; ============================================================

; Exercise 4.14

(defun merge2 (x y)
  (declare (xargs :mode :program))
  (cond ((endp x) y)
	((endp y) x)
	((< (car x) (car y))
	 (cons (car x)
	       (merge2 (cdr x) y)))
	(t (cons (car y)
		 (merge2 x (cdr y))))))

; ============================================================

; Exercise 4.15

(defun mergesort (x)
  (declare (xargs :mode :program))
  (if (and (consp x)
           (consp (cdr x)))
      (mv-let (odds evens)
              (split-list x)
              (merge2 (mergesort odds) (mergesort evens)))
    x))

; ============================================================

; Exercise 4.16

(mutual-recursion

(defun acl2-basic-termp (x)
  (or (symbolp x)
      (acl2-numberp x)
      (characterp x)
      (stringp x)
      (and (consp x)
           (symbolp (car x))
           (acl2-basic-term-listp (cdr x)))))

(defun acl2-basic-term-listp (x)
  (if (consp x)
      (and (acl2-basic-termp (car x))
           (acl2-basic-term-listp (cdr x)))
    (equal x nil)))

)

; ============================================================

; Exercise 4.17

(mutual-recursion

(defun acl2-sub (new old x)
  (cond
   ((equal old x)
    new)
   ((consp x)
    (cons (car x)
          (acl2-sub-list new old (cdr x))))
   (t x)))

(defun acl2-sub-list (new old x)
  (if (consp x)
      (cons (acl2-sub new old (car x))
            (acl2-sub-list new old (cdr x)))
    nil))

)

; ============================================================

; Exercise 4.18

(mutual-recursion

(defun acl2-good-termp (x fns)
  (or (symbolp x)
      (acl2-numberp x)
      (characterp x)
      (stringp x)
      (and (consp x)
           (symbolp (car x))
           (mem (car x) fns) ; mem is defined above
           (acl2-good-term-listp (cdr x) fns))))

(defun acl2-good-term-listp (x fns)
  (if (consp x)
      (and (acl2-good-termp (car x) fns)
           (acl2-good-term-listp (cdr x) fns))
    (equal x nil)))

)

(defun acl2-value (x a)
  (cond
   ((consp x)
    (cond
     ((eq (car x) '+)
      (+ (acl2-value (cadr x) a)
	 (acl2-value (caddr x) a)))
     ((eq (car x) '*)
      (* (acl2-value (cadr x) a)
	 (acl2-value (caddr x) a)))
     ;; else (car x) is '= for good terms
     (t
      (equal (acl2-value (cadr x) a)
             (acl2-value (caddr x) a)))))
   ((or (eq x t)
        (eq x nil)
        (acl2-numberp x)
        (characterp x)
        (stringp x))
    x)
   (t ; (symbolp x) for good terms
    (let ((a-val (assoc-eq x a)))
      (if a-val
	  (cdr a-val) ; we do not want to destroy a nil binding
        0)))))

; ============================================================
(program)

; Exercise 4.19

(defun next-k-ar (k ar bound)
  (let ((next-k-try (and (< k bound)
                         (aref1 'next-k-array ar k))))
    (if next-k-try
        (mv next-k-try ar)
      (let ((next-k (next-k k)))
        (mv next-k
            (if (< k bound)
                (aset1 'next-k-array ar k next-k)
              ar))))))

(defun next-k-iterations-ar-rec (k ar bound acc)
  (if (int= k 1)
      (mv acc ar)
    (mv-let (next-k ar)
            (next-k-ar k ar bound)
            (next-k-iterations-ar-rec next-k ar bound (1+ acc)))))

(defun next-k-array (size)
  (compress1 'next-k-array
             `((:header :dimensions (,size)
                        :maximum-length ,(* size 2)
                        :default nil
                        :name next-k-array))))

(defun next-k-iterations-ar (k)
  (next-k-iterations-ar-rec k (next-k-array k) k 0))

(defun next-k-max-iterations-ar-rec (n ar bound max)
  (if (int= n 1)
      max
    (mv-let (iterations ar)
            (next-k-iterations-ar-rec n ar bound 0)
            (next-k-max-iterations-ar-rec
             (1- n)
             ar
             bound
             (max max iterations)))))

(defun next-k-max-iterations-ar (n)
  (next-k-max-iterations-ar-rec n (next-k-array n) n 0))

; ============================================================

; Exercise 4.20

(defstobj st
  ;; The prev field stores scratchwork.  The ans field is an array associating
  ;; with each i the number of iterations of next-k required to reach 1,
  (prev :type integer :initially 0)
  (ans :type (array integer (100001)) :initially -1))

(defconst *len* 100001)

; The following macro increases readability:
; (seq x form1 form2 ... formk)
; binds x to successive values of formi.
(defmacro seq (stobj &rest rst)
  (cond ((endp rst) stobj)
        ((endp (cdr rst)) (car rst))
        (t `(let ((,stobj ,(car rst)))
             (seq ,stobj ,@(cdr rst))))))

; The following function updates st with all values computed along the way to
; computing the number of iterations of next-i required to reach 1 from i.
; That number, for i, is stored in the prev field of the stobj st.
(defun fill-in (i st)
  (declare (xargs :stobjs (st)))
  (cond ((< i *len*)
	 (if (= (ansi i st) -1)
	     (seq st
		  (fill-in (next-k i) st)
		  (update-ansi i (1+ (prev st)) st)
		  (update-prev (1+ (prev st)) st))
	   (update-prev (ansi i st) st)))
	(t (seq st
		(fill-in (next-k i) st)
		(update-prev (1+ (prev st)) st)))))

; Call fill-in on all values from 1 to len, inclusive:
(defun fill-all-in (cnt len st)
  (declare (xargs :stobjs (st)))
  (cond ((> cnt len)
	 st)
	(t (seq st
		(fill-in cnt st)
		(fill-all-in (1+ cnt) len st)))))

; Find the maximum number of iterations for all integers from i to len,
; inclusive:
(defun max-st (cnt m len st)
  (declare (xargs :stobjs (st)))
  (cond ((> cnt len) m)
	(t (if (> (ansi cnt st) m)
	       (max-st (1+ cnt) (ansi cnt st) len st)
	     (max-st (1+ cnt) m len st)))))

; This function fills in st (as described for fill-in above) and then stores
; the maximum number of iterations in the prev field of st.
(defun next-k-max-iterations-stobj-aux (len st)
  (declare (xargs :stobjs (st)))
  (seq st
       (update-ansi 0 0 st)
       (update-ansi 1 0 st)
       (fill-all-in 2 len st)
       (update-prev (max-st 2 0 len st) st)))

(defun next-k-max-iterations-stobj (len st)
  (declare (xargs :stobjs (st)))
  (let ((st (next-k-max-iterations-stobj-aux len st)))
    (mv (prev st) st)))

; ============================================================

; Exercise 4.21

; Here are some run times.

#|
ACL2>(time (next-k-max-iterations 50000)) ; basic
real time : 73.000 secs
run time  : 67.560 secs
323
ACL2>(time (next-k-max-iterations1 50000)) ; tail recursive
real time : 35.000 secs
run time  : 33.270 secs
323
ACL2>(time (next-k-max-iterations-ar 50000)) ; arrays
real time : 14.000 secs
run time  : 12.720 secs
323
ACL2>(time (next-k-max-iterations-stobj 50000 st))
real time : 2.000 secs
run time  : 1.690 secs
323
|#
