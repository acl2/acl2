(in-package "ACL2")

; Turn on guard verification, where missing guards are viewed implicitly as t.
(set-verify-guards-eagerness 2)

; ============================================================

; Exercise 4.1

(defthm true-listp-revappend
  (implies (true-listp y)
           (true-listp (revappend x y)))
  :rule-classes :type-prescription)

(defun from-end (n lst)
  (declare (xargs :guard (and (integerp n)
                              (<= 0 n)
                              (true-listp lst))))
  (nth n (reverse lst)))

; ============================================================

; Exercise 4.2

(defun update-alist (key val alist)
  (cons (cons key val) alist))

; ============================================================

; Exercise 4.3

(defun next-k (k)
  (declare (xargs :guard (and (integerp k) (> k 0))))
  (if (evenp k)
      (/ k 2)
    (1+ (* 3 k))))

#|

Because the guard for evenp requires that its argument is an integer,
the definition of next-k (with body as above) that has the most
general guard is:

(defun next-k (k)
  (declare (xargs :guard (integerp k)))
  (if (evenp k)
      (/ k 2)
    (1+ (* 3 k))))

The extra condition (> k 0) was added to make clear the intended
domain.  Recall that in the book, we imply that k is a positive
integer.

|#


; ============================================================

; Exercise 4.4

; Here is the function mem defined earlier in the text, but with
; guards.

(defun mem (e x)
  (declare (xargs :guard (true-listp x)))
  (if (endp x)
      nil
    (if (equal e (car x))
        t
      (mem e (cdr x)))))

(defun no-dupls-p (lst)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      t
    (if (mem (car lst) (cdr lst))
        nil
      (no-dupls-p (cdr lst)))))

; ============================================================

; Exercise 4.5

(defun get-keys (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      nil
    (cons (caar alist)
          (get-keys (cdr alist)))))

; ============================================================

; Exercise 4.6

(defun del (elt lst)
  (declare (xargs :guard (true-listp lst)))
  (cond ((endp lst) nil)
	((equal elt (car lst))
	 (cdr lst))
	(t (cons (car lst) (del elt (cdr lst))))))

(defun perm (x y)
  (declare (xargs :guard (and (true-listp x) (true-listp y))))
  (cond ((endp x) (endp y))
        (t (and (mem (car x) y)
                (perm (cdr x) (del (car x) y))))))

; ============================================================

; Exercise 4.7

(defun update-alist-rec (key val alist)
  (declare (xargs :guard (alistp alist)))
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
  (declare (xargs :guard (and (integerp k) (> k 0))
                  :mode :program))
  (if (equal k 1) ; or use int= for efficiency
      '(1)
    (cons k (next-k-iter-list (next-k k)))))

(defun next-k-iter (k)
  (declare (xargs :guard (and (integerp k) (> k 0))
                  :mode :program))
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
  (declare (xargs :guard (and (integerp n) (> n 0))
                  :mode :program))
  (if (equal n 1) ; or use int= for efficiency
      0
    (max (next-k-iter n)
         (next-k-max-iterations (1- n)))))

; ============================================================

; Exercise 4.10

#|

Some observations about the following encapsulate.

1.  We use the ihs-lemmas book in order to reduce the effort required
to prove termination of the functions.  We suggest that you acquaint
yourself with the books that come with the ACL2 distribution.

2.  The include-book event is local because we do not want the
ihs-lemmas book to interfere with the rest of this book.

3.  The definition of cast-out-nines is a reasonable definition when n
is assumed to be a positive integer (this is what we ask you to assume
in the problem statement).  However, the termination argument is
complicated slightly because on a non-integer, we call cast-out-nines
recursively.  We could have defined cast-out-nines differently, e.g.:

(defun cast-out-nines (n)
  (declare (xargs :guard (and (integerp n)
                              (< 0 n))
		  :measure (nfix n)))
  (if (or (zp n)
          (< n 10))
      (or (equal n 0) (equal n 9))
    (cast-out-nines (sum-base-10-digits n))))

but this does not seem as clear.

|#

(encapsulate
 nil
 (local (include-book "ihs/ihs-lemmas" :dir :system))
 (defun sum-base-10-digits (n)
   (declare (xargs :guard (and (integerp n)
			       (< 0 n))))
   (cond ((zp n) 0)
	 ((< n 10) n)
	 (t (+ (mod n 10)
	       (sum-base-10-digits (floor n 10))))))

 (defthm sum-base-10-digits-type
   (and (integerp (sum-base-10-digits n))
	(<= 0 (sum-base-10-digits n)))
   :rule-classes :type-prescription)

 (defthm sum-base-10-digits-goes-down
   (implies (and (integerp n) (<= 10 n))
	    (< (sum-base-10-digits n)
	       n)))

 (defun cast-out-nines (n)
   (declare (xargs :guard (and (integerp n)
			       (< 0 n))
		   :measure (if (integerp n)
				(nfix n)
			      1)))
   (cond ((equal n 9) t)
	 ((< n 9) nil)
	 (t (cast-out-nines (sum-base-10-digits n))))))

; ============================================================

; Exercise 4.11

; Here is the definition of fact, as given in the book, but with guards added.
(defun fact (n)
  (declare (xargs :guard (and (integerp n)
                              (<= 0 n))))
  (if (zp n)
      1
    (* n (fact (- n 1)))))

(defun fact-tailrec (n acc)
  (declare (xargs :guard (and (integerp n)
                              (<= 0 n)
                              (acl2-numberp acc))))
  (if (zp n)
      acc
    (fact-tailrec (- n 1) (* n acc))))

(defun fact1 (n)
  (declare (xargs :guard (and (integerp n)
                              (<= 0 n))))
  (fact-tailrec n 1))

; ============================================================

; Exercise 4.12

;;; Tail recursion for Exercise 4.5:

(defun get-keys-tail-rec (alist acc)
  (declare (xargs :guard (and (alistp alist)
                              (true-listp acc))))
  (if (endp alist)
      (reverse acc)
    (get-keys-tail-rec (cdr alist) (cons (caar alist) acc))))

(defun get-keys1 (alist)
  (declare (xargs :guard (alistp alist)))
  (get-keys-tail-rec alist nil))

;;; Tail recursion for Exercise 4.7

(defun update-alist-tail-rec (key val alist acc)
  (declare (xargs :guard (and (alistp acc) (alistp alist))))
  (cond
   ((endp alist)
    (reverse (cons (cons key val) acc)))
   ((equal key (caar alist))
    (revappend acc (cons (cons key val) (cdr alist))))
   (t (update-alist-tail-rec key val (cdr alist) (cons (car alist) acc)))))

(defun update-alist-rec1 (key val alist)
  (declare (xargs :guard (alistp alist)))
  (update-alist-tail-rec key val alist nil))

;;; Tail recursion for Exercise 4.8

(defun next-k-iter-list-tail-rec (k acc)
  (declare (xargs :guard (and (integerp k) (> k 0) (true-listp acc))
                  :mode :program))
  (if (int= k 1)
      (reverse (cons 1 acc))
    (next-k-iter-list-tail-rec (next-k k) (cons k acc))))

(defun next-k-iter-list1 (k)
  (declare (xargs :guard (and (integerp k) (> k 0))
                  :mode :program))
  (next-k-iter-list-tail-rec k nil))

(defun next-k-iter-tail-rec (k acc)
  (declare (xargs :guard (and (integerp k) (> k 0) (integerp acc))
                  :mode :program))
  (if (equal k 1) ; or use int= for efficiency
      acc
    (next-k-iter-tail-rec (next-k k) (1+ acc))))

(defun next-k-iter1 (k)
  (declare (xargs :guard (and (integerp k) (> k 0))
                  :mode :program))
  (next-k-iter-tail-rec k 0))

;;; Tail recursion for Exercise 4.9

(defun next-k-max-iterations-tail-rec (n acc)
  (declare (xargs :guard (and (integerp n)
                              (> n 0)
                              (integerp acc))
                  :mode :program))
  (if (int= n 1)
      acc
    (next-k-max-iterations-tail-rec
     (1- n)
     (max acc (next-k-iter1 n)))))

(defun next-k-max-iterations1 (n)
  (declare (xargs :guard (and (integerp n)
                              (> n 0))
                  :mode :program))
  (next-k-max-iterations-tail-rec n 0))

; ============================================================

; Exercise 4.13

(defun split-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond
   ((endp x)
    (mv nil nil))
   (t (mv-let (evens odds)
	      (split-list (cdr x))
	      (mv (cons (car x) odds) evens)))))

; ============================================================

; Exercise 4.14

(defun merge2 (x y)
  (declare (xargs :guard (and (rational-listp x)
                              (rational-listp y))
                  :measure (+ (len x) (len y))))
  (cond ((endp x) y)
	((endp y) x)
	((< (car x) (car y))
	 (cons (car x)
	       (merge2 (cdr x) y)))
	(t (cons (car y)
		 (merge2 x (cdr y))))))

; ============================================================

; Exercise 4.15

(defthm rational-listp-mv-nth-split-list
  (implies (rational-listp x)
           (and
            (rational-listp (mv-nth 0 (split-list x)))
            (rational-listp (mv-nth 1 (split-list x))))))

(defthm len-mv-nth-split-list
  (and (<= (len (mv-nth 0 (split-list x)))
           (len x))
       (<= (len (mv-nth 1 (split-list x)))
           (len x))
       (implies (consp x)
                (< (len (mv-nth 1 (split-list x)))
                   (len x))))
  :rule-classes :linear)

(in-theory (disable mv-nth))

(defun mergesort (x)
  (declare (xargs :guard (rational-listp x)
                  :measure (len x)
                  :verify-guards nil))
  (if (and (consp x)
           (consp (cdr x)))
      (mv-let (odds evens)
              (split-list x)
              (merge2 (mergesort odds) (mergesort evens)))
    x))

(defthm rational-listp-mergesort
  (implies (rational-listp x)
           (rational-listp (mergesort x))))

(verify-guards mergesort)

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
  (declare (xargs :guard (and (acl2-basic-termp new)
                              (acl2-basic-termp old)
                              (acl2-basic-termp x))))
  (cond
   ((equal old x)
    new)
   ((consp x)
    (cons (car x)
          (acl2-sub-list new old (cdr x))))
   (t x)))

(defun acl2-sub-list (new old x)
  (declare (xargs :guard (and (acl2-basic-termp new)
                              (acl2-basic-termp old)
                              (acl2-basic-term-listp x))))
  (if (consp x)
      (cons (acl2-sub new old (car x))
            (acl2-sub-list new old (cdr x)))
    nil))

)

; ============================================================

; Exercise 4.18

(mutual-recursion

(defun acl2-good-termp (x fns)
  (declare (xargs :guard (true-listp fns))) ;because of call of mem
  (or (symbolp x)
      (acl2-numberp x)
      (characterp x)
      (stringp x)
      (and (consp x)
           (symbolp (car x))
           (mem (car x) fns) ; mem is defined above
           (acl2-good-term-listp (cdr x) fns))))

(defun acl2-good-term-listp (x fns)
  (declare (xargs :guard (true-listp fns)))
  (if (consp x)
      (and (acl2-good-termp (car x) fns)
           (acl2-good-term-listp (cdr x) fns))
    (equal x nil)))

)

(defun safe-times (x y)
  (if (and (acl2-numberp x)
           (acl2-numberp y))
      (* x y)
    0))

(defun safe-plus (x y)
  (if (and (acl2-numberp x)
           (acl2-numberp y))
      (+ x y)
    0))

(defun acl2-value (x a)
  (declare (xargs :guard (and (acl2-good-termp x '(+ * =))
                              (symbol-alistp a))))
  (cond
   ((consp x)
    (cond
     ((eq (car x) '+)
      (safe-plus (acl2-value (cadr x) a)
                 (acl2-value (caddr x) a)))
     ((eq (car x) '*)
      (safe-times (acl2-value (cadr x) a)
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

; Exercise 4.19

(defun next-k-ar (k ar bound)
  (declare (xargs :guard (and (integerp k)
                              (> k 0)
                              (integerp bound)
                              (< 0 bound)
                              (array1p 'next-k-array ar))
                  :mode :program))
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
  (declare (xargs :guard (and (integerp k)
                              (> k 0)
                              (integerp bound)
                              (< 0 bound)
                              (integerp acc)
                              (array1p 'next-k-array ar))
                  :mode :program))
  (if (int= k 1)
      (mv acc ar)
    (mv-let (next-k ar)
            (next-k-ar k ar bound)
            (next-k-iterations-ar-rec next-k ar bound (1+ acc)))))

(defun next-k-array (size)
  (declare (xargs :guard (and (integerp size)
                              (> size 0))
                  :mode :program))
  (compress1 'next-k-array
             `((:header :dimensions (,size)
                        :maximum-length ,(* size 2)
                        :default nil
                        :name next-k-array))))

(defun next-k-iterations-ar (k)
  (declare (xargs :guard (and (integerp k)
                              (> k 0))
                  :mode :program))
  (next-k-iterations-ar-rec k (next-k-array k) k 0))

(defun next-k-max-iterations-ar-rec (n ar bound max)
  (declare (xargs :guard (and (integerp n) (> n 0))
                  :mode :program))
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
  (declare (xargs :guard (and (integerp n) (> n 0))
                  :mode :program))
  (next-k-max-iterations-ar-rec n (next-k-array n) n 0))

; ============================================================

; Exercise 4.20

(defstobj st
  ;; The prev field stores scratchwork.  The ans field is an array associating
  ;; with each i the number of iterations of next-k required to reach 1,
  (prev :type integer :initially 0)
  (ans :type (array integer (100001)) :initially -1))

(defconst *len* 100001)

(program)

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
