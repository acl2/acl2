; Copyright (C) 2019, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "MODAPP")

; ---
; G1 functions

(defun$ square (x) (* x x))

(defun$ cube (x) (* x (square x)))

(defun$ my-append1 (x y)
  (if (consp x)
      (cons (car x) (my-append1 (cdr x) y))
      y))

(defun$ my-rev (x)
  (if (consp x)
      (my-append1 (my-rev (cdr x)) (cons (car x) nil))
      nil))

(defun$ nats (n)
  (if (zp n)
      nil
      (cons n (nats (- n 1)))))

; This next pair illustrate the idea that a function, e.g., expt-2-and-expt-3,
; can have a badge in the badge-table without having a warrant, and then be
; used in a function with a warrant, e.g., expt-5.

(defun$ expt-2-and-expt-3 (x)
  (let ((x2 (* x x)))
    (mv x2 (* x x2))))

(defun$ expt-5 (x)
  (mv-let (x2 x3)
    (expt-2-and-expt-3 x)
    (* x2 x3)))

(defun$ ok-fnp (fn)
  (and (not (equal fn 'QUOTE))
       (not (equal fn 'IF))
       (tamep `(,fn X))))

; The following demonstrates that we can model a G1 function that uses a local
; stobj.  This also shows that not every subfunction of a tame function need be
; badged (i.e., count-atoms1 is unbadgeable because it traffics in stobjs, but
; its caller, count-atoms, can be badged).

(defstobj st (counter :type integer :initially 0))

(defun count-atoms1 (x st)
  (declare (xargs :stobjs (st)))
  (cond ((atom x)
         (update-counter (+ 1 (counter st)) st))
        (t (let ((st (count-atoms1 (car x) st)))
             (count-atoms1 (cdr x) st)))))

(defun$ count-atoms (x)
  (with-local-stobj
    st
    (mv-let (val st)
      (let ((st (count-atoms1 x st)))
        (mv (counter st) st))
      val)))

; ---
; G2 functions

(defun$ collect (lst fn)
  (cond ((endp lst) nil)
        (t (cons (apply$ fn (list (car lst)))
                 (collect (cdr lst) fn)))))

(defun$ sumlist (lst fn)
  (cond ((endp lst) 0)
        (t (+ (apply$ fn (list (car lst)))
              (sumlist (cdr lst) fn)))))

(defun$ sumlist-with-params (lst fn params)
  (cond ((endp lst) 0)
        (t (+ (apply$ fn (cons (car lst) params))
              (sumlist-with-params (cdr lst) fn params)))))

(defun$ filter (lst fn)
  (cond ((endp lst) nil)
        ((apply$ fn (list (car lst)))
         (cons (car lst) (filter (cdr lst) fn)))
        (t (filter (cdr lst) fn))))

(defun$ all (lst fn)
  (cond ((endp lst) t)
        (t (and (apply$ fn (list (car lst)))
                (all (cdr lst) fn)))))

(defun$ xists (lst fn)
; Note this function is Boolean, which is why we didn't define it with OR.
  (cond ((endp lst) nil)
        ((apply$ fn (list (car lst))) t)
        (t (xists (cdr lst) fn))))

(defun$ maxlist (lst fn)
  (cond ((endp lst) nil)
        ((endp (cdr lst)) (apply$ fn (list (car lst))))
        (t (max (apply$ fn (list (car lst)))
                (maxlist (cdr lst) fn)))))

(defun$ collect-on (lst fn)
  (cond ((endp lst) nil)
        (t (cons (apply$ fn (list lst))
                 (collect-on (cdr lst) fn)))))

(defun$ collect-tips (x fn)
  (cond ((atom x) (apply$ fn (list x)))
        (t (cons (collect-tips (car x) fn)
                 (collect-tips (cdr x) fn)))))

(defun$ apply$2 (fn x y)
  (apply$ fn (list x y)))

; These two functions illustrate getting further away from apply$.

(defun$ apply$2x (fn x y)
  (apply$2 fn x y))

(defun$ apply$2xx (fn x y)
  (apply$2x fn x y))

; A Russell-like function: The classic russell function would be

; ( defun$ russell (fn)
;   (not (apply$ fn (list fn))))

; But this abuses our classification system because fn is used both in a
; functional slot and a vanilla slot.  However, the following function raises
; the same problems as Russell's and is admissible here.

(defun$ russell (fn x)
  (not (apply$ fn (list x x))))

; Of interest, of course, is (russell 'russell 'russell) because the
; naive apply$ property would give us:
; (russell 'russell 'russell)                            {def russell}
; = (not (apply$ 'russell (list 'russell 'russell)))     {naive apply$}
; = (not (russell 'russell 'russell))

(defun$ foldr (lst fn init)
  (if (endp lst)
      init
      (apply$ fn
              (list (car lst)
                    (foldr (cdr lst) fn init)))))

(defun$ foldl (lst fn ans)
  (if (endp lst)
      ans
      (foldl (cdr lst)
             fn
             (apply$ fn (list (car lst) ans)))))

(defun$ collect-from-to (i max fn)
  (declare (xargs :measure (nfix (- (+ 1 (ifix max)) (ifix i)))))
  (let ((i (ifix i))
        (max (ifix max)))
    (cond
     ((> i max)
      nil)
     (t (cons (apply$ fn (list i))
              (collect-from-to (+ i 1) max fn))))))

(defun$ collect* (lst fn)
  (if (endp lst)
      nil
      (cons (apply$ fn (car lst))
            (collect* (cdr lst) fn))))

(defun$ collect2 (lst fn1 fn2)
  (if (endp lst)
      nil
      (cons (cons (apply$ fn1 (list (car lst)))
                  (apply$ fn2 (list (car lst))))
            (collect2 (cdr lst) fn1 fn2))))

(defun$ recur-by-collect (lst fn)
  (declare (xargs :measure (len lst)))
  (if (endp lst)
      nil
      (cons (car lst)
	    (recur-by-collect (collect (cdr lst) fn) fn))))

(defun$ prow (lst fn)
  (cond ((or (endp lst) (endp (cdr lst)))
         nil)
        (t (cons (apply$ fn (list (car lst) (cadr lst)))
                 (prow (cdr lst) fn)))))

(defun$ prow* (lst fn)
  (declare (xargs :measure (len lst)))
  (cond ((or (endp lst)
             (endp (cdr lst)))
         (apply$ fn (list lst lst)))
        (t (prow* (prow lst fn) fn))))

; These are nonrecursive mapping functions, the first of which
; is un-warranted because it returns multiple values.

(defun$ fn-2-and-fn-3 (fn x)
; Return (mv (fn x x) (fn x (fn x x)))
  (let ((x2 (apply$ fn (list x x))))
    (mv x2 (apply$ fn (list x x2)))))

(defun$ fn-5 (fn x)
  (mv-let (x2 x3)
    (fn-2-and-fn-3 fn x)
    (apply$ fn (list x2 x3))))

(defun$ map-fn-5 (lst fn)
  (if (endp lst)
      nil
      (cons (fn-5 fn (car lst))
            (map-fn-5 (cdr lst) fn))))

(defun$ sumlist-expr (lst expr alist)
  (cond ((endp lst) 0)
        (t (+ (ev$ expr (cons (cons 'x (car lst)) alist))
              (sumlist-expr (cdr lst) expr alist)))))

(defun$ twofer (lst fn xpr alist)
  (if (endp lst)
      nil
      (cons (cons (apply$ fn (list (car lst)))
                  (ev$ xpr (cons (cons 'TAIL lst) alist)))
            (twofer (cdr lst) fn xpr alist))))

; The following function stresses the method of eliminating tame calls of
; mapping functions from mapping functions.  The sumlist is tame.  The fact
; that it occurs in the apply$ is irrelevant, it just yields a number to be
; used as data for fn.  But the sumlist involves foldr and so eliminating it
; involves defining some helpers and proving that we did it right BEFORE we
; prove sumlist! is sumlist and foldr! is foldr.

(defun$ collect-a (lst fn)
  (cond ((endp lst) nil)
        (t (cons (apply$ fn (list
                             (sumlist (nats (car lst))
                                      '(lambda (i)
                                         (foldr (nats i)
                                                '(lambda (j k)
                                                   (binary-* (square j) k))
                                                '1)))))
                 (collect-a (cdr lst) fn)))))

(defun$ collect-b (lst fn)
  (cond ((endp lst) nil)
        (t (cons (apply$ fn (list (sumlist (nats (car lst)) fn)))
                 (collect-b (cdr lst) fn)))))

(defun$ collect-c (lst fn1 fn2)
  (cond ((endp lst) nil)
        (t (cons (apply$ fn1 (list (sumlist (nats (car lst)) fn2)))
                 (collect-c (cdr lst) fn1 fn2)))))

(defun$ collect-d (lst fn1 fn2)
  (if (endp lst)
      nil
      (cons (cons (apply$ fn1 (list (car lst)))
                  (apply$ fn2 (list (car lst))))
            (collect-d (cdr lst) fn1 fn2))))

(defun$ collect-e (lst fn)
  (if (endp lst)
      nil
      (cons (collect-d lst fn '(lambda (x) (binary-+ '10 (square x))))
            (collect-e (cdr lst) fn))))

(defun$ my-apply-2 (fn1 fn2 x)
  (list (apply$ fn1 x) (apply$ fn2 x)))

(defun$ my-apply-2-1 (fn x)
  (my-apply-2 fn fn x))

; These are G2 functions even though they do not have :FN/:EXPR args.

(defun$ collect-my-rev (lst)
  (collect lst 'MY-REV))

(defun$ my-append2 (x y)
  (foldr x 'CONS y))

(defun$ sqnats (x)
  (collect (filter x 'NATP) 'SQUARE))

(defun$ sum-of-products (lst)
  (sumlist lst
           '(LAMBDA (X)
                    (FOLDR X
                           '(LAMBDA (I A)
                                    (BINARY-* I A))
                           '1))))

(defun$ collect-composition (lst fn gn)
  (if (endp lst)
      nil
      (cons (apply$ fn (list (apply$ gn (list (car lst)))))
            (collect-composition (cdr lst) fn gn))))

(defun$ collect-x1000 (lst fn)
  (collect-composition lst fn '(lambda (x) (binary-* '1000 x))))

(defun$ collect-x1000-caller (lst fn)
  (if (endp lst)
      nil
      (cons (collect-x1000 (car lst) fn)
            (collect-x1000-caller (cdr lst) fn))))

(defun$ guarded-collect (lst fn)
  (declare (xargs :guard (true-listp lst)))
  (if (endp lst)
      nil
      (cons (apply$ fn (list (car lst)))
            (guarded-collect (cdr lst) fn))))

; And two lexicographic measures, one of length 2 and the other of length 3.

(defun$ ack$ (fn k n m)
  (declare (xargs :measure (llist k m)
                  :well-founded-relation l<))
  (if (zp k)
      (apply$ fn (list (+ 1 n)))
      (if (zp m)
          (if (equal k 2)
              0
              (if (equal k 3)
                  1
                  n))
          (ack$ fn
                (- k 1)
                (ack$ fn k n (- m 1))
                n))))

(defun$ silly$ (fn k n m)
  (declare (xargs :measure (llist k n m)
                  :well-founded-relation l<))
  (if (zp k)
      (apply$ fn (list n))
      (if (zp n)
          (apply$ fn (list k))
          (if (zp m)
              (apply$ fn (list n))
              (silly$ fn
                      (- k 1)
                      (silly$ fn
                              k
                              (- n 1)
                              (silly$ fn
                                      k
                                      n
                                      (- m 1)))
                      m)))))

