; Copyright (C) 2016, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Sample Chronology for which We Will Establish the Apply Hypotheses

; The complete list of functions defined with defun$ in this version of the
; chronology is given below.  The list is in the same order in which the
; functions are defined here.  We include this list to make it easier to
; confirm that model.lisp defines them all.

#||
ap
rev
palindromify-list
list-of-true-listsp
list-of-list-of-true-listsp
ok-fnp
collect
sumlist
sumlist-with-params
filter
all
collect-on
collect-tips
apply$2
russell
foldr
collect-from-to
collect2
recur-by-collect
collect-rev
||#

(in-package "ACL2")

(include-book "misc/eval" :dir :system) ; for testing only

(include-book "apply")

; -----------------------------------------------------------------
; Definitions

; For the sake of later modeling, we exhibit all of our defuns together, even
; though some are only used to state theorems about others.  We group them
; into: ordinary functions, mapping functions, and tame instances of mapping
; functions.  We don't prove theorems about most of these functions in this
; chronology.  We define them simply to exercise the process of developing a
; model.

; ---
; Ordinary Functions

(defun$ ap (x y)
  (if (consp x)
      (cons (car x) (ap (cdr x) y))
      y))

(defun$ rev (x)
  (if (consp x)
      (ap (rev (cdr x)) (cons (car x) nil))
      nil))

(defun$ palindromify-list (lst)
  (cond ((endp lst) nil)
        (t (cons (ap (car lst) (rev (car lst)))
                 (palindromify-list (cdr lst))))))

(defun$ list-of-true-listsp (lst)
  (cond ((atom lst) (equal lst nil))
        (t (and (true-listp (car lst))
                (list-of-true-listsp (cdr lst))))))

(defun$ list-of-list-of-true-listsp (lst)
  (cond ((atom lst) (equal lst nil))
        (t (and (list-of-true-listsp (car lst))
                (list-of-list-of-true-listsp (cdr lst))))))

(defun$ ok-fnp (fn)
  (and (not (equal fn 'QUOTE))
       (not (equal fn 'IF))
       (tamep `(,fn X))))

; ---
; Mapping Functions

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

; A Russell-like function: The classic russell function would be

; (defun$ russell (fn)
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

(defun$ collect-from-to (i max fn)
  (declare (xargs :measure (nfix (- (+ 1 (ifix max)) (ifix i)))))
  (let ((i (ifix i))
        (max (ifix max)))
    (cond
     ((> i max)
      nil)
     (t (cons (apply$ fn (list i))
              (collect-from-to (+ i 1) max fn))))))

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

; ---
; Tame Instances

(defun$ collect-rev (lst)
  (collect lst 'REV))


; -----------------------------------------------------------------
; Some Sample Theorems about Mapping Functions

(defthm recur-by-collect-example
  (equal (recur-by-collect '(1 1 1) '(lambda (x) (binary-+ '1 x)))
         '(1 2 3))
  :rule-classes nil)

(defthm collect-ap
  (equal (collect (ap a b) fn)
         (ap (collect a fn)
             (collect b fn))))

(must-fail
 (with-prover-step-limit
  10000
  (defthm theorem-about-collect-ap-rev
    (equal (collect lst '(lambda (e) (ap e (rev e))))
           (palindromify-list lst))
    :rule-classes nil)))

; But this succeeds in 1671 steps.
(defthm theorem-about-collect-ap-rev
  (implies (Applicablep AP REV)
           (equal (collect lst '(lambda (e) (ap e (rev e))))
                  (palindromify-list lst)))
  :rule-classes nil)

; Here is another theorem.

; Of course, this concept is the same as a nest of all, and we can prove
; that (but we don't make it a rule).

; By the way, this theorem has no applicablep hypotheses because it doesn't use
; any user defined functions.

(defthm list-of-list-of-true-listsp-expessed-as-all
  (implies (Applicablep all)
           (equal (list-of-list-of-true-listsp lst)
                  (and (true-listp lst)
                       (all lst
                                '(lambda (x)
                                   (if (true-listp x)
                                       (all x 'true-listp)
                                       'nil))))))
  :rule-classes nil)

; Note: We have to use IF instead of AND above because AND is a macro and
; apply$ doesn't know how to interpret it.

; We prove three versions of the theorem.  The first is about a composition of
; two collects, each of which map with another collect:

(must-fail ; failed to supply applicablep hypotheses
 (defthm theorem-about-collect-collect-rev-twice-version1
   (implies (list-of-list-of-true-listsp lst)
            (equal (collect
                    (collect lst '(lambda (x) (collect x 'rev)))
                    '(lambda (x) (collect x 'rev)))
                   lst))))

(defthm theorem-about-collect-collect-rev-twice-version1
  (implies (and (Applicablep collect rev)
                (list-of-list-of-true-listsp lst))
           (equal (collect
                   (collect lst '(lambda (x) (collect x 'rev)))
                   '(lambda (x) (collect x 'rev)))
                  lst)))

; The second version is about a composition of two collect-revs.  One might
; think that we must provide an applicablep hypothesis just for COLLECT-REV.
; But that's wrong.  We must also provide one for REV because after (APPLY$
; 'COLLECT-REV ...) expands to (collect-rev ...), that expands to (collect
; ... 'REV) and hence introduces (APPLY$ 'REV ...).  It is possible to detect
; this requirement by looking at the forced subgoals.

(defthm theorem-about-collect-collect-rev-twice-version2
  (implies (and (Applicablep collect-rev rev)
                (list-of-list-of-true-listsp lst))
           (equal (collect
                   (collect lst 'collect-rev)
                   'collect-rev)
                  lst)))

; Here is a version with the hypothesis phrased with ALL:

(defthm theorem-about-collect-collect-rev-twice-version3
  (implies (and (Applicablep all collect rev)
                (true-listp lst)
                (all lst
                         '(lambda (x)
                            (if (true-listp x)
                                (all x 'true-listp)
                                'nil))))
           (equal (collect
                   (collect lst '(lambda (x) (collect x 'rev)))
                   '(lambda (x) (collect x 'rev)))
                  lst)))

; A few theorems manipulating mapping functions and the functions they
; apply:

(defthm sumlist-ap
  (equal (sumlist (ap a b) u)
         (+ (sumlist a u)
            (sumlist b u))))

; Here is a way to move a constant factor out of a sumlist regardless of the
; names of the variables.

(defthm sumlist-binary-*-constant
  (implies (tamep body)
           (equal (sumlist lst (lamb (list v) (list 'binary-* (list 'quote const) body)))
                  (* const (sumlist lst (lamb (list v) body))))))

(defthm lamb-x-x-is-identity
  (implies (atom x)
           (fn-equal (lamb (list x) x) 'identity))
  :hints (("Goal" :in-theory (enable fn-equal))))

; The hint below is only provided to show that the theorem is proved by
; rewriting, not induction.

(defthm example-of-loop$-rewriting
  (equal (sumlist (ap aaa bbb) (lamb '(x) '(binary-* '2 x)))
         (+ (* 2 (sumlist aaa 'identity))
            (* 2 (sumlist bbb 'identity))))
  :hints (("Goal" :do-not-induct t))
  :rule-classes nil)

; A couple of nice foldr theorems

(defthm foldr-is-ap
  (equal (foldr x 'cons y) (ap x y)))

(defthm foldr-is-rev
  (implies (Applicablep foldr)
           (equal (foldr x
                         '(lambda (x y)
                                  (foldr y 'cons (cons x 'nil)))
                         nil)
                  (rev x))))

(defthm collect-is-a-foldr
  (implies (force (ok-fnp fn))
           (equal (collect lst fn)
                  (foldr lst
                         `(LAMBDA (X Y)
                                  (CONS (,fn X) Y))
                         nil))))

(defthm all-is-a-foldr
  (implies (force (ok-fnp fn))
           (equal (all lst fn)
                  (foldr lst
                         `(LAMBDA (X Y)
                                  (IF (,fn X) Y 'NIL))
                         t))))

(defthm sumlist-is-a-foldr
  (implies (force (ok-fnp fn))
           (equal (sumlist lst fn)
                  (foldr lst
                         `(LAMBDA (X Y)
                                  (BINARY-+ (,fn X) Y))
                         0))))

