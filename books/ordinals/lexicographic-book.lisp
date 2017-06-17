(in-package "ACL2")

; 2010-09-16 Pete Manolios: Created two versions of our
; lexicographic-ordering book: one includes
; arithmetic/top-with-meta and one doesn't. This book contains
; all the core theorems.

(include-book "ordinals-without-arithmetic")
(local (include-book "top-with-meta"))

; 2008-07-20, Peter Dillinger:  Added guards and a couple tweaks to make
; common lisp compliant.

; A recognizer for natural number or a list of natural numbers.

(defun lexp (x)
  (declare (xargs :guard t))
  (or (natp x)
      (and (consp x)
           (nat-listp x))))


; d< is intended to be applied to lists of natural numbers of
; equal length.  t is returned iff x is lexicographically less
; than y.

(defun d< (x y)
  (declare (xargs :guard (and (nat-listp x)
                              (nat-listp y))))
  (and (consp x)
       (consp y)
       (or (< (car x) (car y))
           (and (= (car x) (car y))
                (d< (cdr x) (cdr y))))))

; Each of the arguments to l< is intended to be either a list of
; natural numbers, or a natural number. If both are natural
; numbers, l< is equivalent to <. Otherwise, t is returned iff
; the length of x is less than the length of y or (d< x y).

(defun l< (x y)
  (declare (xargs :guard (and (lexp x)
                              (lexp y))))
  (or (< (len x) (len y))
      (and (= (len x) (len y))
           (if (atom x)
               (< x y)
             (d< x y)))))

; How to turn a list of naturals into an ordinal.

(defun lsttoo (x)
  (declare (xargs :guard (nat-listp x)))
  (if (endp x)
      0
    (o+ (o* (o^ (omega) (len x)) (1+ (car x)))
        (lsttoo (cdr x)))))

; How to turn a natural or a list of naturals into an ordinal.

(defun ltoo (x)
  (declare (xargs :guard (lexp x)))
  (if (atom x)
      (mbe :logic (nfix x)
           :exec x)
    (lsttoo x)))

#|

Some examples

(ltoo '(1 3 2))
(ltoo '(1 3 0))
(ltoo '(1 0 2))
(ltoo 2)

|#


(defthm o-p-lsttoo
  (implies (nat-listp x)
           (o-p (lsttoo x))))


(local
 (defthm len-0
   (equal (equal (len x) 0)
          (atom x))))

(defthm ltoo-0
  (implies (nat-listp y)
           (equal (equal (lsttoo y) 0)
                  (equal y nil))))

(defthm o-first-expt-ltoo
  (implies (and (consp x)
                (nat-listp x))
           (equal (o-first-expt (lsttoo x))
                  (len x))))

#|
; We can now prove case 1, but don't have to prove it explicitly.

(defthm well-founded-l<-case-1
  (implies (and (consp x)
                (nat-listp x)
                (consp y)
                (nat-listp y)
                (< (len x) (len y)))
           (o< (lsttoo x) (lsttoo y))))
|#

(encapsulate
 ()
 (local
  (defthm o-first-coeff-ltoo-helper
    (implies (and (consp x)
                  (natp (car x))
                  (equal (o-first-coeff (lsttoo (cdr x))) (1+ (cadr x)))
                  (nat-listp (cdr x)))
             (equal (o-first-coeff (o+ (o* (o^ (omega) (1+ (len (cdr x))))
                                           (1+ (car x)))
                                       (lsttoo (cdr x))))
                    (1+ (car x))))
    :hints (("goal"
             :use (:instance o-first-expt-ltoo (x (cdr x)))))))

 (defthm o-first-coeff-ltoo
   (implies (and (consp x)
                 (nat-listp x))
            (equal (o-first-coeff (lsttoo x))
                   (1+ (car x))))))

(local (in-theory (enable o<)))

(encapsulate
 ()
 (local
  (defthm well-founded-l<-case-2-helper
    (implies (and (consp y)
                  (not (d< (cdr x) (cdr y)))
                  (consp x)
                  (nat-listp x)
                  (nat-listp y)
                  (equal (len x) (len y))
                  (d< x y))
             (o< (lsttoo x) (lsttoo y)))
    :hints (("goal"
             :use ((:instance o-first-expt-ltoo) (:instance o-first-expt-ltoo (x y))
                   (:instance o-first-coeff-ltoo) (:instance o-first-coeff-ltoo (x y)))))))


 (local
  (defthm well-founded-l<-case-2-helper-2
    (implies (and (consp y)
                  (not (d< (cdr x) (cdr y)))
                  (consp x)
                  (nat-listp x)
                  (nat-listp y)
                  (equal (len x) (len y))
                  (d< x y))
             (o< (lsttoo x) (lsttoo y)))
    :hints (("goal" :in-theory (disable lsttoo)))
    :rule-classes :forward-chaining))

 (defthm well-founded-l<-case-2
   (implies (and (consp x)
                 (nat-listp x)
                 (consp y)
                 (nat-listp y)
                 (equal (len x) (len y))
                 (d< x y))
            (o< (lsttoo x) (lsttoo y))))
 )

(defthm well-founded-l<
  (and (implies (lexp x) (o-p (ltoo x)))
       (implies (and (lexp x)
                     (lexp y)
                     (l< x y))
                (o< (ltoo x) (ltoo y))))
  :rule-classes :well-founded-relation)

(defun llist-macro (lst)
  (declare (xargs :guard t))
  (if (consp lst)
      `((nfix ,(car lst)) ,@(llist-macro (cdr lst)))
    nil))

(defmacro llist (&rest lst)
  (cons 'list (llist-macro lst)))

#|
Llist is a useful macro, as shown in the following example (Ackermann's
function).

For example

:trans1 (llist 1 2 3)

gives

(list (nfix 1) (nfix 2) (nfix x))

That is, llist forces all of its arguments to be natural numbers.

Here is an example of how we can use l<.  Note that the :well-founded-relation
directive can be omitted in the definition below if it is preceded by the form
(set-well-founded-relation l<).

(defun ack (x y)
  (declare (xargs :measure (llist x y)
                  :well-founded-relation l<))
  (if (zp x)
      (1+ y)
    (if (zp y)
        (ack (1- x) 1)
      (ack (1- x) (ack x (1- y))))))

Note that the reason for defining l< so that it does something
reasonable with natural numbers is that we want l< to get along
with acl2-count, the default measure chosen by ACL2, e.g., the
following definition is accepted by acl2.

(defun app (x y)
  (if (endp x)
      y
    (cons (car x) (app (cdr x) y))))

|#

