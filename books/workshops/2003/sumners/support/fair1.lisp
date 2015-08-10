(in-package "ACL2")
(set-match-free-default :all)

(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

#| fair1.lisp

This "book" provides an equivalence proof between a straightforward statement
of "fair input selection" using defun-sk and the existence of a fair measure
function which decreases with every step. In order to use the measure function
introduced in this book, one would need to introduce (fair-selection)
assumptions in any theorems which required the properties of the environment
measure function. Because of this, we do not recommend using this book, and
instead recommend using the book fair2.lisp.

|#

(encapsulate ;; arbitrary environment input sequence
 (((env1 *) => *))
 (local (defun env1 (x) x)))

; The following was removed with the addition of natp-compound-recognizer to
; ACL2 2.9.2.
;(defthm natp-compound-recognizer
;  (iff (natp x)
;       (and (integerp x)
;            (>= x 0)))
;  :rule-classes :compound-recognizer)

(in-theory (disable natp))

(defun time>= (y x)
  (and (natp y) (implies (natp x) (>= y x))))

(defun next1* (i n k)
  (declare (xargs :measure (nfix (- k n))))
  (if (or (equal (env1 n) i) (zp (- k n))) n (next1* i (1+ n) k)))

(defthm next1*-natp
  (implies (natp n) (natp (next1* i n k)))
  :rule-classes :type-prescription)

(defthm next1*>
  (>= (next1* i n k) n)
  :rule-classes :linear)

(defthm next1*-property
  (implies (and (natp n) (natp k1) (natp k2)
                (>= k1 n) (>= k2 n)
                (equal (env1 k1) i)
                (equal (env1 k2) i))
           (equal (equal (next1* i n k1)
                         (next1* i n k2))
                  t)))

(defun-sk exists-future (i x)
  (exists y (and (time>= y x) (equal (env1 y) i))))

(defun-sk fair-selection ()
  (forall (i x) (exists-future i x)))

(defun next1 (i n)
  (next1* i n (exists-future-witness i n)))

(defthm next1-natp
  (implies (natp n)
           (natp (next1 i n)))
  :rule-classes :type-prescription)

(defthm next1>
  (>= (next1 i n) n)
  :rule-classes :linear)

(defthm next1-no-change
  (implies (and (natp n)
                (fair-selection)
                (not (equal (env1 n) i)))
           (equal (next1 i (1+ n))
                  (next1 i n)))
  :hints (("Goal"
           :use ((:instance fair-selection-necc (x n))
                 (:instance fair-selection-necc (x (1+ n))))
           :in-theory (disable fair-selection-necc))))

(defun env1-measure (i n)
  (if (natp n) (- (next1 i n) n) (next1 i 0)))

(defthm env1-measure-natural
  (natp (env1-measure i n))
  :hints (("Goal" :in-theory (enable natp))))

(defthm env1-measure-decreases
  (implies (and (natp n)
                (fair-selection)
                (not (equal (env1 n) i)))
           (< (env1-measure i (1+ n))
              (env1-measure i n)))
  :hints (("Goal" :in-theory (disable fair-selection))))

(in-theory (disable fair-selection))

#|

IMPORTANT NOTE:

We include an extra "k" parameter to the functions env and env-measure, to
allow the use of multiple independent fair selectors. We generally use the
following macro define-env to define a fair environment with support for
multiple fair selectors for "fields" in an input. These "fields" of the input
are defined using the "s" and "g" operators from the records book:
books/misc/records.lisp. These operators could be replaced with updaters and
accessors of your choosing, but the properties of "s" and "g" should hold (or
suitable equivalent properties) and "g" should be a free accessor in that the
range of "g" should be the ACL2 universe. This is necessary to ensure that the
modeling of the fair selector is not inadvertently and inappropriately
constrained.

|#

(encapsulate
 (((env! * *) => *)
  ((env-measure! * * *) => *))

(local (defun env! (k n) (declare (ignore k))
         (env1 n)))
(local (defun env-measure! (k i n) (declare (ignore k))
         (env1-measure i n)))

(defthm env-measure!-is-natural
  (natp (env-measure! k i n))
  :rule-classes (:type-prescription :rewrite))

(defthm env-measure!-decreases
  (implies (and (fair-selection)
                (natp n)
                (not (equal i (env! k n))))
           (< (env-measure! k i (1+ n))
              (env-measure! k i n)))
  :rule-classes (:linear :rewrite))
)

(defun mk-env-body (keys)
  (if (endp keys) '(env! 0 n)
    `(s (quote ,(first keys))
        (env! (quote ,(first keys)) n)
        ,(mk-env-body (rest keys)))))

(defmacro define-env (&rest keys)
  (declare (xargs :guard (symbol-listp keys)))
  `(progn (defun env (n) ,(mk-env-body keys))
          ,(if (endp keys)
               '(defun env-measure (i n)
                  (env-measure! 0 i n))
             '(defun env-measure (k i n)
                (env-measure! k i n)))))

#|

We conclude this book with a "proof" that the existence of a fair-measure
implies (fair-selection) -- we proved the other direction above. This other
direction is not relevant to the output of this file, so we make all of the
following forms local.

|#

(local
(defstub env1-msr$ (i n) t))

(local
(defun-sk env1-msr$-property ()
  (forall (i n)
          (and (natp (env1-msr$ i n))
               (implies (and (natp n)
                             (not (equal (env1 n) i)))
                        (< (env1-msr$ i (1+ n))
                           (env1-msr$ i n)))))))

(local
(defthm env1-msr$-is-natural
  (implies (env1-msr$-property)
           (natp (env1-msr$ i n)))
  :hints (("Goal"
           :use (:instance env1-msr$-property-necc)
           :in-theory (disable env1-msr$-property-necc)))
  :rule-classes :type-prescription))

(local
(defthm env1-msr$-decreases
  (implies (and (env1-msr$-property)
                (natp n)
                (not (equal (env1 n) i)))
           (< (env1-msr$ i (1+ n))
              (env1-msr$ i n)))
  :hints (("Goal"
           :use (:instance env1-msr$-property-necc)
           :in-theory (disable env1-msr$-property-necc)))
  :rule-classes :linear))

(local
(in-theory (disable env1-msr$-property)))

(local
(defun witness1$ (i x)
  (declare (xargs :measure (cons (if (natp x) 1 2)
                                 (if (env1-msr$-property)
                                     (env1-msr$ i x)
                                   0))))
  (cond ((not (env1-msr$-property)) 0)
        ((not (natp x)) (witness1$ i 0))
        ((equal (env1 x) i) x)
        (t (witness1$ i (1+ x))))))

(local
(defthm witness1$-is-env1
  (implies (env1-msr$-property)
           (equal (env1 (witness1$ i x)) i))))

(local
(defthm witness1$-in-future
  (implies (and (natp x)
                (env1-msr$-property))
           (>= (witness1$ i x) x))
  :rule-classes :linear))

(local
(in-theory (disable exists-future exists-future-suff)))

(local
(defthm env1-msr$-property-implies-fair-selection
  (implies (env1-msr$-property)
           (fair-selection))
  :hints (("Goal"
           :use ((:instance exists-future-suff
                            (i (mv-nth 0 (fair-selection-witness)))
                            (x (mv-nth 1 (fair-selection-witness)))
                            (y (witness1$ (mv-nth 0 (fair-selection-witness))
                                          (mv-nth 1 (fair-selection-witness))))))
           :in-theory (enable fair-selection)))))
