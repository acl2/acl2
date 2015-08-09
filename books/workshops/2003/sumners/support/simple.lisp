(in-package "ACL2")
(set-match-free-default :all)

#| simple.lisp

This book defines a basic fair selector over a bounded set of natural
numbers. Note that this selector is completely subsumed by the fair selector
defined in fair.lisp which defines a fair selector over a superset of the
objects selected by the functions in this book. Thus, this book is included
solely for the purposes of exposition and completeness, but we do not suggest
the use of this book.

|#

; The following was removed with the addition of natp-compound-recognizer to
; ACL2 2.9.2.
;(defthm natp-compound-recognizer
;  (iff (natp x)
;       (and (integerp x)
;            (>= x 0)))
;  :rule-classes :compound-recognizer)

(in-theory (disable natp))

(encapsulate
 (((upper-bound) => *))

 (local (defun upper-bound () 1))

 (defthm upper-bound-positive-natural
   (and (integerp (upper-bound))
        (> (upper-bound) 0))
   :rule-classes :type-prescription)
)

(defun selectp (i)
  (and (natp i) (< i (upper-bound))))

(defun fair-select (f) f)

(defun fair-measure (i f)
  (if (selectp i)
      (if (< i f)
          (+ i (- (upper-bound) f))
        (- i f))
    0))

(defun fair-step (f)
  (let ((f (1+ f))) (if (< f (upper-bound)) f 0)))

(defun fair-inv (f) (selectp f))

(defun fair-init () 0)

(local
(defthm fair-measure-natural
  (implies (fair-inv f)
           (natp (fair-measure i f)))
  :hints (("Goal" :in-theory (enable natp)))))

(local
(defthm fair-measure-decreases
  (implies (and (selectp i)
                (fair-inv f)
                (not (equal i (fair-select f))))
           (< (fair-measure i (fair-step f))
              (fair-measure i f)))
  :rule-classes :linear))

(local
(defthm fair-inv-is-invariant
  (implies (fair-inv f)
           (fair-inv (fair-step f)))))

(in-theory (disable (fair-inv) (selectp)))

(local
(defthm fair-inv-of-init
  (fair-inv 0)))

(in-theory (disable fair-step fair-inv fair-measure fair-select))


(defun fair-run (n)
  (if (zp n) (fair-init) (fair-step (fair-run (1- n)))))

(defthm fair-inv-of-fair-run
  (fair-inv (fair-run n)))

(local
(defthm linear-factoid1
  (implies (and (natp n)
                (natp x))
           (equal (+ n (- n) x) x))))

(local
(defthm linear-factoid2
  (implies (and (natp n)
                (natp x))
           (equal (+ (- n) n x) x))))

(local
(defthm fair-run-of-1+
  (implies (natp n)
           (equal (fair-run (1+ n))
                  (fair-step (fair-run n))))))

(in-theory (disable fair-run))
(in-theory (enable (:induction fair-run)))

(in-theory (disable (fair-run) (fair-step) (fair-select)))

(encapsulate
 (((env *) => *)
  ((env-measure * *) => *))

(local (defun env (n)
         (fair-select (fair-run n))))
(local (defun env-measure (i n)
         (fair-measure i (fair-run n))))

(defthm env-measure+-is-natural
  (natp (env-measure i n))
  :rule-classes (:type-prescription :rewrite))

(defthm env-measure+-decreases
  (implies (and (selectp i)
                (natp n)
                (not (equal i (env n))))
           (< (env-measure i (1+ n))
              (env-measure i n)))
  :rule-classes (:linear :rewrite))
)
