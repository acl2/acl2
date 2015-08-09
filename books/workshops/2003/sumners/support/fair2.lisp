(in-package "ACL2")
(set-match-free-default :all)

(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

#| fair.lisp

This book defines a basic strong (i.e. unconditional) fair selector over the
nice objects (as defined in n2n.lisp). The relevant properties about env$ and
env-measure! are defined at the end of the file. We expect this fair selector
will be sufficient in most cases, but for "weak" fairness, one should consult
weak.lisp.

|#

(include-book "n2n")

(defun fair-ctr (goal ctr top)
  (declare (xargs :measure
                  (cons (1+ (nfix (- goal top)))
                        (nfix (if (>= goal ctr)
                                  (- goal ctr)
                                (+ 1 (- top ctr) goal))))))
  (cond ((not (and (natp ctr)
                   (natp top)
                   (natp goal)
                   (<= ctr top)))
         0)
        ((equal ctr goal) 1)
        ((< ctr top)
         (1+ (fair-ctr goal (1+ ctr) top)))
        (t
         (1+ (fair-ctr goal 0 (1+ top))))))

(defun fair-select (f)
  (nat->nice (car f)))

(defun fair-measure (i f)
  (fair-ctr (nice->nat i) (car f) (cdr f)))

(defun fair-step (f)
  (let ((a (car f)) (d (cdr f)))
    (if (< a d) (cons (1+ a) d) (cons 0 (1+ d)))))

(defun fair-inv (f)
  (and (consp f)
       (natp (car f))
       (natp (cdr f))
       (<= (car f) (cdr f))))

(defun fair-init ()
  (cons 0 0))

(defmacro selectp (i) `(nicep ,i))

;; ACL2 is actually able to infer this already, but we include it here for
;; better correspondence with the paper

(local
(defthm fair-measure-natural
  (natp (fair-measure i f))
  :rule-classes :type-prescription))

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
         (fair-select (fair-run n))))
(local (defun env-measure! (k i n) (declare (ignore k))
         (fair-measure i (fair-run n))))

(defthm env-measure!-is-natural
  (natp (env-measure! k i n))
  :rule-classes (:type-prescription :rewrite))

(defthm env-measure!-decreases
  (implies (and (selectp i)
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

