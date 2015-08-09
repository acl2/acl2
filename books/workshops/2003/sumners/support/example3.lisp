(in-package "ACL2")
(set-match-free-default :all)

#| example3.lisp

We present a slightly more complex model which uses the fair environment in
fair2.lisp. This example is a mutual exclusion model where the state of the
system is abstracted into a process pointer and a list of program counters (one
for each process). This is a fairly simple system to define, but has a subtle
argument for progress because the "arbiter" does not wait until a process
reaches its critical section. The function good-measure is the key to the
argument and utilizes two calls of env-measure (one for the arbitrary node in
the property (pick-pr) and another for the current node selected by the
arbiter).

|#

(include-book "fair2")
(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

;; the following macro defines the functions env and env-measure

(define-env)

; The following was removed with the addition of natp-compound-recognizer to
; ACL2 2.9.2.
;(defthm posp-compound-recognizer
;  (iff (posp x)
;       (and (integerp x)
;            (> x 0)))
;  :rule-classes :compound-recognizer)

(in-theory (disable posp))

(encapsulate
 (((last-pr) => *)
  ((crit-pc) => *)
  ((last-pc) => *))

 (local (defun last-pr () 0))
 (local (defun crit-pc () 1))
 (local (defun last-pc () 2))

 (defthm last-pr-natp
   (natp (last-pr))
   :rule-classes :type-prescription)

 (defthm crit-pc-posp
   (posp (crit-pc))
   :rule-classes :type-prescription)

 (defthm last-pc-posp
   (posp (last-pc))
   :rule-classes :type-prescription)

 (defthm last-pc-gt-crit-pc
   (< (crit-pc) (last-pc)))
)

(defun prp (x)
  (and (natp x) (<= x (last-pr))))

(defthm prp-forward
  (implies (prp x)
           (and (natp x)
                (<= x (last-pr))))
  :rule-classes :forward-chaining)

(defthm prp-backward1
  (implies (and (natp x)
                (<= x (last-pr)))
           (prp x)))

(defthm prp-backward2
  (implies (not (and (natp x)
                     (<= x (last-pr))))
           (not (prp x))))

(in-theory (disable prp (prp)))

(defun pcp (x)
  (and (natp x) (<= x (last-pc))))

(defthm pcp-forward
  (implies (pcp x)
           (and (natp x)
                (<= x (last-pc))))
  :rule-classes :forward-chaining)

(defthm pcp-backward1
  (implies (and (natp x)
                (<= x (last-pc)))
           (pcp x)))

(defthm pcp-backward2
  (implies (not (and (natp x)
                     (<= x (last-pc))))
           (not (pcp x))))

(in-theory (disable pcp (pcp)))

(defun getp (n l)
  (if (zp n)
      (if (endp l) 0 (car l))
    (getp (1- n) (cdr l))))

(defun setp (n v l)
  (if (zp n)
      (cons v (cdr l))
    (cons (if (endp l) 0 (car l))
          (setp (1- n) v (cdr l)))))

(defthm getp-of-setp
  (equal (getp n (setp m v l))
         (if (equal (nfix n) (nfix m))
             v
           (getp n l))))

(defthm getp-of-atom
  (implies (atom l)
           (equal (getp n l) 0)))

(defun pc-listp (l)
  (or (null l)
      (and (consp l)
           (pcp (car l))
           (pc-listp (cdr l)))))

(defthm setp-pc-listp
  (implies (and (pc-listp l)
                (pcp v))
           (pc-listp (setp n v l))))

(defthm getp-of-pc-listp1
  (implies (pc-listp l)
           (pcp (getp n l)))
  :rule-classes (:type-prescription
                 :rewrite))

(defthm getp-of-pc-listp2
  (implies (pc-listp l)
           (natp (getp n l)))
  :rule-classes :type-prescription)

(defthm getp-of-pc-listp3
  (implies (pc-listp l)
           (<= (getp n l) (last-pc)))
  :rule-classes :linear)

(defun next-pr (x)
  (let ((x (1+ x))) (if (> x (last-pr)) 0 x)))

(defun next-pc (x)
  (let ((x (1+ x))) (if (> x (last-pc)) 0 x)))

(defun in-crit (p)
  (>= p (crit-pc)))

(defun sys-step (s i)
  (if (prp i)
      (let* ((ndx (car s))
             (prs (cdr s))
             (p (getp i prs))
             (p+ (next-pc p))
             (p+ (if (and (in-crit p+) (/= i ndx)) p p+))
             (prs (setp i p+ prs))
             (n+ (next-pr ndx))
             (ndx (if (and (not (in-crit p+)) (= i ndx)) n+ ndx)))
        (cons ndx prs))
    s))

(in-theory (disable (sys-step) (next-pr) (next-pc) (in-crit)))

(defun sys-init () (cons 0 ()))

(defun run (n)
  (if (zp n) (sys-init)
    (let ((n (1- n)))
      (sys-step (run n) (env n)))))

(in-theory (disable (run) (env)))

;; the following is just a rewrite rule we need from linear arithmetic (which
;; does not "rewrite")
(local
 (defthm linear-factoid3
   (implies (and (integerp x)
                 (integerp y))
            (equal (+ (- y) y x) x))))

(local
(defthm expand-run-1+
  (implies (natp n)
           (equal (run (1+ n))
                  (sys-step (run n) (env n))))
  :hints (("Goal" :in-theory (disable sys-step)))))

(defthm pc-listp-cdr-run
  (pc-listp (cdr (run n)))
  :rule-classes :type-prescription)

(defthm natp-car-run
  (natp (car (run n)))
  :rule-classes :type-prescription)

(defthm car-run-<=-last-pr
  (<= (car (run n)) (last-pr))
  :rule-classes :linear)

(defthm prp-car-run
  (prp (car (run n)))
  :rule-classes :type-prescription)

(encapsulate
 (((pick-pr) => *))
 (local (defun pick-pr () 0))

 (defthm pick-pr-natp
   (natp (pick-pr))
   :rule-classes :type-prescription)

 (defthm pick-pr-<=-last-pr
   (<= (pick-pr) (last-pr)))

 (defthm pick-pr-is-prp
   (prp (pick-pr)))
)

(defun good (s)
  (in-crit (getp (pick-pr) (cdr s))))

(in-theory (disable (good)))

(defthm natp-is-nicep
  (implies (natp x)
           (nicep x))
  :rule-classes :type-prescription)

(defthm prp-not-equal1
  (implies (and (prp x)
                (not (prp y)))
           (not (equal x y))))

(defthm prp-not-equal2
  (implies (and (prp x)
                (not (prp y)))
           (not (equal y x))))

(defthm natp-pick-pr--
  (implies (and (natp y)
                (<= y (pick-pr)))
           (natp (- (pick-pr) y)))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes :type-prescription)

(defthm natp-last-pr--1
  (implies (and (natp y)
                (<= y (last-pr))
                (natp a)
                (natp b))
           (natp (+ (last-pr) a b (- y))))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes :type-prescription)

(defthm natp-last-pr--2
  (implies (and (natp y)
                (<= y (last-pr))
                (natp a)
                (natp b))
           (natp (+ a (last-pr) b (- y))))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes :type-prescription)

(defthm natp-last-pr--3
  (implies (and (natp y)
                (<= y (last-pr))
                (natp a)
                (natp b))
           (natp (+ a b (last-pr) (- y))))
  :hints (("Goal" :in-theory (enable natp)))
  :rule-classes :type-prescription)

(defmacro lexprod (&rest r)
  (cond ((endp r) 0)
        ((endp (rest r)) (first r))
        (t `(cons (lexprod ,@(butlast r 1))
                  ,(car (last r))))))

(defun good-measure (n)
  (let* ((s (run n))
         (ndx (car s))
         (prs (cdr s))
         (nogo (not (equal ndx (pick-pr)))))
    (lexprod
     (if (natp n) 1 2)
     (nfix (- (crit-pc) (getp (pick-pr) prs)))
     (if nogo 2 1)
     (if nogo
         (if (> ndx (pick-pr))
             (+ (- (last-pr) ndx)
                (1+ (pick-pr)))
           (- (pick-pr) ndx))
       0)
     (if nogo
         (- (last-pc) (getp ndx prs))
       0)
     (env-measure ndx n))))

(in-theory (disable (good-measure)))

(defun good-time (n)
  (declare (xargs :measure (good-measure n)
                  :hints (("Subgoal 1"
                           :use ((:instance last-pc-gt-crit-pc)
                                 (:instance pick-pr-<=-last-pr))
                           :in-theory (disable last-pc-gt-crit-pc
                                               pick-pr-<=-last-pr
                                               getp setp)))))
  (cond ((not (natp n)) (good-time 0))
        ((good (run n)) n)
        (t (good-time (1+ n)))))

(in-theory (disable good (good-time)))

(defthm good-of-good-time
  (good (run (good-time n))))

(defthm good-time->=
  (implies (integerp n)
           (>= (good-time n) n))
  :rule-classes :linear)

(defthm good-time-is-natp
  (natp (good-time n))
  :rule-classes :type-prescription)

(defun time>= (y x)
  (and (natp y) (implies (natp x) (>= y x))))

(defun-sk eventually-good (x)
  (exists (y) (and (time>= y x) (good (run y)))))

(defthm progress-or-liveness
  (eventually-good n)
  :hints (("Goal" :use (:instance eventually-good-suff
                                  (x n)
                                  (y (good-time n))))))

