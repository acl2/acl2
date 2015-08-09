(in-package "ACL2")
(set-match-free-default :all)

#| cfair.lisp

This book defines a "conditional" fair selector which is restricted to select
only "legal" inputs specified for the system. Complications arise in defining
this type of fairness. In particular, the fair selection is now dependent on
the system state and as such, the definition of fair-run will be mutually
recursive with run (or alternatively, they could be merged into a single "run"
function which updates a pair of system state with fair selector state). Given
this added complexity, we do not suggest the use of this selector, but instead
suggest the use of the strong selector in fair.lisp which affords a cleaner
composition. We provide the definition of this selector nonetheless since it
may prove useful in some contexts.

|#

(include-book "n2n")
(include-book "../../../../ordinals/e0-ordinal")
(set-well-founded-relation e0-ord-<)

(encapsulate
 (((legal-input * *) => *)
  ((legal-witness *) => *))

 (local (defun legal-input (s i) (equal (nfix s) (nfix i))))
 (local (defun legal-witness (s) (nfix s)))

 (defthm legal-witness-is-legal
   (legal-input s (legal-witness s)))
 (defthm legal-witness-is-nice
   (nicep (legal-witness s)))
)

(defun legal-in-lst (s lst)
  (and (consp lst)
       (if (legal-input s (nat->nice (first lst)))
           (first lst)
         (legal-in-lst s (rest lst)))))

(defun drop-lst (lst n)
  (cond ((endp lst) ())
        ((equal n (first lst))
         (drop-lst (rest lst) n))
        (t (cons (first lst)
                 (drop-lst (rest lst) n)))))

(defun pos-in-lst (lst n)
  (cond ((endp lst) nil)
        ((equal n (first lst)) 0)
        (t (and (pos-in-lst (rest lst) n)
                (1+ (pos-in-lst (rest lst) n))))))

(defthm impossible-case-for-ctr
  (implies (equal ctr (nice->nat (legal-witness s)))
           (legal-input s (nat->nice ctr))))

(defun find-ndx (s top ctr)
  (declare (xargs :measure
                  (let ((goal (nice->nat (legal-witness s))))
                    (cons (1+ (nfix (- goal top)))
                          (nfix (if (>= goal ctr)
                                    (- goal ctr)
                                  (+ 1 (- top ctr) goal)))))))
  (cond ((or (not (natp ctr))
             (not (natp top))
             (> ctr top))
         0)
        ((legal-input s (nat->nice ctr))
         ctr)
        ((< ctr top)
         (find-ndx s top (1+ ctr)))
        (t
         (find-ndx s (1+ top) 0))))

(defun snoc (e x)
  (if (endp x) (list e)
    (cons (first x) (snoc e (rest x)))))

(defun step-env (s hold top ctr)
  (declare (xargs :measure
                  (let ((goal (nice->nat (legal-witness s))))
                    (cons (1+ (nfix (- goal top)))
                          (nfix (if (>= goal ctr)
                                    (- goal ctr)
                                  (+ 1 (- top ctr) goal)))))))
  (cond ((or (not (natp ctr))
             (not (natp top))
             (> ctr top))
         (list hold 1 0))
        ((legal-input s (nat->nice ctr))
         (if (= top ctr)
             (list hold (1+ top) 0)
           (list hold top (1+ ctr))))
        ((< ctr top)
         (step-env s (snoc ctr hold) top (1+ ctr)))
        (t
         (step-env s (snoc top hold) (1+ top) 0))))

;; we now prove some theorems about these functions which we will need in the
;; following encapsulate

(defun in-lst (e x)
  (and (consp x)
       (or (equal e (first x))
           (in-lst e (rest x)))))

(defthm legal-in-lst-is-in-lst
  (implies (legal-in-lst s x)
           (in-lst (legal-in-lst s x) x)))

(defthm drop-lst-<=-len
  (<= (len (drop-lst lst e))
      (len lst))
  :rule-classes :linear)

(defthm drop-lst-<-len-in-lst
  (implies (in-lst e lst)
           (< (len (drop-lst lst e))
              (len lst)))
  :rule-classes :linear)

(defthm pos-in-lst-<=-drop-lst
  (implies (and (in-lst a lst)
                (not (equal a b)))
           (<= (pos-in-lst (drop-lst lst b) a)
               (pos-in-lst lst a)))
  :rule-classes :linear)

(defthm pos-in-lst-<-not-legal-in-lst-help
  (implies (and (nat-listp lst)
                (in-lst a lst)
                (legal-input s (nat->nice a))
                (not (equal a (legal-in-lst s lst))))
           (< (pos-in-lst (drop-lst lst (legal-in-lst s lst)) a)
              (pos-in-lst lst a)))
  :rule-classes nil)

(defthm pos-in-lst-<-not-legal-in-lst
  (let ((a (nice->nat i)))
    (implies (and (nicep i)
                  (nat-listp lst)
                  (in-lst a lst)
                  (legal-input s i)
                  (not (equal a (legal-in-lst s lst))))
             (< (pos-in-lst (drop-lst lst (legal-in-lst s lst)) a)
                (pos-in-lst lst a))))
  :hints (("Goal" :use
           (:instance pos-in-lst-<-not-legal-in-lst-help
                      (a (nice->nat i)))))
  :rule-classes :linear)

(defthm pos-in-lst-iff-in-lst
  (iff (pos-in-lst x n)
       (in-lst n x)))

(defthm in-lst-of-drop-lst
  (equal (in-lst n (drop-lst lst a))
         (and (not (equal n a))
              (in-lst n lst))))

(defun env-ctr (goal top ctr)
  (declare (xargs :measure
                  (cons (1+ (nfix (- goal top)))
                        (nfix (if (>= goal ctr)
                                  (- goal ctr)
                                (+ 1 (- top ctr) goal))))))
  (cond ((or (not (natp ctr))
             (not (natp top))
             (not (natp goal))
             (> ctr top))
         0)
        ((equal ctr goal)
         1)
        ((< ctr top)
         (1+ (env-ctr goal top (1+ ctr))))
        (t
         (1+ (env-ctr goal (1+ top) 0)))))

(defun env-msr (i hold top ctr)
  (let ((ndx (nice->nat i)))
    (or (pos-in-lst hold ndx)
        (+ (len hold)
           (env-ctr ndx top ctr)))))

(defthm <=-env-msr-drop-lst
  (implies (not (equal (nice->nat i) ndx))
           (<= (env-msr i (drop-lst hold ndx) top ctr)
               (env-msr i hold top ctr)))
  :rule-classes :linear)

(defthm <-env-msr-if-not-selected
  (let ((ndx (legal-in-lst s hold)))
    (implies (and ndx
                  (nicep i)
                  (nat-listp hold)
                  (legal-input s i)
                  (not (equal (nice->nat i) ndx)))
             (< (env-msr i (drop-lst hold ndx) top ctr)
                (env-msr i hold top ctr))))
  :rule-classes :linear)

(defthm pos-in-lst-snoc-unchanged
  (implies (in-lst ndx hold)
           (equal (pos-in-lst (snoc e hold) ndx)
                  (pos-in-lst hold ndx))))

(defthm in-lst-of-snoc-rewrite
  (equal (in-lst ndx (snoc e hold))
         (or (equal ndx e)
             (in-lst ndx hold))))

(defthm pos-in-lst-hold-step-env-unchanged
  (implies (in-lst ndx hold)
           (equal (pos-in-lst (car (step-env s hold top ctr)) ndx)
                  (pos-in-lst hold ndx))))

(defthm in-lst-hold-step-env-unchanged
  (implies (in-lst ndx hold)
           (in-lst ndx (car (step-env s hold top ctr)))))

(defthm len-of-snoc
  (equal (len (snoc e x))
         (1+ (len x))))

(defthm <=-env-msr-in-lst-case
  (let ((hold+ (car (step-env s hold top ctr))))
    (implies (and (natp top)
                  (natp ctr)
                  (<= ctr top)
                  (natp goal)
                  (not (in-lst goal hold))
                  (in-lst goal hold+))
             (<= (pos-in-lst hold+ goal)
                 (+ (len hold)
                    (env-ctr goal top ctr)))))
  :rule-classes :linear)

(defthm <=-env-msr-not-in-lst-case
  (let* ((nxt (step-env s hold top ctr))
         (hold+ (first nxt))
         (top+ (second nxt))
         (ctr+ (third nxt)))
    (implies (and (natp top)
                  (natp ctr)
                  (<= ctr top)
                  (natp goal)
                  (not (in-lst goal hold+))
                  (not (equal goal (find-ndx s top ctr))))
             (<= (+ (len hold+)
                    (env-ctr goal top+ ctr+))
                 (+ (len hold)
                    (env-ctr goal top ctr)))))
  :rule-classes :linear)

(defthm <=-env-msr-step-env
  (let* ((nxt (step-env s hold top ctr))
         (hold+ (first nxt))
         (top+ (second nxt))
         (ctr+ (third nxt)))
    (implies (and (natp top)
                  (natp ctr)
                  (<= ctr top)
                  (not (equal (nice->nat i)
                              (find-ndx s top ctr))))
             (<= (env-msr i hold+ top+ ctr+)
                 (env-msr i hold top ctr))))
  :rule-classes :linear)

(defthm if-in-lst-and-not-legal-in-lst
  (implies (and (nicep i)
                (nat-listp lst)
                (in-lst (nice->nat i) lst)
                (legal-input s i))
           (legal-in-lst s lst)))

(defthm not-in-hold+-if-legal-input
  (implies (and (nicep i)
                (not (in-lst (nice->nat i) hold))
                (legal-input s i))
           (not (in-lst (nice->nat i)
                        (car (step-env s hold top ctr))))))

(defthm nat-listp-of-snoc
  (implies (and (natp e)
                (nat-listp x))
           (nat-listp (snoc e x))))

(defthm <-env-ctr-step-env-main
  (let* ((nxt (step-env s hold top ctr))
         (hold+ (first nxt))
         (top+ (second nxt))
         (ctr+ (third nxt)))
    (implies (and (natp top)
                  (natp ctr)
                  (<= ctr top)
                  (nicep i)
                  (nat-listp hold)
                  (legal-input s i)
                  (not (in-lst (nice->nat i) hold+))
                  (not (equal (nice->nat i)
                              (find-ndx s top ctr))))
             (< (+ (len hold+)
                   (env-ctr (nice->nat i) top+ ctr+))
                (+ (len hold)
                   (env-ctr (nice->nat i) top ctr)))))
  :rule-classes :linear)

(defthm <-env-msr-step-env
  (let* ((nxt (step-env s hold top ctr))
         (hold+ (first nxt))
         (top+ (second nxt))
         (ctr+ (third nxt)))
    (implies (and (natp top)
                  (natp ctr)
                  (<= ctr top)
                  (nicep i)
                  (nat-listp hold)
                  (legal-input s i)
                  (not (legal-in-lst s hold))
                  (not (equal (nice->nat i)
                              (find-ndx s top ctr))))
             (< (env-msr i hold+ top+ ctr+)
                (env-msr i hold top ctr))))
  :rule-classes :linear)

(defthm drop-lst-preserves-nat-listp
  (implies (nat-listp x)
           (nat-listp (drop-lst x e))))

(defun good-env (e)
  (let ((hold (first e))
        (top  (second e))
        (ctr  (third e)))
    (and (natp top)
         (natp ctr)
         (<= ctr top)
         (nat-listp hold))))

(defthm step-env-preserves-env-inv
  (implies (nat-listp hold)
           (good-env (step-env s hold top ctr))))

(defthm legal-in-lst-is-legal-input
  (implies (and (nat-listp x)
                (legal-in-lst s x))
           (legal-input s (nat->nice (legal-in-lst s x)))))

(defthm find-ndx-is-legal-input
  (implies (and (natp ctr)
                (natp top)
                (<= ctr top))
           (legal-input s (nat->nice (find-ndx s top ctr)))))

(defthm transfer-nice->nat-over
  (implies (and (nicep i)
                (not (equal (nat->nice n) i)))
           (not (equal (nice->nat i) n))))

(encapsulate
 (((fair-select * *) => *)
  ((fair-measure * *) => *)
  ((fair-update * *) => *)
  ((env-inv *) => *)
  ((env-init) => *))

 (local
  (defun env-init ()
    (list () 0 0)))

 (local
  (defun env-inv (e) (good-env e)))

 (local
  (defun fair-update (e s)
    (let ((hold (first e))
          (top  (second e))
          (ctr  (third e)))
      (let ((ndx (legal-in-lst s hold)))
        (if ndx
            (list (drop-lst hold ndx) top ctr)
          (step-env s hold top ctr))))))

 (local
  (defun fair-select (e s)
    (let ((hold (first e))
          (top  (second e))
          (ctr  (third e)))
      (nat->nice (or (legal-in-lst s hold)
                     (find-ndx s top ctr))))))

 (local
  (defun fair-measure (e i)
    (let ((hold (first e))
          (top  (second e))
          (ctr  (third e)))
      (env-msr i hold top ctr))))

 ;; the following are the exported theorems for our constrained functions
 ;; defining a fair environment.

 (defthm env-init-satisfies-invariant
   (env-inv (env-init)))

 (defthm fair-update-preserves-env
   (implies (env-inv e)
            (env-inv (fair-update e s))))

 (defthm fair-select-must-be-legal
   (implies (env-inv e)
            (legal-input s (fair-select e s))))

 (defthm fair-measure-is-natural
   (implies (env-inv e)
            (natp (fair-measure e i))))

 (defthm fair-measure-may-decrease
   (implies (and (env-inv e)
                 (nicep i)
                 (not (equal (fair-select e s) i)))
            (<= (fair-measure (fair-update e s) i)
                (fair-measure e i)))
   :hints (("Goal" :in-theory (disable env-msr)))
   :rule-classes (:linear :rewrite))

 (defthm fair-measure-must-decrease-strictly
   (implies (and (env-inv e)
                 (nicep i)
                 (not (equal (fair-select e s) i))
                 (legal-input s i))
            (< (fair-measure (fair-update e s) i)
               (fair-measure e i)))
   :hints (("Goal" :in-theory (disable env-msr)))
   :rule-classes (:linear :rewrite))
)

