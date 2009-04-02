(in-package "ACL2")

(include-book "perm-append")

; ---------------------------------------------------------------------------
; Exercise 11.8

(defun less (x lst)
  (cond ((atom lst) nil)
	((< (car lst) x)
	 (cons (car lst) (less x (cdr lst))))
	(t (less x (cdr lst)))))

#| For example:
ACL2 !>(less 3 '(1 3 5 7 5 3 2))
(1 2)
ACL2 !>
|#

; ---------------------------------------------------------------------------
; Exercise 11.9

(defun notless (x lst)
  (cond ((endp lst) nil)
	((< (car lst) x)
	 (notless x (cdr lst)))
	(t (cons (car lst) (notless x (cdr lst))))))

#| For example:
ACL2 !>(notless 3 '(1 3 5 7 5 3 2))
(3 5 7 5 3)
ACL2 !>
|#

; ---------------------------------------------------------------------------
; Exercise 11.10

(defun qsort (x)
  (cond ((atom x) nil)
        (t (append (qsort (less (car x) (cdr x)))
                   (list (car x))
                   (qsort (notless (car x) (cdr x)))))))


; Our first attempt to prove perm-qsort leads us to the following goal.

#|
Subgoal *1/2'4'
(IMPLIES (AND (PERM (QSORT (LESS X1 X2)) (LESS X1 X2))
              (PERM (QSORT (NOTLESS X1 X2))
                    (NOTLESS X1 X2)))
         (PERM (APPEND (LESS X1 X2)
                       (CONS X1 (NOTLESS X1 X2)))
               (CONS X1 X2)))
|#

; The hypotheses appear to be irrelevant, so we remove them in order to obtain
; the simple lemma perm-append-less-notless below.

; An attempt to prove that lemma leads to the following subgoal that is proved
; for proof by induction.  Normally we prefer to focus on the first
; simplification checkpoint, but in this case the prover has done a fine job
; of using generlization and we take advantage of that work in order to focus
; on a simple task, as explained just below the following goal.

#|
Subgoal *1/3'5'
(IMPLIES (AND (TRUE-LISTP NS)
              (TRUE-LISTP LS)
              (<= X1 X3)
              (PERM (APPEND LS (CONS X1 NS))
                    (CONS X1 X4)))
         (PERM (APPEND LS (LIST* X1 X3 NS))
               (LIST* X1 X3 X4)))
|#

; It is pretty clear that the following simple lemma will reduce the goal above
; to T.

#|
(defthm perm-append-cons-2-first-try
  (equal (perm (append x (cons a y)) (cons a z))
         (perm (append x y) z)))
|#

; However, the prover has some trouble proving this lemma, so we ask ourselves:
; Is there a simpler rule that may apply?  Recall the congruence rules proved
; in book perm-append, which allow us to create rewrite rules about append in
; which perm is the top-level equivalence relation, rather than the usual
; equal.

(defthm perm-append-cons-2
  (perm (append x (cons a y))
        (cons a (append x y))))

; We can now prove the following, finally.

(defthm perm-append-less-notless
  (perm (append (less x1 x2)
                (cons x1 (notless x1 x2)))
        (cons x1 x2)))

(defthm perm-qsort
  (perm (qsort x) x))

; ---------------------------------------------------------------------------
; Exercise 11.11

(defun lessp (x lst)
  (if (endp lst)
      t
    (and (< (car lst) x)
         (lessp x (cdr lst)))))

; ---------------------------------------------------------------------------
; Exercise 11.12

(defun notlessp (x lst)
  (if (endp lst)
      t
    (and (not (< (car lst) x))
         (notlessp x (cdr lst)))))

(defun orderedp (lst)
  (if (or (endp lst) (endp (cdr lst)))
      t
    (and (<= (car lst) (cadr lst))
         (orderedp (cdr lst)))))

; ---------------------------------------------------------------------------
; Exercise 11.13

; The script below is actually an attack on (orderedp (qsort lst)).
; But following The Method it leads us to the subgoal of proving the
; congruence lemmas required by 11.13.

; Here is the first simplification checkpoint in the first attempt to prove
; orderedp-qsort.

#|
Subgoal *1/2''
(IMPLIES (AND (CONSP LST)
              (ORDEREDP (QSORT (LESS (CAR LST) (CDR LST))))
              (ORDEREDP (QSORT (NOTLESS (CAR LST) (CDR LST)))))
         (ORDEREDP (APPEND (QSORT (LESS (CAR LST) (CDR LST)))
                           (CONS (CAR LST)
                                 (QSORT (NOTLESS (CAR LST) (CDR LST)))))))
|#

; The goal above suggests the following lemma.  We decide to go ahead and prove
; it, even though it probably will not suffice for proving orderedp-qsort since
; a rule will probably be necessary for dealing with the instance
; of (<= (car (last x)) (car y)) that the following lemma generates.

(defthm orderedp-append
  (equal (orderedp (append x y))
         (if (consp x)
             (if (consp y)
                 (and (orderedp x)
                      (orderedp y)
                      (<= (car (last x)) (car y)))
               (orderedp x))
           (orderedp y))))

; Sure enough, orderedp-qsort still fails.  Here is the first simplification
; checkpoint.

#|
Subgoal *1/2.2
(IMPLIES (AND (CONSP LST)
              (ORDEREDP (QSORT (LESS (CAR LST) (CDR LST))))
              (ORDEREDP (QSORT (NOTLESS (CAR LST) (CDR LST))))
              (CONSP (QSORT (NOTLESS (CAR LST) (CDR LST)))))
         (<= (CAR LST)
             (CAR (QSORT (NOTLESS (CAR LST) (CDR LST))))))
|#

; Our plan is for the conclusion of the above goal to follow from the fact
; that (car lst) is less than or equal to every member of the qsort term in the
; conclusion, hence in particular, the car of that term.  Predicate notlessp,
; defined above, may be used for this purpose.  In order to prove that notlessp
; holds of (car lst) and the qsort term, we could first prove a lemma that
; eliminates the call of qsort:

#|
(defthm notlessp-qsort
  (equal (notlessp a (qsort lst))
         (notlessp a lst)))
|#

; But instead, let us exploit the fact that perm is an equivalence relation and
; that (qsort lst) is perm-equivalent to lst:

(defcong perm equal (notlessp x lst) 2)

; While we are at it, we prove the analog for lessp of the above:

(defcong perm equal (lessp x lst) 2)

; ---------------------------------------------------------------------------
; Exercise 11.14

; So, the prover now knows that when reasoning about a call of notlessp it need
; only preserve perm in the second argument, and hence it can eliminate a
; top-level call of qsort in the second argument.  We still need the following
; fact:

(defthm notlessp-notless
  (notlessp a (notless a lst)))

; We might as well prove a corresponding analogue for lessp and less while we
; are thinking of it:

(defthm lessp-less
  (lessp a (less a lst)))

; Finally, the point of introducing notlessp-notless is:

(defthm notlessp-implies-not-<
  (implies (and (notlessp a lst)
                (member x lst))
           (not (< x a))))

; And while we are at it, the analogous lemma for lessp:

(defthm lessp-implies-<
  (implies (and (lessp a lst)
                (member x lst))
           (< x a)))

; Subgoal *1/2.2 above remains unchanged when we try to prove orderedp-qsort at
; this point, and presumably the free variables in notlessp-implies-not-< and
; lessp-implies-< are the problem.  We are interested in the following
; special cases of those lemmas.

(defthm notlessp-implies-not-<-car
  (implies (and (notlessp a lst)
                (consp lst))
           (not (< (car lst) a))))

(defthm lessp-implies-<-car
  (implies (and (lessp a lst)
                (consp lst))
           (< (car lst) a)))

; We can now prove the following, which was mentioned earlier.
; (Is it necessary??!!)

(defthm notlessp-qsort
  (equal (notlessp a (qsort lst))
         (notlessp a lst)))

(defthm lessp-qsort
  (equal (lessp a (qsort lst))
         (lessp a lst)))

; The proof of orderedp-qsort now generates this simplification checkpoint.
; This makes sense, given the earlier rule orderedp-append.

#|
Subgoal *1/2''
(IMPLIES (AND (CONSP LST)
              (ORDEREDP (QSORT (LESS (CAR LST) (CDR LST))))
              (ORDEREDP (QSORT (NOTLESS (CAR LST) (CDR LST))))
              (CONSP (QSORT (LESS (CAR LST) (CDR LST)))))
         (<= (CAR (LAST (QSORT (LESS (CAR LST) (CDR LST)))))
             (CAR LST)))
|#

; The goal above suggests an analogue of earlier rule lessp-implies-<-car:

(defthm lessp-implies-<-car-last
  (implies (and (lessp a lst)
                (consp lst))
           (<= (car (last lst)) a)))

(defthm orderedp-qsort
  (orderedp (qsort lst)))
