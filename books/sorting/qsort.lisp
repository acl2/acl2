; (certify-book "qsort")

(in-package "ACL2")

(include-book "perm")
(include-book "ordered-perms")
(include-book "convert-perm-to-how-many")

(defun rel (fn i j)
  (case fn
    (LT  (and (lexorder i j) (not (equal i j))))
    (LTE (lexorder i j))
    (GT  (and (lexorder j i) (not (equal i j))))
    (otherwise (lexorder j i))))

(defun filter (fn x e)
  (cond
   ((endp x) nil)
   ((rel fn (car x) e)
    (cons (car x) (filter fn (cdr x) e)))
   (t (filter fn (cdr x) e))))

(defun qsort (x)
  (cond ((endp x)
         nil)
        ((endp (cdr x))
         (list (car x)))
        (t (append (qsort (filter 'LT (cdr x) (car x)))
                   (cons (car x)
                         (qsort (filter 'GTE (cdr x) (car x))))))))


(defthm how-many-append
  (equal (how-many e (append x y))
         (+ (how-many e x)
            (how-many e y))))

(include-book "arithmetic-3/extra/top-ext" :dir :system)

(defthm how-many-filter-1
  (equal (+ (how-many e (filter 'lt x d))
            (how-many e (filter 'gte x d)))
         (how-many e x)))

(defthm how-many-qsort
  (equal (how-many e (qsort x))
         (how-many e x)))

; I need this to do the orderedp proof!

(defthm perm-qsort
  (perm (qsort x) x))

; When we prove that qsort produces ordered output, we will get two
; induction hypotheses:
; (ordered (qsort (filter 'LT (cdr x) (car x))))
; and
; (orderedp (qsort (filter 'GTE (cdr x) (car x))))

; We need to prove
; (orderedp (append (qsort (filter 'LT (cdr x) (car x)))
;                   (cons (car x)
;                         (qsort (filter 'GTE (cdr x) (car x))))))

; Using a lemma below, we'll rewrite this (orderedp (append ...))
; to something involving orderedp of the parts and the fact
; (all-rel 'LTE (qsort (filter 'LT (cdr x) (car x))) (car x))
; etc.   But how do we establish this all-rel of qsort?

; If we know that perm is a congruence for all-rel, we can drop the qsort!
; Then we just have to rely on the all-rel filter lemmas.

(defun all-rel (fn x e)
  (cond ((endp x) t)
        ((rel fn (car x) e)
         (all-rel fn (cdr x) e))
        (t nil)))

(defthm car-append
  (equal (car (append a b))
         (if (consp a)
             (car a)
           (car b))))

(defthm orderedp-append
  (implies (orderedp a)
           (iff (orderedp (append a (cons e b)))
                (and (orderedp b)
                     (all-rel 'LTE a e)
                     (all-rel 'GTE b e)))))


(defthm all-rel-filter-1
  (all-rel 'LTE (filter 'LT x e) e))

(defthm all-rel-filter-2
  (all-rel 'GTE (filter 'GTE x e) e))

; This work is to prove that perm is a congruence for all-rel:

(defthm all-rel-rm-1
  (implies (all-rel fn x e)
           (all-rel fn (rm d x) e)))

(defthm all-rel-rm-2
  (implies (and (all-rel fn (rm d x) e)
                (rel fn d e))
           (all-rel fn x e)))

(defcong perm equal (all-rel fn x e) 2
  :hints (("Goal" :in-theory (disable CONVERT-PERM-TO-HOW-MANY))))

; So now we're done:

(defthm orderedp-qsort
  (orderedp (qsort x)))

(defthm true-listp-qsort
  (true-listp (qsort x)))