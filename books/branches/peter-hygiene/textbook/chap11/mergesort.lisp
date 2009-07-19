(in-package "ACL2")

; ---------------------------------------------------------------------------
; Exercise 11.15

(defun split-list (x)
  (cond ((atom x) (mv nil nil))
	((atom (cdr x)) (mv x nil))
	(t (mv-let (a b)
		   (split-list (cddr x))
		   (mv (cons (car x) a) (cons (cadr x) b))))))

(defun merge2 (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (cond ((atom x) y)
	((atom y) x)
	((< (car x) (car y))
	 (cons (car x) (merge2 (cdr x) y)))
	(t (cons (car y) (merge2 x (cdr y))))))

(defthm split-list-smaller
  (implies (and (consp x) (consp (cdr x)))
           (and (< (acl2-count (car (split-list x)))
                   (acl2-count x))
                ;; Originally we used (cadr ..) instead of (mv-nth 1 ..) below,
                ;; but the mv-nth didn't open up to cadr in the termination
                ;; proof of mergesort, so we are going with mv-nth below.
                (< (acl2-count (mv-nth 1 (split-list x)))
                   (acl2-count x)))))

(defun mergesort (x)
  (cond ((atom x) nil)
	((atom (cdr x)) x)
	(t (mv-let (a b)
		   (split-list x)
		   (merge2 (mergesort a) (mergesort b))))))

(defun orderedp (x)
  (cond ((atom (cdr x)) t)
	(t (and (<= (car x) (cadr x))
		(orderedp (cdr x))))))

; We might have first proved a lemma about (orderedp (merge2 x y)) first, but
; the following goes through automatically.

(defthm orderedp-mergesort
  (orderedp (mergesort lst)))

; ---------------------------------------------------------------------------
; Exercise 11.16

(include-book "perm")

; Our attempt to prove perm-mergesort automatically is not successful.  Here is
; the first simplification checkpoint.

#|
Subgoal *1/3'''
(IMPLIES (AND (CONSP LST)
              (CONSP (CDR LST))
              (PERM (MERGESORT (CAR (SPLIT-LIST LST)))
                    (CAR (SPLIT-LIST LST)))
              (PERM (MERGESORT (MV-NTH 1 (SPLIT-LIST LST)))
                    (MV-NTH 1 (SPLIT-LIST LST))))
         (PERM (MERGE2 (MERGESORT (CAR (SPLIT-LIST LST)))
                       (MERGESORT (MV-NTH 1 (SPLIT-LIST LST))))
               LST))
|#

; If we think of perm as an equivalence relation like equal, we can imagine
; using the hypotheses above to eliminate the mergesort terms in the
; conclusion, provided that merge2 preserves perm when each of its
; arguments is replaced by one that is perm-equivalent to it.  Since merge2 is
; a bit complicated to reason about (feel free to try!), we choose to trade in
; merge2 for append.  For that purpose, it is likely to be useful to use our
; previously-proved results about perm and append:

(include-book "perm-append")

; We try merge2-is-append with the :induct hint shown below, since that seems
; to leave us with goals that involve append rather than merge2.  Here, for
; example, is the first simplification checkpoint.

#|
Subgoal *1/4.2
(IMPLIES (AND (CONSP X)
              (CONSP Y)
              (<= (CAR Y) (CAR X))
              (PERM (MERGE2 X (CDR Y))
                    (APPEND X (CDR Y)))
              (IN (CAR Y) X))
         (PERM (APPEND X (CDR Y))
               (APPEND (DEL (CAR Y) X) Y)))
|#

; This suggests the lemma perm-append-del below.  If we imagine switching the
; arguments to each call of append in that lemma, it looks quite trivial.  So,
; the following lemma makes the proof of perm-append-del simple.

(defthm perm-append
  (perm (append x y) (append y x)))

(defthm perm-append-del
  (implies (and (consp y)
                (in (car y) x))
           (perm (append (del (car y) x) y)
                 (append x (cdr y)))))

(defthm merge2-is-append
  (perm (merge2 x y)
        (append x y))
  :hints (("Goal" :induct (merge2 x y))))

; Now let us try perm-mergesort again.  The first simplification checkpoint is
; shown below.

#|
Subgoal *1/3'''
(IMPLIES (AND (CONSP LST)
              (CONSP (CDR LST))
              (PERM (MERGESORT (CAR (SPLIT-LIST LST)))
                    (CAR (SPLIT-LIST LST)))
              (PERM (MERGESORT (MV-NTH 1 (SPLIT-LIST LST)))
                    (MV-NTH 1 (SPLIT-LIST LST))))
         (PERM (APPEND (CAR (SPLIT-LIST LST))
                       (MV-NTH 1 (SPLIT-LIST LST)))
               LST))
|#

; This suggests the lemma perm-append-spit-list below.  The proof attempt fails
; with the first simplification checkpoint shown here:

#|
Subgoal *1/3''
(IMPLIES (AND (CONSP LST)
              (CONSP (CDR LST))
              (PERM (APPEND (CAR (SPLIT-LIST (CDDR LST)))
                            (MV-NTH 1 (SPLIT-LIST (CDDR LST))))
                    (CDDR LST)))
         (PERM (APPEND (CAR (SPLIT-LIST (CDDR LST)))
                       (CONS (CADR LST)
                             (MV-NTH 1 (SPLIT-LIST (CDDR LST)))))
               (CDR LST)))
|#

; This suggests pulling the cons out from under the append in the conclusion.

(defthm perm-append-cons-2
  (perm (append x (cons a y))
        (cons a (append x y))))

(defthm perm-append-split-list
  (perm (append (car (split-list lst)) (mv-nth 1 (split-list lst)))
        lst))

(defthm perm-mergesort
  (perm (mergesort lst) lst))
