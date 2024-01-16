(in-package "ACL2")

; ---------------------------------------------------------------------------
; Exercise 11.17

(defun compress (x)
  (cond ((or (endp x) (endp (cdr x)))
	 x)
	((equal (car x) (cadr x))
	 (compress (cdr x)))
	(t (cons (car x) (compress (cdr x))))))

; ---------------------------------------------------------------------------
; Exercise 11.18


; An attempt to prove compress-compress below yields the following as the first
; simplification checkpoint.

#|
Subgoal *1/3''
(IMPLIES (AND (CONSP X)
              (CONSP (CDR X))
              (NOT (EQUAL (CAR X) (CADR X)))
              (EQUAL (COMPRESS (COMPRESS (CDR X)))
                     (COMPRESS (CDR X)))
              (CONSP (COMPRESS (CDR X))))
         (NOT (EQUAL (CAR X)
                     (CAR (COMPRESS (CDR X))))))
|#

; We see a term of the form (car (compress ..)) and this suggests the following
; lemma.

(defthm car-compress
  (implies (consp x)
           (equal (car (compress x))
                  (car x))))

(defthm compress-compress
  (equal (compress (compress x))
         (compress x)))

; ---------------------------------------------------------------------------
; Exercise 11.19


; Now we attempt to prove compress-append-compress.  The first simplification
; checkpoint is as follows.

#|
Subgoal *1/2.3.1'
(IMPLIES (AND (CONSP X)
              (EQUAL (COMPRESS (APPEND (COMPRESS (CDR X)) Y))
                     (COMPRESS (APPEND (CDR X) Y)))
              (CONSP (CDR X))
              (NOT (EQUAL (CAR X) (CADR X)))
              (CONSP (APPEND (CDR X) Y))
              (NOT (EQUAL (CAR X)
                          (CAR (APPEND (CDR X) Y))))
              (CONSP (APPEND (COMPRESS (CDR X)) Y)))
         (NOT (EQUAL (CAR X)
                     (CAR (APPEND (COMPRESS (CDR X)) Y)))))
|#

; We can get ACL2 to simplify the last line of this goal using the following two
; lemmas.

(defthm car-append
  (equal (car (append x y))
         (if (consp x)
             (car x)
           (car y))))

(defthm consp-compress
  (equal (consp (compress x))
         (consp x)))

(defthm compress-append-compress
  (equal (compress (append (compress x) y))
         (compress (append x y))))

; ---------------------------------------------------------------------------
; Exercise 11.20

(defun mem (e x)
  (if (endp x)
      nil
    (if (equal e (car x))
        t
      (mem e (cdr x)))))

(defun no-dupls-p (x)
  (cond ((endp x) t)
        ((mem (car x) (cdr x)) nil)
        (t (no-dupls-p (cdr x)))))

(defun orderedp (x)
  (cond ((atom (cdr x)) t)
	(t (and (<= (car x) (cadr x))
		(orderedp (cdr x))))))

; We wish to prove something like the following.

#|
(defthm no-dupls-p-compress
  (implies (orderedp x)
           (no-dupls-p (compress x))))
|#

; An attempt to prove no-dupls-p-compress as stated above leaves us with the
; following simplification checkpoint:

#|
Subgoal *1/5'
(IMPLIES (AND (CONSP X)
              (CONSP (CDR X))
              (NOT (EQUAL (CAR X) (CADR X)))
              (NO-DUPLS-P (COMPRESS (CDR X)))
              (<= (CAR X) (CADR X))
              (ORDEREDP (CDR X)))
         (NOT (MEM (CAR X) (COMPRESS (CDR X)))))
|#

; The last line above suggests the following lemma.

(defthm mem-compress
  (equal (mem a (compress x))
         (mem a x)))

; Now when we try no-dupls-p-compress above again, the proof fails in a
; different way, leaving us with this checkpoint:

#|
Subgoal *1/5'
(IMPLIES (AND (CONSP X)
              (CONSP (CDR X))
              (NOT (EQUAL (CAR X) (CADR X)))
              (NO-DUPLS-P (COMPRESS (CDR X)))
              (<= (CAR X) (CADR X))
              (ORDEREDP (CDR X)))
         (NOT (MEM (CAR X) (CDR X))))
|#

; This formula is not a theorem because it is treating the elements of X as
; rationals (they are being compared with <=) but there is no requirement that
; they are numbers.  For example, let X be '(t nil t).  Then the hypotheses are
; all true but the conclusion is not.  We can test that claim by execution but
; we first have to turn off guard checking since <=.  (Note: (<= i j)
; macroexpands to (not (< j i)), and < has a guard requiring its arguments to
; be rationals.  Logically speaking though, (< j i) defaults each argument to 0
; if it's not rational.  By turning off guard checking we cause the ACL2 evaluation
; mechanism to just adhere to the axiomatic semantics without imposing the runtime
; expectations on guards.)

#|
ACL2 !>:set-guard-checking nil

Masking guard violations but still checking guards except for self-
recursive calls.  To avoid guard checking entirely, :SET-GUARD-CHECKING
:NONE.  See :DOC set-guard-checking.

ACL2 >(let ((x '(t nil t)))
;Subgoal *1/5'
(IMPLIES (AND (CONSP X)
              (CONSP (CDR X))
              (NOT (EQUAL (CAR X) (CADR X)))
              (NO-DUPLS-P (COMPRESS (CDR X)))
              (<= (CAR X) (CADR X))
              (ORDEREDP (CDR X)))
         (NOT (MEM (CAR X) (CDR X)))))
NIL

; In fact, our main ``theorem,'' no-dupls-p-compress, is not a theorem
; either!

ACL2 >(let ((x '(t nil t)))
	 (implies (orderedp x)
		  (no-dupls-p (compress x))))
NIL
ACL2 >(let ((x '(t nil t)))
	 (compress x))
(T NIL T)
ACL2 >

; So we introduce the notion of a list of numbers (we could restrict it
; rationals but needn't) and add that hypothesis to the main theorem to
; finish the exercise.
|#

(defun number-listp (x)
  (if (endp x)
      t
    (and (acl2-numberp (car x))
         (number-listp (cdr x)))))

(defthm no-dupls-p-compress
  (implies (and (orderedp x)
                (number-listp x))
           (no-dupls-p (compress x))))

; ---------------------------------------------------------------------------
; Exercise 11.21

(defun same-compress (x y)
  (equal (compress x) (compress y)))

; ---------------------------------------------------------------------------
; Exercise 11.22

(defequiv same-compress)

; ---------------------------------------------------------------------------
; Exercise 11.23

; The defcong below fails to be proved, generatig the following as the first
; simplification checkpoint.

#|
Subgoal *1/2.4''
(IMPLIES (AND (CONSP X)
              (EQUAL (COMPRESS Y) (COMPRESS Y-EQUIV))
              (CONSP Y)
              (NOT (CONSP (CDR X)))
              (NOT (EQUAL (CAR X) (CAR Y)))
              (CONSP Y-EQUIV))
         (NOT (EQUAL (CAR X) (CAR Y-EQUIV))))
|#

; The second hypothesis tells us that y and y-equiv have the first element,
; which is enough to prove the goal; so we bring such information to the
; attention of ACL2 with equal-compresses-forward-to-equal-cars below.  We try
; a proof by induction, but the prover chooses to induct on (compress x).  We
; define a function that cdrs both x and y as it recurs and then use that
; function in an :induct hint, but that approach fails.  Then we realize that
; we can use the previously proved result car-compress, so we do so, disabling
; this rule so that the :use hint isn't undone by rewriting.

(defthm equal-compresses-forward-to-equal-cars
  (implies (and (equal (compress x) (compress y))
                (consp x))
           (equal (car x) (car y)))
  :hints (("Goal" :use
           (car-compress
            (:instance car-compress (x y)))
           :in-theory (disable car-compress)))
  :rule-classes :forward-chaining)

(defcong same-compress same-compress (append x y) 2)

; ---------------------------------------------------------------------------
; Exercise 11.24

; The next defcong takes some more work.  After struggling for a bit, we choose
; to do some thinking (!).  Consider the following.

#|
ACL2 !>:trans1 (defcong same-compress same-compress (append x y) 1)
 (DEFTHM SAME-COMPRESS-IMPLIES-SAME-COMPRESS-APPEND-1
         (IMPLIES (SAME-COMPRESS X X-EQUIV)
                  (SAME-COMPRESS (APPEND X Y)
                                 (APPEND X-EQUIV Y)))
         :RULE-CLASSES (:CONGRUENCE))
ACL2 !>
|#

; If we can replace same-compress by its definition

#|
 (implies (equal (compress x) (compress x-equiv))
          (equal (compress (append x y))
                 (compress (append x-equiv y))))
|#

; then we can see that when we use previous result compress-append-compress to
; replace (append x y) by (append (compress x) y) and simiarly for the other
; append call above, the result will be trivial.

(defcong same-compress same-compress (append x y) 1
  :hints
  (("Goal" :use
    (compress-append-compress
     (:instance compress-append-compress (x x-equiv)))
    ;; Disable the rule used above so that the used terms aren't rewritten
    ;; away:
    :in-theory (disable compress-append-compress))))

; ---------------------------------------------------------------------------
; Exercise 11.25

; Here is the definition of rev (along its supporting function, app) from the
; book.

(defun app (x y)
  (if (endp x)
      y
    (cons (car x)
          (app (cdr x) y))))

(defun rev (x)
  (if (endp x)
      nil
    (app (rev (cdr x)) (list (car x)))))

; Since we have already done some exercises above involving append, we
; eliminate app in favor of append so that we only have to reason about one of
; these notions below.

(defthm app-is-append
  (equal (app x y)
         (append x y)))

; When we try to prove rev-compress we get the following as the first
; simplification checkpoint.

#|
Subgoal *1/2.2'
(IMPLIES (AND (CONSP X)
              (EQUAL (REV (COMPRESS (CDR X)))
                     (COMPRESS (REV (CDR X))))
              (CONSP (CDR X))
              (EQUAL (CAR X) (CADR X)))
         (EQUAL (COMPRESS (REV (CDR X)))
                (COMPRESS (APPEND (REV (CDR X))
                                  (LIST (CAR X))))))
|#

; Let us prove a rule simplifying terms of the form (compress (append ..)).

(defthm compress-append-to-singleton
  (equal (compress (append x (list a)))
         (if (and (consp x)
                  (equal (car (last x)) a))
             (append (compress x) nil)
           (append (compress x) (list a)))))

; The next try yields the following as the first simplification checkpoint.

#|
Subgoal *1/2.6'
(IMPLIES (AND (CONSP X)
              (EQUAL (REV (COMPRESS (CDR X)))
                     (COMPRESS (REV (CDR X))))
              (CONSP (CDR X))
              (NOT (EQUAL (CAR X) (CADR X)))
              (CONSP (REV (CDR X)))
              (EQUAL (CAR (LAST (REV (CDR X))))
                     (CAR X)))
         (EQUAL (APPEND (COMPRESS (REV (CDR X)))
                        (LIST (CAR X)))
                (APPEND (COMPRESS (REV (CDR X))) NIL)))
|#

; The hypotheses are contradictory, as is seen from the following lemma.

(defthm car-last-rev
  (implies (consp x)
           (equal (car (last (rev x)))
                  (car x))))

; Tryig rev-compress again, we get the following as the first simplification
; checkpoint.

#|
Subgoal *1/2.5'
(IMPLIES (AND (CONSP X)
              (EQUAL (REV (COMPRESS (CDR X)))
                     (COMPRESS (REV (CDR X))))
              (CONSP (CDR X))
              (EQUAL (CAR X) (CADR X))
              (CONSP (REV (CDR X))))
         (EQUAL (COMPRESS (REV (CDR X)))
                (APPEND (COMPRESS (REV (CDR X))) NIL))).
|#

; This is clear if the compress term on the last line above returnss a
; true-listp, which follows from the following three rules.

(defthm true-listp-rev
  (true-listp (rev x))
  ;; might as well make it a type-prescription rule
  :rule-classes :type-prescription)

(defthm true-listp-compress
  (equal (true-listp (compress x))
         (true-listp x)))

(defthm append-to-nil
  (implies (true-listp x)
           (equal (append x nil) x)))

(defthm rev-compress
  (equal (rev (compress x))
         (compress (rev x))))
