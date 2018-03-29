
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; disjoint.lisp
;;;
;;; disjointp, range, and subrange are the main functions defined in
;;; this book.  The first two will be used to specify pairwise
;;; disjoint memory regions.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(table acl2-defaults-table :state-ok t)

(local
 (include-book "arithmetic/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; I like a boolean membership test.

(defun memberp (e x)
  (declare (xargs :guard t))
  (cond ((atom x)
         'NIL)
        ((equal e (car x))
         'T)
        (t
         (memberp e (cdr x)))))

(defthm |(memberp e (list x))|
  (implies (equal e x)
           (memberp e (list x))))

;;; a few utility functions

(defun arg1 (x)
  ;; copied from arithmetic-5
  (declare (xargs :guard t))
  (if (and (consp x) (consp (cdr x)))
      (cadr x)
      nil))

(defun arg2 (x)
  ;; copied from arithmetic-5
  (declare (xargs :guard t))
  (if (and (consp x)
           (consp (cdr x))
           (consp (cddr x)))
      (caddr x)
      nil))

(defun non-quotep-addends (sum)
  (declare (xargs :guard t))
  (if (eq (fn-symb sum) 'BINARY-+)
      (if (quotep (arg1 sum))
          (non-quotep-addends (arg2 sum))
        (cons (arg1 sum)
              (non-quotep-addends (arg2 sum))))
    (list sum)))

(defun rewriting-goal-literal (x mfc state)
  ;; copied from arithmetic-5
  (declare (xargs :guard t))
  (declare (ignore x state))
  (null (mfc-ancestors mfc)))

(defun term-equal (term1 term2)
  ;; copied from arithmetic-5
  (declare (xargs :guard t))
  (if (equal (fn-symb term1) 'EQUAL)
      (and (equal (fn-symb term2) 'EQUAL)
	   (or (and (equal (arg1 term1) (arg1 term2))
		    (equal (arg2 term1) (arg2 term2)))
	       (and (equal (arg1 term1) (arg2 term2))
		    (equal (arg2 term1) (arg1 term2)))))
    (equal term1 term2)))

(defun present-in-hyps (term goal)
  ;; copied from arithmetic-5
  (declare (xargs :guard t))
  (cond ((atom goal)  ; for the guard.
	 nil)
	((atom (cdr goal))
	 ;; We only check the hypotheses of a goal, not the
	 ;; conclusion.  Presumably, if a weak inequality
	 ;; appeared in the conclusion, the goal would already
	 ;; have been proven via linear arithmetic.
         nil)
        ((term-equal term (car goal))
         'positive)
        ((and (eq (fn-symb (car goal)) 'NOT)
              (term-equal term (arg1 (car goal))))
         'negative)
        (t
         (present-in-hyps term (cdr goal)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun disjoint-bags-p (x y)
  (cond ((endp x)
         'T)
        ((memberp (car x) y)
         'NIL)
        (t
         (disjoint-bags-p (cdr x) y))))

(defun disjointp-1 (x list)
  (cond ((endp list)
         'T)
        ((disjoint-bags-p x (car list))
         (disjointp-1 x (cdr list)))
        (t
         'NIL)))

(defun disjointp (list)
  (cond ((endp list)
         'T)
        ((disjointp-1 (car list) (cdr list))
         (disjointp (cdr list)))
        (t
         'NIL)))

(local
 (defthm disjointp-thm-1
   (implies (and (disjointp list)
                 (memberp x list)
                 (memberp y list)
                 (not (equal x y))
                 (memberp e1 x)
                 (memberp e2 y))
            (not (equal e1 e2)))
   :rule-classes nil))

(local
 (encapsulate
  ()

  (local
   (defthm crock-1
     (implies (memberp e1 (nth i list))
              (memberp (nth i list) list))))

  (local
   (defthm crock-2
     (implies (and (DISJOINTP-1 x list)
                   (MEMBERP E1 x))
              (NOT (MEMBERP E1 (NTH j list))))))

  (defthm disjoint-thm-2
    (implies (and (disjointp list)
                  (equal (nth i list) x)
                  (equal (nth j list) y)
                  (natp i)
                  (natp j)
                  (not (equal i j))
                  (memberp e1 x)
                  (memberp e2 y))
             (not (equal e1 e2)))
    :hints (("Goal" :use ((:instance disjointp-thm-1
                                     (x (nth i list))
                                     (y (nth j list))))))
    :rule-classes nil)
  ))

(in-theory (disable memberp
                   disjoint-bags-p
                   disjointp-1
                   disjointp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun range-1 (start end acc)
  (declare (xargs :measure (nfix (+ 1 end (- start)))))
  (cond ((or (not (integerp start))
             (not (integerp end))
             (< (+ end (- start)) 0))
         acc)
        (t
         (range-1 start (+ -1 end) (cons end acc)))))

(defun range (base offset length)
  (range-1 (+ base offset) (+ -1 base offset length) nil))

(encapsulate
 ()

 (local
  (in-theory (enable memberp)))

 (local
  (defthm crock-1-1
    (implies (and (memberp e acc)
                  (integerp start)
                  (integerp end))
             (memberp e (range-1 start end acc)))))

 (local
  (defthm crock-1
    (implies (and (integerp e)
                  (integerp start)
                  (integerp end)
                  (<= start e)
                  (<= e end)
                  )
             (memberp e (range-1 start end acc)))
    :hints (("Subgoal *1/3" :expand ((RANGE-1 START E ACC))))))

 (defthm |(memberp e (range base offset length))|
   (implies (and (integerp e)
                 (integerp base)
                 (integerp offset)
                 (integerp length)
                 (<= (+ base offset) e)
                 (<= e (+ -1 base offset length)))
            (memberp e (range base offset length))))
 )

(in-theory (disable range-1
                    range))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun subrangep (range1 range2)
  (cond ((endp range1)
         'T)
        ((memberp (car range1) range2)
         (subrangep (cdr range1) range2))
        (t
         'NIL)))

(local
 (defthm |(disjointp subrange1 subrange2)|
   (implies (and (disjointp (list range1 range2))
                 (subrangep subrange1 range1)
                 (subrangep subrange2 range2))
            (disjointp (list subrange1 subrange2)))
   :hints (("Goal" :in-theory (enable disjointp
                                      disjointp-1
                                      disjoint-bags-p
                                      memberp)))))

(encapsulate
 ()

 (local
  (defun range-1-v2 (start end)
    (declare (xargs :measure (nfix (+ 1 (+ end (- start))))))
    (cond ((or (not (integerp start))
               (not (integerp end))
               (< (+ end (- start)) 0))
           '())
          (t
           (cons start (range-1-v2 (+ 1 start) end))))))

 (local
  (defun range-v2 (base offset length)
    (range-1-v2 (+ base offset) (+ -1 base offset length))))

 (local
  (defthm crock-1-1-1
    (IMPLIES (AND (INTEGERP START)
                  (INTEGERP END)
                  (<= 0 (+ END (- START))))
             (equal (APPEND (RANGE-1-V2 START (+ -1 END))
                            (CONS END ACC))
                    (APPEND (RANGE-1-V2 START END) ACC)))))

 (local
  (defthm crock-1-1
    (EQUAL (RANGE-1 start
                    end
                    acc)
           (append (RANGE-1-V2 start
                               end)
                   acc))
    :hints (("Goal" :in-theory (enable range-1)))))

 (local
  (defthm crock-1
    (equal (range base offset length)
           (range-v2 base offset length))
    :hints (("Goal" :in-theory (enable range)))))

 (local
  (defthm crock-2-2
    (IMPLIES (AND (<= START1 END2)
                  (INTEGERP START1)
                  (INTEGERP START2)
                  (<= START2 START1)
                  (INTEGERP END2))
             (MEMBERP START1 (RANGE-1-V2 START2 END2)))
    :hints (("Goal" :in-theory (enable memberp)))))

 (local
  (defthm crock-2
    (IMPLIES (AND (INTEGERP start1)
                  (INTEGERP start2)
                  (<= start2 start1)
                  (INTEGERP end1)
                  (INTEGERP end2)
                  (<= end1
                      end2))
             (SUBRANGEP (RANGE-1-V2 start1
                                    end1)
                        (RANGE-1-V2 start2
                                    end2)))))

 ;; We export this
 (defthm |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|
   ;; The syntaxp test is meant to limit "useless" work.  Is this
   ;; safe?
   (implies (and (syntaxp (intersectp-equal (non-quotep-addends base1)
                                            (non-quotep-addends base2)))
                 (integerp base1)
                 (integerp base2)
                 (integerp offset1)
                 (integerp offset2)
                 (integerp length1)
                 (integerp length2)
                 (<= (+ base2 offset2)
                     (+ base1 offset1))
                 (<= (+ base1 offset1 length1)
                     (+ base2 offset2 length2)))
            (subrangep (range base1 offset1 length1)
                       (range base2 offset2 length2)))
   :hints (("Goal" :in-theory (enable range))))
 )

(defthm |(subrangep (list x) (range base offset length))|
  ;; The syntaxp test is meant to limit "useless" work.  Is this safe?
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends x)
                                           (non-quotep-addends base)))
                (integerp x)
                (integerp base)
                (integerp offset)
                (integerp length)
                 (<= (+ base offset)
                     x)
                 (<= (+ 1 x)
                     (+ base offset length)))
           (subrangep (list x)
                      (range base offset length)))
  :hints (("Goal" :use ((:instance  |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|
                                    (base1 x)
                                    (offset1 0)
                                    (length1 1)
                                    (base2 base)
                                    (offset2 offset)
                                    (length2 length))))))

(defthm |(subrangep (range base offset length) (list x)|
  ;; The syntaxp test is meant to limit "useless" work.  Is this safe?
  (implies (and (syntaxp (intersectp-equal (non-quotep-addends base)
                                           (non-quotep-addends x)))
                (integerp base)
                (integerp offset)
                (equal length 1)
                (equal (+ base offset) x))
           (subrangep (range base offset length)
                      (list x)))
  :hints (("Goal" :expand ((RANGE BASE OFFSET 1)
                           (RANGE-1 (+ BASE OFFSET)
                                    (+ BASE OFFSET)
                                    NIL)
                           (RANGE-1 (+ BASE OFFSET)
                                    (+ -1 BASE OFFSET)
                                    (LIST (+ BASE OFFSET)))))))

;;; If you remove the syntaxp test below, be ready for some surprises.
;;; The problem stem from ancestors-check.  To see what is going on,
;;; consider how we could get here.  In memory-low, we are using
;;; disjointp hypotheses to prove that addr1 is not equal to addr2 ---
;;; that is we have to relieve the hypothesis
;;; (not (equal addr1 addr2)).  So, (equal addr1 addr2) is pushed on
;;; to the ancestors stack.  Now, if in disjoint-thms-bind-free-fn-4
;;; we ask (subrangep (list addr1) (list addr2)), this will rewrite to
;;; true!  After all, they are assumed to be equal!  This should be
;;; fixable by hacking at ancestors-check some more.

(defthm |(subrangep (list x) (list y)|
  ;; The syntaxp test is meant to limit "useless" work.  Is this safe?
  (implies (and (syntaxp (equal x y))
                (equal x y))
           (subrangep (list x)
                      (list y))))

(encapsulate
 ()

 (local
  (defthm crock-1
    (implies (subrangep x (cdr y))
             (subrangep x y))
    :hints (("Goal" :in-theory (enable memberp)))))

 (defthm |(subrangep x x)|
   (subrangep x x)
   :hints (("Goal" :in-theory (enable memberp))))
 )

(in-theory (disable subrangep))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Now we can start the show.

(defun disjoint-thms-bind-free-fn-4 (subrange range mfc state)
  ;; We use the intersectp-equal tests to try to limit the number of
  ;; calls to mfc-rw+.  Is this the right test?
  (declare (xargs :guard t))
  (equal (mfc-rw+ '(subrangep subrange range)
                  `((SUBRANGE . ,subrange)
                    (RANGE    . ,range))
                  t t mfc state)
         *t*))

(defun disjoint-thms-bind-free-fn-3 (range range-list i mfc state)
  ;; we paw through the range-list for a match.
  ;;
  ;; The range-list is presumably a CONS structure, hence the use of
  ;; arg1 and arg2 in our search.
  (declare (xargs :guard (integerp i)
                  :hints (("Goal" :in-theory (disable disjoint-thms-bind-free-fn-4)))))
  (cond ((atom range-list)
         (mv nil nil))
        ((equal (fn-symb range-list) 'CONS)
         (if (disjoint-thms-bind-free-fn-4 range
                                           (arg1 range-list)
                                           mfc state)
             (mv (arg1 range-list) (kwote i))
           (disjoint-thms-bind-free-fn-3 range
                                         (arg2 range-list)
                                         (+ 1 i)
                                         mfc state)))
        (t
         (mv nil nil))))

(defun disjoint-thms-bind-free-fn-2 (range1 range2 range-list mfc state)
  ;; can we match the two ranges in hand to the range-list?
  (declare (xargs :guard t))
  (mv-let (r1 i)
    (disjoint-thms-bind-free-fn-3 range1
                                  range-list 0
                                  mfc state)
    (if r1
        (mv-let (r2 j)
          (disjoint-thms-bind-free-fn-3 range2
                                        range-list 0
                                        mfc state)
          (if r2
              (list (cons 'list range-list)
                    (cons 'r1 r1)
                    (cons 'r2 r2)
                    (cons 'i i)
                    (cons 'j j))
            'NIL))
      'NIL)))

(defun disjoint-thms-bind-free-fn-1 (range1 range2 clause mfc state)
  ;; We recur through the clause, looking for disjointp lists
  (declare (xargs :guard t))
  (cond ((atom clause)
         'NIL)
        ((and (equal (fn-symb (car clause))
                     'NOT)
              (equal (fn-symb (arg1 (car clause)))
                     'DISJOINTP))
         ;; grab the list of disjoint bags, and pass it on in.
         (let ((ans (disjoint-thms-bind-free-fn-2 range1 range2
                                                  (arg1 (arg1 (car clause)))
                                                  mfc state)))
           (if ans
               ;; success
               ans
             ;; try again
             (disjoint-thms-bind-free-fn-1 range1 range2
                                           (cdr clause)
                                           mfc state))))
        (t
         (disjoint-thms-bind-free-fn-1 range1 range2
                                       (cdr clause)
                                       mfc state))))

(defun disjoint-thms-bind-free-fn (range1 range2 mfc state)
  (declare (xargs :guard t))
  (disjoint-thms-bind-free-fn-1 range1 range2
                                (mfc-clause mfc)
                                mfc state))

;;; Too expensive and unlikely to apply for general use.  But, we will
;;; need it in memory-low, to transition away from memory-acl2's use
;;; of equality.
(defthm |(not (equal x y)) --- disjointp|
  (implies (and (syntaxp (not (rewriting-goal-literal x mfc state)))
                (bind-free (disjoint-thms-bind-free-fn `(CONS ,x 'NIL)
                                                       `(CONS ,y 'NIL)
                                                       mfc state)
                           (list r1 r2 i j))
                (disjointp list)
                (equal (nth i list) r1)
                (equal (nth j list) r2)
                (natp i)
                (natp j)
                (not (equal i j))
                (memberp x r1)
                (memberp y r2))
           (not (equal x y)))
  :hints (("Goal" :use ((:instance disjoint-thm-2
                                   (x r1)
                                   (y r2)
                                   (e1 x)
                                   (e2 y))))))

(in-theory (disable |(not (equal x y)) --- disjointp|))

(encapsulate
 ()

(local
 (defthm crock-1-1
   (implies (disjointp-1 x list)
            (disjoint-bags-p x (nth i list)))
   :hints (("Goal" :in-theory (enable disjointp
                                      disjointp-1
                                      disjoint-bags-p
                                      memberp)))))

(local
 (defthm crock-1-2
   (disjoint-bags-p x nil)
   :hints (("Goal" :in-theory (enable disjointp
                                      disjointp-1
                                      disjoint-bags-p
                                      memberp)))))

(local
 (defthm crock-1-3
   (equal (disjoint-bags-p y x)
          (disjoint-bags-p x y))
   :hints (("Goal" :in-theory (enable disjointp
                                      disjointp-1
                                      disjoint-bags-p
                                      memberp)))))


(local
 (defthm crock-1
   (implies (AND (DISJOINTP LIST)
                 (NATP I)
                 (NATP J)
                 (NOT (EQUAL I J)))
            (DISJOINT-BAGS-P (NTH I LIST)
                             (NTH J LIST)))
   :hints (("Goal" :in-theory (enable disjointp
                                      disjointp-1
                                      disjoint-bags-p
                                      memberp)))))

;;; Are we either backchaining, or rewriting a (not (disjointp ...))
;;; hypothesis.
;;; We need this as a separate function, because if mfc is used, it
;;; and state must be the last two args of the syntaxp, and they must
;;; appear in that order.
(defun disjoint-syntaxp-fn (x y mfc state)
  (or (not (rewriting-goal-literal x mfc state))
      (equal (present-in-hyps `(DISJOINTP (CONS ,x
                                                (CONS ,y 'NIL)))
                              (mfc-clause mfc))
             'positive)))

(defthm |(disjointp (list x y)) --- disjoint super-ranges|
   (implies (and (syntaxp (disjoint-syntaxp-fn x y mfc state))
                 (bind-free (disjoint-thms-bind-free-fn x y mfc state)
                            (list r1 r2 i j))
                 (disjointp list)
                 (equal (nth i list) r1)
                 (equal (nth j list) r2)
                 (natp i)
                 (natp j)
                 (not (equal i j))
                 (subrangep x r1)
                 (subrangep y r2))
            (disjointp (list x y)))
   :hints (("Goal" :use ((:instance |(disjointp subrange1 subrange2)|
                                    (range1 (NTH I LIST))
                                    (range2 (NTH J LIST) )
                                    (subrange1 x)
                                    (subrange2 y)))
            :in-theory (e/d (disjointp
                             disjointp-1
                             disjoint-bags-p
                             memberp)
                            ())))
   :otf-flg t)
)


;;; !!! Why did I not see this before !!!
;;; Need to fix above, so that it generalizes to n regions.
(defthm disjoint-3-items
  (implies (and (disjointp (list x y))
                (disjointp (list x z))
                (disjointp (list y z)))
           (disjointp (list x y z)))
  :hints (("Goal" :in-theory (enable disjointp
                                     disjointp-1))))

(defthm disjoint-4-items
  (implies (and (disjointp (list w x))
                (disjointp (list w y))
                (disjointp (list w z))
                (disjointp (list x y))
                (disjointp (list x z))
                (disjointp (list y z)))
           (disjointp (list w x y z)))
  :hints (("Goal" :in-theory (enable disjointp
                                     disjointp-1))))

(defthm disjoint-5-items
  (implies (and (disjointp (list v w))
                (disjointp (list v x))
                (disjointp (list v y))
                (disjointp (list v z))
                (disjointp (list w x))
                (disjointp (list w y))
                (disjointp (list w z))
                (disjointp (list x y))
                (disjointp (list x z))
                (disjointp (list y z)))
           (disjointp (list v w x y z)))
  :hints (("Goal" :in-theory (enable disjointp
                                     disjointp-1))))

(defthm disjoint-6-items
  (implies (and (disjointp (list u v))
                (disjointp (list u w))
                (disjointp (list u x))
                (disjointp (list u y))
                (disjointp (list u z))
                (disjointp (list v w))
                (disjointp (list v x))
                (disjointp (list v y))
                (disjointp (list v z))
                (disjointp (list w x))
                (disjointp (list w y))
                (disjointp (list w z))
                (disjointp (list x y))
                (disjointp (list x z))
                (disjointp (list y z)))
           (disjointp (list u v w x y z)))
  :hints (("Goal" :in-theory (enable disjointp
                                     disjointp-1))))

(defthm disjoint-7-items
  (implies (and (disjointp (list s u))
                (disjointp (list s v))
                (disjointp (list s w))
                (disjointp (list s x))
                (disjointp (list s y))
                (disjointp (list s z))
                (disjointp (list u v))
                (disjointp (list u w))
                (disjointp (list u x))
                (disjointp (list u y))
                (disjointp (list u z))
                (disjointp (list v w))
                (disjointp (list v x))
                (disjointp (list v y))
                (disjointp (list v z))
                (disjointp (list w x))
                (disjointp (list w y))
                (disjointp (list w z))
                (disjointp (list x y))
                (disjointp (list x z))
                (disjointp (list y z)))
           (disjointp (list s u v w x y z)))
  :hints (("Goal" :in-theory (enable disjointp
                                     disjointp-1))))

(defthm disjoint-8-items
  (implies (and (disjointp (list r s))
                (disjointp (list r u))
                (disjointp (list r v))
                (disjointp (list r w))
                (disjointp (list r x))
                (disjointp (list r y))
                (disjointp (list r z))
                (disjointp (list s u))
                (disjointp (list s v))
                (disjointp (list s w))
                (disjointp (list s x))
                (disjointp (list s y))
                (disjointp (list s z))
                (disjointp (list u v))
                (disjointp (list u w))
                (disjointp (list u x))
                (disjointp (list u y))
                (disjointp (list u z))
                (disjointp (list v w))
                (disjointp (list v x))
                (disjointp (list v y))
                (disjointp (list v z))
                (disjointp (list w x))
                (disjointp (list w y))
                (disjointp (list w z))
                (disjointp (list x y))
                (disjointp (list x z))
                (disjointp (list y z)))
           (disjointp (list r s u v w x y z)))
  :hints (("Goal" :in-theory (enable disjointp
                                     disjointp-1))))

(defthm disjoint-9-items
  (implies (and (disjointp (list q r))
                (disjointp (list q s))
                (disjointp (list q u))
                (disjointp (list q v))
                (disjointp (list q w))
                (disjointp (list q x))
                (disjointp (list q y))
                (disjointp (list q z))
                (disjointp (list r s))
                (disjointp (list r u))
                (disjointp (list r v))
                (disjointp (list r w))
                (disjointp (list r x))
                (disjointp (list r y))
                (disjointp (list r z))
                (disjointp (list s u))
                (disjointp (list s v))
                (disjointp (list s w))
                (disjointp (list s x))
                (disjointp (list s y))
                (disjointp (list s z))
                (disjointp (list u v))
                (disjointp (list u w))
                (disjointp (list u x))
                (disjointp (list u y))
                (disjointp (list u z))
                (disjointp (list v w))
                (disjointp (list v x))
                (disjointp (list v y))
                (disjointp (list v z))
                (disjointp (list w x))
                (disjointp (list w y))
                (disjointp (list w z))
                (disjointp (list x y))
                (disjointp (list x z))
                (disjointp (list y z)))
           (disjointp (list q r s u v w x y z)))
  :hints (("Goal" :in-theory (enable disjointp
                                     disjointp-1))))

(defthm disjoint-10-items
  (implies (and (disjointp (list p q))
                (disjointp (list p r))
                (disjointp (list p s))
                (disjointp (list p u))
                (disjointp (list p v))
                (disjointp (list p w))
                (disjointp (list p x))
                (disjointp (list p y))
                (disjointp (list p z))
                (disjointp (list q r))
                (disjointp (list q s))
                (disjointp (list q u))
                (disjointp (list q v))
                (disjointp (list q w))
                (disjointp (list q x))
                (disjointp (list q y))
                (disjointp (list q z))
                (disjointp (list r s))
                (disjointp (list r u))
                (disjointp (list r v))
                (disjointp (list r w))
                (disjointp (list r x))
                (disjointp (list r y))
                (disjointp (list r z))
                (disjointp (list s u))
                (disjointp (list s v))
                (disjointp (list s w))
                (disjointp (list s x))
                (disjointp (list s y))
                (disjointp (list s z))
                (disjointp (list u v))
                (disjointp (list u w))
                (disjointp (list u x))
                (disjointp (list u y))
                (disjointp (list u z))
                (disjointp (list v w))
                (disjointp (list v x))
                (disjointp (list v y))
                (disjointp (list v z))
                (disjointp (list w x))
                (disjointp (list w y))
                (disjointp (list w z))
                (disjointp (list x y))
                (disjointp (list x z))
                (disjointp (list y z)))
           (disjointp (list p q r s u v w x y z)))
  :hints (("Goal" :in-theory (enable disjointp
                                     disjointp-1))))

(encapsulate
 ()

 (local
  (defthm crock-1-1
    (equal (disjoint-bags-p y x)
           (disjoint-bags-p x y))
    :hints (("Goal" :in-theory (enable disjoint-bags-p
                                       memberp)))))

 (local
  (defthm crock-1-2
    (implies (< END1 START2)
             (equal (MEMBERP END1 (RANGE-1 START2 END2 ACC2))
                    (memberp end1 acc2)))
    :hints (("Goal" :in-theory (enable range-1
                                       memberp)))))

 (local
  (defthm crock-1-3-1
    (equal (disjoint-bags-p (cons x y) z)
           (and (not (memberp x z))
                (disjoint-bags-p y z)))
    :hints (("Goal" :in-theory (enable disjoint-bags-p
                                       memberp)))))


 (local
  (defthm crock-1-3
    (implies (disjoint-bags-p x (range-1 start end acc))
             (disjoint-bags-p x acc))
    :hints (("Goal" :in-theory (enable disjoint-bags-p
                                       range-1
                                       memberp)))))

 (local
  (defthm crock-1
    (IMPLIES (and (disjoint-bags-p (range-1 start1 end1 acc1)
                                   acc2)
                  (disjoint-bags-p (range-1 start2 end2 acc2)
                                   acc1)
                  (< end1 start2))
             (DISJOINT-BAGS-P (RANGE-1 start1
                                       end1
                                       acc1)
                              (RANGE-1 start2
                                       end2
                                       acc2)))
    :hints (("Goal" :in-theory (enable disjoint-bags-p
                                       range-1))
            ("Subgoal *1/3''" :use ((:instance crock-1-3
                                               (x acc2)
                                               (start start1)
                                               (end (+ -1 end1))
                                               (acc (cons end1 acc1)))
                                    (:instance crock-1-3-1
                                               (x end1)
                                               (y acc1)
                                               (z acc2)))
             :in-theory (disable crock-1-3
                                 crock-1-3-1)))))

 (local
  (defthm crock-2
    (disjoint-bags-p x nil)
    :hints (("Goal" :in-theory (enable disjoint-bags-p
                                       memberp)))))

;;; !!! generalize these to not require ues of reange ???
 (defthm |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|
   (implies (and (syntaxp (not (rewriting-goal-literal base1 mfc state)))
                 ;; because of the intersectp-equal, we may not be able
                 ;; to find disjoint ranges, of which these are
                 ;; subranges, as required for
                 ;; |(disjointp (list x y)) --- disjoint super-ranges|
                 ;; |to work.
                 (syntaxp (intersectp-equal (non-quotep-addends base1)
                                            (non-quotep-addends base2)))
                 (< (+ base1 offset1 (+ -1 length1))
                    (+ base2 offset2)))
            (disjointp (list (range base1 offset1 length1)
                             (range base2 offset2 length2))))
   :hints (("Goal" :in-theory (enable disjointp
                                      disjointp-1
                                      range))))

 (defthm |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|
   (implies (and (syntaxp (not (rewriting-goal-literal base1 mfc state)))
                 ;; because of the intersectp-equal, we may not be able
                 ;; to find disjoint ranges, of which these are
                 ;; subranges, as required for
                 ;; |(disjointp (list x y)) --- disjoint super-ranges|
                 ;; |to work.
                 (syntaxp (intersectp-equal (non-quotep-addends base1)
                                            (non-quotep-addends base2)))
                 (< (+ base2 offset2 (+ -1 length2))
                    (+ base1 offset1)))
            (disjointp (list (range base1 offset1 length1)
                             (range base2 offset2 length2))))
   :hints (("Goal" :use ((:instance |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|
                                    (base1 base2)
                                    (offset1 offset2)
                                    (length1 length2)
                                    (base2 base1)
                                    (offset2 offset1)
                                    (length2 length1)))
            :in-theory (enable disjointp
                               disjointp-1))))
 )
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Because we will almost always fail the worse-than test inside
;;; ancestors-check, we use the mighty defattach to subvert this.

(defun ancestors-check-disjointp-hack (lit ancestors tokens)
 (declare (xargs :guard (and (pseudo-termp lit)
                             (ancestor-listp ancestors)
                             (true-listp tokens))))
 (cond ((memberp tokens '(((:REWRITE |(not (equal x y)) --- disjointp|))
                          ((:REWRITE DISJOINTP-ADDR-ADDR))
                          ((:REWRITE DISJOINTP-ADDR-RANGE))
                          ((:REWRITE DISJOINTP-RANGE-ADDR))
                          ((:REWRITE DISJOINTP-RANGE-RANGE))))
        (mv nil nil))
       ((atom ancestors)
        (mv nil nil))
       (t (mv-let (not-flg lit-atm)
            (strip-not lit)
            (declare (ignore not-flg))
            (mv-let (var-cnt fn-cnt p-fn-cnt)
              (var-fn-count lit-atm nil) ; Matt K. change from fn-count after v6-1
              (ancestors-check1 lit-atm lit var-cnt fn-cnt p-fn-cnt
                                ancestors tokens))))))

(defthm ancestors-check-disjointp-hack-constraint
 (mv-let (on-ancestors assumed-true)
   (ancestors-check-disjointp-hack lit ancestors tokens)
   (implies (and on-ancestors
                 assumed-true)
            (member-equal-mod-commuting lit (strip-ancestor-literals ancestors) nil)))
 :hints (("Goal" :use ancestors-check-builtin-property))
 :rule-classes nil)

(defattach (ancestors-check ancestors-check-disjointp-hack)
 :system-ok t
 :hints (("Goal" :use ancestors-check-disjointp-hack-constraint)))
