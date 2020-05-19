; Here is a classic Boyer-Moore test.
; (ld "proveall-input.lsp" :ld-pre-eval-print t)
(include-book "../paco")
(in-package "PACO")

(acl2::set-gag-mode :goals)

(acl2::table acl2::theory-invariant-table nil nil :clear)

(ACL2::SET-MATCH-FREE-ERROR NIL)

; In this proveall test suite we tend to define old functions with new
; names, e.g., app for append, simply so that we don't succeed in
; proofs because of lemmas ACL2 has already proved about the standard
; functions.

(defun app (x y)
  (if (endp x)
      y
    (cons (car x)
          (app (cdr x) y))))

(defun rv (x)
  (if (endp x)
      nil
    (app (rv (cdr x)) (list (car x)))))

(dthm assoc-of-app
      (equal (app (app a b) c)
             (app a (app b c))))

; This will do two inductions, because the first simplification splits
; the goal into two.

(dthm true-listp-app
      (iff (true-listp (app a b))
           (true-listp b)))

; Alternatively, this will do one induction.

; (dthm true-listp-app
;       (iff (true-listp (app a b))
;            (true-listp b))
;       :hint-settings ((nil (:induct . t))))

(dthm true-listp-rv
      (true-listp (rv a)))

; If you do a :prf 1 after this next one you see a simplification that
; doesn't appear to change the goal -- but it actually converts an
; implies into a clause.

(dthm app-right-id
      (implies (true-listp a)
               (equal (app a nil) a)))

; This next is needed because Paco doesn't do destructor elimination
; or cross-fertilization.

(dthm rv-app-xfert-bridge
      (implies (equal xxx (app a b))
               (equal (app xxx c) (app a (app b c)))))

(dthm rv-app
      (equal (rv (app a b)) (app (rv b) (rv a))))

(dthm rv-rv
      (implies (true-listp x) (equal (rv (rv x)) x)))

(dthm len-app
      (equal (len (app a b)) (+ (len a) (len b))))

(dthm member-app
      (iff (member e (app a b))
           (or (member e a)
               (member e b))))

(dthm member-rv
      (iff (member e (rv x))
           (member e x)))

(dthm member-equal-union-equal-lemma
      (implies (member-equal e b)
               (member-equal e (union-equal a b))))

(dthm member-equal-union-equal
  (iff (member-equal e (union-equal a b))
       (or (member-equal e a)
           (member-equal e b))))

(defun intersection-equal (x y)
  (cond ((endp x) nil)
        ((member-equal (car x) y)
         (cons (car x) (intersection-equal (cdr x) y)))
        (t (intersection-equal (cdr x) y))))

(dthm member-equal-intersection-equal-lemma
      (implies (not (member-equal e b))
               (not (member-equal e (intersection-equal a b)))))

(dthm member-equal-intersection-equal
      (iff (member-equal e (intersection-equal a b))
           (and (member-equal e a)
                (member-equal e b))))

(defun flatten (x)
  (cond ((atom x) (list x))
        (t (app (flatten (car x))
                   (flatten (cdr x))))))

(defun mc-flatten (x a)
  (cond ((atom x) (cons x a))
        (t (mc-flatten (car x)
                       (mc-flatten (cdr x) a)))))

(dthm mc-flatten-is-flatten-gen
      (equal (mc-flatten x a)
             (app (flatten x) a)))

(dthm true-listp-flatten
      (true-listp (flatten x)))

(dthm mc-flatten-is-flatten
      (equal (mc-flatten x nil) (flatten x)))


(defun insert (e x)
  (cond ((endp x) (cons e x))
        ((<= e (car x))
         (cons e x))
        (t (cons (car x) (insert e (cdr x))))))

(defun orderedp (x)
  (cond ((endp x) t)
        ((endp (cdr x)) t)
        ((<= (car x) (cadr x)) (orderedp (cdr x)))
        (t nil)))

; Note DEFTHM not DTHM!

(defthm arithmetic-property-1
  (implies (< i j) (not (< j i))))

(dthm car-insert
      (equal (car (insert e x))
             (if (endp x) e (if (<= e (car x)) e (car x)))))

(dthm ordered-insert
      (implies (orderedp x)
               (orderedp (insert e x))))

(defun isort (x)
  (cond ((endp x) nil)
        (t (insert (car x)
                   (isort (cdr x))))))

(dthm orderedp-isort
      (orderedp (isort x)))

(dthm insert-identity
      (implies (and (consp x)
                    (<= e (car x)))
               (equal (insert e x) (cons e x))))

(dthm isort-identity-lemma
      (implies (equal xxx (cdr x))
               (equal (insert e xxx) (insert e (cdr x)))))

(dthm isort-identity
      (implies (and (orderedp x)
                    (true-listp x))
               (equal (isort x) x)))

(dthm true-listp-insert
      (iff (true-listp (insert e x))
           (true-listp x)))

(dthm true-listp-isort
      (true-listp (isort x)))

(dthm idempotent-isort
      (equal (isort (isort x)) (isort x)))

(defun del (x lst)
  (cond ((atom lst) nil)
        ((equal x (car lst)) (cdr lst))
        (t (cons (car lst) (del x (cdr lst))))))

(defun mem (x lst)
  (cond ((atom lst) nil)
        ((equal x (car lst)) t)
        (t (mem x (cdr lst)))))

(defun perm (lst1 lst2)
  (cond ((atom lst1) (atom lst2))
        ((mem (car lst1) lst2)
         (perm (cdr lst1) (del (car lst1) lst2)))
        (t nil)))

(dthm perm-reflexive
  (perm x x))

(dthm perm-x-cons-a-opener
      (implies (mem a x)
               (equal (perm x (cons a y))
                      (if (mem (car x) (cons a y))
                          (perm (cdr x) (del (car x) (cons a y)))
                        nil))))
(dthm car-del
      (equal (car (del a x))
             (if (consp x)
                 (if (equal a (car x))
                     (car (cdr x))
                   (car x))
               nil)))

(dthm cdr-del
      (equal (cdr (del a x))
             (if (consp x)
                 (if (equal a (car x))
                     (cdr (cdr x))
                   (del a (cdr x)))
               nil)))

(dthm consp-del
      (equal (consp (del a x))
             (if (consp x)
                 (if (equal a (car x))
                     (consp (cdr x))
                   t)
               nil)))


; If you don't provide the :induct hint it does an elim.

(dthm perm-cons
  (implies (and (consp z)
                (mem (car z) x))
           (equal (perm x z)
                  (perm (del (car z) x) (cdr z))))
  :hints ((() :induct t)))

(dthm perm-symmetric
  (implies (perm x y) (perm y x)))

(dthm mem-del
      (implies (mem a (del b x)) (mem a x)))

(dthm perm-mem
      (implies (and (perm x y)
                    (mem a x))
               (mem a y)))

(dthm mem-del2
      (implies (and (mem a x)
                    (not (equal a b)))
               (mem a (del b x))))

(dthm comm-del
      (equal (del a (del b x)) (del b (del a x))))

(dthm perm-del
      (implies (perm x y)
               (perm (del a x) (del a y))))

(dthm perm-transitive
      (implies (and (perm x y) (perm y z)) (perm x z)))

(dthm perm-cons-congruence
      (implies (perm x y)
               (perm (cons a x) (cons a y))))

(dthm perm-atom
      (implies (not (consp x)) (perm x nil)))

(dthm perm-insert
  (perm (insert a x) (cons a x)))

; To prove that (isort x) is a perm of x, we need several instances of
; transitivity.

(dthm trans-instance
      (implies (and (perm (insert (car x) (isort (cdr x)))
                          (cons (car x) (isort (cdr x))))
                    (perm (cons (car x) (isort (cdr x))) x))
               (perm (insert (car x) (isort (cdr x)))
                     x))
      :hints ((() :use ((:instance perm-transitive
                                   (x (insert (car x) (isort (cdr x))))
                                   (y (cons (car x) (isort (cdr x))))
                                   (z x))))))

(dthm perm-isort
   (perm (isort x) x))


(defun xor (a b)
  (if a (if b nil t) b))

(defun adder (x y c)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (cond ((and (endp x)
              (endp y))
         (list c))
        (t (cons (xor (car x) (xor (car y) c))
                 (adder (cdr x)
                        (cdr y)
                        (or (and (car x) (car y))
                            (and (car x) c)
                            (and (car y) c)))))))

(defun nat (x)
  (if (endp x)
      0
    (+ (if (car x) 1 0)
       (* 2 (nat (cdr x))))))

; NOTE:  DEFTHM!
(defthm nat-adder-lemma1
  (implies (equal xxx (+ 1 n))
           (equal (* 2 xxx)
                  (+ 1 1 (* 2 n)))))

(dthm nat-adder-lemma2
      (and (equal (nat (adder x nil nil)) (nat x))
           (implies c (equal (nat (adder x nil c))
                             (+ 1 (nat x))))))

(dthm nat-adder-lemma3
      (implies (equal xxx (+ i j))
               (equal (* 2 xxx)
                      (+ (* 2 i) (* 2 j)))))

; Note:  I tried to phrase this lemma this way:

;      (implies (equal xxx (+ i j))
;               (equal (* 2 xxx)
;                      (+ 2 (+ i j))))

; and it didn't work.  I think the reason is that the (+ i j) rewrites
; back to the xxx.

; If you don't induct right away, it splits into two weak theorems.
(dthm nat-adder
      (equal (nat (adder x y c))
             (+ (nat x)
                (nat y)
                (if c 1 0)))
      :hints ((() :induct t)))

(defun multiplier (x y a)
  (cond ((endp x) a)
        ((car x)
         (multiplier (cdr x) (cons nil y) (adder y a nil)))
        (t (multiplier (cdr x) (cons nil y) a))))

(dthm nat-multiplier
      (equal (nat (multiplier x y a))
             (+ (* (nat x) (nat y)) (nat a))))

; Now I test some hints.

(defun conc (x y) ; = (app x y)
  (if (endp x) y (cons (car x) (conc (cdr x) y))))

(defun rve (x)
  (if (endp x) nil (conc (rve (cdr x)) (list (car x)))))

(defun rv1 (x a)
  (if (endp x) a (rv1 (cdr x) (cons (car x) a))))

(dthm associativity-of-conc
      (equal (conc (conc a b) c) (conc a (conc b c))))

(in-theory (disable associativity-of-conc))

; This fails without the :USE hint.
(dthm test-1
      (equal (conc (conc a a) a) (conc a (conc a a)))
      :rule-classes nil
      :hints ((() :use ((:instance associativity-of-conc (a a) (b a) (c a))))))

; This fails without the :IN-THEORY hint.
(dthm test-2
      (equal (conc (conc a a) a) (conc a (conc a a)))
      :rule-classes nil
      :hints ((() :in-theory (enable (:rewrite associativity-of-conc)))))

; This is the same but tests e/d
(dthm test-3
      (equal (conc (conc a a) a) (conc a (conc a a)))
      :rule-classes nil
      :hints ((() :in-theory (e/d ((:rewrite associativity-of-conc)) nil))))

(dthm rv-rv1-a
      (equal (rv1 x a) (conc (rve x) a))
      :hints (((2) :in-theory (enable (:rewrite associativity-of-conc)))))

(defun rv1top (x) (rv1 x nil))

(dthm conc-rv-nil
      (equal (conc (rve x) nil) (rve x))
      :hints (((2) :in-theory (enable (:rewrite associativity-of-conc)))))

; This fails without the :EXPAND hint.  The idea is that with all the
; fns disabled, we cannot get to conc-rv-nil.  But if we force the
; expansion of (rv1top x), we can.

(dthm test-4
      (equal (rv1top x) (rve x))
      :rule-classes nil
      :hints ((()
               :in-theory (disable (:definition rv)
                                   (:definition rv1)
                                   (:definition rv1top)
                                   )
               :expand ((rv1top x)))))

; This fails without the :HANDS-OFF because we open (rve (cons a a))
; and cannot match conc-rv-nil.
(dthm test-5
      (equal (conc (rve (cons a a)) nil) (rve (cons a a)))
      :rule-classes nil
      :hints ((() :hands-off (rve))))

; This fails without the :INDUCT hint because it inducts on a.
(dthm test-6
      (equal (rv1 (conc a b) c) (rv1 b (rv1 a c)))
      :rule-classes nil
      :hints ((() :induct (rv1 a c))
              ((1 2)
               :in-theory (e/d ((:rewrite associativity-of-conc)) nil))))

; This fails without the :do-not because if we simplify the input
; we split it into two subgoals which aren't provable by Paco induction
; separately.

(dthm test-7
      (equal (nat (adder x y c))
             (+ (nat x)
                (nat y)
                (if c 1 0)))
      :hints ((() :in-theory (disable (:rewrite nat-adder))
                             ; to keep old rule out
               :do-not (simplify-clause))
              ((1 2) :do-not nil)
              ((1 1) :do-not nil)))

; Still need to implement and test:
; :CASES
; :BY

; Ok, so here's a heavy duty test!

(include-book "models/jvm/m5/jvm-fact-setup" :dir :system)
(in-package "M5")
(defthm int-lemma0-rewrite
  (implies (intp x)
           (integerp x)))

(defthm zp-prop1
  (implies (and (zp x)
                (integerp x))
           (equal (< 0 x) nil)))

(paco::dthm fact-is-correct
         (implies (poised-to-invoke-fact th s n)
                  (equal
                   (run (fact-sched th n) s)
                   (modify th s
                    :pc (+ 3 (pc (top-frame th s)))
                    :stack (push (int-fix (! n))
                                 (pop (stack (top-frame th s)))))))
         :hints ((() :induct (induction-hint th s n))))
