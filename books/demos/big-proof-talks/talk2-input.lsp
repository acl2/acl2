; start up ACL2 and do:
(set-gag-mode nil)
(set-guard-checking :all)

; --- cut here ---

(defun ap (x y)
           (if (endp x)
               y
               (cons (car x)
                     (ap (cdr x) y))))

(ap '(1 2 3) '(4 5 6))

(defthm ap-is-associative
           (equal (ap (ap a b) c)
                  (ap a (ap b c))))

(defun lte (x y)
         (if (endp x)
             t
             (if (endp y)
                 nil
                 (lte (cdr x) (cdr y)))))

(lte '(a b c) '(d e f g))
(lte '(a b c) '(d e))

(thm (implies (and (lte a b)
                          (lte b c))
                     (lte a c)))

(defun insert (e x)
          (if (endp x)
              (cons e x)
              (if (lexorder e (car x))
                  (cons e x)
                  (cons (car x) (insert e (cdr x))))))

(insert 'BOB '(ALICE CATHY))

(defun isort (x)
          (if (endp x)
              x
              (insert (car x)
                      (isort (cdr x)))))

(isort '(BOB CATHY ALICE))

(defun ordered (x)
          (or (endp x)
              (endp (cdr x))
              (and (lexorder (car x) (car (cdr x)))
                   (ordered (cdr x)))))

(defthm ordered-isort
          (ordered (isort x)))

(defun remarkably-fast-sort (x)
          (declare (ignore x))
          '(ALICE BOB CATHY))

(remarkably-fast-sort '(CATHY ALICE BOB))

(defthm ordered-remarkably-fast-sort
          (ordered (remarkably-fast-sort x)))

(remarkably-fast-sort '(JIM SUSAN))

(include-book "sorting/perm" :dir :system)

(perm '(CATHY ALICE BOB) '(ALICE BOB CATHY))
(perm '(CATHY ALICE BOB) '(CATHY CATHY ALICE))

(pe 'perm)

(defthm perm-isort
          (perm (isort x) x))

(defthm perm-remarkably-fast-sort
          (perm (remarkably-fast-sort x) x))

(quote (end of demo 1))

; This shortens proof output
(set-gag-mode :goals)

; Beginning of Demo 2.  The idea is to show that lemmas are
; necessary and then to show that they're not always suggested
; by the failed proof attempt's checkpoints.

(defthm perm-ap
          (perm (ap a b) (ap b a)))

(defthm memb-ap
          (equal (memb e (ap a b))
                 (or (memb e a)
                     (memb e b))))

(defthm perm-ap
          (perm (ap a b) (ap b a)))

(defthm isort-idempotent
          (equal (isort (isort x)) (isort x)))

(defthm isort-identity
         (implies (ordered x)
                  (equal (isort x) x)))

(defthm isort-idempotent
          (equal (isort (isort x)) (isort x)))

(defthm memb-congruence
          (implies (perm a b)
                   (equal (memb e a) (memb e b)))
          :rule-classes :congruence)

(pe 'perm-isort)

(defthm this-is-not-a-theorem
          (memb e (isort a)))

(quote (end of demo 2))

(defun fib1 (n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (if (zp n)
      0
      (if (equal n 1)
          1
          (+ (fib1 (- n 1))
             (fib1 (- n 2))))))

(fib1 1)
(fib1 2)
(fib1 3)
(fib1 4)
(fib1 5)
(time$ (fib1 10))
(time$ (fib1 20))
(time$ (fib1 30))
(time$ (fib1 40)) ; 30 seconds

(verify-guards fib1)

(time$ (fib1 40)) ; 1 second

(defun fib2 (n j k)
  (declare (xargs :guard (and (natp n) (natp j) (natp k))))
  (if (zp n)
      j
    (if (equal n 1)
        k
    (fib2 (- n 1) k (+ j k)))))

(time$ (fib2 40 0 1)) ; 0 seconds

(defthm fib2-v-fib1
  (implies (and (natp i)
                (natp j)
                (natp k)
                (<= 1 i))
           (equal (fib2 i j k)
                  (+ (* (fib1 (- i 1)) j)
                     (* (fib1 i) k)))))

(defun fib (n)
  (declare (xargs :guard (natp n)))
  (mbe :logic (fib1 n)
       :exec (fib2 n 0 1)))

(time$ (fib 5000))

(thm
 (implies (and (natp n) (equal (fib n) 0))
          (equal n 0)))

(time$ (fib1 40))

(memoize 'fib1)

(time$ (fib1 5000))

(quote (end of demo 3))

(include-book "centaur/gl/gl" :dir :system)

(defun 32* (x y)
  (logand (* x y) (- (expt 2 32) 1)))

(defun fast-logcount-32 (v)
  (let* ((v (- v (logand (ash v -1) #x55555555)))
         (v (+ (logand v #x33333333)
               (logand (ash v -2) #x33333333))))
    (ash (32* (logand (+ v (ash v -4)) #xF0F0F0F)
              #x1010101)
         -24)))

(pf 'logcount) ; :pe gives slightly different output in ACL2 and ACL2(p)
(logcount #B0101001)
(fast-logcount-32 #B0101001)

(def-gl-thm fast-logcount-32-correct
  :hyp   (unsigned-byte-p 32 x)
  :concl (equal (fast-logcount-32 x)
                (logcount x))
  :g-bindings `((x ,(gl::g-int 0 1 33))))

(quote (end of demo 4))

(ubt! 'isort-identity)


(defun lequal (x y)

; We're trying to prove (equal (isort (isort x)) (isort x)).
; We might try rewriting (isort x) to x using
; (perm (isort x) x) as a rewrite rule and exploiting that
; (isort x) = (isort y) if (perm x y).  The latter is
; a congruence rule.  Unfortunately, that rule is not
; valid!  If x is '(1 2 . T) and y is '(1 2 . NIL) then
; they are perms but their isorts are not equal.
; We could prove a weaker version of idempotency,
; namely one that establishes that they have the same
; elements in the same order but not (necessarily) the
; same terminal marker.  We can formalize that as
; an equivalence relation on lists.

         (cond ((atom x) (atom y))
               ((atom y) nil)
               (t (and (equal (car x) (car y))
                       (lequal (cdr x) (cdr y))))))

(defequiv lequal)

(defcong lequal lequal (insert e x) 2)

(defcong perm lequal (isort x) 1)

(defthm isort-idempotent-lequal
          (lequal (isort (isort x)) (isort x)))

(defun terminal-marker (x)
         (cond
          ((atom x) x)
          (t (terminal-marker (cdr x)))))

(defthm terminal-marker-isort
         (equal (terminal-marker (isort x))
                (terminal-marker x)))

(defthm lequal-with-same-terminal-markers-are-equal
         (implies (and (equal (terminal-marker a)
                              (terminal-marker b))
                       (lequal a b))
                  (equal a b))
          :rule-classes nil)

(defthm isort-idempotent
         (equal (isort (isort x)) (isort x))
         :hints
         (("Goal"
           :use
           (:instance lequal-with-same-terminal-markers-are-equal
                      (a (isort (isort x)))
                      (b (isort x))))))


