;; this regression file aims at testing the various features of 
;; counterexample generation in ACL2 Sedan

(include-book "top")

;++++++++++++++++testcase 1 [classic reverse example]++++++++++++++++++++++++++
;Define Reverse function
(defun rev (x)
  (if (endp x)
    nil
    (append (rev (cdr x)) (list (car x)))))

(acl2s-defaults :set verbosity-level 3)
(test? (equal (rev (rev x)) x))

;Modify the conjecture, add the type hypothesis
(test? (implies (true-listp x)
                (equal (rev (rev x)) x)))
;; Issues
;; 1. If a function is not golden (guards not verified), then test?
;; errors out. e.g above rev is not golden and above test? fails with:
#|
ACL2 Error in ( DEFUN DEFDATA::CONCLUSION-VAL-CURRENT ...):  The body
for DEFDATA::CONCLUSION-VAL-CURRENT calls the function REV, the guards
of which have not yet been verified.  See :DOC verify-guards.
|#
;; This happens for each conclusion-val, hypothesis-val and next-sigma
;; This forced me to add (set-verify-guards-eagerness 0) to test?
;; progn loop. But what about thm and defthm ?
;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;; testcase 2 (Shape of triangle - example from testing literature)
(defdata triple (list pos pos pos))

(defun trianglep (v)
  (and (triplep v)
       (< (third v) (+ (first v) (second v)))
       (< (first v) (+ (second v) (third v)))
       (< (second v) (+ (first v) (third v)))))

(defun shape (v)
  (if (trianglep v)
      (cond ((equal (first v) (second v))
             (if (equal (second v) (third v))
                 "equilateral"
               "isosceles"))
            ((equal (second v) (third v)) "isosceles")
            ((equal (first v) (third v)) "isosceles")
            (t "scalene"))
    "error"))
(acl2s-defaults :set num-trials 1000000)
(acl2s-defaults :set testing-enabled :naive)
(time$
(test? 
 (implies (and (triplep x)
               (trianglep x)
               (> (third x) 256)
               (= (third x)
                  (* (second x) (first x))))
          (not (equal "isosceles" (shape x)))))
)

(acl2s-defaults :set num-trials 1000)
;; fixed a bug where get-testing-enabled fn was giving wrong answer
;; leading to backtrack hints being added twice when we eval the
;; following form twice. Idempotency is very important.

(acl2s-defaults :set testing-enabled T)

;; whoa! Without arithmetic-5, I get nowhere with the
;; below example. 
(include-book "arithmetic-5/top" :dir :system)

(test?
 (implies (and (triplep x)
               (trianglep x)
               (> (third x) 256)
               (= (third x)
                  (* (second x) (first x))))
          (not (equal "isosceles" (shape x)))))



;; testcase 3 (memory updates dont commute)
;NOTE: The following example too, 'simple' works good enough

;another example demonstrating how having the ability to find
;counterexamples helps in debugging conjectures
;This also illustrates how data definition framework
;and random testing work together

;update: Address * Value * Memory -> Memory
;If Address is found in Memory, update it, or else add it to the end
;of the memory.
(defdata memory (listof (cons nat integer))) 
;ISSUE: map not working due to guards
;ISSUE: print-summary-user-testing is firing where it shouldnt. How should I
;reset this global flag correctly??

;; (defdata memory (map nat integer))

(nth-memory 9436794189)

(defun update (address value memory)
  (cond ((endp memory)
         (acons address value nil))
        ((equal address (caar memory))
         (acons address value (cdr memory)))
        ((< address (caar memory))
         (acons address value memory))
        (t (cons (car memory) (update address value (cdr memory))))))

(defun make-ordered-list (n acc)
  (if (zp n)
    acc
    (make-ordered-list (- n 1) (cons n acc))))

(make-ordered-list 4 nil)

(defun cons-up-lists (l1 l2)
  (declare (xargs :guard (and (true-listp l1)
                              (true-listp l2)
                              (= (len l1)
                                 (len l2)))))
  (if (endp l1)
    nil
    (cons (cons (car l1) (car l2))
          (cons-up-lists (cdr l1) (cdr l2)))))

(defun nth-ordered-memory (n)
  (let* ((m (nth-memory n))
         (len (len m))
         (vals (strip-cdrs m))
         (keys (make-ordered-list len nil)))
    (cons-up-lists keys vals)))

;attach a custom test enumerator to a defdata type
(defdata-testing memory :test-enumerator nth-ordered-memory)               

;Conjecture - version#1
(test?
 (equal (update a1 v1 (update a2 v2 m))
        (update a2 v2 (update a1 v1 m))))

; Conjecture - version 2

(test?
 (implies (and (memoryp m)
               (natp a1)
               (natp a2))
          (equal (update a1 v1 (update a2 v2 m))
                 (update a2 v2 (update a1 v1 m)))))

;Conjecture - version#3
;TODO - I am not trying hard to refute conclusion in incremental
(test?
 (implies (and (memoryp m)
               (natp a1)
               (natp a2)
               ;(or (in-memory a1 m) (in-memory a2 m))
               (not (equal a1 a2)))
          (equal (update a1 v1 (update a2 v2 m))
                 (update a2 v2 (update a1 v1 m)))))

;Testing didnt come up with any counterexamples, lets try to prove it.
(thm
 (implies (and (memoryp m)
               (natp a1)
               (natp a2)
               ;(or (in-memory a1 m) (in-memory a2 m))
               (not (equal a1 a2)))
          (equal (update a1 v1 (update a2 v2 m))
                 (update a2 v2 (update a1 v1 m)))))


;; testcase 4 (Russinoff's example)

(test? (implies (and (real/rationalp a)
                     (real/rationalp b)
                     (real/rationalp c)
                     (< 0 a)
                     (< 0 b)
                     (< 0 c)
                     (<= (expt a 2) (* b (+ c 1)))
                     (<= b (* 4 c)))
                (< (expt (- a 1) 2) (* b c))))

;;TODO: C is being printed in quoted form in :incremental
(thm (implies (and (real/rationalp a)
                     (real/rationalp b)
                     (real/rationalp c)
                     (< 0 a)
                     (< 0 b)
                     (< 0 c)
                     (<= (expt a 2) (* b (+ c 1)))
                     (<= b (* 4 c)))
                (< (expt (- a 1) 2) (* b c))))

;not giving top-level counterexamples in :incremental
(time$
(test? (implies (and (real/rationalp a)
                     (real/rationalp b)
                     (real/rationalp c)
                     (<= 1 a)
                     (< 0 b)
                     (< 0 c)
                     (<= (expt a 2) (* b (+ c 1)))
                     (<= b (* 4 c)))
                (< (expt (- a 1) 2) (* b c)))))

(thm (implies (and (real/rationalp a)
                   (real/rationalp b)
                   (real/rationalp c)
                   (< 3/4 a)
                   (<= (expt a 2) (* b (+ c 1)))
                   (<= b (* 4 c)))
              (< (expt (- a 1) 2) (* b c)))
     :hints (("goal" :cases ((< 0 b)))))
;08/22/12 ACL2 v5.0 The above thm no longer goes through


;; testcase 5 (only finds cts if arithmetic-5 library is loaded)
(test?
 (implies (and (posp x)
               (posp y)
               (posp z)
               (> z 16)
               (<= (+ x y) (* 2 z)))
          (or (> (* x y z) (* x y x))
              (> (* x y z) (* x y y)))))

;;testcase 6
(test?
 (implies (and (posp x)
               (posp y)
               (posp z)
               ;Idea of introducing variables to help SELECT
               ;(equal w (* z z))
               (<= (+ x y) (* 2 z)))
          (> (* z z) (* x y))))

;; testcase 7 (from Harrison's book)
(defdata formula (oneof pos
                        (list 'not formula)
                        (list 'and formula formula)
                        (list 'or formula formula)
                        (list 'implies formula formula)))

(defun simplify (f)
  ;:input-contract (formulap f)
  ;:output-contract (formulap (simplify f))
  (cond ((posp f) f)
        ((eq (first f) 'not) (list 'not (simplify (second f))))
        ((eq (first f) 'and) (list 'and (simplify (second f)) (simplify (third f))))
        ((eq (first f) 'or) (list 'or (simplify (second f)) (simplify (third f))))
        ((eq (first f) 'implies) (list 'or (list 'not (simplify (second f))) (simplify (third f))))
        (t f)))

(defun is-simplified (f)
  ;:input-contract (formulap f)
  ;:output-contract (booleanp (is-simplified f))
   (cond ((posp f) t)
        ((eq (first f) 'not) (is-simplified (second f)))
        ((eq (first f) 'and) (and (is-simplified (second f)) (is-simplified (third f))))
        ((eq (first f) 'or) (and (is-simplified (second f)) (is-simplified (third f))))
        ((eq (first f) 'implies) nil)
        (t nil)))
  
(defthm simplify-is-stable
  (equal (simplify (simplify f))
         (simplify f)))

(defun nnf (f)
   (cond ((posp f) f)
        ((and (eq (first f) 'not) (posp (second f))) f)
        ((and (eq (first f) 'not) (eq 'not (first (second f))))
         (nnf (second (second f))))
        ((eq (first f) 'and) (list 'and (nnf (second f)) (nnf (third f))))
        ((eq (first f) 'or) (list 'or (nnf (second f)) (nnf (third f))))
        ((eq (first f) 'implies) (list 'implies (nnf (second f)) (nnf (third f))))
        ((and (eq (first f) 'not)
              (eq 'and (first (second f))))
         (let* ((a (second f))
                (lhs (second a))
                (rhs (third a)))
           (list 'or (nnf (list 'not lhs)) (nnf (list 'not rhs)))))
        ((and (eq (first f) 'not)
              (eq 'or (first (second f))))
         (let* ((a (second f))
                (lhs (second a))
                (rhs (third a)))
           (list 'and (nnf (list 'not lhs)) (nnf (list 'not rhs)))))     
         ((and (eq (first f) 'not)
              (eq 'implies (first (second f))))
         (let* ((a (second f))
                (lhs (second a))
                (rhs (third a)))
           (list 'and (nnf lhs) (nnf (list 'not rhs)))))
        (t f)))

(thm ;simp-nnf-commute
  (implies (formulap f)
  (equal (nnf (simplify f))
         (simplify (nnf f)))))

; TODO: print-testing-summary should not appear after the summary when a new
;form is called.

;; testcase 8 (Moore's example)
(defun square-root1 (i ri)
  (declare (xargs :mode :program))
  (if (>= (floor i ri) ri)
      ri
      (square-root1 i (floor (+ ri (floor i ri)) 2))))

(defun square-root (i)
  (declare (xargs :mode :program))
  (square-root1 i (floor i 2)))

(defun square (x)
   (* x x))
 
 
(test?
  (implies (natp i)
           (and (<= (square (square-root i)) i)
                (< i (square (1+ (square-root i)))))))


;; testcase 9 (a thm in 2, but cts in 3 variables)
(defdata small-pos (enum '(1 2 3 4 5 6 7 8 9)))

(acl2s-defaults :set testing-enabled T)
(acl2s-defaults :set num-trials 2500)
;No luck without arithmetic-5.
;Lets add arith-5 lib and see now. Still no luck

(test? 
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (posp x1)
                (posp x2)
                (posp x3)
                (< x1 x2)
                (< x2 x3)
                (equal 0 (+ c1 c2 c3))
                (equal 0 (+ (* c1 x1) (* c2 x2) (* c3 x3))))
           (and (= 0 c1) (= 0 c2) (= 0 c3))))

;;(total-runs/goals - cts/wts - totaltime/testing-time)
;;(5004/4 - 4485/3 - 0.59/0.1) stats

;TODO.bug - incremental is giving assert failure!
(test? 
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (small-posp x1)
                (small-posp x2)
                (small-posp x3)
                (< x1 x2)
                (< x2 x3)
                (equal 0 (+ c1 c2 c3))
                (equal 0 (+ (* c1 x1) (* c2 x2) (* c3 x3))))
           (and (= 0 c1) (= 0 c2) (= 0 c3))))


;; testcase 10 (Euler Counterexample)
;fermat number: f(n) = 1 + 2^2^n
(defun f (n)
  (1+ (expt 2 (expt 2 n))))

(f 5)

;is k a factor of n other than 1 and n?
(defun factor? (k n)
  (and (< 1 k)
       (< k n)
       (natp (/ n k))))

(test?
 (implies (posp k)
          (not (factor? k (f 5)))))


;Euler Insight: All factors of f(n) should have the form k*2^{n+1} + 1
;for some k. Someone improved on this, where all k are even, so:
(defun fermat-factor (k n)
  (1+ (* k (expt 2 (+ 1 n)))))

;TODO: get rid of duplicate cts/wts across subgoals
(test?
 (implies (posp k)
          (not (factor? (fermat-factor k 5) (f 5)))))

;Lets generalize this, for any fermat number, but since these are
;huge numbers we will restrict ourselves to n less than 15.
(f 15) ;1000 digits long

(test?
 (implies (and (posp k)
               (posp n)
               (< n 15))
          (not (factor? k (f n)))))

(acl2s-defaults :set num-trials 100000)
 ;Rerunning the following test 2-3 times will get you atleast two
;counterexamples:
;-- (K 14) and (N 12)
;-- (K 10) and (N 5)


(test? 
 (implies (and (posp k)
               (posp n)
               (< n 15))
          (not (factor? (fermat-factor k n) (f n)))))

;The third case
(acl2s-defaults :set num-trials 1000)
;; Fermats last theorem
; No counterexamples and proof is probably out of ACL2's reach!
; TODO: fix timeout issues. Here exponentiation probably causes problem



(test?
 (implies (and (posp a) (posp b) (posp c)
               (natp n) (> n 2))
          (not (equal (+ (expt a n) (expt b n))
                      (expt c n)))))

;; testcase 11
(defund hash (k)
  (let* ((m (expt 2 23))
         (a 309017/500000)
         (s (* k a))
         (x (- s (floor s 1))))
    (mod (floor (* m x) 1)
         (expt 2 32))))

(defun g (x y z)
  (if (and (equal x (hash y))
           (equal y (hash z)))
      'error
    0))

(acl2s-defaults :set testing-enabled T) ;only works for T
(test? (implies (and (integerp x)
                     (integerp y)
                     (integerp z))
                (/= (g x y z) 'error)))













;========================OLD/SCRATCHPAD=================================

:trans1 (defdata R (record (f1 . nat) (f2 . pos)))

(defdata nats (set nat))


;TODO FIXME
(defdata i-or-loi (oneof integer (listof integer)))

(defun rev (x)
  (if (endp x)
    nil
    (append (rev (cdr x)) (list (car x)))))
;(trace$ defdata::print-bindings defdata::run-tests-on-subgoal-and-summarise)
;TODO: generalization and cross-fert still dont work well with
;output printing
(set-acl2s-random-testing-enabled t)
;TODO: ASK Matt, why is generalization not being captured.
;Maybe bug in my code!!? CHECK
(thm (implies (true-listp x)
              (equal (rev (rev x)) x))) 

(program)
(defun app1 (x y)
  (if (endp x)
    y
    (cons (car x) (app1 (cdr x) y))))

(logic)

(test? (implies (and (true-listp x) (true-listp y))
                (true-listp (app1 x y))))

(defun divisible-by (x i)
  (integerp (/ x i)))
  
(defun divisor<=p (x i)
  (if (or (zp i)
          (= i 1))
    nil
    (if (divisible-by x i)
      t
      (divisor<=p x (- i 1)))))

; COUNT-DIVISORS<=: nat nat -> nat
; (Helper for PRIMEP)
; Counts the number of positive integer divisors of the first argument
; that are less than or equal to the second argument.
(defun count-divisors (x i)
  (if (zp i)
    0
    (if (divisible-by x i)
      (+ 1 (count-divisors x (- i 1)))
      (count-divisors x (- i 1)))))

; PRIMEP: nat -> boolean
; Recognizer for prime numbers, which must have exactly two distinct
; divisors (1 and itself).
(defun primep (x)
  (and (natp x)
       (= (count-divisors x x) 2)))

(defun prime-between2 (l u)
  (declare (ignorable l u))
  (if (zp (- u l))
    2
    (if (primep l)
      l
      (prime-between2 (+ l 1) u))))

(defun prime-bet (l u)
  (prime-between2 l u))

(defun c-lg2-hlp (x i)
  (declare (xargs :measure (acl2-count (- x (expt 2 i)))))
  (cond ((or (not (natp i))
             (zp x)
             (<= x (expt 2 i))) 0)
        ((and (> x (expt 2 i))
              (<= x (expt 2 (+ i 1))))
         (+ i 1))
        (T (c-lg2-hlp x (+ i 1)))))

;; Base-2 logarithm of natural number,
;; rounding up to the nearest natural (returns 0 if x is 0)
(defund c-lg2 (x)
  (c-lg2-hlp x 0))

(defun lb-pn4 (n)
  (*  n (1- (c-lg2  n))))


(defun nth-prime (n)
  (nth n 
       (sieve (upper-bound n))))
  
(defun nth-prime5 (n)
  (if (zp n)
    2
    (let* ((ub (1+ (expt 2 n)))
           (lb (nth-prime-lower-bound n))) 
      (prime-bet lb ub))))
    


(encapsulate
  (((ubsize ) => *))

  (local (defun ubsize () 32))

  (defthm ubsize-thm
    (natp (ubsize))
    :rule-classes ((:rewrite) (:type-prescription)))
  )

(defun usbvp (x)
  (and (natp x)
       (<= 0 x)
       (< x (expt 2 (ubsize)))))
(set-acl2s-random-testing-enabled nil)
(encapsulate
  (((whatever) => *))

  (local (defun whatever () 0))

  (defthm whatever-thm
    (usbvp (whatever))
    )
  )

(acl2s-defaults :set num-trials 1000)
;GOOD EXAMPLE 
(test? ;remove-once-perm
  (implies (and (consp X)
                (sets::in a Y))
           (equal (defdata::permutation (sets::delete a X)
                        (sets::delete a Y))
                  (defdata::permutation X Y))))
 
;#|
;air turbulence logic puzzle (Jim Steinberg gave me the link)
;http://www.mysterymaster.com/puzzles/AirTurbulence.html
(defdata officials (enum '(:M :DA :JP :DC)))
(defdata grooming (enum '(:Beard :Manicure :Shampoo :TeethC)))
(defdata runway-num (enum '(2 3 4 6)))

(defdata off-mapping (map officials runway-num))

;BUG: finite record is giving rise to *off-mapping-values*?!!
(defdata grooming-map (map grooming runway-num))
                              
(defdata off-groom (map officials grooming))
                           
(defun unique-4map (alst)
  (no-duplicatesp (strip-cdrs alst)))

(acl2s-defaults :set num-trials 100)

(test? ;constraint
 (implies (and (off-mappingp O-R)
               (grooming-mapp G-R)
               
               (off-groomp O-G)
               (unique-4map O-R)
               (equal (mget (mget :M  O-G) G-R) (mget :M O-R))
               (equal (mget (mget :DA O-G) G-R) (mget :DA O-R))
               (equal (mget (mget :JP O-G) G-R) (mget :JP O-R))
               (equal (mget (mget :DC O-G) G-R) (mget :DC O-R))
               (equal (mget :DA O-R) 3);1st constraint               
               (equal (mget :Shampoo G-R) (1+ (mget :Manicure G-R)));second constraint
               (> (mget :M O-R) (mget :DC O-R));third constraint
               (equal (mget :JP O-R) (* 2 (mget :TeethC G-R)));fourth constraint
               (equal (mget :DA O-G) :Beard));5th constraint
          nil))

;10 July 2011 (I dont know what I did, but we shud get some
;counterexample here)
;Okay got it(u have to be lucky for naive testing):
#|
We falsified the conjecture. Here is the counterexample:
 -- (G-R ((:BEARD . 2) (:MANICURE . 2) (:SHAMPOO . 3) (:TEETHC . 2))),
(O-R ((:DA . 3) (:DC . 2) (:JP . 4) (:M . 6))) and 
(O-G ((:DA . :BEARD) (:DC . :BEARD) (:JP . :MANICURE) (:M . :SHAMPOO)))
|# 
(test? ;constraint
 (implies (and (off-mappingp O-R)
               (grooming-mapp G-R)
               (off-groomp O-G)
               (unique-4map O-R)
               (equal (mget (mget :M  O-G) G-R) (mget :M O-R))
               (equal (mget (mget :DA O-G) G-R) (mget :DA O-R))
               (equal (mget (mget :JP O-G) G-R) (mget :JP O-R))
               (equal (mget (mget :DC O-G) G-R) (mget :DC O-R))
               (equal (mget :Shampoo G-R) (1+ (mget :Manicure G-R)))
               (> (mget :M O-R) (mget :DC O-R))
               (equal (mget :JP O-R) (* 2 (mget :TeethC G-R)))
               (equal (mget :DA O-R) 3);1st constraint
               (equal (mget :DA O-G) :Beard))
          nil))
;|#

(defun hash (k)
  (let* ((m (expt 2 23))
         (a 309017/500000)
         (s (* k a))
         (x (- s (floor s 1))))
    (mod (floor (* m x) 1)
         (expt 2 32))))

(in-theory (disable hash))


(defun f (x y)
  (if (equal x (hash y))
    'error
    0))
(acl2s-defaults :set instantiation-method :incremental)
(test? (/= (f x y) 'error))

(test? ;(implies (and (integerp x) (integerp y))
                (NOT (EQUAL X (HASH Y))))

(set-acl2s-random-testing-enabled nil)
(thm (implies (and (integerp x) (integerp y))
                (/= (f x y) 'error)))

(set-acl2s-random-testing-enabled t)

(defun hash1 (x)
  (mod (+ (* x (1- (expt 2 27)))
          (1- (expt 2 19)))
       (expt 2 32)))

;simple 8.2sec
;incr: 12.42 sec
;10 July 2011: same times for both 9.7sec
(acl2s-defaults :set instantiation-method :incremental)
(time$
(test?
 (implies (and (integerp x)
               (integerp y)
               (integerp z)
               (integerp w)
               (equal x (hash1 y))
               (equal y (hash1 z))
               (equal w (max x y)))
          (< w z))))

;tests multiple dest-elim
(test? (implies (AND (CONSP X)
                (NOT (EQUAL (LEN X) 2))
                (EQUAL (CADR X) '+))
              (not (equal x x))))


;TODO CHECK THIS OUT
   (defdata::RUN-TESTS-AND-PRINT-SUMMARY
    'RANDOMTESTING
    '(IMPLIES (AND (CONSP X)
                  (NOT (EQUAL (LEN X) 2))
                  (EQUAL (CADR X) '+))
             (NOT (EQUAL X X)))
    '((X CONS))
    2 :simple 'TEST? state)

#|
(local (include-book "arithmetic-5/top" :dir :system))
(thm (implies (and (rationalp a)
                  (rationalp b)
                  (rationalp c)
                  (< 0 a)
                  (< 0 b)
                  (< 0 c)
                  (<= (expt a 2) (* b (+ c 1)))
                  (<= b (* 4 c)))
             (< (expt (- a 1) 2) (* b c))));(set-acl2s-random-testing-use-instantiation-method 'concrete)

(local (set-default-hints
        '((nonlinearp-default-hint stable-under-simplificationp
                                   hist pspv))))
 
 (defthm russinoff2
  (implies (and (rationalp a)
                (rationalp b)
                (rationalp c)
                (<= 1 a)
                ;(< 0 b)
                ;(< 0 c)
                (<= (expt a 2) (* b (+ c 1)))
                (<= b (* 4 c)))
           (< (expt (- a 1) 2) (* b c)))
  :hints (("goal" :cases ((<= 0 b)))))
|#
;(defdata poss (enum 1 2 3 4 5 6 7 8 9))
(acl2s-defaults :set instantiation-method :simple)
(time$
(test? 
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (posp x1)
                (posp x2)
                (posp x3)
                (< x1 x2)
                (< x2 x3)
                (< x3 10)
                (equal 0 (+ c1 c2 c3))
                (equal 0 (+ (* c1 x1) (* c2 x2) (* c3 x3))))
           (and (= 0 c1) (= 0 c2) (= 0 c3)))))
;simple: 2.82 sec
;incr: 8.21 sec
;10 July 2011: 100 trials incremental finds 3 wts and 3 cts: 56.78 sec
;10 July 2011: 100 trials simple finds 0 wts and 0 cts: 2.47 sec

(acl2s-defaults :set verbosity-level 1)
(acl2s-defaults :set num-trials 100)
(acl2s-defaults :set instantiation-method :simple)
(test?
 ;(let ((z 21) (y 22) (x 2))
 (implies (and (posp x)
               (posp y)
               (posp z)
               (> z 16)
               (<= x y)
               (>= (+ x y) z))
          (>= (* x (* y z)) (* x (* x y)))))

(acl2s-defaults :set instantiation-method :simple)
;10July-11 incremental takes time but finds ctx consistently 
(test?
 (implies (and (posp x)
               (posp y)
               (posp z)
               ;(> z 16)
               (<= (+ x y) (* 2 z)))
          (> (* z z) (* x y))))

(acl2s-defaults :set instantiation-method :simple)
(test?
 (implies (and (posp x)
               (posp y)
               (posp z)
               (> z 16)
               (<= x z))
          (> (* z z) (* x x))))

(test?
 (implies (and (posp x)
               (posp y)
               (posp z)
               (> z 16)
               (<= (+ x y) (* 2 z)))
          (or (> (* x y z) (* x y x))
              (> (* x y z) (* x y y)))))

#|
;(trace$ defdata::find-recursive-records)
;TERMINATION ISSUES with records
(defdata form (oneof pos
                     (fnot (f . form))
                     (fand (lhs . form) (rhs . form))
                     (for (lhs . form) (rhs . form))
                     (fimplies (lhs . form) (rhs . form))))

(defdata formula (oneof pos
                        (list 'not formula)
                        (list 'and formula formula)
                        (list 'or formula formula)
                        (list 'implies formula formula)))
;(untrace$)
(defunc simplify (f)
  :input-contract (formulap f)
  :output-contract (formulap (simplify f))
  (cond ((posp f) f)
        ((eq (first f) 'not) (list 'not (simplify (second f))))
        ((eq (first f) 'and) (list 'and (simplify (second f)) (simplify (third f))))
        ((eq (first f) 'or) (list 'or (simplify (second f)) (simplify (third f))))
        ((eq (first f) 'implies) (list 'or (list 'not (simplify (second f))) (simplify (third f))))
        (t f)))

(set-acl2s-random-testing-use-instantiation-method 'simple)
(set-acl2s-random-testing-max-num-of-random-trials 10)
(defunc simplifiedp (f)
  :input-contract (formulap f)
  :output-contract (booleanp (simplifiedp f))
   (cond ((posp f) t)
        ((eq (first f) 'not) (simplifiedp (second f)))
        ((eq (first f) 'and) (and (simplifiedp (second f)) (simplifiedp (third f))))
        ((eq (first f) 'or) (and (simplifiedp (second f)) (simplifiedp (third f))))
        ((eq (first f) 'implies) nil)
        (t nil)))
  
(defthm simplify-is-stable
  (implies (formulap f)
           (equal (simplify (simplify f))
                  (simplify f))))

(defunc nnf (f)
  :input-contract (formulap f)
  :output-contract (formulap (nnf f))
   (cond ((posp f) f)
        ((and (eq (first f) 'not) (posp (second f))) f)
        ((and (eq (first f) 'not) (eq 'not (first (second f))))
         (nnf (second (second f))))
        ((eq (first f) 'and) (list 'and (nnf (second f)) (nnf (third f))))
        ((eq (first f) 'or) (list 'or (nnf (second f)) (nnf (third f))))
        ((eq (first f) 'implies) (list 'implies (nnf (second f)) (nnf (third f))))
        ((and (eq (first f) 'not)
              (eq 'and (first (second f))))
         (let* ((a (second f))
                (lhs (second a))
                (rhs (third a)))
           (list 'or (nnf (list 'not lhs)) (nnf (list 'not rhs)))))
        ((and (eq (first f) 'not)
              (eq 'or (first (second f))))
         (let* ((a (second f))
                (lhs (second a))
                (rhs (third a)))
           (list 'and (nnf (list 'not lhs)) (nnf (list 'not rhs)))))     
         ((and (eq (first f) 'not)
              (eq 'implies (first (second f))))
         (let* ((a (second f))
                (lhs (second a))
                (rhs (third a)))
           (list 'and (nnf lhs) (nnf (list 'not rhs)))))
        (t f)))
;(trace$ run-trials)

(SET-ACL2S-RANDOM-TESTING-SEED-GENERATION-TYPE 'nat-tree)
(er-let* ((tr (build-rand-tree-top 'formula state)))
  (value (nth-formula tr)))
;TODO BUG
(SET-ACL2S-RANDOM-TESTING-SEED-GENERATION-TYPE 'nat)

(top-level-test? ;simp-nnf-commute
  (implies (formulap f)
  (equal (nnf (simplify f))
         (simplify (nnf f)))))

|#
(defdata file (cons nat string))
(defdata dir (listof (cons string (oneof file dir))))
;FIX TODO
(defdata (dir1 (map string dir-entry1))
         (dir-entry1 (oneof file dir1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;fermat number
(defun fermat (n)
  (1+ (expt 2 (expt 2 (nfix n)))))

;Euler: All factors of f(n) should have the form k*2^{n+1} + 1
;Lucas: for all n > 1, factors of f(n) are of form k*2^{n+2} + 1
(defun f-factor (k n)
  (let ((k (nfix k))
        (n (nfix n)))
    (1+ (* k (expt 2 (+ 1 n))))))

;is k a factor of n other than 1 and n?
(defun factor (k n)
  (and (< 1 k)
       (< k n)
       (natp (/ n k))))

(test?
 (implies (posp k)
          (not (factor k (fermat 5)))))

(test?
 (implies (posp k)
          (not (factor (f-factor k 5) (fermat 5)))))

(acl2s-defaults :set num-witnesses 0)
(acl2s-defaults :set num-trials 10000)

(time$
(top-level-test?
 (implies (and (posp k)
               (posp n)
               (< n 15))
          (not (factor k (fermat n)))))
)
(acl2s-defaults :set instantiation-method :simple)
(acl2s-defaults :set num-trials 10000)
;1000
;incr: 44.88
;simple: 0.11
;10,000
;simple: 1.07
;incr: no patience to check
(acl2s-defaults :set verbosity-level 1)
(time$
 (top-level-test?
 (implies (and (posp k)
               (posp n)
               (< n 15))
          (not (factor (f-factor k n) (fermat n)))))
 )


(test? (implies (true-listp x) (not (equal x (list y v w z)))))

;; take : Nat * List-of-Int -> List-of-Int
(defun take-n (n lst)
  (if (endp lst)
    nil
    (if (zp n)
      nil
      (cons (car lst) (take-n (1- n) (cdr lst))))))

;; drop : Nat * List-of-Int -> List-of-Int
(defun drop-n (n lst)
  (if (endp lst)
    nil
    (if (zp n)
      lst
      (drop-n (1- n) (cdr lst)))))

;; Prove commutativity of take and drop
(acl2s-defaults :set num-trials 100)

(defthm take-drop-commute
  (implies (and (integerp i)
                (integerp j)
                (integer-listp lst))
           (equal
            (take-n j (drop-n i lst))
            (drop-n i (take-n (+ i j) lst)))))
 
(top-level-test? 
 (implies (and (posp (car x))
               (posp (cdr x)))
          (<= (cdr x) (len x)))
 )
;this checks that top goal counterexamples are printed
;no longer works, as counterexample is found before ACL2 dest elims
(acl2s-defaults :set num-witnesses 5)

(test? (implies (and (posp (car x))
                     (posp (cdr x)))
                (<= (cdr x) (len x)))
       )
(defdata loi (listof integer))
(test?
 (implies (and (posp i)
               (posp j)
               (loip lst))
          (equal
           (take-n j (drop-n i lst))
           (drop-n i (take-n j lst)))))

(defun large-list (x)
  (and  (or (character-listp x) (loip x))
        (> (len x) 3)))

(test?  (implies (large-list x) (> (len x) 6)))

;old
(thm (implies (large-list x) (> (len x) 6)));this gives an example where acl2check infers stronger than acl2 type-alist? YES!!
;but note that acl2 does have that knowledge in the type context.

(test? (implies (and (or (true-listp x)
                             (stringp x))
                         (not (equal x nil))
                         (not (equal x "")))
                    (> (len x) 0)))

(test? (iff (implies p q) (or (not p) p)))

;this checks that top goal counterexamples are printed
;;this checks and also checks eliminated variables
(test? (implies (and (posp (car x))
                     (equal y y)
                     (equal z y)
                     (posp (cdr x)))
                (<= (cdr x) (len x))))
(acl2s-defaults :set verbosity-level 1)
;;checking commutative property for take and drop
(test? ;take-drop-commute
 (implies (and (posp i) (posp j) (loip lst)) 
  (equal
   (take-n j (drop-n i lst))
   (drop-n i (take-n j lst)))))

;;Ahh counter-example ...lets modify the property
(test? ;take-drop-commute-modified
 (implies (and (natp i) (natp j) (loip lst )) 
  (equal
   (take-n j (drop-n i lst))
   (drop-n i (take-n (+ i j) lst)))))

;counterexample:
 ;-- (Y 40/7) and (X 12)
;hard
(acl2s-defaults :set verbosity-level 1)
(thm (IMPLIES (AND (RATIONALP X)
                    (RATIONALP Y)
                    (NOT (EQUAL Y 0))
                    (<= 0 Y)
                    (<= 0 X)
                    (<= Y X)
                    (INTEGERP (+ 1 (- X)))
                    (< 1 X)
                    (NOT (INTEGERP (+ 1 (- X) (* 2 Y))))
                    (<= X (+ 1 (* 2 Y))))
               (< X
                  (+ 1 (DENOMINATOR (+ 1 (- X) (* 2 Y)))
                     (NUMERATOR (+ 1 (- X) (* 2 Y)))))))

(thm (IMPLIES (AND (RATIONALP X)
              (RATIONALP Y)
              (NOT (EQUAL Y 0))
              (<= 0 Y)
              (<= 0 X)
              (<= Y X))
         (O< (ACL2-COUNT (+ 1 0 (- (+ (+ X (- Y)) Y))))
             (ACL2-COUNT (+ 1 Y (- (+ X (- Y))))))))
(acl2s-defaults :set num-witnesses 2)
(acl2s-defaults :set num-counterexamples 2)
(thm 
 (implies (and (natp i)
               (natp x)
               ;(> x 0);testting found
               (<= i x))
          (equal (nth i (cons a (defdata::make-list-logic a x)))
                 (nth (- i 1) (defdata::make-list-logic a x)))))

(test? 
  (implies (and (integerp c1)
                (integerp c2)
                (posp x1)
                (posp x2)
                (< x1 x2)
                (equal 0 (+ c1 c2))
                (equal 0 (+ (* c1 x1) (* c2 x2))))
           (and (= 0 c1) (= 0 c2))))

;excellent, this never worked before
;first example demontrating the superiority of
; :incremental (DPLL) over :simple (naive random testing)
(acl2s-defaults :set instantiation-method :incremental)
(acl2s-defaults :set backtrack-limit 4)
(time$
 ;simple: 2.13 seconds no counterexample no witness
;incr: 41.52 seconds blimit:4 cts:2 and wts:2
;incr: 48.56 seconds blimit:0 cts:0 and wts:0
;incr: 63.08 seconds blimit:3 cts:2 and wts:2
;incr: 78.08 seconds blimit:3 cts:2 and wts:2
;incr: 143.13 seconds blimit:2 cts:2 and wts:2
;incr: 105.95 seconds blimit:2 cts:2 and wts:2
;incr: 175.94 seconds blimit:1 cts:1 and wts:2 + 1
(test? 
  (implies (and (integerp c1)
                (integerp c2)
                (integerp c3)
                (posp x1)
                (posp x2)
                (posp x3)
                (< x1 x2)
                (< x2 x3)
                (equal 0 (+ c1 c2 c3))
                (equal 0 (+ (* c1 x1) (* c2 x2) (* c3 x3))))
           (and (= 0 c1) (= 0 c2) (= 0 c3))))
)
;IDEA: Need to create a rule manager (sorter) which will
;manage the rule database looking for rules that will
;give me almost linear variable dependency graph with
;the edges mostly a relation like equality which will
;propagate the decisions made at the source

;MORE:
;Can we store some output/input information on each
;function/predicate, that might help glean more information
;for dependency analysius````?

#|
We falsified the conjecture. Here are counterexamples:
 -- (X3 8), (X2 7), (X1 6), (C3 -2), (C2 4) and (C1 -2)
 -- (X3 6), (X2 4), (X1 3), (C3 1), (C2 -3) and (C1 2)
 -- (X3 10), (X2 8), (X1 2), (C3 -3), (C2 4) and (C1 -1)
|#

;(defdata memory (listof (cons nat integer)))
(defdata memory (map nat integer))

(nth-memory 9436794189)

(defun update (address value memory)
  (cond ((endp memory)
         (acons address value nil))
        ((equal address (caar memory))
         (acons address value (cdr memory)))
        ((< address (caar memory))
         (acons address value memory))
        (t (cons (car memory) 
                 (update address value (cdr memory))))))


;Conjecture - version#1
(test?
 (equal (update a1 v1 (update a2 v2 m))
        (update a2 v2 (update a1 v1 m))))
(acl2s-defaults :set backtrack-limit 3)
(acl2s-defaults :set instantiation-method :simple)
; Conjecture - version 2
(time$
 ;10july incr:16.5 sec
 ;10july simple:0.06 sec
(test?
 (implies (and (memoryp m)
               (natp a1)
               (natp a2))
          (equal (update a1 v1 (update a2 v2 m))
                 (update a2 v2 (update a1 v1 m))))))

(defdata::build-enumcall-top 'memory state)

(defun in-memory (a m)
  (if (endp m)
    nil
    (or (equal a (caar m))
        (in-memory a (cdr m)))))

(acl2s-defaults :set instantiation-method :incremental)
(acl2s-defaults :set backtrack-limit 2)
;Conjecture - version#3
(time$
 ;10jul: incremental -> 21.58/12.44 (3) 8.21/11.73 (2)
(test?
 (implies (and (memoryp m)
               (natp a1)
               (natp a2)
               (or (in-memory a1 m)
                   (in-memory a2 m)))
          (equal (update a1 v1 (update a2 v2 m))
                 (update a2 v2 (update a1 v1 m))))))


(acl2s-defaults :set instantiation-method :simple)
;(acl2s-defaults :set backtrack-limit 4)
;Conjecture - version#4
;28.19 seconds with random testing incremental (blimit 3)
;26.69 seconds with random testing incremental (blimit 2)
;22.15 seconds with random testing incremental (blimit 1)
;8.62 seconds with random testing incremental (blimit 0)
;1.84 seconds with random testing simple
;1.75 seconds with random testing disabled
;50.5 seconds on July 10 2011 (incremental blimit 2)
(thm
 (implies (and (memoryp m)
               (natp a1)
               (natp a2)
               (or (in-memory a1 m)
                   (in-memory a2 m))
               (not (equal a1 a2)))
          (equal (update a1 v1 (update a2 v2 m))
                 (update a2 v2 (update a1 v1 m)))))
;23.36 seconds with random testing incremental (blimit 4 and 5)

;AA Trees
(defdata aa-tree (oneof 'Bottom 
                        (node (key . pos)
                              (level . nat)
                              (left . aa-tree)
                              (right . aa-tree))))

;FIX TODO Both left and right trees are always of same size
(defdata::build-enumcall-top 'aa-tree state)


;Performance of Nat-tree vs Nat
(defun run4-for-i (i type state)
  (declare (xargs :mode :program :stobjs (state)))
  (if (zp i)
    (value nil)
    (er-progn
     (if (not (acl2s-defaults :get flatten-defdata))
       (er-let* ((enum-info (defdata::get-enum-info type 'test (w state) state)))
         (defdata::build-enumcall-from-enum-info type enum-info 'test state))
       (defdata::build-enumcall-top type state))
     (run4-for-i (1- i) type state))))

(acl2s-defaults :set flatten-defdata t) 
;stupid performance bug due to acl2::current-acl2-world package name
(time$ (run4-for-i 100000 'aa-tree state))
;something is slower (is it CCL/SBCL?) Jul 10 -> 1.41 vs 7.85
;0.49 vs 4.89

(defun skew (tree)
  (if (eq 'Bottom tree)
    tree
    (if (= (mget :level (mget :left tree)) (mget :level tree))
      ;;rotate right
      (let ((ltree (mget :left tree))
            (rtree (mget :right tree)))
        (node (mget :key ltree)
              (mget :level ltree)
              (mget :left ltree)
              (node (mget :key tree)
                    (mget :level tree)
                    (mget :right ltree)
                    rtree)))
      tree)))

(defun split (tree)
  (if (eq 'Bottom tree)
    tree
    (if (<= (mget :level tree)
            (mget :level (mget :right (mget :right tree))))
      ;;rotate left
      (let* ((rtree (mget :right tree))
             (rrtree (mget :right rtree)))
        (node (mget :key rtree)
              (1+ (mget :level rtree))
              (node (mget :key tree)
                    (mget :level tree)
                    (mget :left tree)
                    (mget :left rtree))
              rrtree))
      tree)))

(set-acl2s-random-testing-enabled nil)
(defun insert (data tree)
  (if (or (eq 'Bottom tree) (not (aa-treep tree)))
    (node data 1 'Bottom 'Bottom)
    (if (equal data (mget :key tree))
      tree
      (let ((newtree (if (< data (mget :key tree))
                       (mset :left 
                             (insert data (mget :left tree))
                             tree)
                       (mset :right
                             (insert data (mget :right tree))
                             tree))))
        (split
         ;(skew
          newtree)))))

(defun wf-aa-treep (tree)
  (if (not (aa-treep tree))
    nil
    (if (eq 'Bottom tree)
      t
      (let ((n (mget :level tree))
            (l (mget :left tree))
            (r (mget :right tree)))
        (if (eq 'Bottom l)
          (and (= 1 n)
               (or (eq 'Bottom r)
                   (and (= 1 (mget :level r))
                        (eq 'Bottom (mget :left r))
                        (eq 'Bottom (mget :right r)))))
          (and (wf-aa-treep l)
               (wf-aa-treep r)
               (not (eq 'Bottom r))
             (< (mget :level l) n)
             (<= (mget :level r) n)
             (< (mget :level (mget :right r)) n)))))))

(defthm skew-wf
  (implies (and (aa-treep v)
                (wf-aa-treep v))
           (equal (skew v) v)))

(defthm split-wf
  (implies (and (aa-treep v)
                (wf-aa-treep v))
           (equal (split v) v)))
(set-acl2s-random-testing-enabled t)

(acl2s-defaults :set flatten-defdata nil)
(acl2s-defaults :set backtrack-limit 3)
(acl2s-defaults :set verbosity-level 1)
(acl2s-defaults :set instantiation-method :simple)
(test? (implies (and (aa-treep tr);type hyp
                     (posp n);type hyp
                     (wf-aa-treep tr));constraint
                (wf-aa-treep (insert n tr))))

;#|
;Experimenting:
(set-acl2s-random-testing-enabled nil)
(defun insert3 (data tree)
  (if (or (eq 'Bottom tree) (not (aa-treep tree)))
    (node data 1 'Bottom 'Bottom)
    (if (equal data (mget :key tree))
      tree
      (let ((newtree (if (< data (mget :key tree))
                       (mset :left 
                             (insert3 data (mget :left tree))
                             tree)
                       (mset :right
                             (insert3 data (mget :right tree))
                             tree))))
        ;(split
         (skew
          newtree)))))

(acl2s-defaults :set flatten-defdata nil)

(test? (implies (and (aa-treep tr);type hyp
                   (posp n);type hyp
                   (wf-aa-treep tr));constraint
              (wf-aa-treep (insert3 n tr))))

(top-level-test? (implies (and (aa-treep tr))
                (wf-aa-treep tr)))

(top-level-test? (implies (and (aa-treep tr))
                (wf-aa-treep tr)))
                   
                
(test? 
 (implies (aa-treep tr)
          (equal (split (split tr))
                 (split tr))))
 


(test?
 (IMPLIES (AND (AA-TREEP TR)
               (= N '(z x y z w r t y b d fg dfg dfg))
               (WF-AA-TREEP TR)
               ;(>>= N (MGET :KEY TR))
               (NOT (EQUAL (MGET :LEVEL (MGET :LEFT TR))
                           (MGET :LEVEL TR))))
          (not (WF-AA-TREEP (MSET :RIGHT (INSERT3 N (MGET :RIGHT TR))
                             TR)))))


;---------interesting code for students
;(defdata adjacency-list (map symbol symbol-list))
(defun adjacency-list1p (v)
  (if (null v)
      t
    (if (atom v)
        nil
      (let ((entry (car v)))
      (and (symbolp (car entry))
           (symbol-listp (cdr entry))
           (no-duplicatesp (cdr entry))
           (adjacency-list1p (cdr v)))))))

(defun adjacency-listp (v)
  (and (adjacency-list1p v)
       (no-duplicatesp (strip-cars v))))

(defun make-empty-adj-list (vars)
  (declare (xargs :guard (and (symbol-listp vars)
                              (no-duplicatesp vars))))
  ;order important 
  ;order of keys alst created is the same as order of vars
  (if (endp vars)
    nil
    (cons (cons (car vars) nil)
          (make-empty-adj-list (cdr vars)))))



;fs means Functionaly dependent vars
;ASSUMPTION: alst has all the variables as keys already
;this function just updates the entries, doesnt insert
;new entries.
(defun union-entry-in-adj-list (var fvars alst)
  (if (endp alst)
      nil
    (if (eq var (caar alst))
      (cons (cons var (union-equal fvars 
                                   (cdar alst)))
            (cdr alst))
      (cons (car alst)
            (union-entry-in-adj-list var fvars (cdr alst))))))
  
  
;recurse above fun over list of indices
(defun union-entries-in-adj-list (is fis alst)
 (if (endp is)
    alst
    (union-entries-in-adj-list 
     (cdr is) fis (union-entry-in-adj-list (car is) fis alst))))

  
(defun transpose-alst1 (alst ans)
;Scan G at index i and transpose the result corresponding to i in ans
  (if (endp alst)
      ans
    (b* (((cons v vs) (car alst)))
      (transpose-alst1 (cdr alst)
                       (union-entries-in-adj-list vs (list v) ans)))))
  

(defun transpose-alst (alst)
;Return transpose/reverse of alst
;INVARIANT: Order is very important
  (transpose-alst1 alst (make-empty-adj-list (strip-cars alst))))

(defun non-empty-symbol-list1p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (symbol-listp x)))

(defun nth-non-empty-symbol-list1 (n)
  (nth-symbol-list (1+ n)))
(register-custom-type 
         non-empty-symbol-list1 t
         nth-non-empty-symbol-list1
         non-empty-symbol-list1p)
(defun non-boolean-symbolp (x)
  (declare (xargs :guard t))
  (and (not (booleanp x))
       (symbolp x)))
(defun nth-non-boolean-symbol (n)
  (if (eq nil (nth-symbol n))
    'a
    (nth-symbol n)))
(register-custom-type 
         non-boolean-symbol t
         nth-non-boolean-symbol
         non-boolean-symbolp)
(defdata adjacency-list2 (map non-boolean-symbol non-empty-symbol-list1))

(defthm transpose-idempotent
  (implies (and (adjacency-list2p x)
                (adjacency-listp x))
           (equal (transpose-alst (transpose-alst x))
                  x)))

(defthm transpose-doesnt-change-order
  (implies (and (adjacency-list2p x)
                (adjacency-list1p x))
           (equal (strip-cars (transpose-alst x))
                  (strip-cars x))))

;;; boyer alternating.events
;;; Use these to automatically generate generators from predcates or do
;;; mode-analysis etc --harshrc

; Now on to my formalization.  We first define the six functions
; needed in the statement of the theorem.  The main, all encompassing,
; theorem is stated at the very end, and is named ``all''.

; Intuitively, we imagine that cards are arbitrary objects, but
; numbers are ``red'' and nonnumbers are ``black.''

(defn opposite-color (x y)

; This is the definition of ``opposite-color,'' which checks that its
; two arguments, x and y, are of opposite color, in the intuitive
; sense mentioned above.

  (or (and (numberp x) (not (numberp y)))
      (and (numberp y) (not (numberp x)))))

(defn alternating-colors (x)  

; This is the definition of ``alternating-colors,'' which checks that
; its argument, x, is a list of objects whose colors alternate.  In the
; base case, if the list is empty or the list has length one, then we
; say it is indeed alternating.  In the inductive or recursive case,
; we require that the first two elements be of opposite color and that
; the ``rest,'' i.e., cdr, i.e., all but the first, of the list be
; alternating.

  (if (or (nlistp x)
          (nlistp (cdr x)))
      t
    (and (opposite-color (car x) (cadr x))
         (alternating-colors (cdr x)))))

(defn paired-colors (x) 

; This is the definition of ``paired-colors,'' which checks that its
; argument, x, is a list such that if its elements are pealed off from
; the front in pairs, the pairs are found to be of opposite color.  In
; the base case, we say a list of length 0 or 1 is paired.  In the
; inductive or recursive case, where the list has at least length 2,
; we insist that the first and second elements be of opposite color,
; and that the ``cddr,'' i.e., the rest of the list past the first two
; elements, is paired.

  (if (or (nlistp x)
          (nlistp (cdr x)))
      t
    (and (opposite-color (car x) (cadr x))
         (paired-colors (cddr x)))))



(defn shufflep (x y z)

; This is the definition of ``shufflep,'' which checks that its third
; argument, z, is a ``merge'' or ``shuffling'' of its first two
; arguments, x and y.  Shufflep also requires that x, y, and z all be
; ``plistp''.

; In the base case, where z is empty, we insist that x, y, and z all
; be NIL.

; In the ``almost'' base cases in which z is not empty, but either x
; or y is empty, we insist that if x is empty, then x is NIL, y is
; equal to z, and y is ``plistp'', whereas if x is not empty but y is,
; we insist that y is NIL, x is equal to z, and x is ``plistp''.

; In the fully inductive case, where none of x, y, or z, is empty, we
; insist that either (a) the first element of x is the first element
; of z and (cdr z) is a shuffle of (cdr x) and y, or (b) the first
; element of y is the first element of z and (cdr z) is a shuffle of x
; and (cdr y).

  (if (nlistp z)
      (and (equal x nil)
           (equal y nil)
           (equal z nil))
    (if (nlistp x)
        (and (equal x nil)
             (equal y z)
             (plistp y))
      (if (nlistp y)
          (and (equal y nil)
               (equal x z)
               (plistp x))
        (or (and (equal (car x) (car z))
                 (shufflep (cdr x) y (cdr z)))
            (and (equal (car y) (car z))
                 (shufflep x (cdr y) (cdr z))))))))

(defn even-length (l)

; This is the definition of ``even-length,'' which checks that the
; length of its argument, l, is even.  In the base cases, if l is
; empty we return true and if l has one element we return false.  In
; the inductive or recursive case, we insist that (cddr l), i.e., the
; rest of l after its second element, has even length.

  (if (nlistp l)
      t
    (if (nlistp (cdr l))
         f
      (even-length (cddr l)))))

