; ****************** BEGIN INITIALIZATION FOR ACL2s MODE ****************** ;
; (Nothing to see here!  Your actual file is after this initialization code);

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading the CCG book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "ccg/ccg" :uncertified-okp nil :dir :acl2s-modes :ttags ((:ccg)) :load-compiled-file nil);v4.0 change

;Common base theory for all modes.
#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s base theory book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "base-theory" :dir :acl2s-modes)


#+acl2s-startup (er-progn (assign fmt-error-msg "Problem loading ACL2s customizations book.~%Please choose \"Recertify ACL2s system books\" under the ACL2s menu and retry after successful recertification.") (value :invisible))
(include-book "custom" :dir :acl2s-modes :uncertified-okp nil :ttags :all)

#+acl2s-startup (er-progn (assign fmt-error-msg "Problem setting up ACL2s mode.") (value :invisible))

;Settings common to all ACL2s modes
(acl2s-common-settings)
;(acl2::xdoc acl2s::defunc) ;; 3 seconds is too much time to spare -- commenting out [2015-02-01 Sun]

(acl2::xdoc acl2s::defunc) ; almost 3 seconds

; Non-events:
;(set-guard-checking :none)

(acl2::in-package "ACL2S")

; ******************* END INITIALIZATION FOR ACL2s MODE ******************* ;
;$ACL2s-SMode$;ACL2s
;; this regression file aims at testing the various features of 
;; counterexample generation in ACL2 Sedan


;(add-include-book-dir :acl2s-modes "../")
;(ld "acl2s-mode.lsp" :dir :acl2s-modes)

;(include-book "cgen/top" :dir :acl2s-modes)
(include-book "misc/eval" :dir :system)
(acl2s-defaults :set verbosity-level 2)
(acl2s-defaults :set sampling-method :uniform-random)

;jmitesh BAE example (test the test/enum feature)
;; a pair of number
(defdata num-pair (record (m . nat)
                          (n . nat)))

(defun prop (p)
  "a predicate that checks if the second is greater than the first"
  (let ((m (num-pair-m p))
        (n (num-pair-n p)))
    (> n m)))

(defun filter-num-pair (p)
  "a filter which returns a pair of numbers such that property prop holds"
  (let ((m (num-pair-m p))
        (n (num-pair-n p)))
    (if (prop p)
        p
      (num-pair m (* (1+ n) (1+ m))))))

;; a new enumerator for the type num-pair it needs to be in program
;; mode because the nth-num-pair is a progran mode function.
(program)
(defun nth-num-pair-user (n)
  (filter-num-pair (nth-num-pair-builtin n)))

(defun nth-num-pair/acc-user (m seed)
  (b* (((mv pair seed) (nth-num-pair/acc-builtin m seed))
       ((num-pair m n) pair))
      (if (> n m)
        (mv pair seed)
        (mv (num-pair m (+ m n 1)) seed))))
(logic)

;; instruct CGEN to use the enumerator defined by the user
(defdata-attach num-pair :enumerator nth-num-pair-user)
(defdata-attach num-pair :enum/acc nth-num-pair/acc-user)
(must-fail ; fail or pass?
(test?
 (implies (and (num-pairp p)
               ;(prop p)
               )
           (> (num-pair-n p) (num-pair-m p))))

)













;from elliot hwkk 5 sprint 2015
(defdata rationallist (listof rational))
        
        
(defunc out-of-order-help (l a)
  :input-contract (and (rationallistp l) (natp a))
  :output-contract (natp (out-of-order-help l a))
  (cond 
   ((endp l) a)
   ((endp (rest l)) (+ a 1))
   ((> (first l) (second l)) a)
   (t (out-of-order-help (rest l) (+ a 1)))))

(defunc out-of-order (l)
  :input-contract (rationallistp l)
  :output-contract (natp (out-of-order l))
  (out-of-order-help l 0))

(check= (out-of-order '(1 2))   2) ; nothing swappable
(check= (out-of-order '(0 2 1)) 1)
(check= (out-of-order '(0 2 1 3)) 1)
(check= (out-of-order '(1 2 3 4 1)) 3)


(acl2s-defaults :set num-trials 2000)
(set-gag-mode nil)
(acl2s-defaults :set verbosity-level 3)
(test?
  (IMPLIES (AND (ACL2::EXTRA-INFO '(:GUARD (:BODY SORT-HELPER))
                                  '(SWAP (OUT-OF-ORDER L) L))
                ;(NATP K)
                (RATIONALLISTP L)
                (CONSP L)
                ;(NOT (EQUAL K 0))
                (NOT (EQUAL (OUT-OF-ORDER L) (LEN L))))
           (< (+ 1 (OUT-OF-ORDER L)) (LEN L))))




; testcase -1 (from acl2s-issues)
(must-fail
 (test? (implies (complex-rationalp j)
                 (> j -45)))
 )

;++++++++++++++testcase 0 [check if checkpoints are tested]++++++++++++++++++++

(acl2s-defaults :set num-counterexamples 10)
(must-fail
 (test? (implies (and (posp (car x))
                      (posp (cdr x)))
                 (= (cdr x) (len x))))
 )


;Find a long running thm, put it here, interrupt it and
; then see if the following still gives valid results
(must-fail
 (thm (implies  (natp x) (posp x)))
)

;++++++++++++++++testcase 1 [classic reverse example]++++++++++++++++++++++++++
(acl2s-defaults :set num-counterexamples 3) ;default
(acl2s-defaults :set testing-enabled :naive)


;Define Reverse function
(defun rev1 (x)
  (if (endp x)
    nil
    (append (rev1 (cdr x)) (list (car x)))))

(must-fail
 (test? (equal (rev1 (rev1 x)) x))
)



(acl2s-defaults :set testing-enabled T)
;(trace$ cgen::compute-event-ctx cgen::allowed-cgen-event-ctx-p cgen::init-cgen-state/event)
;(acl2s-defaults :set verbosity-level 5)
(must-fail
 (thm (equal (rev1 (rev1 x)) x))
 )


(acl2s-defaults :set testing-enabled :naive)
;Modify the conjecture, add the type hypothesis
(test? (implies (true-listp x)
                (equal (rev1 (rev1 x)) x)))


;++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

;; testcase 2 (Shape of triangle - example from testing literature)
;(defdata triple (list pos pos pos))

(defun trianglep (v)
  (and (pos-listp v)
       (consp v) (consp (cdr v)) (consp (cddr v))
       (< (third v) (+ (first v) (second v)))
       (< (first v) (+ (second v) (third v)))
       (< (second v) (+ (first v) (third v)))))

#|
(defun triangle-enum_old (n)
  (b* (((list n1 n2 n3) (defdata::split-nat 3 n))
       (x1 (nth-pos n1))
       (x2 (nth-pos n2))
       (x3 (nth-integer-between n3 1 (+ x1 x2 -1))))
    (list x1 x2 x3)))
|#

(defun triangle-enum (n)
    (b* (((list p n) (split 2 n))
         ((when (< p 5)) (list 1 1 1))
         ((list n1 n2) (split 2 n))
         (lo 1)
         (hi (+ p (- 2)))
         (x1 (nth-integer-between n1 lo hi))
         (hi (+ p (- x1) (- 1)))
         (x2 (nth-integer-between n2 lo hi))
         (x3 (+ p (- x1) (- x2))))
      (list x1 x2 x3)))

(register-type triangle
               :predicate trianglep
               :enumerator triangle-enum)

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
(acl2s-defaults :set cgen-local-timeout 50)

(time$
; 27th Aug '12
;Note: random is slightly less than twice as fast as BE
; random - ; 4.95 seconds realtime, 4.96 seconds runtime
;            (927,923,408 bytes allocated)
; be -     ; 8.12 seconds realtime, 8.14 seconds runtime
;            (1,902,023,552 bytes allocated).
; Investigate this!
 (test? 
  (implies (and ;(triplep x)
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

(acl2s-defaults :set testing-enabled t)


;; whoa! Without arithmetic-5, I get nowhere with the
;; below example. 
;; 20th March 2013 - lets try arithmetic with meta

;(include-book "arithmetic/top-with-meta" :dir :system)
; But even without these books, now the following works fine,
; but with the above book, it produces way more cts (201 vs 4)

(must-fail
(test?
 (implies (and ;(triplep x)
               (trianglep x)
               (> (third x) 256)
               (= (third x)
                  (* (second x) (first x))))
          (not (equal "isosceles" (shape x)))))
)

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

;; (defdata memory (map nat integer))

(nth-memory 943679411)

(defun update (address value memory)
  (cond ((endp memory)
         (acons address value nil))
        ((equal address (acons-caar memory))
         (acons address value (cdr memory)))
        ((< address (acons-caar memory))
         (acons address value memory))
        (t (cons (car memory) (update address value (cdr memory))))))

(defun make-ordered-list (n acc)
  (if (zp n)
    acc
    (make-ordered-list (- n 1) (cons n acc))))

(make-ordered-list 4 nil)
(defun nth-ordered-memory (n)
  ;(declare (xargs :guard (natp n))) ;fix the guard eagerness in nth-ordered-memory-uniform
  (declare (xargs :mode :program))
  (let* ((m (nth-memory-builtin n))
         (len (len m))
         (vals (strip-cdrs m))
         (keys (make-ordered-list len nil)))
    (pairlis$ keys vals)))

;attach a custom test enumerator to a defdata type
(defdata-attach memory :test-enumerator nth-ordered-memory :verbose t)               

;Conjecture - version#1
(must-fail
(test?
 (equal (update a1 v1 (update a2 v2 m))
        (update a2 v2 (update a1 v1 m))))
)
; NOTE: BE gets no counterexamples in the above for numtrials 1000!
; Makes sense.


; Conjecture - version 2
(must-fail
 (test?
  (implies (and (memoryp m)
                (natp a1)
                (natp a2))
           (equal (update a1 v1 (update a2 v2 m))
                  (update a2 v2 (update a1 v1 m)))))
 )
; NOTE: BE gets no counterexamples in the above even for numtrials 100000!
; This is not good. This is probably due to the faulty DEFDATA::|next BE args|
; function which enumerates the variables in a naive way. See note after
; testcase 5.
; 1000000 timesout


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
                 (update a2 v2 (update a1 v1 m))))
 :hints (("Goal" :in-theory (enable update acons acons-caar acons-cdar))))

;; testcase 4 (Russinoff's example)
(must-fail
 (test? (implies (and (real/rationalp a)
                      (real/rationalp b)
                      (real/rationalp c)
                      (< 0 a)
                      (< 0 b)
                      (< 0 c)
                      (<= (expt a 2) (* b (+ c 1)))
                      (<= b (* 4 c)))
                 (< (expt (- a 1) 2) (* b c))))
 )
;; TODO: C is being printed in quoted form in :incremental
;; It seems the above has been fixed.

;; TODO harshrc 27th Aug '12
;; IMP NOTE: incremental does a bad job if the initial value for the first
;; variable chosen is BAD. If it was good, it does an efficient job.
;; WHich means, I need to look into how I am using num-trials,
;; backtrack-limit and stopping condition in the case of incremental.
;; I need to revisit the implementation design of incremental!!
(must-fail
 (thm (implies (and (real/rationalp a)
                    (real/rationalp b)
                    (real/rationalp c)
                    (< 0 a)
                    (< 0 b)
                    (< 0 c)
                    (<= (expt a 2) (* b (+ c 1)))
                    (<= b (* 4 c)))
               (< (expt (- a 1) 2) (* b c))))
 )
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
;09/05/13 ACL2 v6.2 - its goes through now

; testcase 4.1 (from Pete)

(acl2s-defaults :set search-strategy :simple)
(acl2s-defaults :set num-trials 100000)
(acl2s-defaults :set :sampling-method :uniform-random)
(test?
 (IMPLIES (AND (RATIONALP x)
               (RATIONALP y)
               (RATIONALP z)
               (< x 20)
               (< y (+ 25 x))
               (< z (+ x y)))
          (< z 62)))

(set-gag-mode nil)
(must-fail
 (test?
  (IMPLIES (AND (RATIONALP x)
                (RATIONALP y)
                (RATIONALP z)
                (< x 20) 
                (> x 17) ;added 
                (positive-rationalp n1) 
                (equal y (- (+ 25 x) n1))
                (positive-rationalp n2)
                (equal z (- (+ x y) n2)))
           (< z 62)))
;:hints (("Goal" :cases ((> x 18)))))
 )

(acl2s-defaults :set num-trials 1000)

;from BM88 paper
(must-fail
 (test?
  (implies (and (positive-rationalp k)
                (positive-rationalp l)
                (<= (+ (* 2 k) 1) (* 2 l)))
           (<= (+ (* 2 k) 2) (* 2 l)))) 
 )

(acl2s-defaults :set search-strategy :simple)
;; testcase 5 (only finds cts if arithmetic-5 library is loaded)
(must-fail
 (test?
  (implies (and (posp x)
                (posp y)
                (posp z)
                (> z 16)
                (<= (+ x y) (* 2 z)))
           (or (> (* x y z) (* x y x))
               (> (* x y z) (* x y y)))))
 )

; Aug 27th '12
; Note: BE does exceptionally well in the above example. The reason is
; to do with the faulty DEFDATA::|next BE args| function. In the above
; example this is how BE enumerates X Y Z:
; 0 0 0 -> 1 0 0 -> 1 1 0 -> 1 1 1 -> 2 1 1 -> 2 2 1 -> and so on
; clearly such an enumeration will find cts easily for the above conjecture.


;;testcase 6
(must-fail
 (test?
  (implies (and (posp x)
                (posp y)
                (posp z)
;Idea of introducing variables to help SELECT
;(equal w (* z z))
                (<= (+ x y) (* 2 z)))
           (> (* z z) (* x y))))
 )

;; testcase 7 (from Harrison's book)
(defdata formula (oneof pos
                        (list 'not formula)
                        (list 'and formula formula)
                        (list 'or formula formula)
                        (list 'implies formula formula)))



;ISSUE: made defdata idempotent (redundant events)
(defun simplify-formula (f)
  ;:input-contract (formulap f)
  ;:output-contract (formulap (simplify-formula f))
  (cond ((posp f) f)
        ((eq (first f) 'not) (list 'not (simplify-formula (second f))))
        ((eq (first f) 'and) (list 'and (simplify-formula (second f)) (simplify-formula (third f))))
        ((eq (first f) 'or) (list 'or (simplify-formula (second f)) (simplify-formula (third f))))
        ((eq (first f) 'implies) (list 'or (list 'not (simplify-formula (second f))) (simplify-formula (third f))))
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
  
(defthm simplify-formula-is-stable
  (equal (simplify-formula (simplify-formula f))
         (simplify-formula f)))

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

;(acl2s-defaults :set sampling-method :uniform-random)

(must-fail
 (test? ;simp-nnf-commute
  (implies (formulap f)
           (equal (nnf (simplify-formula f))
                  (simplify-formula (nnf f)))))
 )

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
 
(must-fail 
 (test?
  (implies (natp i)
           (and (<= (square (square-root i)) i)
                (< i (square (1+ (square-root i)))))))
 )

;; testcase 9 (a thm in 2, but cts in 3 variables)
(defdata small-pos (enum '(1 2 3 4 5 6 7 8 9)))

(acl2s-defaults :set testing-enabled T)
;(acl2s-defaults :set num-trials 2500)
(acl2s-defaults :set search-strategy :incremental)
(acl2s-defaults :set num-witnesses 0) ;recommended for incremental
(must-fail
 (test? (implies (and (integerp x1)
                      (integerp x2)
                      (integerp x3)
                      (integerp x4)
                      (integerp x5)
                      (integerp x6)
                      (< x1 (* 2 x2))
                      (< x2 (* 2 x3))
                      (< x3 (* 2 x4))
                      (< x4 (* 2 x5))
                      )
                 (< x6 x5)))
 )
;No luck without arithmetic-5.
;Lets add arith-5 lib and see now. Still no luck
; 19th March - I saw some counterexamples with (ld acl2s-mode.lsp)
; 20th March 2013 - arithmetic/top-with-meta no luck.
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
; This is due to the way easy-simplify works and propagate
; blindly throws away a simplification that is not smaller
; in term-order than the original hyp.
; 27th Aug '12, to get rid of the above error, one needs to
; submit a compound recognizer rule.
; Additionally I also make sure that I dont break the invariant
; that after propagating a X=const assignment, X will not appear
; as a free variable in the resulting simplified hyp

(defthm small-posp-is-a-posp
  (implies (small-posp x)
           (and (integerp x)
                (< 0 x)))
  :rule-classes :compound-recognizer)

;Sep 5 2013 - strange timeout + cts, but no summary. (incremental)
(acl2s-defaults :set search-strategy :simple)
(must-fail
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
 )

(acl2s-defaults :set num-witnesses 3)
;; testcase 10
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

(acl2s-defaults :set testing-enabled T) ;if simple, then only T works

(must-fail
 (test? (implies (and (integerp x)
                      (integerp y)
                      (integerp z))
                 (/= (g x y z) 'error)))
 )

(acl2s-defaults :set testing-enabled :naive) ;for incremental, naive works too
; Actually :simple works too with naive.
(must-fail
 (test? (implies (and (integerp x)
                      (integerp y)
                      (integerp z)
                      (equal x (hash y))
                      (equal y (hash z)))
                 NIL))

 )

;; testcase 11 (Euler Counterexample)
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
(must-fail
 (test?
  (implies (posp k)
           (not (factor? (fermat-factor k 5) (f 5)))))
 )
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


;Note: incremental does a really bad job with this test?
(acl2s-defaults :set search-strategy :simple)

;BOZO 20th March 2013 - arithmetic-5 caused the following to hang.
(must-fail
 (test?
  (implies (and (posp k)
                (posp n)
                (< n 15))
           (not (factor? (fermat-factor k n) (f n)))))
 )

;09/28/12
;wow i found for the above a brand new counterexample:
;; We tested 71059 examples across 1 subgoals, of which 37635 (37635 unique)
;; satisfied the hypotheses, and found 3 counterexamples and 37632 witnesses.
;; The total time taken (incl. prover time) is 0.57 seconds
;; The time taken by testing is 0.57 seconds

;; We falsified the conjecture. Here are counterexamples:
;;  [found in : "top"]
;;  -- (K 238) and (N 11)
;;  -- (K 14) and (N 12)
;;  -- (K 10) and (N 5)

;; 20th March 2013 - The above example does much better with
;; arithmetic-5 loaded and that too in the acl2s-mode env.

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


; pipeline test case example
;---------------pete's email before demo Summer 2013 pipeline example-------------
(defdata reg nat)
(defdata program-counter nat)
(defdata register (map reg integer))

(defdata dmemory (map nat integer))
                      
(defdata operation-code (enum '(add sub mul load loadi store bez jump)))

(defdata inst (record (opcode . operation-code)
                      (rc . reg)
                      (ra . reg)
                      (rb . reg)))

(defdata imemory (map nat inst))

(defdata ISA (record (pc . program-counter)
                     (regs . register)
                     (imem . imemory)
                     (dmem . dmemory)))

(defdata latch1 (record (validp . boolean)
                        (op . operation-code)
                        (rc . reg)
                        (ra . reg)
                        (rb . reg)
                        (pch . program-counter)))

(defdata latch2 (record (validp . boolean)
                        (op . operation-code)
                        (rc . reg)
                        (ra-val . integer)
                        (rb-val . integer)
                        (pch . program-counter)))

(defdata MAA (record  (pc . program-counter)
                     (regs . register)
                     (imem . imemory)
                     (dmem . dmemory)
                     (ltch1 . latch1)
                     (ltch2 . latch2)))

(acl2s-defaults :set testing-enabled t)
(acl2s-defaults :set num-trials 1000)
(acl2s-defaults :set num-witnesses 0)
(acl2s-defaults :set num-counterexamples 10)
(acl2s-defaults :set cgen-timeout 101)
;Here is one of the 3000 subgoals which failed:


;Sep 5 2013 - incremental took long time, but no results
; Sep 20 2015 - simple does not work anymore
(acl2s-defaults :set search-strategy :incremental)  
(acl2s-defaults :set sampling-method :uniform-random)


#|
;Cgen refuted version of this without hyps (NICE)
; INteresting: DIff induction scheme gives more cex. 
; i.e inducting on acl2::mset-wf gave (V 3), (X ((8 . -1/4))) and (A 8)
; so now i need to change hyp mget a x to (integerp (mget a x))
(defthm stronger-registerp-modifier-lemma
  (implies (and (integerp (mget-wf a x))
                ;(wf-keyp a)
                v 
                )
           (equal (REGISTERP (MSET-WF A V X))
                  (AND (REGISTERP X) (REGP A) (INTEGERP V))))
  :hints (("Goal" :induct (acl2::mset-wf a v x)
                  :in-theory (e/d (registerp acl2::good-map)
                                  (map-elim-rule regp integerp acl2::wf-keyp)))))


|#

(in-theory (disable operation-codep ACL2::NON-NIL-IF-MGET-NON-NIL))
(acl2s-defaults :set verbosity-level 3)
;(acl2s-defaults :set search-strategy :incremental)

(must-fail
 (test?
  (implies (and (maap w)
                (equal (mget :pc w)
                       (+ 1 (mget :pch (mget :ltch2 w))))
                
;(mget (mget :pch (mget :ltch2 w)) (mget :imem w)) ;added later
                
                (equal t (mget :validp (mget :ltch2 w)))
                
                (equal (mget (mget :rb (mget (mget :pch (mget :ltch2 w)) (mget :imem w)))
                             (mget :regs w))
                       (mget :rb-val (mget :ltch2 w)))
                
                (equal (mget :opcode (mget (mget :pch (mget :ltch2 w)) (mget :imem w)))
                       'bez)
                
                (equal 0
                       (mget (mget :ra (mget (mget :pch (mget :ltch2 w)) (mget :imem w)))
                             (mget :regs w)))
                (equal 0 (mget :ra-val (mget :ltch2 w))))
           (not (equal (mget :op (mget :ltch2 w)) 'bez))))
 )


; for all the following simple works fine so lets try incremental too
(acl2s-defaults :set search-strategy :incremental)
;(acl2s-defaults :set search-strategy :simple)
;GOOD EXAMPLE 
(defun perm (x y)
  (if (endp x)
    (endp y)
    (and (member-equal (car x) y)
         (perm (cdr x) (remove1-equal (car x) y)))))

(acl2s-defaults :set testing-enabled t)

(must-fail
 (test? ;remove-once-perm
  (implies (and (consp X)
                (member-equal a Y))
           (equal (perm (remove-equal a X)
                        (remove-equal a Y))
                  (perm X Y))))
 )

(let ((X '("a" "b" "c")) 
      (Y '("b" "a" "d" "c"))
      (a "d"))
  (implies (and (string-listp X)
                (string-listp Y)
                (consp X)
                (member-equal a Y)
                (perm (remove1-equal a X) (remove1-equal a Y)))
           (perm X Y)))

(must-fail
 (test?; lucky cex: -- ((A "A") (X (LIST "BA")) (Y (LIST "A" "BA")))
  (implies (and (pos-listp X)
                (pos-listp Y)
                (consp X) ;TODO why is CONS /\ LIST[:a] not working!
                (member-equal a Y)
                (perm (remove1-equal a X) (remove1-equal a Y)))
           (perm X Y)))
 )#|ACL2s-ToDo-Line|#



(must-fail
 (thm (implies (and (booleanp p)
                    (booleanp q))
               (not (equal (implies p q)
                           (implies q p)))))
 )

#|
; test case for timeouts and interrupt behavior
(set-guard-checking :all)

(acl2s-defaults :set testing-enabled t)
(acl2s-defaults :set verbosity-level 4)
(defunc ^ (k n)
  ; k^n
  :input-contract (and (natp k) (natp n))
  :output-contract (natp (^ k n))
  (if (equal n 0) ;(zp n)
    1
    (* k (^ k (- n 1)))))


(defunc ! (n)
  :input-contract (natp n)
  :output-contract (posp (! n))
  (if (equal n 0) ;(zp n)
    1
    (* n (! (- n 1)))))

;(acl2s-defaults :set testing-enabled :naive)

;(acl2s-defaults :set cgen-timeout 1)
(acl2s-defaults :set verbosity-level 3)

(test?
 (implies (and (natp n)
               (< 500 n))
          (< (^ 2 n) (! n))))
|#

; pretty amazing
(defun make-inverse-map (A i)
  (if (endp A)
      '()
    (cons (cons (car A) i)
          (make-inverse-map (cdr A) (1+ i)))))

(acl2s-defaults :set sampling-method :uniform-random)
;(acl2s-defaults :set search-strategy :simple)

;(include-book "data-structures/list-defthms" :dir :system)
;(include-book "std/lists/top" :dir :system)
(include-book "std/alists/top" :dir :system)

(acl2::must-fail
 (test?; make-inverse-map-with-update-nth
  (implies (and (pos-listp A)
                (no-duplicatesp A)
                (natp k)
                (natp i)
                (posp e)
                (member e A)
                (< i (len A)))
           (equal (make-inverse-map (update-nth i e A) k)
                  (put-assoc-equal e (+ k i) (make-inverse-map A k)))))
 )

(acl2::must-fail
 (test?; make-inverse-map-with-update-nth
  (implies (and (pos-listp A)
                (no-duplicatesp A)
                (natp k)
                (natp i)
                (posp e)
                (member e A)
                (< i (len A)))
           (equal (make-inverse-map (update-nth i e A) k)
                  (put-assoc e (+ k i) (delete-assoc (nth i A) (make-inverse-map A k))))))
)

(acl2::must-fail
(test?; make-inverse-map-with-update-nth
  (implies (and (pos-listp A)
                (no-duplicatesp A)
                (natp k)
                (natp i)
                (natp j)
                (not (= i j))
                (posp e)
                (member e A)
                (< i (len A)))
           (acl2::alist-equiv (make-inverse-map (update-nth i (nth j A) A) k)
                        (put-assoc (nth j A) (+ k i) 
                                   (delete-assoc (nth i A) (make-inverse-map A k))))))
)


;; CHeck singleton range types are working correctly.

(DEFDATA DECIMAL_30_TO_30 (RANGE RATIONAL (30 <= _ <= 30)))
(test? (implies (DECIMAL_30_TO_30P x) (= x 30)))


;; Check len support in Cgen.
(defdata d1 (oneof 'a 'b 'c 'd 'e 'f))

(defdata ld1-aux
  (listof d1)
  :min-rec-depth 2
  :max-rec-depth 201)

(acl2s::defunc ld1p (x)
  :input-contract t
  :output-contract (booleanp (ld1p x))
 (and (ld1-auxp x)
      (>= (len x) 3)
      (<= (len x) 200)))

;; (defdata ld1 (listof d1))

(defdata d2 'g)

(defdata ld2-aux
  (listof d2)
  :min-rec-depth 0
  :max-rec-depth 7)

(acl2s::defunc ld2p (x)
  :input-contract t
  :output-contract (booleanp (ld2p x))
  (and (ld2-auxp x)
       (<= (len x) 6)))

;Now, cgen fails to find a counterexample for this.
(acl2s-defaults :set verbosity-level 3)

(test?
 (implies (and (ld2p a)
               (ld1p b)
               (ld1p c)
               (integerp x)
               (<= x (len a))
               (> x 0)
               (equal (len a) (len b)))
               
          (and (consp c)
               (<= x (len c)))))
