(in-package "ACL2")

#|

 tiny-fib-correct.lisp
 ~~~~~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Incorporating modifications by: Daron Vroon
Incorporating bug-fix and modifications by: Lee Pike
Added Sun Oct 16 23:36:17 2005: Incorporating a bug fix by Lee Pike.


In this book, we use the defsimulate macro to show that the fibonacci program
on the tiny machine is correct. I show both partial and total correctness. I do
nothing with the definitions either of the model or of the program, but I do
change the way cutpoints, assertions, and pre and post conditions are
represented.

|#

(include-book "../tiny-fib/tiny-rewrites")
(include-book "../tiny-fib/fib-def")
(include-book "ordinals/ordinals" :dir :system)

;; I dont care about guards at the moment. So do not verify guards.

(set-verify-guards-eagerness 0)

(defconst *word-size* 32)
(defconst *max-prog-address*
  (1- (+ *prog-start-address*
         (len *fib-prog*))))



;; First the fibonacci specification.

(defun fib-spec (n)
  (cond ((zp n) 1)
        ((equal n 1) 1)
        (t (plus<32> (fib-spec (- n 1))
                     (fib-spec (- n 2))))))


;; Maybe I should relax the restriction here. But my initial macro requires
;; that each of cutpoint, assertion, precondition, postcondition, etc. must
;; have the same arity. I dont know a way to relax this restriction because
;; otherwise my macro needs to look at the state and then it would not remain
;; an embedded-event form. Otherwise I can ask the user to provide the arity of
;; each function which is no clumsier than this requirement.

(defun tiny-fib-cutpoint (n tiny-state)
  (declare (xargs :stobjs tiny-state) (ignore n))
  (member (progc tiny-state) *fib-cutpoints*))


;; Here are the assertions.

(defun tiny-fib-assertion (n tiny-state)
  (declare (xargs :stobjs tiny-state))
   (and (program-loaded tiny-state *fib-prog* *prog-start-address*)
        (tiny-statep tiny-state)
        ;; I dont know if the predicate (signed-byte-p *word-size* n) below is
        ;; vital. The proofs dont go thru for the loop label otherwise (I
        ;; think). But I have little understanding of the machine so feel free
        ;; to change this.
        (signed-byte-p *word-size* n)
        (<= 0 n)
        (equal (dtos tiny-state) *init-dtos*)
        (cond ((equal (progc tiny-state) *prog-start-address*)
               (and (<= 0 (dtos-val tiny-state 0))
                    (equal n (dtos-val tiny-state 0))))
              ((equal (progc tiny-state) *loop-label*)
               (and (<= 0 (dtos-val tiny-state 0))
                    (if (< 0 n)
                        (< (dtos-val tiny-state 0) n)
                       (<= (dtos-val tiny-state 0) n))
                    (equal (memi *fib-1-adr* tiny-state)
                           (fib-spec (1- (- n (dtos-val tiny-state 0)))))
                    (equal (memi *fib-adr* tiny-state)
                      (fib-spec (- n (dtos-val tiny-state 0))))))
              ((equal (progc tiny-state) *done-label*)
               (and (= 0 (dtos-val tiny-state 0))
                    (equal (memi *fib-adr* tiny-state) (fib-spec n))))
              ((equal (progc tiny-state) *prog-halt-address*)
               (equal (dtos-val tiny-state 0) (fib-spec n)))
              (t t))))

;; I probably need to fix this. I had specified in the defsimulate macro that
;; the default-state is a nullary function. Unfortunately the function used for
;; TINY fibonacci example is a unary function that takes the stobj. Of course
;; it is logically equivalent to a nullary function. But I might consider the
;; possibility of having the default state take parameters in the defsimulate
;; macro. In lieu of that the only option I have is to make dummy-tiny-state be
;; :non-executable.

(defun-nx dummy-tiny-state ()
  (create-tiny-state))

;; Now correspondingly define the exitpoints, precondition and
;; postcondition.

(defun tiny-fib-exitpoint (n tiny-state)
  (declare (xargs :stobjs tiny-state) (ignore n))
  (equal (progc tiny-state) *prog-halt-address*))


(defun tiny-fib-precondition (n tiny-state)
  (declare (xargs :stobjs tiny-state))
  (and (program-loaded tiny-state *fib-prog* *prog-start-address*)
        (tiny-statep tiny-state)
        (equal (dtos tiny-state) *init-dtos*)
        (equal (progc tiny-state) *prog-start-address*)
        (<= 0 (dtos-val tiny-state 0))
        (equal n (dtos-val tiny-state 0))))

(defun tiny-fib-postcondition (n tiny-state)
  (declare (xargs :stobjs tiny-state))
  (equal (dtos-val tiny-state 0) (fib-spec n)))

;; Ok, now some theorems. I need to prove that fib-spec is always signed-byte-p
;; 32 and the reason is that after *done-label* there is a (plus<32> x 0)
;; around for whatever x is in address 20. But this is identity only if
;; fib-spec itself is a signed-byte-p 32.

(local
 (defthm plus<32>-is-signed-byte
   (implies (and (signed-byte-p *word-size* x)
                 (signed-byte-p *word-size* y))
            (signed-byte-p *word-size* (plus<32> x y)))
   :hints (("Goal"
            :in-theory (enable plus<32>)))))

(local
 (defthm fib-is-signed-byte-p
   (signed-byte-p *word-size* (fib-spec n))))

;; The theorem below says that if you add 0 to it, you are fine. This takes us
;; from *done-label* to the postcondition.

(local
 (defthm signed-byte-p-plus
   (implies (signed-byte-p 32 x)
            (equal (plus<32> x 0) x))))



(defun tiny-fib-measure (n tiny-state)
   (declare (xargs :stobjs tiny-state))
  (if (tiny-fib-exitpoint n tiny-state)
      0
    (o+ (o* (omega) (nfix (dtos-val tiny-state 0)))
        (nfix (- *max-prog-address* (progc tiny-state))))))


;; The following lemma is used to help in termination. Maybe this should go in
;; the ordinal arithmetic books somewhere?

(local
  (defthm l1
    (implies (and (natp a)
                  (natp b)
                  (natp c)
                  (natp d)
                  (< a b))
             (o< (o+ (o* (omega) a) c)
                 (o+ (o* (omega) b) d)))
    :hints (("goal" :cases ((equal a 0))))))


;; Finally we are done, so just throw in defsimulate, define the function run,
;; and get done.

(include-book "defsimulate")

(defun tiny-fib-run (tiny-state n)
  (declare (xargs :stobjs tiny-state))
  (if (zp n) tiny-state
    (let* ((tiny-state (next tiny-state)))
      (tiny-fib-run tiny-state (1- n)))))

;; OK, let's see how my macro performs.......:->:->

(defsimulate next
  :pre tiny-fib-precondition
  :post tiny-fib-postcondition
  :cutpoint tiny-fib-cutpoint
  :assertion tiny-fib-assertion
  :arity 2
  :run tiny-fib-run
  :exitpoint tiny-fib-exitpoint
  :exitsteps tiny-fib-partial-exitsteps
  :default dummy-tiny-state)

(defsimulate next
  :mode :total
  :pre tiny-fib-precondition
  :post tiny-fib-postcondition
  :cutpoint tiny-fib-cutpoint
  :assertion tiny-fib-assertion
  :arity 2
  :measure tiny-fib-measure
  :run tiny-fib-run
  :exitpoint tiny-fib-exitpoint
  :exitsteps tiny-fib-total-exitsteps
  :default dummy-tiny-state)


