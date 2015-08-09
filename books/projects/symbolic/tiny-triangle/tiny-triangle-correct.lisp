(in-package "ACL2")

#|

Author: Lee Pike
Based On Sandip's tiny-fib-correct.lisp file.

|#

(include-book "../tiny-fib/tiny-rewrites")
(include-book "ordinals/ordinals" :dir :system)
(include-book "triangle-def")

;; Dont worry about guards for this one.

(set-verify-guards-eagerness 0)

(defconst *word-size* 32)
(defconst *max-prog-address*
  (1- (+ *prog-start-address*
         (len *tri-prog*))))

;; The triangle program in indexed form.

(DEFUN |idx| (n)
  (IF (NOT (NATP n)) 0
     (COND ((< n 1) 1)
	    ;; signed-arith
            (T (plus<32> (|idx| (- n 1)) 1)))))

(DEFUN tri (n)
  (IF (NOT (NATP n)) 0
      (COND ((< n 1) 0)
	    ;; signed-arith
            (T (plus<32> (tri (- n 1)) (|idx| (- n 1)))))))


;; Maybe I should relax the restriction here. But my initial macro requires
;; that each of cutpoint, assertion, precondition, postcondition, etc. must
;; have the same arity. I dont know a way to relax this restriction because
;; otherwise my macro needs to look at the state and then it would not remain
;; an embedded-event form. Otherwise I can ask the user to provide the arity of
;; each function which is no clumsier than this requirement.

(defun tiny-tri-cutpoint (n tiny-state)
  (declare (xargs :stobjs tiny-state) (ignore n))
  (member (progc tiny-state) *tri-cutpoints*))


;; Here are the assertions.

(defun tiny-tri-assertion (n tiny-state)
  (declare (xargs :stobjs tiny-state))
   (and (program-loaded tiny-state *tri-prog* *prog-start-address*)
        (tiny-statep tiny-state)
        (signed-byte-p *word-size* n)
        (<= 0 n)
        (equal (dtos tiny-state) *init-dtos*)
        (cond ((equal (progc tiny-state) *prog-start-address*)
               (and (<= 0 (dtos-val tiny-state 0))
                    (equal n (dtos-val tiny-state 0))))
              ((equal (progc tiny-state) *loop-label*)
               (and (<= 0 (dtos-val tiny-state 0))
                    (<= (dtos-val tiny-state 0) n)
                    (equal (memi *idx-adr* tiny-state)
                           (|idx| (- n (dtos-val tiny-state 0))))
                    (equal (memi *tri-adr* tiny-state)
			   (tri (- n (dtos-val tiny-state 0))))))
              ((equal (progc tiny-state) *done-label*)
               (and (= 0 (dtos-val tiny-state 0))
                    (equal (memi *tri-adr* tiny-state) (tri n))))
              ((equal (progc tiny-state) *prog-halt-address*)
               (equal (dtos-val tiny-state 0) (tri n)))
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
;; postcondition. John and Daron, fell free to modify these.

(defun tiny-tri-exitpoint (n tiny-state)
  (declare (xargs :stobjs tiny-state) (ignore n))
  (equal (progc tiny-state) *prog-halt-address*))


(defun tiny-tri-precondition (n tiny-state)
  (declare (xargs :stobjs tiny-state))
  (and (program-loaded tiny-state *tri-prog* *prog-start-address*)
        (tiny-statep tiny-state)
        (equal (dtos tiny-state) *init-dtos*)
        (equal (progc tiny-state) *prog-start-address*)
	(<= 0 (dtos-val tiny-state 0))
        (equal n (dtos-val tiny-state 0))))

(defun tiny-tri-postcondition (n tiny-state)
  (declare (xargs :stobjs tiny-state))
  (equal (dtos-val tiny-state 0) (tri n)))

;; Ok, now some theorems. I need to prove that tri is always signed-byte-p
;; 32 and the reason is that after *done-label* there is a (plus<32> x 0)
;; around for whatever x is in address 20. But this is identity only if
;; tri itself is a signed-byte-p 32.

(local
 (defthm plus<32>-is-signed-byte
   (implies (and (signed-byte-p *word-size* x)
                 (signed-byte-p *word-size* y))
            (signed-byte-p *word-size* (plus<32> x y)))
   :hints (("Goal"
            :in-theory (enable plus<32>)))))

;; NEW
(local
 (defthm idx-is-signed-byte-p
   (signed-byte-p *word-size* (|idx| n))))

(local
 (defthm tri-is-signed-byte-p
   (signed-byte-p *word-size* (tri n))))

;; The theorem below says that if you add 0 to it, you are fine. This takes us
;; from *done-label* to the postcondition.

(local
 (defthm signed-byte-p-plus
   (implies (signed-byte-p 32 x)
            (equal (plus<32> x 0) x))))

(defun tiny-tri-measure (n tiny-state)
   (declare (xargs :stobjs tiny-state))
  (if (tiny-tri-exitpoint n tiny-state)
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

(include-book "../generic/defsimulate")

(defun tiny-tri-run (tiny-state n)
  (declare (xargs :stobjs tiny-state))
  (if (zp n) tiny-state
    (let* ((tiny-state (next tiny-state)))
      (tiny-tri-run tiny-state (1- n)))))

;; OK, let's see how my macro performs.......:->:->

(defsimulate next
  :pre tiny-tri-precondition
  :post tiny-tri-postcondition
  :cutpoint tiny-tri-cutpoint
  :assertion tiny-tri-assertion
  :arity 2
  :run tiny-tri-run
  :exitpoint tiny-tri-exitpoint
  :exitsteps tiny-tri-partial-exitsteps
  :default dummy-tiny-state)


(defsimulate next
  :mode :total
  :pre tiny-tri-precondition
  :post tiny-tri-postcondition
  :cutpoint tiny-tri-cutpoint
  :assertion tiny-tri-assertion
  :arity 2
  :measure tiny-tri-measure
  :run tiny-tri-run
  :exitpoint tiny-tri-exitpoint
  :exitsteps tiny-tri-total-exitsteps
  :default dummy-tiny-state)


