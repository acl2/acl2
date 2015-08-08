(in-package "M5")

#|

 factorial-jvm-correct.lisp
 ~~~~~~~~~~~~~~~~~~~~~~~~~~

Author: Sandip Ray
Date: Mon Jan 10 04:46:19 2005

In this book I show the use of defsimulate to prove the correctness of a
recursive factorial program written in JVM. The JVM model is M5, which has been
developed by Robert Krug, Hanbing Liu, and J Moore at UT Austin. They have
proved various theorems about this model, but mostly using the so-called "clock
functions". J has actually also proved partial correctness theorems using the
method referred to in "Inductive Assertions and Operational Semantics".

|#

;; The book is included to get the class file in.
(include-book "../m5/demo")
(include-book "ordinals/ordinals" :dir :system)

;; Here is the definition of mathematical factorial function, referred to as
;; mfact in the paper.
(defun fact (n)
  (if (zp n) 1
    (* n (fact (1- n)))))

;; I need to specify some stuff first before we can get into the situation when
;; we can talk about precondition, postcondition, etc. The first thing is
;; really technical, and might even be considered stupidity on my part. I allow
;; step to take only one argument, namely the current state, in the macro
;; implementation. But M5 programs take two arguments, namely the state and the
;; thread to step. This is because M5 is really a multithraded and
;; non-deterministic model, while our technique affords verification of
;; sequential [deterministic] programs. To reconcile this, I will specify a
;; particular thread for this entire exercise.

(defstub th () => *)
(defun mono-step (s) (step (th) s))
(defun mono-run (s n) (if (zp n) s (mono-run (mono-step s) (1- n))))

;; OK so we are done with this little set of technicalities. Now I want to
;; specify the precondition, postcondition, cutpoints, etc. So what are these
;; predicates? I want to specify the precondition, postcondition, cutpoints,
;; and assertions. These are adapted from Moore's work with his "Inductive
;; Assertions and Operational Semantics" book, but modified to be applied to
;; the current method, and in addition, total correctness is proved.

;; The function sdepth here is used to specify the size of the recursion stack
;; which can then be used to indicate whether we are done with the run. In
;; other words I will start the recursive call specifying that the depth of the
;; stack initially is some depth d0 and at postcondition the depth must be <
;; d0.
(defun sdepth (stk)
  (declare (xargs :hints (("Goal" :in-theory (enable pop)))))
  (if (endp stk)
      0
    (+ 1 (sdepth (pop stk)))))

;; At depth k of recursion I must know that all the previous recursive calls
;; have been invoked correctly. This is specified by the fact-caller-framesp
;; function below. This specifies that the last k recursive calls are calls to
;; fact. So here it goes. This is simply picked from the corresponding
;; assertion in Moore's method relating inductive assertions and operational
;; semantics.
(defun fact-caller-framesp (cs n0 k)
  (declare (xargs :measure (acl2-count k)))
  (cond ((zp k) t)
        ((and (equal (pc (top cs)) 11)
              (equal (program (top cs)) (cdddr *fact-def*))
              (equal (sync-flg (top cs)) 'UNLOCKED)
              (intp (nth 0 (locals (top cs))))
              (equal (+ n0 (- k)) (- (nth 0 (locals (top cs))) 1))
              (equal (nth 0 (locals (top cs)))
                     (top (stack (top cs)))))
         (fact-caller-framesp (pop cs) n0 (- k 1)))
        (t nil)))

;; The assertion for this program is specified pretty naturally. These are
;; adapted from J's book.

(defun fact-assertion (n0 d0 s)
  (and (integerp d0)
       (< 1 d0)
       (equal (status (th) s) 'scheduled)
       (cond
        ((< (sdepth (call-stack (th) s)) d0)
         (equal (top (stack (top-frame (th) s)))
                (int-fix (fact n0))))
        (t
         (let ((n (nth 0 (locals (top-frame (th) s)))))
           (and (equal (program (top-frame (th) s)) (cdddr *fact-def*))
                (equal (lookup-method "fact" "Demo" (class-table s))
                       *fact-def*)
                (equal (sync-flg (top-frame (th) s)) 'UNLOCKED)
                (intp n0)
                (intp n)
                (<= 0 n)
                (<= n n0)
                (equal (sdepth (call-stack (th) s)) (+ d0 (- n0 n)))
                (fact-caller-framesp (pop (call-stack (th) s)) n0 (- n0 n))
                (case (pc (top-frame (th) s))
                  (0 t)
                  ((12 14)
                   (equal (top (stack (top-frame (th) s)))
                          (int-fix (fact n))))
                  (t nil))))))))

;; OK so what are the cutpoints? If I am done that is if I am at a recursive
;; call of depth < d0 of course then I am in a cutpoint. Otherwise I the
;; cutpoint is is I am just invoking a call [pc=0], or returning from a call
;; [pc=12,14]. Note that while this is probably not very important, we can
;; split the assertion for pc=12 and pc=14 if necessary by specifying that at
;; pc=14 we are returning from a call of fact(0), and at pc=12, we are
;; returning from fact(n) with n > 0.

;; Note: You might be surprised to see the (sdepth (call-stack (th) s)) > 0
;; condition in the cutpoint statement. You might wonder: What is this doing
;; here? This is actually around for technical reason. The technical reason is
;; that I want dummy not to be a cutpoint, but here I have defined dummy to be
;; nil.

(defun fact-cutpoint (n0 d0 s)
  (declare (ignore n0))
  (and (> (sdepth (call-stack (th) s)) 0)
       (or (< (sdepth (call-stack (th) s)) d0)
           (equal (pc (top-frame (th) s)) 0)
           (equal (pc (top-frame (th) s)) 12)
           (equal (pc (top-frame (th) s)) 14))))

;; Here is the exitpoint. What I want here is that the depth of the call stack
;; is smaller than d0. This basically will say that I have returned from the
;; call that I started with.

(defun fact-exitpoint (n0 d0 s)
  (declare (ignore n0))
  (and (< (sdepth (call-stack (th) s)) d0)
       (> (sdepth (call-stack (th) s)) 0)))



;; The precondition must just say that I am in a state with d0 being equal to
;; the stack height, and I am poised to execute the factorial of n0. The latter
;; is specified by saying that the locals at the top frame of thread (th) is
;; n0.

(defun fact-precondition (n0 d0 s)
   (and (intp n0)
        (<= 0 n0)
        (integerp d0)
        (< 1 d0)
        (equal (pc (top-frame (th) s)) 0)
        (equal (locals (top-frame (th) s)) (list n0))
        (equal (program (top-frame (th) s))
               (cdddr *fact-def*))
        (equal (status (th) s) 'scheduled)
        (equal (sync-flg (top-frame (th) s)) 'unlocked)
        (equal (lookup-method "fact" "Demo" (class-table s))
               *fact-def*)
        (equal (sdepth (call-stack (th) s)) d0)))

;; And of course the postcondition is merely stating that the thing that is
;; standing at the top of the stack is the factorial.

(defun fact-postcondition (n0 d0 s)
  (declare (ignore d0))
   (equal (top (stack (top-frame (th) s)))
          (int-fix (fact n0))))

;; What is the default state? Well, just nil!!!

(defun dummy-state () nil)

;; And that is it!!! I of course need to do very little to invoke the method,
;; and that is the beauty of the method itself. BTW I have added the disabling
;; of the lookup method itself merely for efficiency, since otherwise there is
;; a case split on whether we have it in the current class or should look up in
;; the superclasses.

(in-theory (disable lookup-method))

;; OK let's see how my macro performs here.....:->

(include-book "defsimulate")

;; You see why I added the thms and hints. If I simply
;; open up step to get what I want, but that is sometimes inefficient and
;; causes a huge case split. Especially in the context of a model like JVM you
;; dont want to do that. You need specialized openers which are actually pretty
;; mechanical. And here I show one. This opener is just specifying to open up
;; the function when the pc is known. Notice that I can also provide the right
;; hints to the macro. Isn't this cool? Of course this is just to show that
;; these facilities exist with the macro in case somebody wants to use
;; them. For this particular program it is possible to avoid both with the
;; right syntaxp hypothesis. But this need not be possible in general, and I
;; like to provide such control in software I write.

(acl2::defsimulate mono-step
  :default dummy-state
  :cutpoint fact-cutpoint
  :pre fact-precondition
  :post fact-postcondition
  :assertion fact-assertion
  :arity 3
  :exitpoint fact-exitpoint
  :exitsteps fact-exitsteps
  :run mono-run
  :thms
  ((local
    (defthm cutpoint-opener
      (implies (and (equal pc (pc (top-frame (th) s)))
                    (syntaxp (quotep pc)))
               (equal (acl2::concrete-nextt-cutpoint n0 d0 s)
                      (if (fact-cutpoint n0 d0 s) s
                        (acl2::concrete-nextt-cutpoint
                         n0 d0
                         (mono-step s))))))))
   :hints (("Goal"
              :cases ((equal (pc (top-frame (th) acl2::s2)) 0)
                      (equal (pc (top-frame (th) acl2::s2)) 12)
                      (equal (pc (top-frame (th) acl2::s2)) 14)))
             ("Subgoal 2"
              :in-theory (disable fact-caller-framesp)
              :use ((:instance (:definition fact-caller-framesp)
                               (cs (pop
                                    (CADR (ASSOC-EQUAL (TH)
                                                       (THREAD-TABLE acl2::S2)))))
                               (n0 acl2::s0)
                               (k (- acl2::s0 (car (locals (top-frame (th) acl2::s2))))))))
             ("Subgoal 1"
              :in-theory (disable fact-caller-framesp)
              :use ((:instance (:definition fact-caller-framesp)
                               (cs (pop
                                    (CADR (ASSOC-EQUAL (TH)
                                                       (THREAD-TABLE acl2::S2)))))
                               (n0 acl2::s0)
                               (k (- acl2::s0 (car (locals (top-frame (th) acl2::s2))))))))))


;; Finally for total correctness here is the rank function. The function is
;; handles recursion. It is meant so that
;; the call to ther recursion is given a slightly larger ordinal than the
;; return. It should be thought more as a pair giving more priority to the calls than
;; returns. This is also illustrative of the kind of ranking functions one needs
;; to write for recursive methods.

(defun factorial-rank (n0 d0 s)
  (if (fact-exitpoint n0 d0 s)
      0
    (acl2::o+ (acl2::o* (acl2::omega)
                        (if (and (equal (pc (top-frame (th) s)) 0)
                                 (>= (sdepth (call-stack (th) s)) d0))
                            (nfix (+ 2 (nth 0 (locals (top-frame (th) s)))))
                          1))
              (sdepth (call-stack (th) s)))))

;; This is the same theorem about ordinals that we used for tiny-fib. I really
;; believe that this should actually go to where it belongs, namely the
;; ordinals book.

(local
  (defthm l1
    (implies (and (natp a)
                  (natp b)
                  (natp c)
                  (natp d)
                  (< a b))
             (acl2::o< (acl2::o+ (acl2::o* (acl2::omega) a) c)
                 (acl2::o+ (acl2::o* (acl2::omega) b) d)))
    :hints (("goal" :cases ((equal a 0))))))

;; And now, the magic of my macro....:->

(acl2::defsimulate mono-step
  :default dummy-state
  :cutpoint fact-cutpoint
  :pre fact-precondition
  :post fact-postcondition
  :assertion fact-assertion
  :mode :total
  :arity 3
  :measure factorial-rank
  :exitpoint fact-exitpoint
  :exitsteps fact-total-exitsteps
  :run mono-run
  :thms
  ((local
    (defthm cutpoint-opener
      (implies (and (equal pc (pc (top-frame (th) s)))
                    (syntaxp (quotep pc)))
               (equal (acl2::concrete-nextt-cutpoint n0 d0 s)
                      (if (fact-cutpoint n0 d0 s) s
                        (acl2::concrete-nextt-cutpoint
                         n0 d0
                         (mono-step s))))))))
  :hints (("Goal"
           :cases ((equal (pc (top-frame (th) acl2::s2)) 0)
                   (equal (pc (top-frame (th) acl2::s2)) 12)
                   (equal (pc (top-frame (th) acl2::s2)) 14)))
          ("Subgoal 2"
           :in-theory (disable fact-caller-framesp)
           :use ((:instance (:definition fact-caller-framesp)
                            (cs (pop
                                 (CADR (ASSOC-EQUAL (TH)
                                                    (THREAD-TABLE acl2::S2)))))
                            (n0 acl2::s0)
                            (k (- acl2::s0 (car (locals (top-frame (th) acl2::s2))))))))
          ("Subgoal 1"
           :in-theory (disable fact-caller-framesp)
           :use ((:instance (:definition fact-caller-framesp)
                            (cs (pop
                                 (CADR (ASSOC-EQUAL (TH)
                                                    (THREAD-TABLE acl2::S2)))))
                            (n0 acl2::s0)
                            (k (- acl2::s0 (car (locals (top-frame (th) acl2::s2))))))))))


