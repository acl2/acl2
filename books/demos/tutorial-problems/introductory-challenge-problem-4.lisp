; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore, January, 2010
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "introductory-challenge-problem-4")
; -----------------------------------------------------------------

; Some Solutions to Introductory Challenge Problem 4

; See :doc introductory-challenge-problem-4

; In this book we define a primitive recursive function for collecting one copy of
; each element of a list, x.  We also define a tail-recursive version version that
; is the analogue of a while loop that does the same thing.  However, the two versions
; collect the elements in opposite orders and, in fact, collect "opposite occurrences"
; of the elements, as explained below.  We then prove that each method is correct
; in the sense that each returns a subset of x that contains no duplications.  We also
; prove them ``equivalent'' modulo some rearrangements.

; This book not only presents the solutions but records how The Method was used
; to find them.  That makes it hard to read, with many deleted (commented out)
; defthms and comments about checkpoints and ``stack depth''.  The typical ACL2
; user does not record that information and instead just produces a book
; containing the fully formed proof script.  This book thus has a mate, called
; introductory-challenge-problem-4-athena.lisp, the reference to Athena being
; that she sprung, ready for action, from Zeus' head.  It is often the case
; that ACL2 users subsequently take the ``Athena'' script and clean it up still
; further, employing LOCAL to hide lemmas that should not be exported and even
; perhaps exploring better proofs.

(in-package "ACL2")

; We wish to collect one copy of each element in x.  We'll actually define the
; method two ways, primitive recursively and tail-recursively, the latter
; method being analogous to the program:

; a = nil;
; while (x not empty) {
;  a = if (member (car x) a) then a else (cons (car x) a);
;  x = (cdr x);
;  }
; return a;

; We'll prove the two ``equivalent'' and we'll prove that they return a subset
; of x that contains no duplications.

; This book is organized into four sections.  (A) We will start by proving that
; the primitive recursive version correct: it returns a subset of its argument
; that is duplication free.  This will be straightforward.  (B) Then we'll
; define the while-loop version and we will prove it ``equivalent'' to the
; primitive recursive version.  This will be challenging primarily because the
; two methods collect their answers in different orders; even stating the
; relationship between the two is interesting.  Proving it will involve a few
; lemmas.  But once we prove their ``equivalence'' the correctness of the
; while-loop version will be straightforward from the correctness of the
; primitive recursive version.  (C) We will disable the rules we prove about
; the while-loop version and prove it correct directly, without exploiting the
; primitive recursive version.  This requires leading the theorem prover more
; carefully because reasoning about tail-recursive functions that accumulate
; results is sometimes delicate.  (D) Lessons learned -- a narrative that
; summarizes what we learn from these examples.

; We follow The Method, which, recall, involves us in recursive attempts to
; prove lemmas.  We use a notation to indicate our sequence of proof attempts.
; Here is an example (although in actual use we print things across multiple
; lines).  The number in bracket indicates our ``stack depth''.  The ``key
; term'' is some term from a Key Checkpoint in the failed proof which is
; responsible for our subsequent action.  Sometimes instead of a Key Term we
; just give an English explanation of what we're thinking.

; [0] (defthm main ...)     Failed!    Key Term: ...
; [1] (defthm lemma-1 ...)  Succeeded!
; [0] (defthm main ...)     Failed!    Key Term: ...
; [1] (defthm lemma-2 ...)  Failed!    Key Term: ...
; [2] (defthm lemma-2a ...) Succeeded!
; [2] (defthm lemma-2b ...) Succeeded!
; [1] (defthm lemma-2 ...)  Succeeded!
; [0] (defthm main ...)     Succeeded!

; -----------------------------------------------------------------
; Section A:  The Primitive Recursive Version and Its Correctness

; The property of having duplications is defined as:

(defun dupsp (x)
  (if (endp x)
      nil
      (if (member (car x) (cdr x))
          t
          (dupsp (cdr x)))))

; The primitive recursive method of collecting one copy of each element is:

(defun collect-once (x)
  (if (endp x)
      nil
      (if (member (car x) (cdr x))
          (collect-once (cdr x))
          (cons (car x) (collect-once (cdr x))))))

; [0]
(defthm main-theorem-1-about-collect-once
  (subsetp (collect-once x) x))
; Succeeded!

; [0]
; (defthm main-theorem-2-about-collect-once
;   (not (dupsp (collect-once x))))
; Failed!
; Key Term:  (MEMBER (CAR X) (COLLECT-ONCE (CDR X)))

; [1]
(defthm member-collect-once
  (iff (member e (collect-once a))
       (member e a)))
; Succeeded!

; [0]
(defthm main-theorem-2-about-collect-once
  (not (dupsp (collect-once x))))
; Succeeded!

; That was really easy!

;-----------------------------------------------------------------
; Section B:  The While-Loop Version and Its Correctness --
;  presented in two parts:  its equivalence to the primitive recursive
;  version and then its correctness proved via that equivalence

; The tail-recursive, or while-loop version, is defined as follows.  The
; function below is the loop itself and it ought to be called with a = nil to
; implement the initialization of a in the pseudo-code above.

(defun while-loop-version (x a)
  (if (endp x)
      a
      (while-loop-version (cdr x)
                          (if (member (car x) a)
                              a
                              (cons (car x) a)))))

; We wish to prove that the two are equivalent.  But they are actually
; very different.  For example,

; (collect-once '(2 4 1 3 1 2 3 4))           = (1 2 3 4)
; (while-loop-version '(2 4 1 3 1 2 3 4) nil) = (3 1 4 2)

; Things get a little more complicated if a is non-nil:
; (while-loop-version '(2 4 1 3 1 2 3 4) '(2 2 4 4)) = (3 1 2 2 4 4)

; Several observations help explain what is happening.  (1) Collect-once
; collects the last occurrence of each element, in the order of their last
; occurrences.  So, for example, since the last occurrence of 2 preceeds the
; last occurrence of 3 in '(2 4 1 3 1 2 3 4)), then the collected 2 preceeds
; the collected 3 in the answer.  But while-loop-version collects the first
; occurrence of each element, in the reverse order of that occurrence.  So it
; adds 2 to its accumulator first and adds 3 last, making 3 preceed 2 in the
; answer.

; (2) The while-loop-version does not collect anything already in a and indeed
; just adds stuff to the front of a, returning everything initially in a plus
; one occurrence of everything in x not in a.

; To state the relationship that holds between these two we have to define two
; other functions.

; This is our familiar list reverse function...
(defun rev (x)
  (if (endp x)
      nil
      (append (rev (cdr x))
              (list (car x)))))

; And this function ``removes'' from x all the elements in y, i.e., copies x
; while dropping the elements of y.

(defun list-minus (x y)
  (if (endp x)
      nil
      (if (member (car x) y)
          (list-minus (cdr x) y)
          (cons (car x) (list-minus (cdr x) y)))))

; The specific equivalence we're really interested in is
; (equal (while-loop-version x nil)
;        (collect-once (rev x)))

; But we will not be able to prove that by induction because it has the
; constant nil where we need a variable, a, in order to admit an appropriate
; inductive instance.  So we will attack the most general problem.  What is
; (while-loop-version x a) equal to, in terms of collect-once?

; The most general relationship between the two collection functions is:

; (equal (while-loop-version x a)
;        (append (collect-once (list-minus (rev x) a)) a))

; This formula bears thinking about!  If you're like us, you won't believe it
; until it is proved!

; [0]
; (defthm general-equivalence
;   (equal (while-loop-version x a)
;          (append (collect-once (list-minus (rev x) a)) a)))
; Failed!
; Key term in checkpoint:
; (LIST-MINUS (APPEND (REV (CDR X)) (LIST (CAR X))) A)

; [1]
(defthm list-minus-append
  (equal (list-minus (append a b) c)
         (append (list-minus a c)
                 (list-minus b c))))
; Succeeded!

; [0]
; (defthm general-equivalence
;   (equal (while-loop-version x a)
;          (append (collect-once (list-minus (rev x) a)) a)))
; Failed!
; Key term in checkpoint:
; (COLLECT-ONCE (APPEND (LIST-MINUS (REV (CDR X)) A) (LIST (CAR X))))

; [1]
; (defthm collect-once-append
;   (equal (collect-once (append a b))
;          (append (list-minus (collect-once a) b)
;                  (collect-once b))))
; Failed!
; Key term:
; (MEMBER (CAR A) (APPEND (CDR A) B))

; [2]
(defthm member-append
  (iff (member e (append a b))
       (or (member e a)
           (member e b))))
; Succeeded!

; [1]
(defthm collect-once-append
  (equal (collect-once (append a b))
         (append (list-minus (collect-once a)
                             b)
                 (collect-once b))))
; Succeeded!

; [0]
; (defthm general-equivalence
;   (equal (while-loop-version x a)
;          (append (collect-once (list-minus (rev x) a)) a)))
; Failed!
; Key term:
; (APPEND (APPEND (LIST-MINUS (COLLECT-ONCE (LIST-MINUS (REV (CDR X)) A))

; [1]
(defthm assoc-append
  (equal (append (append a b) c)
         (append a (append b c))))
; Succeeded!

; [0]
; (defthm general-equivalence
;   (equal (while-loop-version x a)
;          (append (collect-once (list-minus (rev x) a)) a)))
; Failed!
; Key term:
; (LIST-MINUS (COLLECT-ONCE (LIST-MINUS (REV (CDR X)) A)) ...)

; This key term makes us think of the lemma to move the LIST-MINUS inside the
; COLLECT-ONCE.  But when that's done, we will have two LIST-MINUS terms
; nestled together and we will want to combine them into one.  Call these two
; lemmas (a) and (b).

; [1] (a)
; (defthm list-minus-collect-once
;   (equal (list-minus (collect-once x) a)
;          (collect-once (list-minus x a))))
; Failed!
; Key term:
; (MEMBER (CAR X) (LIST-MINUS (CDR X) A))

; [2] (A pretty fact)
(defthm member-list-minus
  (iff (member e (list-minus x a))
       (and (member e x)
            (not (member e a)))))
; Succeeded!

; [1] (a)
(defthm list-minus-collect-once
  (equal (list-minus (collect-once x) a)
         (collect-once (list-minus x a))))
; Succeeded!

; [1] (b)
(defthm list-minus-list-minus
  (equal (list-minus (list-minus x a) b)
         (list-minus x (append b a))))
; Succeeded!

; [0]
(defthm general-equivalence
  (equal (while-loop-version x a)
         (append (collect-once (list-minus (rev x) a)) a)))
; Succeeded!

; That completes the proof of the "equivalence" of the two methods.

; Now we prove (1) that the result of while-loop-version is a subset, and (2)
; that it contains no duplications.  We prove the two conjuncts separately.

; [0]
(defthm main-theorem-1-about-while-loop
  (subsetp (while-loop-version x nil) x))
; Succeeded!

; But the theorem prover works harder to do the proof above than one might have
; expected because it doesn't turn into an instance of
; main-theorem-1-about-collect-once because of the presence of the rev term.
; However, we're content that ACL2 managed to do the proof on its own.

; [0]
(defthm main-theorem-2-about-while-loop
  (not (dupsp (while-loop-version x nil))))

; So we see that the proof of correctness of while-loop-version isn't hard,
; after we establish the relationship with the primitive recursive version.
; But finding and proving the relationship is fairly challenging.

; -----------------------------------------------------------------
; Section C:  A Direct Proof of the Correctness of the While-Loop Version

; Some would consider the proof in Section B "indirect" because we first showed
; how while-loop-version could be expressed as a collect-once and then proved
; our main theorems about while-loop-version, which means those main proofs
; were conducted in terms of collect-once, not while-loop-version.

; It is interesting to compare this proof with the "direct" one in which
; we don't use collect-once at all and reason only about while-loop-version.

; So to do that comparison, let's disable all the lemmas we've proved about
; while-loop-version and try to prove the two main theorems above about
; while-loop-version.

(in-theory (disable general-equivalence
                    main-theorem-1-about-while-loop
                    main-theorem-2-about-while-loop))


; [0]
; (defthm main-theorem-1-about-while-loop-redux
;   (subsetp (while-loop-version x nil) x))
; Failed!  [Well, the truth is below...]

; We don't even submit this event above because we recognize that it is not
; general enough to permit proof by induction.  We need to deal with the nil in
; the second argument of while-loop-version.  Experience with induction tells
; us this should be a variable, so we can assume an appropriate inductive
; instance.  Therefore, we adopt this subgoal immediately:

; [1]
; (defthm main-lemma-1-about-while-loop-version
;   (subsetp (while-loop-version x a) (append x a)))
; Failed!
; Key Term:  Does the wrong induction.

; [1]
; (defthm main-lemma-1-about-while-loop-version
;   (subsetp (while-loop-version x a) (append x a))
;   :hints (("Goal" :induct (while-loop-version x a))))
; Failed!  Two key terms are suggested
; Key term: (IMPLIES (AND ... (SUBSETP (WHILE-LOOP-VERSION (CDR X) A) (APPEND (CDR X) A)))
;                    (SUBSETP (WHILE-LOOP-VERSION (CDR X) A) (CONS ... (APPEND (CDR X) A))))
; Key term: (SUBSETP A A)
; So we'll prove both before trying again.
; [2]
(defthm subsetp-cons
  (implies (subsetp a b)
           (subsetp a (cons e b))))
; Succeeded!

; [2]
(defthm subsetp-reflexive
  (subsetp a a))
; Succeeded!

; [1]
; (defthm main-lemma-1-about-while-loop-version
;   (subsetp (while-loop-version x a) (append x a))
;   :hints (("Goal" :induct (while-loop-version x a))))
; Failed!
; Key Term:
; (IMPLIES (AND ...
;               (SUBSETP (WHILE-LOOP-VERSION (CDR X) (CONS (CAR X) A))
;                        (APPEND (CDR X) (CONS (CAR X) A))))
;          (SUBSETP (WHILE-LOOP-VERSION (CDR X) (CONS (CAR X) A))
;                   (CONS (CAR X) (APPEND (CDR X) A))))

; We'd be done if we could rewrite the
; (APPEND (CDR X) (CONS (CAR X) A))
; to
; (CONS (CAR X) (APPEND (CDR X) A))
; These two terms are not equal!  But they are ``set-equal'' and this kind of
; rewriting is possible using user-defined equivalences and congruence rules.
; But the new user should not dive into congruences yet.  So we will do this
; with ordinary lemmas:

; The plan then is to prove
; (iff (subsetp a (append b (cons e c)))
;      (subsetp a (cons e (append b c))))

; Consider the first half of this bi-implication:
; (implies (subsetp a (append b (cons e c)))            ; hyp1
;          (subsetp a (cons e (append b c))))           ; concl
; Notice that if we knew
; (subsetp (append b (cons e c)) (cons e (append b c))) ; hyp2
; then we could use hyp1 and hyp2 together with the transitivity of
; subsetp to get concl.

; The proof in the other direction is comparable but requires the
; (subsetp (cons e (append b c)) (append b (cons e c)))

; Thus, our plan is prove
; (a) transitivity of subsetp
; (b) (subsetp (append b (cons e c)) (cons e (append b c)))
; (c) (subsetp (cons e (append b c)) (append b (cons e c)))

; in order to prove
; (d) (iff (subsetp a (append b (cons e c)))
;         (subsetp a (cons e (append b c))))

; [2] (a)
(defthm trans-subsetp
  (implies (and (subsetp a b)
                (subsetp b c))
           (subsetp a c)))
; Succeeded!

; [2] (b)
(defthm append-cons-v-cons-append-1
  (subsetp (append b (cons e c))
           (cons e (append b c))))
; Succeeded!

; [2] (c)
(defthm append-cons-v-cons-append-2
  (subsetp (cons e (append b c))
           (append b (cons e c))))
; Succeeded!

; [2] (d)
(defthm subsetp-append-cons-cons-append
  (iff (subsetp a (append b (cons e c)))
       (subsetp a (cons e (append b c)))))
; Succeeded!

; [1]
(defthm main-lemma-1-about-while-loop-version
  (subsetp (while-loop-version x a) (append x a))
  :hints (("Goal" :induct (while-loop-version x a))))
; Succeeded!

; [0]
; (defthm main-theorem-1-about-while-loop-version
;   (subsetp (while-loop-version x nil) x))
; Failed!  [But the truth is below...]

; But we don't submit this because we don't expect it to be proved
; from the main lemma just proved:  they don't match!  But
; note that if we instantiated the main lemma, replacing a by nil,
; we get:

; (subsetp (while-loop-version x nil) (append x nil))

; and we could simplify the (append x nil) to x in this context, with
; another congruence rule -- if we were using them.  So let's prove
; first that we can simplify (append x nil) inside a subsetp:

; [1]
(defthm subsetp-append-nil
  (iff (subsetp x (append y nil))
       (subsetp x y)))
; Succeeded!

; and then just tell ACL2 how to use the lemma to get the main theorem.  Note
; that we give a hint to instantiate main-lemma-1... but we also disable
; main-lemma-1... because otherwise it will rewrite itself away!  Once the
; instance of main-lemma-1... is sitting around as a hypothesis,
; subsetp-append-nil will rewrite the (append x nil) to x for us and finish the
; proof.

; [0]
(defthm main-theorem-1-about-while-loop-version
  (subsetp (while-loop-version x nil) x)
  :hints (("Goal"
           :use (:instance main-lemma-1-about-while-loop-version
                           (x x)
                           (a nil))
           :in-theory (disable main-lemma-1-about-while-loop-version))))
; Succeeded!

; Recall that the main-theorem-1... just proved is just half of what we want.
; We also want:

; [0]
; (defthm main-theorem-2-about-while-loop-version
;   (not (dupsp (while-loop-version x nil))))
; Failed!  [But the truth is below...]

; But, again, we don't submit that because the nil makes it not general enough for
; induction.  Instead we go immediately to:

; [1]
(defthm main-lemma-2-about-while-loop-version
  (implies (not (dupsp a))
           (not (dupsp (while-loop-version x a)))))
; Succeeded!

; This time we know our main-lemma-2... will match (there's no (append x nil)
; in there to mess things up) and so we can complete the proof with:

; [0]
(defthm main-theorem-2-about-while-loop-version
  (not (dupsp (while-loop-version x nil))))
; Succeeded!

;-----------------------------------------------------------------
; Section D:  Lessons Learned

; The most obvious lesson is that it is easier to reason about the primitive
; recursive collect-once than about the while-loop-version.  Thus, if your only
; need is for a function that collects one occurrence of each element of a list
; and you don't care about the order in which you collect them and you don't
; need it to be very sparing of stack space when it executes, then use the
; primitive recursive definition and don't even think about while loops!

; So why might you be driven to while-loop-version?  One possibility is that
; the list you wish to process is very long and the primitive recursive version
; would produce a stack overflow.  In ACL2, that would mean the list would have
; to be several thousand long.  Is your application really so demanding?

; Another possibility is that you are modeling in Lisp a while loop expressed
; in some other programming language.  In that case, the fidelity of your model to
; the artifact being modeled is important and you should use while-loop-version.

; Another possibility is that for some reason order matters and you really are
; interested in collecting the first occurrence rather than the last.  Of
; course this is most likely to be relevant in more interesting applications
; where the occurrences are somehow distinguishable.

; If you are forced to deal with the while-loop-version the question is do you
; do an indirect proof as in Section B or a direct proof as in Section C?
; The indirect proof involved 10 theorems and the direct proof involved 11.
; That is not a significant difference.

; But our sense is that the indirect proof is easier to find, once you figure
; out the basic shape of the relation between while-loop-version collect-once.
; In particular, we had to give the theorem prover two hints in the direct
; proof (versus no hints in the indirect proof).  One of our hints was about
; what induction to do and the other was about how to use a previously proved
; instance of a lemma involving an accumulator.  Furthermore, we had to think
; carefully about the use of the transitivity of subsetp and we had to hack our
; way around rewriting (append a (cons e b)) to (cons e (append a b)) in a
; subsetp-expression.

; Some of these "set" problems could have been handled a lot more elegantly by
; defining set-equal as an equivalence relation and proving the congruence
; rules to allow the rewriting of set-equal terms to set-equal terms inside
; certain expressions like subsetp and member.  However, that involves a lot of
; overhead in the form of congruence rules showing that set-equality is
; maintained by replacement of set-equals by set-equals in various argument
; positions of the various functions.  See :doc congruence.  In general, we
; find congruence-based reasoning extremely neat and powerful when the
; appropriate infrastructure has been built up.  But because the infrastructure
; is ``heavy'' we tend not to invest in it for small projects.

; In summary, different users might take home different lessons about whether a
; direct or indirect proof is better here.  This is in part due to the
; complexity of the functional relationship between collect-once and
; while-loop-version, which additionall involved append, list-minus, and rev.
; Had the relationship been simpler, the indirect proof would have been
; preferred.

; An undeniable lesson, however, is that it is helpful to know both styles of
; proof and to be able to explore both as needed in your applications.


