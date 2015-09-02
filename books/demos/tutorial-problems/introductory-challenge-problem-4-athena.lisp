; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore, January, 2010
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; (certify-book "introductory-challenge-problem-4-athena")
; -----------------------------------------------------------------

; Some Solutions to Introductory Challenge Problem 4

; See :doc introductory-challenge-problem-4

; This book is a companion to introductory-challenge-problem-4.lisp.  While
; that book records the use of The Method to discover the proofs, this book
; just presents the resulting sequence of events.  This is what most ACL2
; user's prepare during a proof development.  In some senses it is easier to
; read -- it doesn't contain the distracting meta-comments about what goes
; wrong if another tack is pursued -- but it also obscures the discovery
; process.  The sequence below appears to leap fully formed from the brow of
; Zeus, which is why we call it the ``Athena'' script.

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

(defthm main-theorem-1-about-collect-once
  (subsetp (collect-once x) x))

(defthm member-collect-once
  (iff (member e (collect-once a))
       (member e a)))

(defthm main-theorem-2-about-collect-once
  (not (dupsp (collect-once x))))

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
; Of course, that is too specific to prove by induction and we attack this
; instead:

; (equal (while-loop-version x a)
;        (append (collect-once (list-minus (rev x) a)) a))

; This formula bears thinking about!  If you're like us, you won't believe it
; until it is proved!

(defthm list-minus-append
  (equal (list-minus (append a b) c)
         (append (list-minus a c)
                 (list-minus b c))))

(defthm member-append
  (iff (member e (append a b))
       (or (member e a)
           (member e b))))

(defthm collect-once-append
  (equal (collect-once (append a b))
         (append (list-minus (collect-once a)
                             b)
                 (collect-once b))))

(defthm assoc-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm member-list-minus
  (iff (member e (list-minus x a))
       (and (member e x)
            (not (member e a)))))

(defthm list-minus-collect-once
  (equal (list-minus (collect-once x) a)
         (collect-once (list-minus x a))))

(defthm list-minus-list-minus
  (equal (list-minus (list-minus x a) b)
         (list-minus x (append b a))))

(defthm general-equivalence
  (equal (while-loop-version x a)
         (append (collect-once (list-minus (rev x) a)) a)))

(defthm main-theorem-1-about-while-loop
  (subsetp (while-loop-version x nil) x))

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

(defthm subsetp-cons
  (implies (subsetp a b)
           (subsetp a (cons e b))))

(defthm subsetp-reflexive
  (subsetp a a))

(defthm trans-subsetp
  (implies (and (subsetp a b)
                (subsetp b c))
           (subsetp a c)))

(defthm append-cons-v-cons-append-1
  (subsetp (append b (cons e c))
           (cons e (append b c))))

(defthm append-cons-v-cons-append-2
  (subsetp (cons e (append b c))
           (append b (cons e c))))

(defthm subsetp-append-cons-cons-append
  (iff (subsetp a (append b (cons e c)))
       (subsetp a (cons e (append b c)))))

(defthm main-lemma-1-about-while-loop-version
  (subsetp (while-loop-version x a) (append x a))
  :hints (("Goal" :induct (while-loop-version x a))))

(defthm subsetp-append-nil
  (iff (subsetp x (append y nil))
       (subsetp x y)))

(defthm main-theorem-1-about-while-loop-version
  (subsetp (while-loop-version x nil) x)
  :hints (("Goal"
           :use (:instance main-lemma-1-about-while-loop-version
                           (x x)
                           (a nil))
           :in-theory (disable main-lemma-1-about-while-loop-version))))

(defthm main-lemma-2-about-while-loop-version
  (implies (not (dupsp a))
           (not (dupsp (while-loop-version x a)))))

(defthm main-theorem-2-about-while-loop-version
  (not (dupsp (while-loop-version x nil))))

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


