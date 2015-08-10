#||

See the README file on this directory for an overview of this work.

In this file, I define good-statep, the predicate that determines whether an M1
state is well-formed.  This is analogous to the Java Bytecode Verifier.
Good-statep will be in the guard of M1.  That is, M1 should only be applied to
states satisfying good-statep and may apply any of the standard operations to
it without any runtime checking.  In particular, by proving the guards of the
model, ACL2 guarantees that every instruction in a well-formed M1 program can
be executed without error.  The basic constraints are thus:

* the state is a 4-tuple composed of a pc, locals, stack, and program
* the pc is a natural number strictly less than the length of the program
* the locals and stack are true lists rationals
* the program is a true list of well-formed instructions
* all the local variables (indices) used are legal wrt the locals
* every jump or branch is to a legal pc
* every instruction that removes elements from the stack will always
   find sufficient elements on the stack

Because good-statep is used in the guard of M1, it must be guard verified
itself.  The bulk of this file is devoted to the proofs that the functions
defined here are defined and are used in compliance with their own guards.

If you are playing with this file, it is best to define the M1 symbol package
and then ld the file.  That way you can undo back through the events here and
modify them.  For a comment on the M1 package, see below.

(defpkg "M1"
  (set-difference-eq (union-eq *acl2-exports*
                               *common-lisp-symbols-from-main-lisp-package*)
                     '(push pop pc program step)))

(ld ; linebreak here to help certification infrastructure
 "good-statep.lisp" :ld-pre-eval-print t)

If you are certifying this file, define the M1 symbol package and issue the
certify-book command below.

Comment on the M1 Symbol Package: I don't import certain Common Lisp symbols,
like PUSH and POP, because of their existing ACL2 or Common Lisp definitions
are incompatible with the intended definitions below.  Others of the symbols I
don't import are defined acceptably in the ACL2 package, e.g., NTH, but I want
to students to see their definitions as warm-up exercises.

(defpkg "M1"
  (set-difference-eq (union-eq *acl2-exports*
                               *common-lisp-symbols-from-main-lisp-package*)
                     '(push pop pc program step)))

(certify-book "good-statep" 1)

|#

(in-package "M1")

; cert_param: (non-acl2r)

; -----------------------------------------------------------------
; Stack Manipulation -- Step 1:  Define the (well-guarded) functions

(defun stackp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (equal lst nil))
        (t (and (rationalp (car lst))
                (stackp (cdr lst))))))

; -----------------------------------------------------------------

; Indexing into a List:

; The only difference between new2 and new3 is that in new3 the symbols
; nth and update-nth are imported into "M1".  But we need NTH to behave
; as it does in new2.  Fortunately, the definitions of NTH in "ACL2"
; and new2's "M1" are equivalent, just different.  So we prove the
; alternative definition rule and disable the built-in rule.

(defthm nth-alt-def
  (equal (nth n list)
         (IF (ZP N)
             (CAR LIST)
             (NTH (- N 1) (CDR LIST))))
  :rule-classes ((:definition :controller-alist ((nth t nil)))))

(in-theory (disable (:definition nth)))

; -----------------------------------------------------------------
; The pc of a State

(defun pcp (x max-pc)
  (declare (xargs :guard (natp max-pc)))
  (and (natp x)
       (< x max-pc)))

; -----------------------------------------------------------------
; The Locals of a State

; The locals must be a list of integers.  This is equivalent to stackp but
; we'll define it separately for sanity.

(defun localsp (lst)
  (declare (xargs :guard t))
  (cond ((atom lst) (equal lst nil))
        (t (and (rationalp (car lst))
                (localsp (cdr lst))))))


; -----------------------------------------------------------------
; Instruction Accessors

(defun op-code (inst)
  (declare (xargs :guard (true-listp inst)))
  (nth 0 inst))

(defun arg1 (inst)
  (declare (xargs :guard (true-listp inst)))
  (nth 1 inst))

; Since there are no functions for creating instructions, we don't need
; ``accessor-constructor'' lemmas like top-push, etc.  We will just disable
; these functions so that on symbolic expressions they do not expand.

(in-theory (disable op-code arg1))

;  Note that since we did not disable the executable-counterparts of these
; functions they will compute out on constants, e.g. (arg1 '(ILOAD 3)) = 3.

; -----------------------------------------------------------------
; Instruction Well-Formedness



; First we check ``syntactic'' (context-free) conditions on the shape of the
; program.

(defun instructionp (inst)
  (declare (xargs :guard t))
  (and (true-listp inst)
       (consp inst)
       (case (op-code inst)
         ((IADD ISUB IMUL HALT)
          (equal (len inst) 1))
         ((ILOAD ISTORE)
          (and (equal (len inst) 2)
               (natp (arg1 inst))))
         (ICONST
          (and (equal (len inst) 2)
               (rationalp (arg1 inst))))
         ((GOTO IFEQ)
          (and (equal (len inst) 2)
               (integerp (arg1 inst))))
         (otherwise nil))))

(defun programp (lst)
  (declare (xargs :guard t))
  (cond
   ((atom lst) (equal lst nil))
   (t (and (instructionp (car lst))
           (programp (cdr lst))))))

(defthm instructionp-nth
  (implies (and (programp lst)
                (natp pc)
                (< pc (len lst)))
           (instructionp (nth pc lst)))
  :rule-classes nil)

; Note: The lemma above isn't a lot of use as a :rewrite or :forward-chaining
; rule because too much information is buried inside the instructionp
; conclusion, e.g., that the arg1 of the inst is a rational if the op-code is
; ICONST.  So we arrange for this lemma to be :used automatically whenever
; instances of (programp lst) and (nth pc lst) both occur the goal.

(include-book "use-when")

(acl2::use-when instructionp-nth         ; lemma name
                nil                      ; initial substitution
                :hyp (programp lst)      ; patterns to look for as
                :subterm (nth pc lst))   ; either hyps or subterms

; Now we check more context-sensitive constraints, e.g., that every local
; variable index is legal, and that every ``next pc'' is legal.  We then
; develop the machinery for checking that the stack always has enough things on
; it.

; Two methods come to mind to check the local variable indices.
; (a) visit every ILOAD and ISTORE and check that its index is less than the
;     length of the locals in the state in question
; (b) visit every ILOAD and ISTORE and compute the maximum local, saving
;     the state-related question until later.

; We choose (b) because then we will be able to more easily show that if a
; program is legal with some local variable array it is legal with any larger
; one.  We need this property when we do code proofs because our code
; correctness lemmas do not fully specify the length of the local variable
; array.

; Choosing (a) -- which we actually did the first time we implemented guards --
; complicates the proof because we drag full states down into the simple
; question of whether a program uses too big an index.

(defun max-local (program)
  (declare (xargs :guard (programp program)))
  (cond ((endp program) -1)
        ((or (eq (op-code (car program)) 'ILOAD)
             (eq (op-code (car program)) 'ISTORE))
         (max (arg1 (car program))
              (max-local (cdr program))))
        (t (max-local (cdr program)))))

(defthm integerp-max-local
  (implies (programp program)
           (integerp (max-local program))))

(defthm max-local-almost-natp
  (implies (programp program)
           (<= -1 (max-local program)))
  :rule-classes :linear)

(defthm max-local-nth
  (implies (and (natp i)
                (< i (len program))
                (or (eq (op-code (nth i program)) 'ILOAD)
                    (eq (op-code (nth i program)) 'ISTORE)))
           (<= (arg1 (nth i program)) (max-local program)))
  :rule-classes :linear)

; Now we check that the next pc is always legal.

(defun next-pc-okp (inst pc max-pc)
  (declare (xargs :guard (and (instructionp inst)
                              (natp pc)
                              (natp max-pc)
                              (< pc max-pc))))
  (case (op-code inst)
    ((ILOAD ISTORE ICONST IADD ISUB IMUL)
     (pcp (+ 1 pc) max-pc))
    (GOTO
     (pcp (+ pc (arg1 inst)) max-pc))
    (IFEQ
     (and (pcp (+ pc (arg1 inst)) max-pc)
          (pcp (+ pc 1) max-pc)))
    (HALT t)
    (otherwise nil)))

(defthm programp-true-listp
  (implies (programp lst)
           (true-listp lst))
  :rule-classes :forward-chaining)

(defun all-pcs-okp (program pc)
  (declare (xargs :measure (nfix (- (len program) (nfix pc)))
                  :guard (and (programp program)
                              (natp pc))))
  (cond ((or (not (natp pc))
             (>= pc (len program)))
         t)
        (t (and (next-pc-okp (nth pc program) pc (len program))
                (all-pcs-okp program (+ 1 pc))))))

(defthm next-pc-okp-nth
  (implies (and (all-pcs-okp program pc)
                (programp program)
                (natp pc)
                (natp i)
                (<= pc i)
                (< i (len program)))
           (next-pc-okp (nth i program) i (len program)))
  :rule-classes nil)

; The lemma above is like instructionp-nth above: not very useful if stored as
; :rewrite or :foreward-chaining rule.  So again, we force its automatic use:

(acl2::use-when next-pc-okp-nth
                ((pc . '0))
                :hyp (all-pcs-okp program pc)
                :subterm (nth i program))

; Note that the first trigger is (all-pcs-okp program 0), given the initial
; alist.

; -----------------------------------------------------------------

; State Manipulation:

(defun pc (s)
  (declare (xargs :guard (true-listp s)))
  (nth 0 s))
(defun locals (s)
  (declare (xargs :guard (true-listp s)))
  (nth 1 s))
(defun stack (s)
  (declare (xargs :guard (true-listp s)))
  (nth 2 s))
(defun program (s)
  (declare (xargs :guard (true-listp s)))
  (nth 3 s))

(in-theory (disable pc locals stack program))

; -----------------------------------------------------------------
; Computing a Stack Map

; A ``stack map'' is an association list that maps program counters to the
; depth of the stack at arrival at that program counter.  It shall be a
; requirement that every program counter have a fixed stack depth upon every
; arrival.  I.e., a bytecode program is illegal if the stack is of different
; sizes upon different arrivals at a given program counter.  (Of course, there
; are perfectly ``nice'' programs that violate this requirement and, indeed, we
; verify one such program in our suite of examples; see funny-fact.lisp.)

; To check whether an M1 program satisfies the rule, we try to generate a stack
; map.  This is done by the function gsm (``generate stack map'') and its
; subfunction gsm1.  Gsm1 is essentially an abstract interpreter for M1 code.
; Instead of manipulating actual data it just records the stack depth at each
; instruction.  Upon encountering the branch instruction, IFEQ, it pursues both
; branches.  It builds up the map as it goes, storing the current stack depth
; upon arrival at a pc never before seen, and aborting with failure if it
; arrives at a given pc with a different stack depth than previously stored.
; It halts because the number of unvisited pcs shrinks as it recurs.  The
; definitions between here and that for gsm1 are devoted to proving that.

(defthm len-set-difference-equal
  (implies (and (member e big)
                (not (member e small)))
           (< (len (set-difference-equal big (cons e small)))
              (len (set-difference-equal big small))))
  :rule-classes :linear)

(defun nats-below (n)
  (declare (xargs :guard (natp n)))
  (cond ((zp n) nil)
        (t (cons (- n 1) (nats-below (- n 1))))))

(defun nat-to-nat-alistp (x)
  (declare (xargs :guard t))
  (cond
   ((atom x) (equal x nil))
   ((consp (car x))
    (and (natp (car (car x)))
         (natp (cdr (car x)))
         (nat-to-nat-alistp (cdr x))))
   (t nil)))

(defthm nat-to-nat-alistp-to-alistp
  (implies (nat-to-nat-alistp x)
           (alistp x))
  :rule-classes (:rewrite :forward-chaining))

(defthm nats-below-property
  (implies (and (natp max-pc)
                (natp pc)
                (< pc max-pc))
           (member pc (nats-below max-pc))))

(defthm subsetp-implies-member
  (implies (and (subsetp a b)
                (member e a))
           (member e b)))

; This is an unusual rule because the lhs is smaller than the rhs, but
; the proofs below fail if I reverse the orientation.  I'm not sure why.

(defthm assoc-is-member-strip-cars
  (implies (alistp alist)
           (iff (assoc key alist)
                (member key (strip-cars alist)))))

(defthm nat-to-nat-alistp-property
  (implies (and (nat-to-nat-alistp alist)
                (assoc x alist))
           (natp (cdr (assoc x alist))))
  :rule-classes (:rewrite
                 (:rewrite
                  :corollary
                  (implies (and (nat-to-nat-alistp alist)
                                (assoc x alist))
                           (integerp (cdr (assoc x alist)))))
                 (:linear
                  :corollary
                  (implies (and (nat-to-nat-alistp alist)
                                (assoc x alist))
                           (<= 0 (cdr (assoc x alist)))))))

(defun gsm1 (pc stackn program map)
  (declare (xargs :measure (len (set-difference-equal (nats-below (len program))
                                                      (strip-cars map)))
                  :guard (and (pcp pc (len program))
                              (natp stackn)
                              (programp program)
                              (all-pcs-okp program 0)
                              (nat-to-nat-alistp map))
                  :verify-guards nil))
  (let ((inst (nth pc program))
        (temp (assoc pc map)))
    (cond
     ((mbe :logic (not (and (pcp pc (len program))
                            (natp stackn)
                            (programp program)
                            (all-pcs-okp program 0)
                            (nat-to-nat-alistp map)))
           :exec nil)
      nil)
     (temp (if (equal stackn (cdr temp))
               map
               nil))
     (t (let ((map1 (cons (cons pc stackn) map)))
          (case (op-code inst)
            ((ILOAD ICONST)
             (gsm1 (+ pc 1) (+ 1 stackn) program map1))
            (ISTORE
             (if (<= 1 stackn)
                 (gsm1 (+ pc 1) (- stackn 1) program map1)
                 nil))
            ((IADD ISUB IMUL)
             (if (<= 2 stackn)
                 (gsm1 (+ pc 1) (- stackn 1) program map1)
                 nil))
            (GOTO
             (gsm1 (+ pc (arg1 inst)) stackn program map1))
            (IFEQ
             (if (< 0 stackn)
                 (let ((map2 (gsm1 (+ pc (arg1 inst)) (- stackn 1) program map1)))
                   (cond
                    ((null map2) nil)
                    ((mbe :logic
                          (< (len (set-difference-equal (nats-below (len program)) (strip-cars map2)))
                             (len (set-difference-equal (nats-below (len program)) (strip-cars map))))
                          :exec
                          t)
                     (gsm1 (+ pc 1) (- stackn 1) program map2))
                    (t nil)))
                 nil))
            (HALT map1)
            (otherwise nil)))))))

; Todo:
; I don't know why I need the expand hint below, but I need it repeatedly.
; I also believe I could get the proof a lot faster if I disabled everything
; not involved in the construction of the new map.

(defthm nat-to-nat-alistp-gsm1
  (implies (nat-to-nat-alistp map)
           (nat-to-nat-alistp (gsm1 pc stackn program map)))
  :hints (("Subgoal *1/2''"
           :expand
           (GSM1 PC (CDR (ASSOC-EQUAL PC MAP))
                 PROGRAM MAP))))

(defthm subsetp-cons
  (implies (subsetp a b)
           (subsetp a (cons e b))))

(defthm subsetp-refl
  (subsetp a a))

(defthm subsetp-trans
  (implies (and (subsetp a b)
                (subsetp b c))
           (subsetp a c)))

(defthm member-subsetp
  (implies (and (member e a)
                (subsetp a b))
           (member e b)))


; Todo: This is like pulling teeth...  Why do I need these hints?

; Todo:  Hints!  Yuck...

(defthm subsetp-strip-cars-gsm1
  (implies (gsm1 pc stackn program map)
           (subsetp (strip-cars map)
                    (strip-cars (gsm1 pc stackn program map))))
  :hints
  (("Subgoal *1/2''"  ; Same hint as above...
    :expand
    (GSM1 PC (CDR (ASSOC-EQUAL PC MAP))
          PROGRAM MAP))))

(defthm strong-set-difference-equal-subsetp
  (implies (and (not (member e little2))
                (member e little1)
                (member e big)
                (subsetp little2 little1))
           (< (len (set-difference-equal big little1))
              (len (set-difference-equal big little2))))
  :rule-classes nil)

(in-theory (disable all-pcs-okp))

(verify-guards gsm1
               :hints
               (("Goal" :do-not-induct t)
                ("Subgoal 5'"
                 :use ((:instance subsetp-strip-cars-gsm1
                                  (pc (+ pc (arg1 (nth pc program))))
                                  (stackn (+ -1 stackn))
                                  (program program)
                                  (map (cons (cons pc stackn) map)))
                       (:instance member-subsetp
                                  (e pc)
                                  (a (strip-cars (cons (cons pc stackn) map)))
                                  (b (strip-cars (gsm1 (+ pc (arg1 (nth pc program)))
                                                       (+ -1 stackn)
                                                       program (cons (cons pc stackn) map)))))
                       (:instance subsetp-trans
                                  (a (strip-cars map))
                                  (b (strip-cars (cons (cons pc stackn) map)))
                                  (c (strip-cars (gsm1 (+ pc (arg1 (nth pc program)))
                                                       (+ -1 stackn)
                                                       program (cons (cons pc stackn) map)))))
                       (:instance strong-set-difference-equal-subsetp
                                  (e pc)
                                  (little2 (strip-cars map))
                                  (little1 (strip-cars (gsm1 (+ pc (arg1 (nth pc program)))
                                                             (+ -1 stackn)
                                                             program (cons (cons pc stackn) map))))
                                  (big (nats-below (len program)))))
                 :in-theory (disable subsetp-strip-cars-gsm1
                                     member-subsetp
                                     subsetp-trans))))

(defthm eqlable-listp-nats-below
  (eqlable-listp (nats-below n)))

(defun gsm (program)
  (declare (xargs :guard (and (programp program)
                              (all-pcs-okp program 0))))
  (let ((alist (if (null program)
                   nil
                   (gsm1 0 0 program nil))))
    (if (subsetp (nats-below (len program))
                 (strip-cars alist))
        alist
        nil)))

; -----------------------------------------------------------------
; Checking a Stack Map

; Because the stack map changes as it is built up, I found it easier to define
; the function that checks that a stack map is legal, i.e., maps every pc to
; some stack depth that is correctly related to the stack depth of the next
; instruction.  This property is checked by csm (``check stack map'').  I then
; use the construct (csm ...(gsm ...) ...), i.e., is the stack map generated by
; gsm a legal one?

; I believe it is the case that if gsm returns non-nil then its result is a
; legal stack map.  A nice piece of future work would be to prove that.  But
; this approach suffices to give us an effective guard.

(defthm integerp-implies-rationalp ; give me a break!
  (implies (integerp x)
           (rationalp x)))

(defun csm1 (pc program stack-map)
  (declare (xargs :measure (nfix (- (len program) (nfix pc)))
                  :guard (and (natp pc)
                              (programp program)
                              (all-pcs-okp program 0)
                              (nat-to-nat-alistp stack-map))))
  (cond
   ((mbe :logic (not (and (natp pc)
                          (programp program)
                          (all-pcs-okp program 0)
                          (nat-to-nat-alistp stack-map)))
         :exec nil)
    nil)
   ((>= pc (len program)) t)
   (t
    (let ((inst (nth pc program))
          (temp (assoc pc stack-map)))
      (cond
       ((null temp) nil)
       (t (case (op-code inst)
            ((ILOAD ICONST)
             (and (assoc (+ 1 pc) stack-map)
                  (equal (+ 1 (cdr temp))
                         (cdr (assoc (+ 1 pc) stack-map)))
                  (csm1 (+ pc 1) program stack-map)))
            (ISTORE
             (and (<= 1 (cdr temp))
                  (assoc (+ 1 pc) stack-map)
                  (equal (+ -1 (cdr temp))
                         (cdr (assoc (+ 1 pc) stack-map)))
                  (csm1 (+ pc 1) program stack-map)))
            ((IADD ISUB IMUL)
             (and (<= 2 (cdr temp))
                  (assoc (+ 1 pc) stack-map)
                  (equal (+ -1 (cdr temp))
                         (cdr (assoc (+ 1 pc) stack-map)))
                  (csm1 (+ pc 1) program stack-map)))
            (GOTO
             (and (assoc (+ pc (arg1 inst)) stack-map)
                  (equal (cdr temp)
                         (cdr (assoc (+ pc (arg1 inst)) stack-map)))
                  (csm1 (+ pc 1) program stack-map)))
            (IFEQ
             (and (<= 1 (cdr temp))
                  (assoc (+ 1 pc) stack-map)
                  (equal (+ -1 (cdr temp))
                         (cdr (assoc (+ 1 pc) stack-map)))
                  (assoc (+ pc (arg1 inst)) stack-map)
                  (equal (+ -1 (cdr temp))
                         (cdr (assoc (+ pc (arg1 inst)) stack-map)))
                  (csm1 (+ pc 1) program stack-map)))
            (HALT (csm1 (+ pc 1) program stack-map))
            (otherwise nil))))))))

(defun csm (program stack-map)
  (declare (xargs :guard (and (programp program)
                              (all-pcs-okp program 0)
                              (nat-to-nat-alistp stack-map))))
  (cond
   ((null program)
    (equal stack-map nil))
   ((not (nat-to-nat-alistp stack-map)) nil)
   (t (csm1 0 program stack-map))))

(in-theory (disable csm))

; -----------------------------------------------------------------
; Well-Formed States

(defthm consp-assoc
  (implies (and (alistp a)
                (assoc k a))
           (consp (assoc k a))))

(defun good-statep (s)
  (declare (xargs :guard t))
  (and (true-listp s)                 ; state is right shape
       (equal (len s) 4)

       (natp (pc s))                  ; components are right shape
       (localsp (locals s))
       (stackp (stack s))
       (programp (program s))
                                      ; context-sensitive constraints
       (< (pc s) (len (program s)))   ; * pc in bounds of program
       (< (max-local (program s))     ; * all local vars exist
          (len (locals s)))
       (all-pcs-okp (program s) 0)    ; * all pcs in bounds
       (csm (program s)               ; * stack map exists
            (gsm (program s)))
       (equal (len (stack s))         ; * stack right depth
              (cdr (assoc (pc s)
                          (gsm (program s)))))

       ))

; Note that it might be the case that there are no good states!  For example,
; it might be that gsm NEVER produces a stack map that csm approves.  In this
; case, all the theorems hypothesizing good-statep would be vacuously true.
; Just to establish that this is not the case, here is a theorem that shows
; that there is at least one good state!  The one I choose is non-trivial: an
; initial state for the M1 program verified in the file sum.lisp.

(defthm good-statep-is-not-always-false
  (good-statep (list 0 '(5 0) nil
                     '((ICONST 0)       ;  0
                       (ISTORE 1)       ;  1
                       (ILOAD 0)        ;  2
                       (IFEQ 10)        ;  3
                       (ILOAD 1)        ;  4
                       (ILOAD 0)        ;  5
                       (IADD)           ;  6
                       (ISTORE 1)       ;  7
                       (ILOAD 0)        ;  8
                       (ICONST 1)       ;  9
                       (ISUB)           ; 10
                       (ISTORE 0)       ; 11
                       (GOTO -10)       ; 12
                       (ILOAD 1)        ; 13
                       (HALT))))
  :rule-classes nil)
