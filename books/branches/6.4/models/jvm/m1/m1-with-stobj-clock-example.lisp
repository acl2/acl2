; Verification of Multiplication-by-Repeated-Addition
; on the Stobj Version of M1

; J Strother Moore

; To recertify:
; (include-book "m1-with-stobj")
; (certify-book "m1-with-stobj-clock-example" 1)

; Summary: The models/jvm/m1 directory contains a definition of the M1 machine
; defined in the ``constructor style.''  That is, each new state is constructed
; with makes-state which symbolically exhibits all four components of the new
; state.  An alternative style is the ``updater style'' where the state is
; ``modified'' only in the selected slots.  When single-threaded objects and
; destructive assignment are supported (see :doc stobj) this can be more
; efficient for big states.  However, use of this definitional style changes
; slightly how theorems are stated and proved.

; In the file m1-with-stobj.lisp we define M1 in the updater style and here we
; prove a program for it correct.  The program is another trivial one:
; multiplication by repeated addition.  Virtually all the constructor-style
; program proofs exhibited in models/jvm/m1 rigidly followed a certain
; template, defining such functions as ok-inputs, theta, etc.  That template
; was imposed on undergraduates taking my JVM class because it kept rules from
; interfering with each other in the hands of users who don't really understand
; how to use ACL2 rewrite rules.  In most cases the rigidity is pointless and
; here I abandon it entirely.  I do follow the basic methodology of first
; proving that the code implements an algorithm (g) and then that the algorithm
; implements multiplication, and I use clock functions.

(in-package "M1")
(set-verify-guards-eagerness 0)

(defconst *pi*
       '((ICONST 0)   ; 0
         (ISTORE 2)   ; 1  a := 0;
         (ILOAD 0)    ; 2  [loop:]
         (IFEQ 10)    ; 3  if x=0 then go to end;
         (ILOAD 0)    ; 4
         (ICONST 1)   ; 5
         (ISUB)       ; 6
         (ISTORE 0)   ; 7  x := x-1;
         (ILOAD 1)    ; 8
         (ILOAD 2)    ; 9
         (IADD)       ;10
         (ISTORE 2)   ;11  a := y+a;
         (GOTO -10)   ;12  go to loop
         (ILOAD 2)    ;13  [end:]
         (HALT)       ;14 ``return'' a
         ))

; The algorithm
(defun g (x y a)
       (if (zp x)
           a
           (g (- x 1) y (+ y a))))

; The clock
(defun loop-clk (x)
         (if (zp x)
             3
             (clk+ 11
                   (loop-clk (- x 1)))))

(defun clk (x)
         (clk+ 2
               (loop-clk x)))

; A test harness to show how we typically handle the live stobj s
(defun test-program (x y s)
         (declare (xargs :stobjs (s)))
         (let* ((s (!pc 0 s))
                (s (!loi 0 x s))
                (s (!loi 1 y s))
                (s (!stack nil s))
                (s (wr :program *pi* s)) ; I don't define (!program ...)
                (k (clk x))
                (s (m1 s k)))
           (mv `((:clk ,k)
                 (:haltedp ,(haltedp s))
                 (:tos ,(top (stack s))))
               s)))

; M1 !>(test-program 5 7 s)
; (((:CLK 60) (:HALTEDP T) (:TOS 35)) <s>)
; M1 !>(test-program 7 5 s)
; (((:CLK 82) (:HALTEDP T) (:TOS 35)) <s>)
; M1 !>(test-program 700 500 s)
; (((:CLK 7705) (:HALTEDP T) (:TOS 350000))
;  <s>)

; Define the predicate that recognizes well formed states:

(defun natp-listp (x)
       (if (endp x)
           (equal x nil)
           (and (natp (car x))
                (natp-listp (cdr x)))))

(defun good-statep (s)
       (declare (xargs :stobjs (s)))
       (and (sp s)
            (natp (rd :pc s))
            (natp-listp (rd :locals s))
            (<= 3 (len (rd :locals s)))
            (natp-listp (rd :stack s))
            (equal (rd :program s) *pi*)))

; The three lemmas below are necessary proving
; (thm (implies (and (good-statep s)
;                    (equal (pc s) 2))
;               (good-statep (m1 s 11))))

(defthm natp-listp-nth
        (implies (and (natp-listp x)
                      (natp i)
                      (< i (len x)))
                 (natp (nth i x)))
        :rule-classes (:rewrite :type-prescription))

(defthm natp-listp-update-nth
        (implies (and (natp i)
                      (< i (len x))
                      (natp (nth i x)))
                 (equal (natp-listp (update-nth i v x))
                        (and (natp v)
                             (natp-listp x)))))

(defthm natp-listp-push
       (implies (natp-listp stk)
		(equal (natp-listp (push i stk))
		       (natp i)))
       :hints (("Goal" :in-theory (enable push))))

(in-theory (disable natp-listp len nth update-nth))

; The induction hint: Note that we inductively assume the theorem for the state
; obtained by going around the loop once (11 steps from pc 2 in the non-zero
; case).

(defun hint (s)
       (declare (xargs :stobjs (s)
			:measure (acl2-count (loi 0 s))))
       (if (and (good-statep s)
		(equal (pc s) 2))
	   (if (zp (loi 0 s))
	       s
	       (let ((s (m1 s 11)))
		 (hint s)))
	   s))

; This is the crux lemma:  the proof that the loop implements g.
; But note that after proving the lemma, I store a different version of it
; as a :rewrite rule.  The difference is in how the left-hand side of
; the conclusion is written.

; lhs as proved:  (m1 s (loop-clk (loi 0 s)))
; lhs as stored:  (m1 s (loop-clk x)), where x must be equal to (loi 0 s)

; The ``as proved'' expression is suitable for proof by induction on s.  The
; ``as stored'' expression is general enough to match our intended target when
; the lemma is used to finish the proof of entry-correct below.  In that proof
; we encounter (m1 s' (loop-clk (loi 0 s))), where s' is the result of setting
; loi 2 to 0 in s.  Note that the parameter supplied to loop-clk is not
; syntactically (loi 0 s'), but is equal to it.  To really understand, just
; delete the :rule-classes entry below so loop-correct is stored as proved, and
; then proceed to the entry-correct proof and watch it fail and figure out why!

; But this general idea of proving one version and storing a syntactically
; ``more general'' one is common in stobj-style code proofs and I just follow
; the pattern: apply the clock to a new variable and require the proof that the
; value of that variable is as written in the proved version.

(defthm loop-correct
       (implies
	(and (good-statep s)
	     (equal (rd :pc s) 2))
	(equal
	 (m1 s (loop-clk (loi 0 s)))  ; ``as proved''
	 (!pc 14
	      (!loi 0 0
		    (!loi 2 (g (loi 0 s) (loi 1 s) (loi 2 s))
			  (!stack (push (g (loi 0 s)
                                           (loi 1 s)
                                           (loi 2 s))
					(stack s))
				  s))))))

       :hints (("Goal" :induct (hint s)))
       :rule-classes
       ((:rewrite
         :corollary
         (implies
          (and (good-statep s)
               (equal (rd :pc s) 2)
               (equal x (loi 0 s)))
          (equal
           (m1 s (loop-clk x))  ; ``as stored''
           (!pc 14
                (!loi 0 0
                      (!loi 2 (g (loi 0 s) (loi 1 s) (loi 2 s))
                            (!stack (push (g (loi 0 s)
                                             (loi 1 s)
                                             (loi 2 s))
                                          (stack s))
                                    s)))))))))

(in-theory (disable loop-clk))

(defthm entry-correct
(implies
 (and (good-statep s)
      (equal (pc s) 0))
 (equal
  (m1 s (clk (loi 0 s)))  ; ``as proved''
  (!pc 14
   (!loi 0 0
    (!loi 2 (g (loi 0 s) (loi 1 s) 0)
     (!stack (push (g (loi 0 s) (loi 1 s) 0)
                   (stack s))
             s))))))
:rule-classes
((:rewrite
  :corollary
  (implies
   (and (good-statep s)
        (equal (pc s) 0)
        (equal x (loi 0 s)))
   (equal
    (m1 s (clk x))  ; ``as stored''
    (!pc 14
     (!loi 0 0
      (!loi 2 (g (loi 0 s) (loi 1 s) 0)
       (!stack (push (g (loi 0 s) (loi 1 s) 0)
                     (stack s))
               s)))))))))

(in-theory (disable clk))

; Now we prove that the algorithm g is multiplication.

(defthm lemma
       (implies (and (natp x) (natp y) (natp a))
                (equal (g x y a)
                       (+ a (* x y)))))

(defthm algorithm-implements-spec
       (implies (and (natp x) (natp y))
                (equal (g x y 0)
                       (* x y))))

; And then we wrap it all up to our ``advertised'' result:

(defthm main-goal
       (implies (and (good-statep s)
                     (equal (pc s) 0)
                     (equal sf (m1 s (clk (loi 0 s)))))
                (and (haltedp sf)
                     (equal (top (stack sf))
                            (* (loi 0 s)
                               (loi 1 s)))))
       :rule-classes nil)


