;(include-book "m1")
;(certify-book "theorems-a-and-b" 1)
(in-package "M1")

(include-book "tmi-reductions")
(include-book "implementation")

; The tmi-reductions book contains a theorem establishing that the function
; TMI, as defined in the Boyer-Moore paper, "A Mechanical Proof of the Turing
; Completeness of Pure Lisp," is equivalent (modulo the representation of
; tapes) to an algorithm named tmi3 implementable on M1.  The implementation
; book defines an M1 program (PI) and various schedules and proves that (PI)
; implements tmi3.

; For what it's worth: proof-1 required 160 defthms.  This proof requires 138,
; mainly because defsys handles almost all of the implementation.lisp proofs.
; I also cleaned up the theorem A and B proofs a bit.

; In the Boyer-Moore paper, "A Mechanical Proof of the Turing Completeness of
; Pure Lisp" we prove two things: about a computational paradigm emulating a
; Turing machine.

; (a) If the Turing machine runs forever, then the emulator runs forever.
; This theorem is stated in its contrapositive form:  if the emulator halts
; then the Turing machine halts.

; (b) If the Turing machine halts with tape tape, then the emulator halts with
; the same tape (modulo representation).

; Outline:

; Both of these theorems depend on a stronger Simulation Theorem that precisely
; relates running (PI) and TMI.  So our first goal below is to prove the
; Simulation Theorem.  Theorem B follows immediately from the Simulation
; Theorem.  Theorem A, however, requires a little more work: we have to define
; a clock function that converts a schedule (under which the M1 emulator halts)
; to a clock (under which TMI halts).  The definition of this conversion
; function depends crucially on the Monotonicity property of the M1 schedule
; function used in the Simulation Theorem: TMI doesn't halt, then the schedule
; for n+1 steps is greater than the schedule for n steps.  Given Monotonicity,
; we can find an appropriate clock by searching upwards for ever greater
; clocks, knowing that the corresponding schedule gets longer and longer and
; that eventually it will exceed the length of the schedule that makes M1 halt.

; So our subgoals are: The Simulation Theorem, Monotonicity, Theorem A, and,
; finally, Theorem B.

; Convention on Clocks and Schedules

; Both tmi and run are ``non-terminating'' interpreters that have had
; artificial means imposed upon them to insure (abnormal) termination.  For tmi
; the artificial means is a number that is decreased every time tmi recurs.
; When abnormal termination occurs, tmi returns nil; normal termination is
; indicated by returning the final tape, a cons.  We call the number
; controlling tmi a ``clock.''

; For M1's run the artificial means is a list that is cdr'd every time run
; recurs.  Abnormal termination is indicated by returning an M1 state that is
; not HALTed, by which we mean the next-inst in the returned state is something
; other than a HALT instruction.  Normal termination is indicated by returning
; a state in which the next instruction is HALT.  We call the list controlling
; run a ``thread schedule'' (in preparation for the eventual addition of
; threads to the model).  But because M1's run isn't sensitive to the ``thread
; identifier'' listed in its schedule -- it always steps the only thread -- we
; can convert an M1 schedule to a ``clock,'' a number that determines how long
; the schedule is.  The typical idiom for applications of run will be (run
; (repeat 'tick <clock>) s), where <clock> is a numeric expression.

; Our two theorems, A and B involve clocks.

; A: If run halts normally in so many clock ticks, then there exists a clock
; that makes tmi halt normally.

; B: If tmi halts normally in so many clock ticks, then there exists a clock
; that makes run halt normally and return the ``same'' tape.

; We thus talk about 4 clocks and we adopt the following naming conventions, by
; restating A and B in terms that explicitly identify the symbol we will use
; for each clock:

; A: If run halts normally in i clock ticks, then there exists a j
; that makes tmi halt normally.

; B: If tmi halts normally in n clock ticks, then there exists a k
; that makes run halt normally and return the ``same'' tape.

; Summarizing our clock naming conventions:
; i -- the number of steps run takes to halt in the hypothesis of theorem A
; j -- the number of steps tmi takes to halt in the conclusion of theorem A
; n -- the number of steps tmi takes to halt in the hypothesis of theorem B
; k -- the number of steps run takes to halt in the conclusion of theorem B

; Note that j is actually a function of i:  given i, there exists a j.
; Note that k is actually a function of n:  given n, there exists a k.

; So while i and n are variable symbols, j and k are function symbols in our
; quantifier-free setting.

; The Simulation Theorem

(defun psi-clock (st tape pos tm w nnil n)
  (clk+ 2
      (main-clock nil st tape pos tm w nnil n)))

; Our goal is to express precisely the relationship between TMI and an m1 run of
; the M1 system (PSI).  We take it in steps.  First, we express the relationship
; between an m1 run of (PSI) and tmi3.  Then we move to TMI terms by applying the
; functions that re-represent Turing machines and tapes.

(defthm tmi3-simulation
  (implies (and (natp st)
                (natp tape)
                (natp pos)
                (natp tm)
                (natp w)
                (equal nnil (nnil w))
                (< st (expt 2 w)))
           (equal
            (m1 (make-state 0
                             '(0 0 0 0 0 0 0 0 0 0 0 0 0)
                             (push nnil
                                   (push w
                                         (push tm
                                               (push pos (push tape (push st nil))))))
                             (psi))
                 (psi-clock st tape pos tm w nnil n))

            (let ((s (make-state
                      *main*
                      '(0 0 0 0 0 0 0 0 0 0 0 0 0)
                      (push 2
                            (push nnil
                                  (push w
                                        (push tm
                                              (push pos (push tape (push st nil)))))))
                      (psi))))
              (if
               (equal (mv-nth 0 (tmi3 st tape pos tm w n))
                      0)
               (make-state
                *tmi3-loop*
                (main-final-locals nil st tape pos tm w nnil n s)
                (main-final-stack nil st tape pos tm w nnil n s)
                (psi))
               (make-state
                2
                (update-nth*
                 0
                 '(0 0 0 0 0 0)
                 (main-final-locals nil st tape pos tm w nnil n s))
                (push
                 (mv-nth 3 (tmi3 st tape pos tm w n))
                 (push
                  (mv-nth 2 (tmi3 st tape pos tm w n))
                  (push (mv-nth 1 (tmi3 st tape pos tm w n))
                        (push (mv-nth 0 (tmi3 st tape pos tm w n))
                              nil))))
                (psi)))))))

(in-theory (disable psi-clock))

; I am not convinced the following theorem is sufficient for Theorem A.  But let's go with it
; and see what happens.

(defthm integerp-mv-nth-convert-tape-to-tapen-pos
  (implies (tapep tape)
           (and (integerp (mv-nth 0 (convert-tape-to-tapen-pos tape)))
                (integerp (mv-nth 1 (convert-tape-to-tapen-pos tape)))))
  :hints (("Goal" :in-theory (enable acl2::mv-nth convert-tape-to-tapen-pos tapep)))
  :rule-classes :rewrite)  ;I'd settle for :tau-system if it were used in backchaining!

(defthm nonneg-mv-nth-convert-tape-to-tapen-pos
  (implies (tapep tape)
           (and (<= 0 (mv-nth 0 (convert-tape-to-tapen-pos tape)))
                (<= 0 (mv-nth 1 (convert-tape-to-tapen-pos tape)))))
  :hints (("Goal" :in-theory (enable acl2::mv-nth convert-tape-to-tapen-pos tapep)))
  :rule-classes :linear)

(defthm positive-natp-ncode-rewrite-version
  (implies (and (natp w)
                (turing1-machinep tm w))
           (and (integerp (ncode tm w))
                (< 0 (ncode tm w)))))

(in-theory (disable tmi2-is-tmi1 tmi3-is-tmi2 renaming-map properties-of-instr))

; We disable the intermediate tmi theorems because they rewrite TMI3.  We
; disable RENAMING-MAP otherwise (cdr (assoc st (renaming-map st tm))) becomes
; 0 and doesn't allow the assoc expression in m1-psi-is-tmi below to match the
; corresponding one in the theorem tmi3-is-tmi.  We disable properties-of-instr
; because it (stupidly) FORCEs turing1-machinep when we need to stay at the
; turing-machinep level.

; We really ought to know these tau-like theorems:

(defthm tapep-new-tape
  (implies (and (tapep tape)
                (operationp op))
           (tapep (new-tape op tape)))
  :hints (("Goal" :in-theory (enable tapep new-tape))))

(defthm operationp-nth-2-instr
  (implies (and (turing-machinep tm)
                (instr st current-sym tm))
           (operationp (nth 2 (instr st current-sym tm))))
  :hints (("Goal" :in-theory (disable properties-of-instr)))) ; <--- forces turing1-machinep!

(defthm symbolp-nth-3-instr
  (implies (and (turing-machinep tm)
                (instr st current-sym tm))
           (symbolp (nth 3 (instr st current-sym tm)))))

(defthm tapep-tmi
  (implies (and (symbolp st)
                (tapep tape)
                (turing-machinep tm)
                (tmi st tape tm n))
           (tapep (tmi st tape tm n))))

#|
(defthm run-repeat
  (equal (run (repeat 'tick (len sched)) s)
         (run sched s))
  :hints (("Goal" :in-theory (enable run))))
|#

(defun find-k (st tape tm n)
  (let* ((map (renaming-map st tm))
         (st-prime (cdr (assoc st map)))
         (tape-prime (mv-nth 0 (mv-list 2 (convert-tape-to-tapen-pos tape))))
         (pos-prime (mv-nth 1 (mv-list 2 (convert-tape-to-tapen-pos tape))))
         (w (max-width tm map))
         (tm-prime (ncode (tm-to-tm1 tm map) w)))
    (psi-clock st-prime tape-prime pos-prime tm-prime w (nnil w) n)))

(defthm simulation
  (implies (and (symbolp st)
                (tapep tape)
                (turing-machinep tm))
           (let* ((map (renaming-map st tm))
                  (st-prime (cdr (assoc st map)))
                  (tape-prime (mv-nth 0 (convert-tape-to-tapen-pos tape)))
                  (pos-prime (mv-nth 1 (convert-tape-to-tapen-pos tape)))
                  (w (max-width1 (tm-to-tm1 tm map)))
                  (nnil (nnil w))
                  (tm-prime (ncode (tm-to-tm1 tm map) w))
                  (s-final
                   (m1 (make-state 0
                                    '(0 0 0 0 0 0 0 0 0 0 0 0 0)
                                    (push nnil
                                          (push w
                                                (push tm-prime
                                                      (push pos-prime
                                                            (push tape-prime
                                                                  (push st-prime nil))))))
                                    (psi))
                        (find-k st tape tm n))))
             (and (iff (equal (next-inst s-final) '(HALT))
                       (tmi st tape tm n))
                  (implies (tmi st tape tm n)
                           (equal (decode-tape-and-pos
                                   (top (pop (stack s-final)))
                                   (top (stack s-final)))
                                  (tmi st tape tm n))))))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable find-k next-inst))

(defun ncode-st (st map)
  (cdr (assoc st map)))

(defun ncode-tm (tm map w)
  (ncode (tm-to-tm1 tm map) w))

(defun ncode-tape (tape)
  (mv-let (tapen pos)
          (convert-tape-to-tapen-pos tape)
          (declare (ignore pos))
          tapen))

(defun ncode-pos (tape)
  (mv-let (tapen pos)
          (convert-tape-to-tapen-pos tape)
          (declare (ignore tapen))
          pos))

(defmacro with-conventions (term)
  `(let* ((map (renaming-map st tm))
          (w (max-width tm map))
          (nnil (nnil w))
          (st^prime (ncode-st st map))
          (tm^prime (ncode-tm tm map w))
          (tape^prime (ncode-tape tape))
          (pos^prime (ncode-pos tape))
          (s_0 (make-state 0
                           '(0 0 0 0 0 0 0 0 0 0 0 0 0)
                           (push* nnil w tm^prime pos^prime tape^prime st^prime nil)
                           (Psi))))
     (implies (and (symbolp st) (tapep tape) (turing-machinep tm))
              ,term)))


(defthm theorem-b
  (with-conventions
   (implies (and (natp n)
                 (tmi st tape tm n))
            (let ((s_f (M1 s_0 (find-k st tape tm n))))
              (and (haltedp s_f)
                   (equal (decode-tape-and-pos
                           (top (pop (stack s_f)))
                           (top (stack s_f)))
                          (tmi st tape tm n)))))))

; Now we turn to Theorem A.  Recall that here we have a clock i at which m1
; halts normally and wish to exhibit a j at which tmi halts normally.  We find
; j by searching up from 0.  For each value of j, see if tmi halts normally.
; If not, increment j by 1 and repeat.  Why does this search terminate?
; Consider (find-k ... j), i.e., the clock for m1 corresponding to the current j.
; We know by the Simulation theorem tmi halts (or not) at j iff m1 halts at (find-k
; ... j).  So if tmi is not halted at j, then m1 is not halted at (find-k ...j).
; But eventually, (find-k ...j) exceeds i, the time at which m1 does halt.  Why do
; we know (find-k ...j) will eventually exceed i?  Because k is monotonic: as j
; increases, k increases, provided tmi has not halted.  Note that we are also
; relying on the fact that once m1 halts normally it stays halted, i.e., if
; m1 is halted at i then it is halted at k if i <= k.  So we can bound the
; search for j by looking until i <= (find-k ...j).
;

; So we prove Monotonicity next, then prove that m1 stays halted, then define
; the search mechanism for j, and then prove theorem a.

#|
(defthm len-repeat
  (equal (len (repeat x n))
         (nfix n)))
|#

(in-theory (enable binary-clk+))

(defthm k-non-0
  (implies (and (natp st)
                (natp tape)
                (natp pos)
                (natp tm)
                (natp w)
                (not (zp n)))
           (< 0 (find-k st tape tm n)))
  :hints (("Goal" :in-theory (enable find-k psi-clock)))
  :rule-classes :linear)

; The first problem with monotonicity is that at the level of k it is about
; main-clock, main-loop-clock, tmi3-clock, and tmi3-loop-clock.  But all the
; action is happening at tmi3-loop-clock, where the computation actually hangs.
; So I first prove that tmi3-loop-clock is monotonic and then raise that result
; up through the others.


(defun tmi3-trace (st tape pos tm w n)
  (declare (xargs :measure (acl2-count n)))
  (cond ((zp n)
         nil)
        ((equal (ninstr st (current-symn tape pos) tm w) -1)
         (list (list t st tape pos)))
        (t
         (cons (list nil st tape pos)
               (mv-let (new-tape new-pos)
                       (new-tape2 (nop (ninstr st (current-symn tape pos) tm w) w) tape pos)
                       (tmi3-trace (nst-out (ninstr st (current-symn tape pos) tm w) w)
                                   new-tape
                                   new-pos
                                   tm
                                   w
                                   (- n 1)))))))

(defun k-halt (st tape pos tm w)
  (CLK+ 5
        (CLK+ (CURRENT-SYMN-CLOCK '(1 0 0 14)
                                  TAPE POS)
              (CLK+ 5
                    (CLK+ (NINSTR1-CLOCK '(0 0 14)
                                         ST (!CURRENT-SYMN TAPE POS)
                                         TM W (NNIL w))
                          7)))))
(defun k-step (st tape pos tm w)
  (CLK+
   5
   (CLK+
    (CURRENT-SYMN-CLOCK '(1 0 0 14)
                        TAPE POS)
    (CLK+
     5
     (CLK+
      (NINSTR1-CLOCK '(0 0 14)
                     ST (!CURRENT-SYMN TAPE POS)
                     TM W (NNIL W))
      (CLK+
       8
       (CLK+
        (CURRENT-SYMN-CLOCK '(1 0 0 2 14)
                            TAPE POS)
        (CLK+
         5
         (CLK+
          (NINSTR1-CLOCK '(0 0 2 14)
                         ST (!CURRENT-SYMN TAPE POS)
                         TM W (NNIL W))
          (CLK+
           3
           (CLK+
            (NST-OUT-CLOCK
             '(0 2 14)
             (!NINSTR1 ST (!CURRENT-SYMN TAPE POS)
                       TM W (NNIL W))
             W)
            (CLK+
             5
             (CLK+
              (CURRENT-SYMN-CLOCK '(1 0 0 1 2 14)
                                  TAPE POS)
              (CLK+
               5
               (CLK+
                (NINSTR1-CLOCK '(0 0 1 2 14)
                               ST (!CURRENT-SYMN TAPE POS)
                               TM W (NNIL W))
                (CLK+
                 3
                 (CLK+
                  (NOP-CLOCK
                   '(0 1 2 14)
                   (!NINSTR1 ST (!CURRENT-SYMN TAPE POS)
                             TM W (NNIL W))
                   W)
                  (CLK+
                   4
                   (CLK+
                    (NEW-TAPE2-CLOCK
                     '(1 2 14)
                     (!NOP
                      (!NINSTR1 ST (!CURRENT-SYMN TAPE POS)
                                TM W (NNIL W))
                      W)
                     TAPE POS)
                    10)))))))))))))))))))

(defun k* (trace tm w)
  (if (endp trace)
      0
      (if (car (car trace))
          (k-halt (nth 1 (car trace))
                  (nth 2 (car trace))
                  (nth 3 (car trace))
                  tm w)
          (+ (k-step (nth 1 (car trace))
                     (nth 2 (car trace))
                     (nth 3 (car trace))
                     tm w)
             (k* (cdr trace) tm w)))))

(defthm tmi3-loop-clock-is-k*
  (implies (and (natp st)
                (natp tape)
                (natp pos)
                (natp tm)
                (natp w)
                (< st (expt 2 w)))
           (equal (tmi3-loop-clock st tape pos tm w (nnil w) n)
                  (k* (tmi3-trace st tape pos tm w n) tm w)))
  :hints (("Goal" :in-theory (enable tmi3-loop-clock))
          ("Subgoal *1/10'" :expand (TMI3-LOOP-CLOCK ST TAPE POS TM W (NNIL W) N))))

(defthm positive-k-halt
  (and (integerp (k-halt st tape pos tm w))
       (< 0 (k-halt st tape pos tm w)))
  :rule-classes :type-prescription)

(defthm positive-k-step
  (and (integerp (k-step st tape pos tm w))
       (< 0 (k-step st tape pos tm w)))
  :rule-classes :type-prescription)

(in-theory (disable k-halt k-step))

(defthm positive-k*
  (implies (consp x)
           (< 0 (k* x tm w)))
  :rule-classes :linear)

; -----------------------------------------------------------------

(defthm trace-extension
  (implies (and (natp n)
                (equal (mv-nth 0 (tmi3 st tape pos tm w n)) 0))
           (equal (tmi3-trace st tape pos tm w (+ 1 n))
                  (append (tmi3-trace st tape pos tm w n)
                      (mv-let (flg st1 tape1 pos1)
                              (tmi3 st tape pos tm w n)
                              (declare (ignore flg))
                              (list (list (EQUAL (NINSTR ST1 (CURRENT-SYMN tape1 pos1) TM W)
                                                 -1)
                                          st1 tape1 pos1)))))))


(defun tracep (x)
  (cond ((endp x) t)
        ((car (car x)) (endp (cdr x)))
        (t (tracep (cdr x)))))

(defthm tracep-tmi3-trace
  (tracep (tmi3-trace st tape pos tm w n)))

(defthm k*-append
  (implies (tracep (append a b))
           (equal (k* (append a b) tm w)
                  (+ (k* a tm w) (k* b tm w)))))

(defthm tracep-append
  (equal (tracep (append a b))
         (if (tracep a)
             (if (car (car (last a)))
                 (endp b)
                 (tracep b))
             nil)))

(defthm tmi3-v-last-tmi3-trace
  (implies (and (integerp n)
                (<= 0 n)
                (force (equal 0 (mv-nth 0 (tmi3 st tape pos tm w n)))))
           (not (car (car (last (tmi3-trace st tape pos tm w n))))))
  :hints (("Goal" :in-theory (enable tmi3))))

(defthm k*-tmi3-trace-monotonic
  (implies (and (natp n)
                (equal (mv-nth 0 (tmi3 st tape pos tm w n))
                       0))
           (< (k* (tmi3-trace st tape pos tm w n) tm w)
              (k* (tmi3-trace st tape pos tm w (+ n 1)) tm w)))
  :rule-classes :linear)

(defthm final-tmi3-state-is-proper
  (implies (and (natp st)
                (natp tape)
                (natp pos)
                (natp tm)
                (natp w)
                (< st (expt 2 w)))
           (and (natp (mv-nth 1 (tmi3 st tape pos tm w n)))
                (< (mv-nth 1 (tmi3 st tape pos tm w n)) (expt 2 w))))
  :rule-classes
  ((:linear :corollary
            (implies (and (natp st)
                          (natp tape)
                          (natp pos)
                          (natp tm)
                          (natp w)
                          (< st (expt 2 w)))
                     (and (<= 0 (mv-nth 1 (tmi3 st tape pos tm w n)))
                          (< (mv-nth 1 (tmi3 st tape pos tm w n)) (expt 2 w)))))
   (:rewrite
    :corollary
    (implies (and (natp st)
                  (natp tape)
                  (natp pos)
                  (natp tm)
                  (natp w)
                  (< st (expt 2 w)))
             (integerp (mv-nth 1 (tmi3 st tape pos tm w n)))))))

(defthm acl2-numberp-cdr-assoc-equal-st-renaming-map-st
  (acl2-numberp (CDR (ASSOC-EQUAL ST (RENAMING-MAP ST TM))))
  :hints (("Goal" :in-theory (enable renaming-map))))

(defthm find-k-monotonic
  (implies (and (symbolp st)
                (tapep tape)
                (turing-machinep tm)
                (natp n)
                (force (not (tmi st tape tm n))))
           (< (find-k st tape tm n)
              (find-k st tape tm (+ 1 n))))
  :hints (("Goal" :do-not-induct t
                  :in-theory (e/d (find-k psi-clock main-clock main-loop-clock tmi3-clock)
                                  (turing1-4-tuple)
                                  )))
  :rule-classes :linear)

(defthm 0<-find-k
  (< 0 (find-k st tape tm n))
  :hints (("Goal" :in-theory (enable find-k psi-clock))))

(defun find-j1 (st tape tm i j)

  (declare (xargs :measure (nfix (- (+ 1 (nfix i))
                                    (find-k st tape tm j)))
                  :otf-flg t))
  (if (and (symbolp st)
           (tapep tape)
           (turing-machinep tm)
           (natp i)
           (natp j))
      (if (equal (tmi st tape tm j) nil)
          (if (<= i (find-k st tape tm j))
              j
              (find-j1 st tape tm i (+ 1 j)))
          j)
      0))

(defun find-j (st tape tm i)
  (find-j1 st tape tm i 0))

; The crucial property of find-j1 is that it either returns a j
; that makes tmi halt or else an j whose k is greater than i.

(defthm crucial-property-of-find-j1
  (implies (and (symbolp st)
                (tapep tape)
                (turing-machinep tm)
                (natp i)
                (natp j))
           (or (tmi st tape tm (find-j1 st tape tm i j))
               (<= i (find-k st tape tm
                             (find-j1 st tape tm i j)))))
  :rule-classes nil)

; Now we work on the M1 Stays Halted theorem.

(defthm program-step
  (equal (program (step s))
         (program s))
  :hints (("Goal" :in-theory (enable step))))

(defthm program-m1
  (equal (program (m1 s a))
         (program s))
  :hints (("Goal" :in-theory (enable m1))))

(defthm m1-stays-halted
  (implies (equal (next-inst s) '(HALT))
           (equal (m1 s clock) s))
  :hints (("Goal" :induct (m1 s clock)
           :in-theory (enable m1 step))))

;(defun run-repeat-hint (k s)
;  (if (zp k)
;      s
;      (run-repeat-hint (- k 1) (step s))))

(defthm m1-stays-halted-clk+-version
  (implies (equal (next-inst (m1 s a)) '(HALT))
           (equal (m1 s (clk+ a b))
                  (m1 s a)))
  :hints (("Goal" :in-theory (disable binary-clk+))))

#|
(defthm ap-repeat
  (implies (and (natp i)
                (natp j))
           (equal (clk+ (repeat 'tick i)
                      (repeat 'tick j))
                  (repeat 'tick (+ i j)))))
|#

(defthm m1-stays-halted-repeat-version
  (implies (and (<= i k)
                (natp i)
                (natp k)
                (equal (next-inst (m1 s i)) '(HALT)))
           (equal (m1 s k)
                  (m1 s i)))
  :hints (("Goal" :use (:instance m1-stays-halted-clk+-version
                                  (a i)
                                  (b (- k i)))
           :do-not-induct t
           :in-theory (disable m1-clk+ m1-stays-halted-clk+-version)))
  :rule-classes nil)

(in-theory (disable find-j1))

(defthm theorem-a
  (with-conventions
   (implies (natp i)
            (let ((s_f (m1 s_0 i)))
              (implies
               (haltedp s_f)
               (tmi st tape tm (find-j st tape tm i))))))

; Proof: Let s-init be the initial M1 state above.  (m1
; s-init i) terminates.  find-j1 marches up from 0 looking for a j that makes tmi
; halt.  If it finds it we're done.  Otherwise, it eventually finds a j such
; tmi doesn't halt but (find-k .... j) exceeds i.  That's a contradiction because if
; tmi doesn't halt at j then M1 doesn't halt at (find-k ... j), by the Simulation
; theorem and the fact that M1 stays halted.  Q.E.D.

  :hints (("Goal" :do-not-induct t
           :use ((:instance crucial-property-of-find-j1 (j 0))
                 (:instance m1-stays-halted-repeat-version
                            (i i)
                            (k (find-k st tape tm (find-j1 st tape tm i 0)))
                            (s (MAKE-STATE
                                0 '(0 0 0 0 0 0 0 0 0 0 0 0 0)
                                (PUSH
                                 (NNIL (MAX-WIDTH TM (RENAMING-MAP ST TM)))
                                 (PUSH
                                  (MAX-WIDTH TM (RENAMING-MAP ST TM))
                                  (PUSH
                                   (NCODE (TM-TO-TM1 TM (RENAMING-MAP ST TM))
                                          (MAX-WIDTH TM (RENAMING-MAP ST TM)))
                                   (PUSH (ACL2::MV-NTH 1 (CONVERT-TAPE-TO-TAPEN-POS TAPE))
                                         (PUSH (ACL2::MV-NTH 0 (CONVERT-TAPE-TO-TAPEN-POS TAPE))
                                               (PUSH (CDR (ACL2::ASSOC-EQUAL ST (RENAMING-MAP ST TM)))
                                                     NIL))))))
                                (PSI))))))))

; Revision


(defun down (st tape tm)
; Down is a computable function.
  (let* ((map (renaming-map st tm))
         (st-prime (cdr (assoc st map)))
         (tape-prime (mv-nth 0 (mv-list 2 (convert-tape-to-tapen-pos tape))))
         (pos-prime (mv-nth 1 (mv-list 2 (convert-tape-to-tapen-pos tape))))
         (w (max-width tm map))
         (nnil (nnil w))
         (tm-prime (ncode (tm-to-tm1 tm map) w)))
    (make-state 0
                '(0 0 0 0 0 0 0 0 0 0 0 0 0)
                (push nnil
                      (push w
                            (push tm-prime
                                  (push pos-prime
                                        (push tape-prime
                                              (push st-prime nil))))))
                (psi))))

(defun up (s)
  (DECODE-TAPE-AND-POS (TOP (POP (STACK s)))
                       (TOP (STACK s))))

(defthm a
  (implies
   (and (symbolp st)
        (tapep tape)
        (turing-machinep tm)
        (natp i))
   (let ((s_f (m1 (down st tape tm) i)))
     (implies (haltedp s_f)
              (tmi st tape tm (find-j st tape tm i)))))
  :hints (("Goal" :use theorem-a :in-theory (disable theorem-a) :do-not-induct t))
  :rule-classes nil)

(defthm b
  (implies (and (symbolp st)
                (tapep tape)
                (turing-machinep tm)
                (tmi st tape tm n))
           (let ((s_f (m1 (down st tape tm)
                          (find-k st tape tm n))))
             (and (haltedp s_f)
                  (equal (up s_f)
                         (tmi st tape tm n)))))
  :rule-classes nil)



