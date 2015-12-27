#|
The Apprentice Example

J Strother Moore and George Porter

Roughly speaking, we prove that a certain Java class file implements a
monotonically increasing counter.  The counter is the subject of
contention by an unbounded number of threads.  To insure monotonicity,
the threads achieve mutually exclusive access to the counter, using
synchronized blocks.   Here is the Java

class Container {
    public int counter;
}

class Job extends Thread {
    Container objref;

    public Job incr () {
        synchronized(objref) {
            objref.counter = objref.counter + 1;
	}
        return this;
    }

    public void setref(Container o) {
        objref = o;
    }

    public void run() {
        for (;;) {
            incr();
	}
    }
}

class Apprentice {
    public static void main(/*String[] args*/) {

        Container container = new Container();

        for (;;) {
            Job job = new Job();
            job.setref(container);
            job.start();
	}
    }
}

We translated this file into the bytecode supported by our M5 model of
the JVM.  The translation is the value of the ACL2 constant *a0* declared
below.  We then proved:

(defthm monotonicity
  (let* ((s1 (run sched *a0*))
         (s2 (step th s1)))
    (implies (not (equal (counter s1) nil))
             (or (equal (counter s1)
                        (counter s2))
                 (equal (int-fix (+ 1 (counter s1)))
                        (counter s2))))))

It may be read as follows.  Let s1 be a JVM state obtained by running
*a0* under an arbitrarily long schedule of interleaved steps by
arbitrary threads.  Think of s2 as the successor state to s1 obtained
by stepping an arbitrary thread th once.  Then if the counter in s1 is
non-null, it and the counter in s2 are related by a predicate named
rel.  Rel holds between two things if either they are the same or else
the second is the result of incrementing the first (in 32-bit
arithmetic).  Roughly speaking, this says the counter increases weakly
monotonically.

Provision must be made for the null value of the counter because the
Container object holding the counter is not yet allocated in *a0*.  It
may remain unallocated for an arbitrary number of thread steps (since
sched may call for the stepping of non-existent or unscheduled
threads).  The Container is not allocated until thread 0 has been
stepped once.

Proof of Monotonicity:

Suppose (good-state s) is a predicate with the following three
properties:

[1] (good-state *a0*)
[2] (good-state s) -> (good-state (step th s))
[3] (good-state s) -> (or (equal (counter s) nil)
                          (rel (counter s)
                               (counter (step th s))))

Then it is easy to get:

[4] (good-state (run sched *a0*))  {by induction, [1], and [2]}

[5] Monotonicity                  {by [3] and [4]}

Q.E.D.

The key is thus the definition of good-state to have properties
[1]-[3].  The proof of [1] will be by computation.

[2] and [3] will be proved in three parts, each, (a) th = 0, (b)
scheduled th such that 1 <= th <= (- (len (heap s)) 9), (c)
unscheduled th.  We will then prove a case analysis that shows
(a)-(b)-(c) are exhaustive.

To prove these we will use staged simplification.

(a) expand (good-state s) in the hypothesis so as to develop each of
    the possible cases.

(b) when that stabilizes for a given case, expand (step th s) to
    symbolically compute the next state for the case in question.

(c) when the next state is stable, expand the good-state predicate on
    and see that it is t.

Unguided expansion just blows up.

History:

The project started with the M4 model of the JVM.  Initially, the
example only had three threads: the main method and two Jobs.  That
was completed on Sep 30, 2000.  Then we changed it to the unbounded
thread version.  That was completed for the first time on Oct 7, 2000.
The proof was cleaned up and presented in the first version of our
paper on this subject, which is /v/hank/v104/text/m4/proofs.tex.
Indeed, all of the m4 work on this example is on the directory above.

In June and July, 2001, George created M5 and the jvm2acl2 tool.  The
Java above was mechanically translated to ACL2 on July 12, 2001.  The
proof here was finished on July 15, 2001.  The key part of the proof
-- the good-state invariant -- was hand-translated by Moore from the
M4 version to the M5 version.  The proof was then hand-translated and
re-certified.

The comments below are historical and concern the original M4 2-Job
version.

 George wrote M4 and the system below.  He then made
 several useful suggestions for simplifying his original code.  The most
 important was to rearrange the code sequence
    (load job1)
    (invokevirtual "Job" "start:()V" 0)
    (load job2)
    (invokevirtual "Job" "start:()V" 0)
 to
    (load job2)
    (load job1)
    (invokevirtual "Job" "start:()V" 0)
    (invokevirtual "Job" "start:()V" 0)
 In retrospect this is not a big deal and could be easily dealt with.
 But at the time I was doing the proof I just couldn't stand the
 idea of carrying more invariants further into the ``pre-*s1*'' state.

 Pete helped me clarify my thoughts after three days of struggle.  He
 also contributed the idea of using computation to define the
 invariant.  I didn't use his idea as fully here as he thinks it could
 be used, but I used it to great and beneficial effect in the
 ``bootstrapping'' proof here, i.e., in proving that the first 25
 states are ok.

Timesheet on the 2-Job Version: I started on this task on Saturday,
Sep 23.  I spent two and a half frustrating days before asking Pete
and George for some time together.  My problem was that I had tried to
tackle the good-state invariant without wanting to say everything I
actually knew.  I should have known better.  On Monday night I didn't
work on it.  On Tuesday I taught and started defining good-state as it
exists below.  I completed good-state on Wednesday and began exploring
ways to control the proof of the good-state invariance through step.
The work I did on Wednesday was largely irrelevant because I had not
seen the simplicity of doing a case for each of th=0,1,2, and other.
I was proving many theorems about parts of good-state.  On Thursday
and Friday I was with Legato.  On Friday night I saw to do the th case
split and I also figured out the very first ``staged simplification''
hack based on a bogus elim lemma and its use to trigger a rewrite
rule.  On Saturday Sep 30, I got the proof done, working about 8
hours.  I presented the 2-Job proof to the ACL2 research seminar on
Wednesday, Oct 4.

At that seminar it became clear that the 2-Job version could yield to
a finite state exploration.  In fact, Pete used ACL2 to prove the
2-Job version within a day or two of when I did, above.  At the
seminar I realized that an unbounded number of threads would not be
significantly harder.  Indeed, I had by then gotten a clear view of
the big picture.

Therefore, on Saturday, Oct 7, I worked several hours on it, while
also working on other things.  On Sunday, Oct 8, I spent another 6
hours and finished.

The next time I turned my attention to this problem was July 12, 2001,
after George showed me jvm2acl2.  But by serendipity, I had that week
implemented computed hints and the :comptuted-hint-replacement feature
by which staged simplification could be more directly programmed as a
hint.

Not much was done on the proof until the evening of Friday, July 13,
when I worked about 8 hours on it.  No real problems were encountered
but it took me many hours to get my head into M5.  In addition, the
programs had changed some because they were now exactly as produced by
Sun's Javac; they contain some dead code and other oddities.  The
presence of the constructor methods, <init>, greatly complicated the
main thread -- the stack in that thread can be four frames deep now.
Some method bodies are identical so it is no longer possible to tell
which frame is which merely by looking at the program.  But the
biggest problem for me to grapple with was the presence in the heap of
representatives of all the classes.  In the simpler n-Job version,
thread i was represented by at heap address i.  This was a fortunate
simplification that permitted me not to distinguish thread numbers
from heap addresses.  But in the new version, thread i is allocated to
the object at heap address i+8.  I had to hand-translate all the
theorems, distinguishing thread numbers from heap addresses.  I got
this down pat by Friday evening and was making good progress at
working my way through the script.

But on Saturday I made a mistake and accidentally strengthened the
a hypothesis of [2b] from

                (<= th (- (len (heap s)) 9))

to
                (< th (- (len (heap s)) 9))

After working about 8 hours on Saturday I was trying to put everything
together and things were not working.  I did not realize why until I
had struggled with it for another 3 hours!  Once I fixed [2b], I got
the good-state invariant proved and spent about 2 hours thinking about
what I wanted the main theorem (monotonicity) to be.  On Sunday, I
proved it after about an hour's work.

----------------------------------------------------------------------------

; Comments on Proof Management.


; These proofs generate many megabytes of output.  Emacs has a serious
; limit of 100MB on buffer size and it is easy in the course of a
; day's work to exceed that with this exercise.  I periodically delete
; old Emacs text from the top region of the buffer, using, e.g.,
;  meta 10000000 ctrl-d
; so as not to put it in the kill ring.

; I sometimes divert output to foo.log and use
;   /u/moore/bin/watchlog foo.log
; to observe it in another buffer.  To get the diversion stuff, do

(include-book
 "watchlog")
(acl2::divert)
...
(acl2::undivert)
; But diversions are not allowed in certified books.  Furthermore,
; if you are diverting output, you cannot use proof trees.

; I tend to use proof trees to watch these proofs during development.
; However you cannot divert output to foo.log and use proof trees, so
; undivert.

; To use proof trees, do
; meta-x start-proof-tree

(start-proof-tree)
...
(stop-proof-tree)

; Here is the standard ld command to load the file skipping proofs.
(ld (cons '(include-book
            "m5")
          "apprentice.lisp")
    :ld-pre-eval-print t :ld-skip-proofsp t)

; Here is how to load it and ship proofs to a log file.
(ld (cons '(include-book
            "m5")
          "apprentice.lisp")
    :ld-pre-eval-print t
    :standard-co "apprentice.log"
    :proofs-co   "apprentice.log")

; Here is how to certify and keep a log file.
(ld '((include-book
       "m5")
      (certify-book "apprentice" 1))
    :standard-co "apprentice.log"
    :proofs-co   "apprentice.log"
    :ld-pre-eval-print t)


JSM
Sun Jul 15 14:17:26 2001
|#

(in-package "M5")
(include-book "classes/Apprentice")
(include-book "classes/Container")
(include-book "classes/Job")

; The material below is the output of jvm2acl2 on Apprentice.java.

(defconst *Apprentice-class-table*
 (make-class-def
  (list
    *Apprentice*
    *Container*
    *Job*)))

(defconst *Apprentice-main*
  (method-program
    (bound? "main:()V"
;    (bound? "main:([Ljava/lang/String;)V"
            (class-decl-methods (bound? "Apprentice" *Apprentice-class-table*)))))

(defun Apprentice-ms ()
  (make-state
   (make-tt (push (make-frame 0
                              nil
                              nil
                              *Apprentice-main*
                              'UNLOCKED
                              "Apprentice")
                  nil))
   nil
   *Apprentice-class-table*
   *default-m5-options*))

(defun Apprentice ()
  (m5_load (Apprentice-ms)))

(defconst *a0* (Apprentice))

(defmacro gf (class field i heap)
  `(binding ,field (binding ,class (binding ,i ,heap))))

; It is known that the Container will be at (REF 8).

(defun counter (s)
  (gf "Container" "counter:I" 8 (heap s)))

(defun rel (c1 c2)
  (or (equal c2 c1)
      (equal c2 (int-fix (+ 1 c1)))))

; We will need a constant corresponding to every method invoked in this
; system.

(defconst *java.lang.Object.<init>*
  '((RETURN)))                                    ;;;  0

(defconst *java.lang.Thread.<init>*
  '((ALOAD_0)                                     ;;;  0
    (INVOKESPECIAL 1)                             ;;;  1 java.lang.Object.<init>:()V
    (RETURN)))                                    ;;;  4

(defconst *Apprentice.main*
  '((NEW 2)                                       ;;;  0 class Container
    (DUP)                                         ;;;  3
    (INVOKESPECIAL 3)                             ;;;  4 Container.<init>:()V
    (ASTORE_0)                                    ;;;  7
    (NEW 4)                                       ;;;  8 class Job
    (DUP)                                         ;;; 11
    (INVOKESPECIAL 5)                             ;;; 12 Job.<init>:()V
    (ASTORE_1)                                    ;;; 15
    (ALOAD_1)                                     ;;; 16
    (ALOAD_0)                                     ;;; 17
    (INVOKEVIRTUAL 6)                             ;;; 18 Job.setref:(LContainer;)V
    (ALOAD_1)                                     ;;; 21
    (INVOKEVIRTUAL 7)                             ;;; 22 java.lang.Thread.start:()V
    (GOTO -17)))                                  ;;; 25
#|
(defconst *Apprentice.main*
  '((NEW 2)                                       ;;;  0 class Container
    (DUP)                                         ;;;  3
    (INVOKESPECIAL 3)                             ;;;  4 Container.<init>:()V
    (ASTORE_1)                                    ;;;  7
    (NEW 4)                                       ;;;  8 class Job
    (DUP)                                         ;;; 11
    (INVOKESPECIAL 5)                             ;;; 12 Job.<init>:()V
    (ASTORE_2)                                    ;;; 15
    (ALOAD_2)                                     ;;; 16
    (ALOAD_1)                                     ;;; 17
    (INVOKEVIRTUAL 6)                             ;;; 18 Job.setref:(LContainer;)V
    (ALOAD_2)                                     ;;; 21
    (INVOKEVIRTUAL 7)                             ;;; java.lang.Thread.start:()V
    (GOTO -17)))                                  ;;; 25
|#
(defconst *Container.<init>*
  '((ALOAD_0)                                     ;;;  0
    (INVOKESPECIAL 1)                             ;;;  1 java.lang.Object.<init>:()V
    (RETURN)))                                    ;;;  4

(defconst *Job.<init>*
  '((ALOAD_0)                                     ;;;  0
    (INVOKESPECIAL 1)                             ;;;  1 java.lang.Thread.<init>:()V
    (RETURN)))                                    ;;;  4

(defconst *Job.incr*
  '((ALOAD_0)                                     ;;;  0
    (GETFIELD 2)                                  ;;;  1 Job.objref:LContainer;
    (DUP)                                         ;;;  4
    (ASTORE_1)                                    ;;;  5
    (MONITORENTER)                                ;;;  6
    (ALOAD_0)                                     ;;;  7
    (GETFIELD 2)                                  ;;;  8 Job.objref:LContainer;
    (ALOAD_0)                                     ;;; 11
    (GETFIELD 2)                                  ;;; 12 Job.objref:LContainer;
    (GETFIELD 3)                                  ;;; 15 Container.counter:I
    (ICONST_1)                                    ;;; 18
    (IADD)                                        ;;; 19
    (PUTFIELD 3)                                  ;;; 20 Container.counter:I
    (ALOAD_1)                                     ;;; 23
    (MONITOREXIT)                                 ;;; 24
    (GOTO 8)                                      ;;; 25
    (ASTORE_2)                                    ;;; 28
    (ALOAD_1)                                     ;;; 29
    (MONITOREXIT)                                 ;;; 30
    (ALOAD_2)                                     ;;; 31
    (ATHROW)                                      ;;; 32
    (ALOAD_0)                                     ;;; 33
    (ARETURN)))                                   ;;; 34

(defconst *Job.setref*
  '((ALOAD_0)                                     ;;;  0
    (ALOAD_1)                                     ;;;  1
    (PUTFIELD 2)                                  ;;;  2 ; Job.objref:LContainer;
    (RETURN)))                                    ;;;  5

(defconst *Job.run*
  '((ALOAD_0)                                     ;;;  0
    (INVOKEVIRTUAL 4)                             ;;;  1 Job.incr:()LJob;
    (POP)                                         ;;;  4
    (GOTO -5)))                                   ;;;  5

; Some of these constants are identical, e.g.,
; *java.lang.Thread.<init>* is equal to *Container.<init>*.
; Therefore, it is not sufficient to test merely the program of a
; frame to decide what we're doing.  We make the following macro,
; which also looks at the cur-class of the frame.

; I don't want to introduce these constants into the proof scripts.
; So I will define the concept of being in a certain program and I
; will arrange for the next-inst to compute to the appropriate
; (constant) instruction given knowledge of which program it's in.
; Then I will disable these concepts.

(defun program1 (class method)
  (cond
   ((equal class "java/lang/Object")
    (cond
     ((equal method "<init>:()V")
      *java.lang.Object.<init>*)
     (t nil)))
   ((equal class "java/lang/Thread")
    (cond
     ((equal method "<init>:()V")
      *java.lang.Thread.<init>*)
     (t nil)))
   ((equal class "Apprentice")
    (cond
     ((equal method "main:()V")
;     ((equal method "main:([Ljava/lang/String;)V")
      *Apprentice.main*)
     (t nil)))
   ((equal class "Container")
    (cond
     ((equal method "<init>:()V")
      *Container.<init>*)
     (t nil)))
   ((equal class "Job")
    (cond
     ((equal method "<init>:()V")
      *Job.<init>*)
     ((equal method "incr:()LJob;")
      *Job.incr*)
     ((equal method "setref:(LContainer;)V")
      *Job.setref*)
     ((equal method "run:()V")
      *Job.run*)
     (t nil)))
   (t nil)))

(defun check-program1 (class method)
  (equal (program1 class method)
         (method-program (bound? method (class-decl-methods (bound? class (class-table *a0*)))))))

(defthm check-program1-all
  (and
    (check-program1 "java.lang.Object" "<init>:()V")
    (check-program1 "java.lang.Thread" "<init>:()V")
    (check-program1 "Apprentice" "main:()V")
;    (check-program1 "Apprentice" "main:([Ljava/lang/String;)V")
    (check-program1 "Container" "<init>:()V")
    (check-program1 "Job" "<init>:()V")
    (check-program1 "Job" "incr:()LJob;")
    (check-program1 "Job" "setref:(LContainer;)V")
    (check-program1 "Job" "run:()V"))
  :rule-classes ())

(defun programp (frame class method)
  (let ((const (program1 class method)))
    (and (equal (cur-class frame) class)
         (equal (program frame) const))))

(defthm next-inst-from-programp
  (implies (and (syntaxp (quotep pc))
                (programp frame class method))
           (equal (INDEX-INTO-PROGRAM pc
                                      (PROGRAM frame))
                  (index-into-program pc
                                      (program1 class method)))))

(defthm cur-class-from-programp
  (implies (programp frame class method)
           (equal (cur-class frame) class)))

; Details: In the defthm above, class and method and pc will always be
; constant.  Generally (program frame) will be undetermined, but
; (programp frame "..." "...") will be settled by some case of the
; good-state invariant.  The lemma above will essentially replace
; (program frame) by (program1 class method), which will then compute.
; Then index-to-program will compute.

(defthm programp-make-frame
  (implies (syntaxp (and (quotep program)
                         (quotep class)
                         (quotep method)))
           (equal (programp (make-frame pc locals stack program sync-flg cur-class)
                            class
                            method)
                  (let ((const (program1 class method)))
                    (and (equal cur-class class)
                         (equal program const))))))

; Details: Programp is disabled but I want it to compute if the
; program of the frame is a constant.  (Typically class and method are
; always constants in my usage.)

(defthm programp-mx-1
  (implies (and (programp frame class1 method1)
                (syntaxp (and (quotep class1)
                              (quotep method1)
                              (quotep class2)
                              (quotep method2)))
                (not (equal (program1 class1 method1) nil))
                (or (not (equal class1 class2))
                    (not (equal method1 method2))))
           (not (programp frame class2 method2))))

; Details: You can't be in two different programs at the same time.
; This is a nice example of something that is manifest if you just
; compute.

(defthm programp-mx-2
  (implies (and (programp frame1 class1 method1)
                (syntaxp (and (quotep class1)
                              (quotep method1)
                              (quotep class2)
                              (quotep method2)))
                (not (equal (program1 class1 method1) nil))
                (equal (cur-class frame1) cur-class)
                (not (equal class1 class2)))
           (not (programp
                 (make-frame pc locals stack (PROGRAM frame1) sync-flg cur-class)
                 class2
                 method2))))

(defthm programp-mx-3
  (implies (and (programp frame1 class1 method1)
                (equal (cur-class frame1) cur-class))
           (programp
                 (make-frame pc locals stack (PROGRAM frame1) sync-flg cur-class)
                 class1
                 method1)))

(defthm programp-mx-4
  (implies (and (programp frame1 class1 method1)
                (syntaxp (and (quotep class1)
                              (quotep method1)
                              (quotep method2)))
                (not (equal (program1 class1 method1) nil))
                (equal (cur-class frame1) cur-class)
                (not (equal method1 method2)))
           (not (programp
                 (make-frame pc locals stack (PROGRAM frame1) sync-flg cur-class)
                 class1
                 method2))))

; Details: It just goes on and on doesn't it?

(in-theory (disable programp index-into-program))

; Now onwards to the invariants.

; My plan is to start by defining the good threads but without stating
; the constraints on the heap that are implicit in the various pcs.
; Then I will define the good heaps and use the basic case analysis
; developed for the threads.

(defun good-java.lang.Object.<init>-frame (frame)
  (let ((pc      (pc frame))
        (flg     (sync-flg frame)))
    (and
     (programp frame "java/lang/Object" "<init>:()V")
     (equal flg 'UNLOCKED)
     (equal pc 0))))

(defun good-java.lang.Thread.<init>-frame (frame)
  (let ((pc      (pc frame))
        (flg     (sync-flg frame)))
    (and
     (programp frame "java/lang/Thread" "<init>:()V")
     (equal flg 'UNLOCKED)
     (or (equal pc 0)
         (equal pc 1)
         (equal pc 4)))))

(defun good-Container.<init>-frame (frame)
  (let ((pc      (pc frame))
        (flg     (sync-flg frame)))
    (and
     (programp frame "Container" "<init>:()V")
     (equal flg 'UNLOCKED)
     (or (equal pc 0)
         (equal pc 1)
         (equal pc 4)))))

(defun good-Job.<init>-frame (frame)
  (let ((pc      (pc frame))
        (flg     (sync-flg frame)))
    (and
     (programp frame "Job" "<init>:()V")
     (equal flg 'UNLOCKED)
     (or (equal pc 0)
         (equal pc 1)
         (equal pc 4)))))

(defun good-Job.setref-frame (i frame)
  (let ((pc      (pc frame))
        (locals  (locals frame))
        (stack   (stack frame))
        (flg     (sync-flg frame)))
    (and
     (programp frame "Job" "setref:(LContainer;)V")
     (equal locals `((REF ,i) (REF 8)))
     (equal flg 'UNLOCKED)
     (case pc
       (0 (equal stack nil))
       (1 (equal stack `((REF ,i))))
       (2 (equal stack `((REF 8) (REF ,i))))
       (5 t)
       (t nil)))))

(defun good-main-frame (i frame suspendedp)

; i is the number of the last item in the heap.  I won't attempt to
; constrain the heap in this function.  Suspendedp is either nil,
; which means the frame is active, or else it is a pc, indicating that
; I am suspended with the indicated pc.


  (let* ((pc        (pc frame))
         (locals    (locals frame))
         (stack     (stack frame))
         (flg       (sync-flg frame))
         (container (nth 0 locals))
         (job       (nth 1 locals)))
;         (container (nth 1 locals))
;         (job       (nth 2 locals)))
    (and
     (programp frame "Apprentice" "main:()V")
;     (programp frame "Apprentice" "main:([Ljava/lang/String;)V")
     (equal flg 'UNLOCKED)
     (case pc
       (0 (and (not suspendedp)
               (equal stack nil)))
       (3 (and (not suspendedp)
               (equal stack '((REF 8)))))
       (4 (and (not suspendedp)
               (equal stack '((REF 8) (REF 8)))))
       (7 (and (or (not suspendedp)
                   (equal suspendedp 7))
               (equal stack '((REF 8)))))
       (8 (and (not suspendedp)
               (equal container '(REF 8))
               (equal stack nil)))
       (11 (and (not suspendedp)
                (equal container '(REF 8))
                (equal stack `((REF ,i)))))
       (12 (and (not suspendedp)
                (equal container '(REF 8))
                (equal stack `((REF ,i) (REF ,i)))))
       (15 (and (or (not suspendedp)
                    (equal suspendedp 15))
                (equal container '(REF 8))
                (equal stack `((REF ,i)))))
       (16 (and (not suspendedp)
                (equal container '(REF 8))
                (equal job `(REF ,i))
                (equal stack nil)))
       (17 (and (not suspendedp)
                (equal container '(REF 8))
                (equal job `(REF ,i))
                (equal stack `((REF ,i)))))
       (18 (and (not suspendedp)
                (equal container '(REF 8))
                (equal job `(REF ,i))
                (equal stack `((REF 8) (REF ,i)))))
       (21 (and (or (not suspendedp)
                    (equal suspendedp 21))
                (equal container '(REF 8))
                (equal job `(REF ,i))
                (equal stack nil)))
       (22 (and (not suspendedp)
                (equal container '(REF 8))
                (equal job `(REF ,i))
                (equal stack `((REF ,i)))))
       (25 (and (not suspendedp)
                (equal container '(REF 8))
                (equal job `(REF ,i))
                (equal stack nil)))
       (t  nil)))))

(defun thread-no         (thread) (nth 0 thread))
(defun thread-call-stack (thread) (nth 1 thread))
(defun thread-status     (thread) (nth 2 thread))
(defun thread-rref       (thread) (nth 3 thread))

(defun frame0 (cs) (first cs))
(defun frame1 (cs) (second cs))
(defun frame2 (cs) (third cs))
(defun frame3 (cs) (fourth cs))

(defun good-thread0 (thread i)

; The variable i here is the heap address of the most recently
; allocated object.

  (let ((n (thread-no thread))
        (cs (thread-call-stack thread))
        (status (thread-status thread))
        (rref (thread-rref thread)))
    (and (equal n 0)
         (equal status 'SCHEDULED)
         (equal rref nil)
         (cond ((endp cs) nil)
               ((programp (frame0 cs) "java/lang/Object" "<init>:()V")
                (cond
                 ((programp (frame1 cs) "java/lang/Thread" "<init>:()V")
                  (and (good-java.lang.Object.<init>-frame (frame0 cs))
                       (not (endp (cdr cs)))
                       (good-java.lang.Thread.<init>-frame (frame1 cs))
                       (not (endp (cddr cs)))
                       (good-Job.<init>-frame (frame2 cs))
                       (not (endp (cdddr cs)))
                       (good-main-frame i (frame3 cs) 15)))
                 ((programp (frame1 cs) "Container" "<init>:()V")
                  (and (good-java.lang.Object.<init>-frame (frame0 cs))
                       (not (endp (cdr cs)))
                       (good-container.<init>-frame (frame1 cs))
                       (not (endp (cddr cs)))
                       (good-main-frame i (frame2 cs) 7)))
                 (t nil)))
               ((programp (frame0 cs) "java/lang/Thread" "<init>:()V")
                (and (good-java.lang.Thread.<init>-frame (frame0 cs))
                     (not (endp (cdr cs)))
                     (good-Job.<init>-frame (frame1 cs))
                     (not (endp (cddr cs)))
                     (good-main-frame i (frame2 cs) 15)))
               ((programp (frame0 cs) "Container" "<init>:()V")
                (and (good-container.<init>-frame (frame0 cs))
                     (not (endp (cdr cs)))
                     (good-main-frame i (frame1 cs) 7)))
               ((programp (frame0 cs) "Job" "<init>:()V")
                (and (good-Job.<init>-frame (frame0 cs))
                     (not (endp (cdr cs)))
                     (good-main-frame i (frame1 cs) 15)))
               ((programp (frame0 cs) "Job" "setref:(LContainer;)V")
                (and (good-Job.setref-frame i (frame0 cs))
                     (not (endp (cdr cs)))
                     (good-main-frame i (frame1 cs) 21)))
               (t (good-main-frame i (frame0 cs) nil))))))

(defun good-objrefs (threads heap-pairs except-last-flg)

; Initially, threads is the cdr of the thread table and heap-pairs is
; the 9th cdr of the heap.  That is where in the heap we have begun
; allocating "Job" instances.  The 8th element of the heap will be the
; Container object (after it is allocated).  Elements 0 through 7 of
; the heap are constant representing classes.

; We walk down both threads and heap-pairs.  They must be the same
; length.  Let the car of threads be (i call-stack status rref) and
; let the car of heap-pairs be (j . (("Job" ("objref:LContainer;" . ref0)) ...)).
; Then we insist that

; * (+ i 8) = j (the thread number is 8 less than the heap address of the
;          object representing the thread)
; * rref = (REF j), and
; * ref0 = (REF 8) (with the exception noted below).

; If except-last-flg is t, then if this is the last item in the heap
; we insist that ref0 = 0, instead of (REF j) as above.

  (cond
   ((endp heap-pairs) (endp threads))
   ((endp threads) nil)
   (t (let* ((threadi (car threads))
             (i (thread-no threadi))
             (rref (thread-rref threadi))
             (j (car (car heap-pairs)))
             (obj (cdr (car heap-pairs))))
        (and (equal (+ 8 i) j)
             (equal rref `(REF ,j))
             (equal obj
                    (if (and (endp (cdr heap-pairs))
                             except-last-flg)
                        '(("Job" ("objref:LContainer;" . (REF -1)))
                          ("java/lang/Thread")
                          ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
                      '(("Job" ("objref:LContainer;" . (REF 8)))
                        ("java/lang/Thread")
                        ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))))
             (good-objrefs (cdr threads)
                           (cdr heap-pairs)
                           except-last-flg))))))

(defun standard-heap-prefixp1 (prefix heap)
  (cond ((endp prefix) t)
        (t (and (equal (car prefix) (car heap))
                (standard-heap-prefixp1 (cdr prefix) (cdr heap))))))

(defun standard-heap-prefixp (heap)
  (standard-heap-prefixp1
   '((0 ("java/lang/Class" ("<sfields>") ("<name>" . "java/lang/Object"))
        ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
     (1 ("java/lang/Class" ("<sfields>") ("<name>" . "[C"))
        ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
     (2 ("java/lang/Class" ("<sfields>") ("<name>" . "java/lang/Thread"))
        ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
     (3 ("java/lang/Class" ("<sfields>") ("<name>" . "java/lang/String"))
        ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
     (4 ("java/lang/Class" ("<sfields>") ("<name>" . "java/lang/Class"))
        ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
     (5 ("java/lang/Class" ("<sfields>") ("<name>" . "Apprentice"))
        ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
     (6 ("java/lang/Class" ("<sfields>") ("<name>" . "Container"))
        ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
     (7 ("java/lang/Class" ("<sfields>") ("<name>" . "Job"))
        ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
   heap))

(defun main-pc (cs)

; Cs is the call stack of thread 0.  It is running main.  What is
; the pc in the main frame?  The main frame may be suspended,
; of course.

  (cond ((programp (frame0 cs) "java/lang/Object" "<init>:()V")
         (cond
          ((programp (frame1 cs) "java/lang/Thread" "<init>:()V")

; The main frame is suspended waiting for the Job.<init>.

           15)
          (t
; Otherwise, the only way we could be in Object.<init> is if the main
; frame is suspended waiting for Container.<init>.

           7)))
        ((programp (frame0 cs) "java/lang/Thread" "<init>:()V")
         15)
        ((programp (frame0 cs) "Container" "<init>:()V")
         7)
        ((programp (frame0 cs) "Job" "<init>:()V")
         15)
        ((programp (frame0 cs) "Job" "setref:(LContainer;)V")
         21)
        (t (pc (frame0 cs)))))

(defun good-heap (tt heap)

; Tt is the thread table of a state and heap is the heap.  We
; determine whether the heap is consistent with the thread table.  We
; assume we know that thread 0 is good wrt the length of heap.  We do
; not enforce here any of the <monitor>/<mcount> invariants on (REF 8) in
; the heap, because they are entirely determined by the details of the
; Job threads.

  (let* ((thread0 (first tt))
         (n0 (thread-no thread0))
         (frame0 (frame0 (thread-call-stack thread0))))
    (and
     (alistp heap)
     (equal n0 0)
     (standard-heap-prefixp heap)
     (case (main-pc (thread-call-stack thread0))
       (0 (null (nthcdr 8 heap)))
       (3 (and (consp (nthcdr 8 heap))
               (equal (car (nth 8 heap)) 8)
               (null (nthcdr 9 heap))))
       (4 (and (consp (nthcdr 8 heap))
               (equal (car (nth 8 heap)) 8)
               (null (nthcdr 9 heap))))
       (7 (and (consp (nthcdr 8 heap))
               (equal (car (nth 8 heap)) 8)
               (null (nthcdr 9 heap))))
       (8 (and (consp (nthcdr 8 heap))
               (equal (car (nth 8 heap)) 8)
               (good-objrefs (cdr tt) (nthcdr 9 heap) nil)))
       (11 (and (equal (car (nth 8 heap)) 8)
                (consp (nthcdr 9 heap))
                (good-objrefs (cdr tt)
                              (nthcdr 9 heap)
                              t)))
       (12 (and (equal (car (nth 8 heap)) 8)
                (consp (nthcdr 9 heap))
                (good-objrefs (cdr tt)
                              (nthcdr 9 heap)
                              t)))
       (15 (and (equal (car (nth 8 heap)) 8)
                (consp (nthcdr 9 heap))
                (good-objrefs (cdr tt)
                              (nthcdr 9 heap)
                              t)))
       (16 (and (equal (car (nth 8 heap)) 8)
                (consp (nthcdr 9 heap))
                (good-objrefs (cdr tt)
                              (nthcdr 9 heap)
                              t)))
       (17 (and (equal (car (nth 8 heap)) 8)
                (consp (nthcdr 9 heap))
                (good-objrefs (cdr tt)
                              (nthcdr 9 heap)
                              t)))
       (18 (and (equal (car (nth 8 heap)) 8)
                (consp (nthcdr 9 heap))
                (good-objrefs (cdr tt)
                              (nthcdr 9 heap)
                              t)))
       (21 (and (equal (car (nth 8 heap)) 8)
                (consp (nthcdr 9 heap))
                (good-objrefs (cdr tt)
                              (nthcdr 9 heap)
; If we are suspended at 21 and frame0 is really the active setref,
; then the flag is t if we're at pc 5 in setref and is nil otherwise.
; If we are active at 21, the flag is nil.

                              (if (equal (pc frame0) 21) nil
                                (not (equal (pc frame0) 5))))))
       (22 (and (equal (car (nth 8 heap)) 8)
                (consp (nthcdr 9 heap))
                (good-objrefs (cdr tt)
                              (nthcdr 9 heap)
                              nil)))
       (25 (and (consp (nthcdr 8 heap))
                (equal (car (nth 8 heap)) 8)
                (good-objrefs (cdr tt)
                              (nthcdr 9 heap)
                              nil)))
       (t nil)))))

(defun good-class-table (ct)
  (equal ct (class-table *a0*)))

; I don't want the class table slipping into my output so I disable it.

(defthm assoc-equal-in-good-class-table
  (implies (and (syntaxp (quotep str))
                (good-class-table ct))
           (equal (assoc-equal str ct)
                  (assoc-equal str (class-table *a0*)))))

(in-theory (disable good-class-table))

(defun object-lockedp (th monitor mcount)
  (and (equal mcount 1)
       (equal th monitor)))

(defun good-run-frame (th frame activep monitor mcount)
  (let ((pc (pc frame))
        (locals (locals frame))
        (stack (stack frame))
        (flg   (sync-flg frame)))
    (and
     (programp frame "Job" "run:()V")
     (equal locals `((REF ,(+ 8 th))))
     (equal flg 'UNLOCKED)
     (if activep
         (not (object-lockedp th monitor mcount))
       t)
     (case pc
       (0 (and activep (equal stack nil)))
       (1 (and activep (equal stack `((REF ,(+ 8 th))))))
       (4 (if activep
              (equal stack `((REF ,(+ 8 th))))
            (equal stack nil)))
       (5 (and activep (equal stack nil)))
       (t nil)))))

(defun good-incr-frame (th frame counter monitor mcount)

; In this system it happens that the heap address of the THIS object
; of every invocation of the "incr" method is always 8 more than the
; number of thread, th, in which that method is running.

  (let ((pc (pc frame))
        (locals (locals frame))
        (stack (stack frame))
        (flg   (sync-flg frame))
        (self `(REF ,(+ 8 th))))
    (and
     (programp frame "Job" "incr:()LJob;")
     (equal flg 'UNLOCKED)
     (case pc
       (0 (and (equal locals `(,self))
               (not (object-lockedp th monitor mcount))
               (equal stack nil)))
       (1 (and (equal locals `(,self))
               (not (object-lockedp th monitor mcount))
               (equal stack `(,self))))
       (4 (and (equal locals `(,self))
               (equal stack '((REF 8)))
               (not (object-lockedp th monitor mcount))))
       (5 (and (equal locals `(,self))
               (equal stack '((REF 8) (REF 8)))
               (not (object-lockedp th monitor mcount))))
       (6 (and (equal locals `(,self (REF 8)))
               (equal stack '((REF 8)))
               (not (object-lockedp th monitor mcount))))
       (7 (and (equal locals
                      `(,self (REF 8)))
               (object-lockedp th monitor mcount)
               (equal stack nil)))
       (8 (and (equal locals
                      `(,self (REF 8)))
               (object-lockedp th monitor mcount)
               (equal stack `(,self))))
       (11 (and (equal locals
                       `(,self (REF 8)))
                (object-lockedp th monitor mcount)
                (equal stack '((REF 8)))))
       (12 (and (equal locals
                       `(,self (REF 8)))
                (object-lockedp th monitor mcount)
                (equal stack `(,self (REF 8)))))
       (15 (and (equal locals
                       `(,self (REF 8)))
                (object-lockedp th monitor mcount)
                (equal stack '((REF 8) (REF 8)))))
       (18 (and (equal locals
                       `(,self (REF 8)))
                (object-lockedp th monitor mcount)
                (equal stack `(,counter (REF 8)))))
       (19 (and (equal locals
                       `(,self (REF 8)))
                (object-lockedp th monitor mcount)
                (equal stack `(1 ,counter (REF 8)))))
       (20 (and (equal locals
                       `(,self (REF 8)))
                (object-lockedp th monitor mcount)
                (equal stack `(,(int-fix (+ 1 counter)) (REF 8)))))
       (23 (and (equal locals
                       `(,self (REF 8)))
                (object-lockedp th monitor mcount)
                (equal stack nil)))
       (24 (and (equal locals
                       `(,self (REF 8)))
                (object-lockedp th monitor mcount)
                (equal stack '((REF 8)))))
       (25 (and (equal locals
                       `(,self (REF 8)))
                (not (object-lockedp th monitor mcount))
                (equal stack nil)))
       (28 nil)
       (29 nil)
       (30 nil)
       (31 nil)
       (32 nil)
       (33 (and (equal locals
                       `(,self (REF 8)))
                (not (object-lockedp th monitor mcount))
                (equal stack nil)))
       (34 (and (equal locals
                       `(,self (REF 8)))
                (not (object-lockedp th monitor mcount))
                (equal stack `(,self))))
       (t nil)))))

(defun good-thread (th scheduled thread counter monitor mcount)
  (let ((n (thread-no thread))
        (cs (thread-call-stack thread))
        (status (thread-status thread))
        (rref (thread-rref thread)))
    (and (equal n th)
         (equal status scheduled)
         (equal rref `(REF ,(+ 8 th)))
         (cond ((equal scheduled 'UNSCHEDULED)
                (and (good-run-frame th (frame0 cs) t monitor mcount)
                     (null (cdr cs))))
               ((endp cs) nil)
               ((programp (frame0 cs) "Job" "incr:()LJob;")
                (and (good-incr-frame th (frame0 cs) counter monitor mcount)
                     (not (endp (frame0 cs)))
                     (good-run-frame th (frame1 cs) nil monitor mcount)))
               (t (good-run-frame th (frame0 cs) t monitor mcount))))))

(defun good-threads (i threads counter monitor mcount except-last-flg)
  (declare (xargs :measure (acl2-count threads)))
  (cond
   ((endp threads) t)
   (t (and (good-thread i
                        (if (and (endp (cdr threads))
                                 except-last-flg)
                            'UNSCHEDULED
                          'SCHEDULED)
                        (car threads)
                        counter monitor mcount)
           (good-threads (+ 1 i)
                         (cdr threads)
                         counter monitor mcount except-last-flg)))))

(defun good-thread-table (tt i counter monitor mcount)
  (let* ((thread0 (first tt))
         (main-pc (main-pc (thread-call-stack thread0))))
    (and
     (alistp tt)
     (equal (thread-no thread0) 0)
     (good-thread0 thread0 i)
     (if (< main-pc 8)
         (equal (cdr tt) nil)
         (good-threads 1 (cdr tt) counter monitor mcount
                       (and (<= 11 main-pc) (< main-pc 25)))))))

(defun good-state (s)
  (let ((counter (gf "Container" "counter:I" 8 (heap s)))
        (monitor (gf "java/lang/Object" "<monitor>" 8 (heap s)))
        (mcount (gf "java/lang/Object" "<mcount>" 8 (heap s))))
    (and (good-class-table (class-table s))
         (good-thread-table (thread-table s)
                            (- (len (heap s)) 1)
                            counter monitor mcount)
         (good-heap (thread-table s) (heap s))

; We must know the monitor is some existing thread, else a thread
; can come into existence owning the lock!

         (or (equal (len (heap s)) 8)
             (and (integerp counter)
                  (if (equal mcount 0)
                      (equal monitor 0)
                    (and (equal mcount 1)
                         (< 0 monitor)
                         (< monitor (- (len (heap s)) 8)))))))))

; ---------------------------------------------------------------------------

; The Proof

(include-book "arithmetic/top-with-meta" :dir :system)

(in-theory (disable acl2::equal-constant-+))

(defthm len-bind
  (implies (alistp alist)
           (equal (len (bind x v alist))
                  (if (bound? x alist)
                      (len alist)
                    (+ 1 (len alist))))))

(defthm assoc-equal-bind
  (equal (assoc-equal x (bind y v alist))
         (if (equal x y) (cons x v) (assoc-equal x alist))))

(defthm nth-add1!
  (implies (and (integerp n)
                (<= 0 n))
           (equal (nth (+ 1 n) lst)
                  (nth n (cdr lst)))))

(defthm nthcdr-add1!
  (implies (and (integerp n)
                (<= 0 n))
           (equal (nthcdr (+ 1 n) lst)
                  (nthcdr n (cdr lst)))))

(defthm alistp-bind
  (implies (alistp alist)
           (alistp (bind x v alist))))

(defthm do-inst-opener
  (implies
   (syntaxp (quotep inst))
   (equal
    (do-inst inst th s)
    (CASE (OP-CODE INST)
      (AALOAD (EXECUTE-AALOAD INST TH S))
      (AASTORE (EXECUTE-AASTORE INST TH S))
      (ACONST_NULL (EXECUTE-ACONST_NULL INST TH S))
      (ALOAD (EXECUTE-ALOAD INST TH S))
      (ALOAD_W (EXECUTE-ALOAD INST TH S))
      (ALOAD_0 (EXECUTE-ALOAD_X INST TH S 0))
      (ALOAD_1 (EXECUTE-ALOAD_X INST TH S 1))
      (ALOAD_2 (EXECUTE-ALOAD_X INST TH S 2))
      (ALOAD_3 (EXECUTE-ALOAD_X INST TH S 3))
      (ANEWARRAY (EXECUTE-ANEWARRAY INST TH S))
      (ARETURN (EXECUTE-ARETURN INST TH S))
      (ARRAYLENGTH (EXECUTE-ARRAYLENGTH INST TH S))
      (ASTORE (EXECUTE-ASTORE INST TH S))
      (ASTORE_W (EXECUTE-ASTORE INST TH S))
      (ASTORE_0 (EXECUTE-ASTORE_X INST TH S 0))
      (ASTORE_1 (EXECUTE-ASTORE_X INST TH S 1))
      (ASTORE_2 (EXECUTE-ASTORE_X INST TH S 2))
      (ASTORE_3 (EXECUTE-ASTORE_X INST TH S 3))
      (BALOAD (EXECUTE-BALOAD INST TH S))
      (BASTORE (EXECUTE-BASTORE INST TH S))
      (BIPUSH (EXECUTE-BIPUSH INST TH S))
      (CALOAD (EXECUTE-CALOAD INST TH S))
      (CASTORE (EXECUTE-CASTORE INST TH S))
      (CHECKCAST (EXECUTE-CHECKCAST INST TH S))
      (D2F (EXECUTE-D2F INST TH S))
      (D2I (EXECUTE-D2I INST TH S))
      (D2L (EXECUTE-D2L INST TH S))
      (DADD (EXECUTE-DADD INST TH S))
      (DALOAD (EXECUTE-DALOAD INST TH S))
      (DASTORE (EXECUTE-DASTORE INST TH S))
      (DCMPG (EXECUTE-DCMPG INST TH S))
      (DCMPL (EXECUTE-DCMPL INST TH S))
      (DCONST_0 (EXECUTE-DCONST_0 INST TH S))
      (DCONST_1 (EXECUTE-DCONST_1 INST TH S))
      (DDIV (EXECUTE-DDIV INST TH S))
      (DLOAD (EXECUTE-DLOAD INST TH S))
      (DLOAD_W (EXECUTE-DLOAD INST TH S))
      (DLOAD_0 (EXECUTE-DLOAD_X INST TH S 0))
      (DLOAD_1 (EXECUTE-DLOAD_X INST TH S 1))
      (DLOAD_2 (EXECUTE-DLOAD_X INST TH S 2))
      (DLOAD_3 (EXECUTE-DLOAD_X INST TH S 3))
      (DMUL (EXECUTE-DMUL INST TH S))
      (DNEG (EXECUTE-DNEG INST TH S))
      (DREM (EXECUTE-DREM INST TH S))
      (DRETURN (EXECUTE-DRETURN INST TH S))
      (DSTORE (EXECUTE-DSTORE INST TH S))
      (DSTORE_W (EXECUTE-DSTORE INST TH S))
      (DSTORE_0 (EXECUTE-DSTORE_X INST TH S 0))
      (DSTORE_1 (EXECUTE-DSTORE_X INST TH S 1))
      (DSTORE_2 (EXECUTE-DSTORE_X INST TH S 2))
      (DSTORE_3 (EXECUTE-DSTORE_X INST TH S 3))
      (DSUB (EXECUTE-DSUB INST TH S))
      (DUP (EXECUTE-DUP INST TH S))
      (DUP_X1 (EXECUTE-DUP_X1 INST TH S))
      (DUP_X2 (EXECUTE-DUP_X2 INST TH S))
      (DUP2 (EXECUTE-DUP2 INST TH S))
      (DUP2_X1 (EXECUTE-DUP2_X1 INST TH S))
      (DUP2_X2 (EXECUTE-DUP2_X2 INST TH S))
      (F2D (EXECUTE-F2D INST TH S))
      (F2I (EXECUTE-F2I INST TH S))
      (F2L (EXECUTE-F2L INST TH S))
      (FADD (EXECUTE-FADD INST TH S))
      (FALOAD (EXECUTE-FALOAD INST TH S))
      (FASTORE (EXECUTE-FASTORE INST TH S))
      (FCMPG (EXECUTE-FCMPG INST TH S))
      (FCMPL (EXECUTE-FCMPL INST TH S))
      (FCONST_0 (EXECUTE-FCONST_0 INST TH S))
      (FCONST_1 (EXECUTE-FCONST_1 INST TH S))
      (FCONST_2 (EXECUTE-FCONST_2 INST TH S))
      (FDIV (EXECUTE-FDIV INST TH S))
      (FLOAD (EXECUTE-FLOAD INST TH S))
      (FLOAD_W (EXECUTE-FLOAD INST TH S))
      (FLOAD_0 (EXECUTE-FLOAD_X INST TH S 0))
      (FLOAD_1 (EXECUTE-FLOAD_X INST TH S 1))
      (FLOAD_2 (EXECUTE-FLOAD_X INST TH S 2))
      (FLOAD_3 (EXECUTE-FLOAD_X INST TH S 3))
      (FMUL (EXECUTE-FMUL INST TH S))
      (FNEG (EXECUTE-FNEG INST TH S))
      (FREM (EXECUTE-FREM INST TH S))
      (FRETURN (EXECUTE-FRETURN INST TH S))
      (FSTORE (EXECUTE-FSTORE INST TH S))
      (FSTORE_W (EXECUTE-FSTORE INST TH S))
      (FSTORE_0 (EXECUTE-FSTORE_X INST TH S 0))
      (FSTORE_1 (EXECUTE-FSTORE_X INST TH S 1))
      (FSTORE_2 (EXECUTE-FSTORE_X INST TH S 2))
      (FSTORE_3 (EXECUTE-FSTORE_X INST TH S 3))
      (FSUB (EXECUTE-FSUB INST TH S))
      (GETFIELD (EXECUTE-GETFIELD INST TH S))
      (GETSTATIC (EXECUTE-GETSTATIC INST TH S))
      (GOTO (EXECUTE-GOTO INST TH S))
      (GOTO_W (EXECUTE-GOTO_W INST TH S))
      (I2B (EXECUTE-I2B INST TH S))
      (I2C (EXECUTE-I2C INST TH S))
      (I2D (EXECUTE-I2D INST TH S))
      (I2F (EXECUTE-I2F INST TH S))
      (I2L (EXECUTE-I2L INST TH S))
      (I2S (EXECUTE-I2S INST TH S))
      (IADD (EXECUTE-IADD INST TH S))
      (IALOAD (EXECUTE-IALOAD INST TH S))
      (IAND (EXECUTE-IAND INST TH S))
      (IASTORE (EXECUTE-IASTORE INST TH S))
      (ICONST_M1 (EXECUTE-ICONST_X INST TH S -1))
      (ICONST_0 (EXECUTE-ICONST_X INST TH S 0))
      (ICONST_1 (EXECUTE-ICONST_X INST TH S 1))
      (ICONST_2 (EXECUTE-ICONST_X INST TH S 2))
      (ICONST_3 (EXECUTE-ICONST_X INST TH S 3))
      (ICONST_4 (EXECUTE-ICONST_X INST TH S 4))
      (ICONST_5 (EXECUTE-ICONST_X INST TH S 5))
      (IDIV (EXECUTE-IDIV INST TH S))
      (IF_ACMPEQ (EXECUTE-IF_ACMPEQ INST TH S))
      (IF_ACMPNE (EXECUTE-IF_ACMPNE INST TH S))
      (IF_ICMPEQ (EXECUTE-IF_ICMPEQ INST TH S))
      (IF_ICMPGE (EXECUTE-IF_ICMPGE INST TH S))
      (IF_ICMPGT (EXECUTE-IF_ICMPGT INST TH S))
      (IF_ICMPLE (EXECUTE-IF_ICMPLE INST TH S))
      (IF_ICMPLT (EXECUTE-IF_ICMPLT INST TH S))
      (IF_ICMPNE (EXECUTE-IF_ICMPNE INST TH S))
      (IFEQ (EXECUTE-IFEQ INST TH S))
      (IFGE (EXECUTE-IFGE INST TH S))
      (IFGT (EXECUTE-IFGT INST TH S))
      (IFLE (EXECUTE-IFLE INST TH S))
      (IFLT (EXECUTE-IFLT INST TH S))
      (IFNE (EXECUTE-IFNE INST TH S))
      (IFNONNULL (EXECUTE-IFNONNULL INST TH S))
      (IFNULL (EXECUTE-IFNULL INST TH S))
      (IINC (EXECUTE-IINC INST TH S))
      (IINC_W (EXECUTE-IINC INST TH S))
      (ILOAD (EXECUTE-ILOAD INST TH S))
      (ILOAD_W (EXECUTE-ILOAD INST TH S))
      (ILOAD_0 (EXECUTE-ILOAD_X INST TH S 0))
      (ILOAD_1 (EXECUTE-ILOAD_X INST TH S 1))
      (ILOAD_2 (EXECUTE-ILOAD_X INST TH S 2))
      (ILOAD_3 (EXECUTE-ILOAD_X INST TH S 3))
      (IMUL (EXECUTE-IMUL INST TH S))
      (INEG (EXECUTE-INEG INST TH S))
      (INSTANCEOF (EXECUTE-INSTANCEOF INST TH S))
      (INVOKESPECIAL (EXECUTE-INVOKESPECIAL INST TH S))
      (INVOKESTATIC (EXECUTE-INVOKESTATIC INST TH S))
      (INVOKEVIRTUAL (EXECUTE-INVOKEVIRTUAL INST TH S))
      (IOR (EXECUTE-IOR INST TH S))
      (IREM (EXECUTE-IREM INST TH S))
      (IRETURN (EXECUTE-IRETURN INST TH S))
      (ISHL (EXECUTE-ISHL INST TH S))
      (ISHR (EXECUTE-ISHR INST TH S))
      (ISTORE (EXECUTE-ISTORE INST TH S))
      (ISTORE_W (EXECUTE-ISTORE INST TH S))
      (ISTORE_0 (EXECUTE-ISTORE_X INST TH S 0))
      (ISTORE_1 (EXECUTE-ISTORE_X INST TH S 1))
      (ISTORE_2 (EXECUTE-ISTORE_X INST TH S 2))
      (ISTORE_3 (EXECUTE-ISTORE_X INST TH S 3))
      (ISUB (EXECUTE-ISUB INST TH S))
      (IUSHR (EXECUTE-IUSHR INST TH S))
      (IXOR (EXECUTE-IXOR INST TH S))
      (JSR (EXECUTE-JSR INST TH S))
      (JSR_W (EXECUTE-JSR_W INST TH S))
      (L2D (EXECUTE-L2D INST TH S))
      (L2F (EXECUTE-L2F INST TH S))
      (L2I (EXECUTE-L2I INST TH S))
      (LADD (EXECUTE-LADD INST TH S))
      (LALOAD (EXECUTE-LALOAD INST TH S))
      (LAND (EXECUTE-LAND INST TH S))
      (LASTORE (EXECUTE-LASTORE INST TH S))
      (LCMP (EXECUTE-LCMP INST TH S))
      (LCONST_0 (EXECUTE-LCONST_X INST TH S 0))
      (LCONST_1 (EXECUTE-LCONST_X INST TH S 1))
      (LDC (EXECUTE-LDC INST TH S))
      (LDC_W (EXECUTE-LDC INST TH S))
      (LDC2_W (EXECUTE-LDC2_W INST TH S))
      (LDIV (EXECUTE-LDIV INST TH S))
      (LLOAD (EXECUTE-LLOAD INST TH S))
      (LLOAD_W (EXECUTE-LLOAD INST TH S))
      (LLOAD_0 (EXECUTE-LLOAD_X INST TH S 0))
      (LLOAD_1 (EXECUTE-LLOAD_X INST TH S 1))
      (LLOAD_2 (EXECUTE-LLOAD_X INST TH S 2))
      (LLOAD_3 (EXECUTE-LLOAD_X INST TH S 3))
      (LMUL (EXECUTE-LMUL INST TH S))
      (LNEG (EXECUTE-LNEG INST TH S))
      (LOOKUPSWITCH (EXECUTE-LOOKUPSWITCH INST TH S))
      (LOR (EXECUTE-LOR INST TH S))
      (LREM (EXECUTE-LREM INST TH S))
      (LRETURN (EXECUTE-LRETURN INST TH S))
      (LSHL (EXECUTE-LSHL INST TH S))
      (LSHR (EXECUTE-LSHR INST TH S))
      (LSTORE (EXECUTE-LSTORE INST TH S))
      (LSTORE_W (EXECUTE-LSTORE INST TH S))
      (LSTORE_0 (EXECUTE-LSTORE_X INST TH S 0))
      (LSTORE_1 (EXECUTE-LSTORE_X INST TH S 1))
      (LSTORE_2 (EXECUTE-LSTORE_X INST TH S 2))
      (LSTORE_3 (EXECUTE-LSTORE_X INST TH S 3))
      (LSUB (EXECUTE-LSUB INST TH S))
      (LUSHR (EXECUTE-LUSHR INST TH S))
      (LXOR (EXECUTE-LXOR INST TH S))
      (MONITORENTER (EXECUTE-MONITORENTER INST TH S))
      (MONITOREXIT (EXECUTE-MONITOREXIT INST TH S))
      (MULTIANEWARRAY (EXECUTE-MULTIANEWARRAY INST TH S))
      (NEW (EXECUTE-NEW INST TH S))
      (NEWARRAY (EXECUTE-NEWARRAY INST TH S))
      (NOP (EXECUTE-NOP INST TH S))
      (POP (EXECUTE-POP INST TH S))
      (POP2 (EXECUTE-POP2 INST TH S))
      (PUTFIELD (EXECUTE-PUTFIELD INST TH S))
      (PUTSTATIC (EXECUTE-PUTSTATIC INST TH S))
      (RET (EXECUTE-RET INST TH S))
      (RET_W (EXECUTE-RET INST TH S))
      (RETURN (EXECUTE-RETURN INST TH S))
      (SALOAD (EXECUTE-SALOAD INST TH S))
      (SASTORE (EXECUTE-SASTORE INST TH S))
      (SIPUSH (EXECUTE-SIPUSH INST TH S))
      (SWAP (EXECUTE-SWAP INST TH S))
      (TABLESWITCH (EXECUTE-TABLESWITCH INST TH S))
      (HALT S)
      (OTHERWISE S))))
  :hints (("Goal"
           :in-theory (disable
      EXECUTE-AALOAD
      EXECUTE-AASTORE
      EXECUTE-ACONST_NULL
      EXECUTE-ALOAD
      EXECUTE-ALOAD_X
      EXECUTE-ALOAD_X
      EXECUTE-ALOAD_X
      EXECUTE-ALOAD_X
      EXECUTE-ANEWARRAY
      EXECUTE-ARETURN
      EXECUTE-ARRAYLENGTH
      EXECUTE-ASTORE
      EXECUTE-ASTORE_X
      EXECUTE-ASTORE_X
      EXECUTE-ASTORE_X
      EXECUTE-ASTORE_X
      EXECUTE-BALOAD
      EXECUTE-BASTORE
      EXECUTE-BIPUSH
      EXECUTE-CALOAD
      EXECUTE-CASTORE
      EXECUTE-CHECKCAST
      EXECUTE-D2F
      EXECUTE-D2I
      EXECUTE-D2L
      EXECUTE-DADD
      EXECUTE-DALOAD
      EXECUTE-DASTORE
      EXECUTE-DCMPG
      EXECUTE-DCMPL
      EXECUTE-DCONST_0
      EXECUTE-DCONST_1
      EXECUTE-DDIV
      EXECUTE-DLOAD_X
      EXECUTE-DLOAD_X
      EXECUTE-DLOAD_X
      EXECUTE-DLOAD_X
      EXECUTE-DMUL
      EXECUTE-DNEG
      EXECUTE-DREM
      EXECUTE-DRETURN
      EXECUTE-DSTORE
      EXECUTE-DSTORE_X
      EXECUTE-DSTORE_X
      EXECUTE-DSTORE_X
      EXECUTE-DSTORE_X
      EXECUTE-DSUB
      EXECUTE-DUP
      EXECUTE-DUP_X1
      EXECUTE-DUP_X2
      EXECUTE-DUP2
      EXECUTE-DUP2_X1
      EXECUTE-DUP2_X2
      EXECUTE-F2D
      EXECUTE-F2I
      EXECUTE-F2L
      EXECUTE-FADD
      EXECUTE-FALOAD
      EXECUTE-FASTORE
      EXECUTE-FCMPG
      EXECUTE-FCMPL
      EXECUTE-FCONST_0
      EXECUTE-FCONST_1
      EXECUTE-FCONST_2
      EXECUTE-FDIV
      EXECUTE-FLOAD
      EXECUTE-FLOAD_X
      EXECUTE-FLOAD_X
      EXECUTE-FLOAD_X
      EXECUTE-FLOAD_X
      EXECUTE-FMUL
      EXECUTE-FNEG
      EXECUTE-FREM
      EXECUTE-FRETURN
      EXECUTE-FSTORE
      EXECUTE-FSTORE_X
      EXECUTE-FSTORE_X
      EXECUTE-FSTORE_X
      EXECUTE-FSTORE_X
      EXECUTE-FSUB
      EXECUTE-GETFIELD
      EXECUTE-GETSTATIC
      EXECUTE-GOTO
      EXECUTE-GOTO_W
      EXECUTE-I2B
      EXECUTE-I2C
      EXECUTE-I2D
      EXECUTE-I2F
      EXECUTE-I2L
      EXECUTE-I2S
      EXECUTE-IADD
      EXECUTE-IALOAD
      EXECUTE-IAND
      EXECUTE-IASTORE
      EXECUTE-ICONST_X
      EXECUTE-ICONST_X
      EXECUTE-ICONST_X
      EXECUTE-ICONST_X
      EXECUTE-ICONST_X
      EXECUTE-ICONST_X
      EXECUTE-ICONST_X
      EXECUTE-IDIV
      EXECUTE-IF_ACMPEQ
      EXECUTE-IF_ACMPNE
      EXECUTE-IF_ICMPEQ
      EXECUTE-IF_ICMPGE
      EXECUTE-IF_ICMPGT
      EXECUTE-IF_ICMPLE
      EXECUTE-IF_ICMPLT
      EXECUTE-IF_ICMPNE
      EXECUTE-IFEQ
      EXECUTE-IFGE
      EXECUTE-IFGT
      EXECUTE-IFLE
      EXECUTE-IFLT
      EXECUTE-IFNE
      EXECUTE-IFNONNULL
      EXECUTE-IFNULL
      EXECUTE-IINC
      EXECUTE-ILOAD
      EXECUTE-ILOAD_X
      EXECUTE-ILOAD_X
      EXECUTE-ILOAD_X
      EXECUTE-ILOAD_X
      EXECUTE-IMUL
      EXECUTE-INEG
      EXECUTE-INSTANCEOF
      EXECUTE-INVOKESPECIAL
      EXECUTE-INVOKESTATIC
      EXECUTE-INVOKEVIRTUAL
      EXECUTE-IOR
      EXECUTE-IREM
      EXECUTE-IRETURN
      EXECUTE-ISHL
      EXECUTE-ISHR
      EXECUTE-ISTORE
      EXECUTE-ISTORE_X
      EXECUTE-ISTORE_X
      EXECUTE-ISTORE_X
      EXECUTE-ISTORE_X
      EXECUTE-ISUB
      EXECUTE-IUSHR
      EXECUTE-IXOR
      EXECUTE-JSR
      EXECUTE-JSR_W
      EXECUTE-L2D
      EXECUTE-L2F
      EXECUTE-L2I
      EXECUTE-LADD
      EXECUTE-LALOAD
      EXECUTE-LAND
      EXECUTE-LASTORE
      EXECUTE-LCMP
      EXECUTE-LCONST_X
      EXECUTE-LCONST_X
      EXECUTE-LDC
      EXECUTE-LDC
      EXECUTE-LDC2_W
      EXECUTE-LDIV
      EXECUTE-LLOAD
      EXECUTE-LLOAD_X
      EXECUTE-LLOAD_X
      EXECUTE-LLOAD_X
      EXECUTE-LLOAD_X
      EXECUTE-LMUL
      EXECUTE-LNEG
      EXECUTE-LOOKUPSWITCH
      EXECUTE-LOR
      EXECUTE-LREM
      EXECUTE-LRETURN
      EXECUTE-LSHL
      EXECUTE-LSHR
      EXECUTE-LSTORE
      EXECUTE-LSTORE_X
      EXECUTE-LSTORE_X
      EXECUTE-LSTORE_X
      EXECUTE-LSTORE_X
      EXECUTE-LSUB
      EXECUTE-LUSHR
      EXECUTE-LXOR
      EXECUTE-MONITORENTER
      EXECUTE-MONITOREXIT
      EXECUTE-MULTIANEWARRAY
      EXECUTE-NEW
      EXECUTE-NEWARRAY
      EXECUTE-NOP
      EXECUTE-POP
      EXECUTE-POP2
      EXECUTE-PUTFIELD
      EXECUTE-PUTSTATIC
      EXECUTE-RET
      EXECUTE-RETURN
      EXECUTE-SALOAD
      EXECUTE-SASTORE
      EXECUTE-SIPUSH
      EXECUTE-SWAP
      EXECUTE-TABLESWITCH))))

(in-theory (disable do-inst))

(defthm step-opener
  (implies (syntaxp (and (quotep th)
                         (integerp (cadr th))))
           (equal (step th s)
                  (if (equal (status th s)
                             'SCHEDULED)
                      (do-inst (next-inst th s) th s)
                      s))))

(in-theory (disable step))

(defthm run-opener
  (and (implies (endp schedule) (equal (run schedule s) s))
       (equal (run (cons th schedule) s)
              (run schedule (step th s)))))

(defthm run-append
  (equal (run (append a b) s)
         (run b (run a s))))

(in-theory (disable run))

; Lemma [1]

(defthm [1]
  (good-state *a0*)
  :rule-classes nil)

; Lemma [2]
; We will decompose [2] into (a) th=0, (b) other scheduled threads, (c)
; unscheduled threads.

; First a few lemmas.

(defthm equal-len-0
  (equal (equal (len x) 0)
         (endp x)))

(defthm assoc-equal-i-cdr-heap
  (implies (and (good-threads j tt c m mc flg1)
                (integerp j)
                (good-objrefs tt  heap flg2))
           (equal (ASSOC-EQUAL i heap)
                  (if (and (integerp i)
                           (<= (+ 8 j) i)
                           (<= i (+ 7 j (len heap))))
                      (if (and flg2 (equal i (+ 7 j (len heap))))
                          (cons i '(("Job"  ("objref:LContainer;" . (REF -1)))
                                    ("java/lang/Thread")
                                    ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0))))
                        (cons i '(("Job" ("objref:LContainer;" REF 8))
                                  ("java/lang/Thread")
                                  ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))))
                    nil)))
  :hints (("Goal" :in-theory (disable good-incr-frame good-run-frame))))

(defthm good-objrefs-setref-gen
  (implies
   (and (consp heap)
        (integerp j)
        (good-threads j tt c m mc flg1)
        (good-objrefs tt heap t))
   (good-objrefs
    tt
    (bind (- (+ 8 (len heap) j) 1)
          '(("Job" ("objref:LContainer;" REF 8))
            ("java/lang/Thread")
            ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
          heap)
    nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable good-incr-frame good-run-frame))))

; This lemma establishes that when setref writes to the "objref:LContainer;" field,
; we can convert the ``except last'' flag of good-objrefs from t to nil.

(defthm good-objrefs-setref
  (implies (and (consp heap)
                (good-threads 1 tt c m mc flg1)
                (good-objrefs tt heap t)
                (force (equal delta (+ 8 (len heap)))))
           (good-objrefs
            tt
            (bind delta
                  '(("Job" ("objref:LContainer;" REF 8))
                    ("java/lang/Thread")
                    ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
                  heap)
            nil))
  :hints (("Goal" :use ((:instance good-objrefs-setref-gen (j 1))))))

; We now prove a symmetric lemma that says when we allocate a new thread
; and a new object in the heap we can convert the flag from nil to t.

(defthm good-objrefs-new-thread
  (implies (and (integerp j)
                (good-threads j tt c m mc flg1)
                (good-objrefs tt heap nil)
                (force (equal delta (+ 8 j))))
           (good-objrefs
            (bind (+ j (len heap))
                  (list cs
                        'UNSCHEDULED
                        (list 'REF (+ delta (len heap))))
                  tt)
            (bind (+ delta (len heap))
                  '(("Job" ("objref:LContainer;" . (REF -1)))
                    ("java/lang/Thread")
                    ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
                  heap)
            t))
  :hints (("Goal" :in-theory (disable good-incr-frame good-run-frame))))

(defthm good-threads-new-thread
  (implies (and (integerp j)
                (good-threads j tt c m mc nil)
                (good-objrefs tt heap flg)
                (< m (+ j (len heap)))
                (force (equal delta (+ 8 j))))
           (good-threads j
                         (bind (+ j (len heap))
                               (list
;                              (make-thread
                                 (list
                                   (make-frame
                                     0
                                     `((REF ,(+ delta (len heap))))
                                     NIL
                                     *Job.run*
                                     'UNLOCKED
                                     "Job"))
                                  'UNSCHEDULED
                                  (list 'REF (+ delta (len heap))))
                               tt)
                         c m mc t))
  :hints (("Goal" :in-theory (disable good-incr-frame))))

(defthm rreftothread-good-threads
  (implies (and (good-threads j tt c m mc flg1)
                (integerp j))
           (equal (rreftothread ref tt)
                  (if (and (consp ref)
                           (equal (car ref) 'REF)
                           (null (cddr ref)))
                      (let ((i (cadr ref)))
                        (if (and (integerp i)
                                 (<= (+ 8 j) i)
                                 (<= i (- (+ 8 j (len tt)) 1)))
                            (- i 8)
                          NIL))
                    nil)))
  :hints (("Goal" :in-theory (disable good-incr-frame good-run-frame))))

(defthm len-thread-table-len-heap-gen
  (implies (and (integerp j)
                (good-threads j tt c m mc flg1)
                (good-objrefs tt heap flg2))
           (equal (len tt)
                  (len heap)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable good-incr-frame good-run-frame))))

; This looks scary because the len expression is replaced by something
; bigger.  But I want to think in terms of the length of the heap, not
; the length of the thread table.

(defthm len-thread-table-len-heap
  (implies (and (good-threads 1 (cdr (thread-table s)) c m mc flg1)
                (good-objrefs (cdr (thread-table s))
                              (CDDDDR (CDDDDR (CDR (heap S))))
                              flg2))
           (equal (len (cdr (thread-table s)))
                  (len (CDDDDR (CDDDDR (CDR (heap S)))))))
  :hints (("Goal" :in-theory (enable thread-table heap)
                  :use ((:instance len-thread-table-len-heap-gen
                                   (j 1)
                                   (tt (cdr (thread-table s)))
                                   (heap (CDDDDR (CDDDDR (CDR (heap S))))))))))

(defthm good-objrefs-new-schedule
  (implies (and (good-threads j tt c m mc flg1)
                (integerp j)
                (good-objrefs tt heap flg2)
                (integerp th)
                (<= j th)
                (<= th (- (+ j (len tt)) 1)))
           (good-objrefs (bind th
                               (list (cadr (assoc-equal th tt))
                                     'SCHEDULED
                                     (cadddr (assoc-equal th tt)))
                               tt)
                         heap
                         flg2))
  :hints (("Goal" :in-theory (disable good-incr-frame good-run-frame))))

(defthm good-threads-new-schedule-gen
  (implies
   (and (good-threads j tt c m mc t)
        (consp heap)
        (integerp j)
        (good-objrefs tt heap flg2))
   (good-threads
    j
    (bind (- (+ j (len heap)) 1)
          (list (cadr (assoc-equal (- (+ j (len heap)) 1) tt))
                'SCHEDULED
                (cadddr (assoc-equal (- (+ j (len heap)) 1) tt)))
          tt)
    c m mc nil))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable good-incr-frame
                                      ; good-run-frame
                                      ))))

(defthm good-threads-new-schedule
  (implies
   (and (good-threads 1 tt c m mc t)
        (good-objrefs tt heap flg2)
        (consp heap)
        (force (equal n (len heap))))
   (good-threads
    1
    (bind n
          (list (cadr (assoc-equal n tt))
                'SCHEDULED
                (cadddr (assoc-equal n tt)))
          tt)
    c m mc nil))
  :hints (("Goal" :use ((:instance good-threads-new-schedule-gen
                                   (j 1))))))

(defthm nth-0 (equal (nth 0 x) (car x)))

(in-theory (disable nth))

(defthm popn-n
  (implies (and (integerp n)
                (<= 0 n))
           (equal (popn (+ 1 n) x)
                  (popn n (cdr x)))))

(defthm ref-hack
  (implies (equal ref (list 'REF n))
           (equal (cadr ref) n)))

(defthm stack-hack-1
  (implies (equal stack (list item0))
           (equal (car stack) item0)))

(defthm stack-hack-2a
  (implies (equal stack (list item0 item1))
           (equal (car stack) item0)))

(defthm stack-hack-2b
  (implies (equal stack (list item0 item1))
           (equal (cadr stack) item1)))


; Phased simplification

(mutual-recursion
 (defun find-first-use (fn term)
   (cond ((acl2::variablep term) nil)
         ((acl2::fquotep term) nil)
         ((eq fn (acl2::ffn-symb term)) term)
         (t (find-first-use-lst fn (acl2::fargs term)))))
 (defun find-first-use-lst (fn terms)
   (cond ((endp terms) nil)
         (t (or (find-first-use fn (car terms))
                (find-first-use-lst fn (cdr terms)))))))

(defun phase1-hint (clause stablep)
  (cond (stablep
         (let ((term (find-first-use-lst 'step clause)))
           (cond
            (term
             `(:computed-hint-replacement
               ((phase2-hint acl2::clause acl2::stable-under-simplificationp))
               :expand (,term)))
            (t nil))))
        (t nil)))

(defun phase2-hint (clause stablep)
  (cond (stablep
         (let ((term (find-first-use-lst 'good-state clause)))
           (cond
            (term
             `(:in-theory (enable good-state)))
            (t nil))))
        (t nil)))

(in-theory (disable good-state step-opener))

(defthm update-nth-n
  (implies (and (integerp n)
                (<= 0 n))
           (equal (update-nth (+ 1 n) v lst)
                  (cons (car lst) (update-nth n v (cdr lst))))))

; (acl2::divert)

(defthm [2a]
  (implies (good-state s)
           (good-state (step 0 s)))
  :rule-classes nil
  :hints
  (("Goal" :expand (good-state s))
   (phase1-hint acl2::clause acl2::stable-under-simplificationp)))

; (acl2::undivert)

(in-theory (disable int-fix))

;I have changed this theorem so it is true but I don't really know what
;form I should use...

(defthm [3a]
  (implies (good-state s)
           (or (equal (counter s) nil)
               (rel (counter s) (counter (step 0 s)))))
  :rule-classes nil
  :hints
  (("Goal" :expand (good-state s))
   (phase1-hint acl2::clause acl2::stable-under-simplificationp)))

; We next deal with stepping an arbitrary Job, i.e, a thread th such
; that 1<= th < (len (heap s)).

; Suppose we know (good-state s).  Now how do we open up (step th s)?
; We need to get
; (good-thread i
;              (if (and (endp (cdr tt))
;                       except-last-flg)
;                  'unscheduled
;                'scheduled)
;              (car tt)
;              counter monitor mcount)
; appropriately instantiated and into the theorem.  Then we need
; to get it splattered open.

(defthm good-threads-step
  (implies
   (and (case-split (good-thread th 'SCHEDULED (cons th thread) c m mc))
        (integerp i)
        (good-threads i tt c m mc flg)
        (equal (cadr (binding th tt)) 'SCHEDULED))
   (good-threads i (bind th thread tt) c m mc flg))
  :hints (("Goal" :in-theory (disable good-run-frame good-incr-frame))))

(defthm good-objrefs-step
  (implies
   (and (equal (caddr thread) (list 'REF (+ 8 th)))
        (assoc-equal th tt)
        (good-objrefs tt heap flg))
   (good-objrefs (bind th thread tt) heap flg)))

; The proof of lemma1 raises the case that (equal th <monitor>) and
; because th is a variable, it is replaced everywhere by <monitor>.  I
; don't want that to happen because its harder for me to read.  So I
; shut off object-lockedp after proving this little theorem.
; Object-lockedp was invented just to hide the (equal th <monitor>).

(defthm object-lockedp-opener-1
  (implies (equal th thmon)
           (equal (object-lockedp th thmon 1) t)))

(defthm object-lockedp-opener-2
  (implies (not (equal th thmon))
           (equal (object-lockedp th thmon 1) nil)))

(defthm object-lockedp-opener-3
  (equal (object-lockedp th1 th2 0) nil))

(in-theory (disable object-lockedp))

; Free-var below prevents frequent tries.

(defthm assoc-equal-non-nil
  (implies (and (equal (car (assoc-equal free-th (cdr (thread-table s)))) th)
                (syntaxp (equal free-th th))
                (equal free-th th)
                (integerp th))
           (assoc-equal th (cdr (thread-table s)))))

(defthm lookup-methodref-incr
  (implies (and (equal ct (class-table *a0*))
                (force (equal class "Job")))
           (equal (lookup-methodref "incr:()LJob;" class ct)
                  '("Job" . ("incr:()LJob;" NIL
                    (ALOAD_0)
                    (GETFIELD 2) ; Job.objref:LContainer;
                    (DUP)
                    (ASTORE_1)
                    (MONITORENTER)
                    (ALOAD_0)
                    (GETFIELD 2) ; Job.objref:LContainer;
                    (ALOAD_0)
                    (GETFIELD 2) ; Job.objref:LContainer;
                    (GETFIELD 3) ; Container.counter:I
                    (ICONST_1)
                    (IADD)
                    (PUTFIELD 3) ; Container.counter:I
                    (ALOAD_1)
                    (MONITOREXIT)
                    (GOTO 8)
                    (ASTORE_2)
                    (ALOAD_1)
                    (MONITOREXIT)
                    (ALOAD_2)
                    (ATHROW)
                    (ALOAD_0)
                    (ARETURN))))))

(defthm lookup-methodref-run
  (implies (and (equal ct (class-table *a0*))
                (force (equal class "Job")))
           (equal (lookup-methodref "run:()V" class ct)
                  '("Job" . ("run:()V" NIL
                    (ALOAD_0)
                    (INVOKEVIRTUAL 4) ; Job.incr:()LJob;
                    (POP)
                    (GOTO -5))))))

(in-theory (disable lookup-methodref))

(defthm good-threads-step-over-monitorenter-lemma1
  (implies
   (and (integerp i)
        (integerp th)
        (< th i)
        (good-threads i tt c 0 0 flg))
   (good-threads i tt c th 1 flg))
  :hints (("Goal" :in-theory (enable object-lockedp))))

(defthm good-threads-step-over-monitorenter
  (implies
   (and (object-lockedp th thmon 1)
        (case-split (good-thread th 'SCHEDULED
                                 (cons th thread) c thmon 1))
        (integerp i)
        (good-threads i tt c 0 0 flg)
        (equal (cadr (binding th tt)) 'SCHEDULED))
   (good-threads i (bind th thread tt) c thmon 1 flg))
  :hints (("Goal" :in-theory (enable object-lockedp))))

(defthm good-threads-step-over-monitorexit-lemma1
  (implies
   (and (integerp i)
        (integerp th)
        (< th i)
        (good-threads i tt c th 1 flg))
   (good-threads i tt c 0 0 flg))
  :hints (("Goal" :in-theory (enable object-lockedp))))

(defthm good-threads-step-over-monitorexit
  (implies
   (and (case-split (good-thread th 'SCHEDULED (cons th thread) c 0 0))
        (integerp i)
        (good-threads i tt c th 1 flg)
        (equal (cadr (binding th tt)) 'SCHEDULED))
   (good-threads i (bind th thread tt) c 0 0 flg))
  :hints (("Goal" :in-theory (enable object-lockedp))))

; Now I need to prove that you can step over the putfield.

(defthm good-threads-step-over-putfield-lemma1
  (implies
   (and (integerp i)
        (integerp th)
        (< th i)
        (good-threads i tt c th 1 flg))
   (good-threads i tt (int-fix (+ 1 c)) th 1 flg))
  :hints (("Goal" :in-theory (enable object-lockedp))))

(defthm good-thread-without-lock-allows-bump
  (implies (and (good-thread i 'SCHEDULED thread c1 m 1)
                (not (equal (car thread) m)))
           (good-thread i 'SCHEDULED thread c2 m 1)))

(defthm good-threads-step-over-putfield
  (implies
   (and (object-lockedp th thmon 1)
        (case-split (good-thread th 'SCHEDULED
                                 (cons th thread)
                                 (int-fix (+ 1 c))
                                 th 1))
        (integerp i)
        (good-threads i tt c thmon 1 flg)
        (equal (cadr (binding th tt)) 'SCHEDULED))
   (good-threads i (bind th thread tt) (int-fix (+ 1 c)) thmon 1 flg))
  :hints (("Goal" :in-theory (cons 'object-lockedp (disable good-thread)))
          ("Subgoal *1/2'"
           :cases ((equal i th))
           :in-theory (enable good-thread))))

(defthm last-thread-sometimes-unscheduled-gen
  (implies (and (integerp i)
                (consp heap)
                (good-threads i tt c m mc T)
                (GOOD-OBJREFS tt heap T))
           (EQUAL (CADDR (ASSOC-EQUAL (- (+ i (LEN heap)) 1) tt))
                  'UNSCHEDULED))
  :rule-classes nil)

(defthm last-thread-sometimes-unscheduled
  (implies (and (good-threads 1 tt c m mc t)
                (consp heap)
                (good-objrefs tt heap t))
           (EQUAL (CADDR (ASSOC-EQUAL (len heap) tt))
                  'UNSCHEDULED))
  :hints (("Goal" :use ((:instance last-thread-sometimes-unscheduled-gen
                                   (i 1))))))

(defthm bind-bind
  (equal (bind i v1 (bind i v2 lst))
         (bind i v1 lst)))

(defthm lookup-methodref-in-good-class-table
  (implies (and (syntaxp (and (quotep class)
                              (quotep method)))
                (good-class-table ct))
           (equal (lookup-methodref class method ct)
                  (lookup-methodref class method (class-table *a0*))))
  :hints (("Goal" :in-theory (enable good-class-table))))

; (acl2::divert)


(in-theory (disable good-thread0 main-pc))

(defthm integerp-int-fix
  (integerp (int-fix x))
  :hints (("Goal" :in-theory (enable int-fix))))

(defthm [2b]
  (implies (and (good-state s)
                (integerp th)
                (<= 1 th)
                (<= th (- (len (heap s)) 9))
                (good-thread th
                             'SCHEDULED
                             (assoc-equal th (thread-table s))
                             (gf "Container" "counter:I" 8 (heap s))
                             (gf "java/lang/Object" "<monitor>" 8 (heap s))
                             (gf "java/lang/Object" "<mcount>" 8 (heap s))))
           (good-state (step th s)))
  :rule-classes nil
  :hints
  (("Goal" :expand (good-state s))
   (phase1-hint acl2::clause acl2::stable-under-simplificationp)))

; (acl2::undivert)

(defthm [3b]
  (implies (and (good-state s)
                (integerp th)
                (<= 1 th)
                (<= th (- (len (heap s)) 9))
                (good-thread th
                             'SCHEDULED
                             (assoc-equal th (thread-table s))
                             (gf "Container" "counter:I" 8 (heap s))
                             (gf "java/lang/Object" "<monitor>" 8 (heap s))
                             (gf "java/lang/Object" "<mcount>" 8 (heap s))))
           (or (equal (counter s) nil)
               (rel (counter s) (counter (step th s)))))
  :rule-classes nil
  :hints
  (("Goal" :expand (good-state s))
   (phase1-hint acl2::clause acl2::stable-under-simplificationp)))


(defthm [2c]
  (implies (and (good-state s)
                (not (equal (status th s) 'SCHEDULED)))
           (good-state (step th s)))
  :rule-classes nil
  :otf-flg t
  :hints
  (("Goal" :in-theory (enable step))))

(defthm [3c]
  (implies (and (good-state s)
                (not (equal (status th s) 'SCHEDULED)))
           (or (equal (counter s) nil)
               (rel (counter s) (counter (step th s)))))
  :rule-classes nil
  :otf-flg t
  :hints
  (("Goal" :in-theory (enable step))))

; Now we put a, b, and c together.

(defthm assoc-equal-th-cdr-thread-table
  (implies (and (alistp tt)
                (good-threads j tt c m mc flg1)
                (integerp j))
           (equal (consp (ASSOC-EQUAL th tt))
                  (and (integerp th)
                       (<= j th)
                       (<= th (- (+ (len tt) j) 1)))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable good-incr-frame good-run-frame))))

; This is a surprisingly long proof at about 530 seconds.  I am sure I
; could shorten it by proving good-state implies good-threads and
; good-objrefs, appropriately.

(defthm cases-on-th
  (implies (good-state s)
           (or (equal th 0)
               (and (integerp th)
                    (<= 1 th)
                    (<= th (- (len (heap s)) 9)))
               (not (equal (status th s) 'SCHEDULED))))
  :rule-classes nil
  :hints (("Goal"
           :use
           (:instance assoc-equal-th-cdr-thread-table
                      (tt (cdr (thread-table s)))
                      (j 1)
                      (c (gf "Container" "counter:I" 8 (heap s)))
                      (m (gf "java/lang/Object" "<monitor>" 8 (heap s)))
                      (mc (gf "java/lang/Object" "<mcount>" 8 (heap s)))
                      (flg1
                       (case (main-pc
                              (thread-call-stack
                               (car (thread-table s))))
                         (8 nil)
                         (25 nil)
                         (otherwise t))
                       ))
           :in-theory (cons 'good-state (disable good-threads
                                                 STANDARD-HEAP-PREFIXP)))))

(defthm good-threads-all-lemma
  (implies (and (good-threads j tt c m mc flg1)
                (integerp th)
                (<= j th)
                (<= th (- (+ (len tt) j) 1))
                (integerp j))
           (good-thread th
                        (if (and flg1 (equal th (- (+ (len tt) j) 1)))
                            'UNSCHEDULED
                          'SCHEDULED)
                        (assoc-equal th tt)
                        c m mc))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable good-incr-frame good-run-frame))))

(defthm good-threads-all
  (implies (and (good-state s)
                (integerp th)
                (<= 1 th)
                (<= th (- (len (heap s)) 9)))
           (good-thread th
                        (if (and (<= 11 (main-pc
                                         (thread-call-stack
                                          (car (thread-table s)))))
                                 (< (main-pc
                                     (thread-call-stack
                                      (car (thread-table s))))
                                    25)
                                 (equal th (- (len (heap s)) 9)))
                            'UNSCHEDULED
                          'SCHEDULED)
                        (assoc-equal th (thread-table s))
                        (gf "Container" "counter:I" 8 (heap s))
                        (gf "java/lang/Object" "<monitor>" 8 (heap s))
                        (gf "java/lang/Object" "<mcount>" 8 (heap s))))
  :rule-classes nil
  :hints (("Goal" :use
           (:instance good-threads-all-lemma
                      (tt (cdr (thread-table s)))
                      (j 1)
                      (c (gf "Container" "counter:I" 8 (heap s)))
                      (m (gf "java/lang/Object" "<monitor>" 8 (heap s)))
                      (mc (gf "java/lang/Object" "<mcount>" 8 (heap s)))
                      (flg1 (and (<= 11 (main-pc
                                         (thread-call-stack
                                          (car (thread-table s)))))
                                 (< (main-pc
                                     (thread-call-stack
                                      (car (thread-table s))))
                                    25))))
           :in-theory (cons 'good-state (disable good-threads
                                                 good-thread
                                                 good-thread0
                                                 )))))

(defthm good-thread-unscheduled-means-not-scheduled
  (implies (good-thread th 'UNSCHEDULED thread c m mc)
           (equal (caddr thread) 'UNSCHEDULED)))

(defthm [2]
  (implies (good-state s)
           (good-state (step th s)))
  :hints
  (("Goal" :use ([2a] [2b] [2c]
                      cases-on-th
                      good-threads-all)
    :in-theory (cons 'main-pc (disable good-thread)))))

(defthm [3]
  (implies (good-state s)
           (or (equal (counter s) nil)
               (rel (counter s) (counter (step th s)))))
  :rule-classes nil
  :hints
  (("Goal" :use ([3a] [3b] [3c]
                      cases-on-th
                      good-threads-all)
    :in-theory (disable good-thread rel))))

(defthm good-state-run
  (implies (good-state s)
           (good-state (run sched s)))
  :hints (("Goal" :in-theory (enable run))))

(defthm [4]
  (good-state (run sched *a0*)))

; In the following theorems, read (run sched *a0*) as ``a state reached
; after an arbitrary amount of computation.''  Monotonicty-1 says that
; if the counter in such a state is non-nil, then it is rel to the
; counter in the next state.  Monotonicity-2, further below, says once
; the counter is non-nil, it stays non-nil.

(defthm Monotonicity
  (let* ((s1 (run sched *a0*))
         (s2 (step th s1)))
    (implies (not (equal (counter s1) nil))
             (or (equal (counter s1)
                        (counter s2))
                 (equal (int-fix (+ 1 (counter s1)))
                        (counter s2)))))
  :rule-classes nil
  :hints (("Goal" :use (:instance [3] (s (run sched *a0*))))))

(defthm Monotonicity-corollary
  (let* ((s1 (run sched *a0*))
         (s2 (step th s1)))
    (implies (not (equal (counter s1) nil))
             (not (equal (counter s2) nil))))
  :rule-classes nil
  :hints (("Goal" :use Monotonicity)))

; ---------------------------------------------------------------------------
; Appendix 1.  Heap Size

; Here are a couple of nice lemmas I proved but don't need.  They
; address the relation between the heap size and the counter allocation.

(defthm null-counter-means-heap-len-8
  (implies (good-state s)
           (if (equal (len (heap s)) 8)
               (null (counter s))
             (integerp (counter s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (cons 'good-state
                                   (disable good-thread-table)))))

(defthm heap-len-never-less-than-8
  (implies (good-state s)
           (<= 8 (len (heap s))))
  :rule-classes nil
  :hints (("Goal" :in-theory (cons 'good-state
                                   (disable good-thread-table)))))

; ---------------------------------------------------------------------------
; Appendix 2.  Some Handy Utilities

#|

; Here is a handy macro.  The global variable s is a pseudo-state for
; M5.  If you evaluate (s (caar (cadaar s))) it will return
; thread0-frame0-pc, telling you what state component that refers to.

(assign s
'(((0 ((thread0-frame0-pc (thread0-frame0-local0
                           thread0-frame0-local1
                           thread0-frame0-local2)
                          (thread0-frame0-stack0
                           thread0-frame0-stack1
                           thread0-frame0-stack2)
                          (thread0-frame0-program0
                           thread0-frame0-program1
                           thread0-frame0-program2)
                          thread0-frame0-sync-flg
                          thread0-frame0-cur-class)
       (thread0-frame1-pc (thread0-frame1-local0
                           thread0-frame1-local1
                           thread0-frame1-local2)
                          (thread0-frame1-stack0
                           thread0-frame1-stack1
                           thread0-frame1-stack2)
                          (thread0-frame1-program0
                           thread0-frame1-program1
                           thread0-frame1-program2)
                          thread0-frame1-sync-flg
                          thread0-frame1-cur-class)
       (thread0-frame2-pc (thread0-frame2-local0
                           thread0-frame2-local1
                           thread0-frame2-local2)
                          (thread0-frame2-stack0
                           thread0-frame2-stack1
                           thread0-frame2-stack2)
                          (thread0-frame2-program0
                           thread0-frame2-program1
                           thread0-frame2-program2)
                          thread0-frame2-sync-flg
                          thread0-frame2-cur-class)
       (thread0-frame3-pc (thread0-frame3-local0
                           thread0-frame3-local1
                           thread0-frame3-local2)
                          (thread0-frame3-stack0
                           thread0-frame3-stack1
                           thread0-frame3-stack2)
                          (thread0-frame3-program0
                           thread0-frame3-program1
                           thread0-frame3-program2)
                          thread0-frame3-sync-flg
                          thread0-frame3-cur-class))
     thread0-scheduled-flg
     thread0-rref)
   (1 ((thread1-frame0-pc (thread1-frame0-local0
                           thread1-frame0-local1
                           thread1-frame0-local2)
                          (thread1-frame0-stack0
                           thread1-frame0-stack1
                           thread1-frame0-stack2)
                          (thread1-frame0-program0
                           thread1-frame0-program1
                           thread1-frame0-program2)
                          thread1-frame0-sync-flg
                          thread1-frame0-cur-class)
       (thread1-frame1-pc (thread1-frame1-local0
                           thread1-frame1-local1
                           thread1-frame1-local2)
                          (thread1-frame1-stack0
                           thread1-frame1-stack1
                           thread1-frame1-stack2)
                          (thread1-frame1-program0
                           thread1-frame1-program1
                           thread1-frame1-program2)
                          thread1-frame1-sync-flg
                          thread1-frame1-cur-class)
       (thread1-frame2-pc (thread1-frame2-local0
                           thread1-frame2-local1
                           thread1-frame2-local2)
                          (thread1-frame2-stack0
                           thread1-frame2-stack1
                           thread1-frame2-stack2)
                          (thread1-frame2-program0
                           thread1-frame2-program1
                           thread1-frame2-program2)
                          thread1-frame2-sync-flg
                          thread1-frame2-cur-class)
       (thread1-frame3-pc (thread1-frame3-local0
                           thread1-frame3-local1
                           thread1-frame3-local2)
                          (thread1-frame3-stack0
                           thread1-frame3-stack1
                           thread1-frame3-stack2)
                          (thread1-frame3-program0
                           thread1-frame3-program1
                           thread1-frame3-program2)
                          thread1-frame3-sync-flg
                          thread1-frame3-cur-class))
     thread1-scheduled-flg
     thread1-rref)
   (2 ((thread2-frame0-pc (thread2-frame0-local0
                           thread2-frame0-local1
                           thread2-frame0-local2)
                          (thread2-frame0-stack0
                           thread2-frame0-stack1
                           thread2-frame0-stack2)
                          (thread2-frame0-program0
                           thread2-frame0-program1
                           thread2-frame0-program2)
                          thread2-frame0-sync-flg
                          thread2-frame0-cur-class)
       (thread2-frame1-pc (thread2-frame1-local0
                           thread2-frame1-local1
                           thread2-frame1-local2)
                          (thread2-frame1-stack0
                           thread2-frame1-stack1
                           thread2-frame1-stack2)
                          (thread2-frame1-program0
                           thread2-frame1-program1
                           thread2-frame1-program2)
                          thread2-frame1-sync-flg
                          thread2-frame1-cur-class)
       (thread2-frame2-pc (thread2-frame2-local0
                           thread2-frame2-local1
                           thread2-frame2-local2)
                          (thread2-frame2-stack0
                           thread2-frame2-stack1
                           thread2-frame2-stack2)
                          (thread2-frame2-program0
                           thread2-frame2-program1
                           thread2-frame2-program2)
                          thread2-frame2-sync-flg
                          thread2-frame2-cur-class)
       (thread2-frame3-pc (thread2-frame3-local0
                           thread2-frame3-local1
                           thread2-frame3-local2)
                          (thread2-frame3-stack0
                           thread2-frame3-stack1
                           thread2-frame3-stack2)
                          (thread2-frame3-program0
                           thread2-frame3-program1
                           thread2-frame3-program2)
                          thread2-frame3-sync-flg
                          thread2-frame3-cur-class))
     thread2-scheduled-flg
     thread2-rref))
 ((0 ("java/lang/Class" ("<name>" . "java/lang/Object"))
     ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
  (1 ("java/lang/Class" ("<name>" . "[C"))
     ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
  (2 ("java/lang/Class" ("<name>" . "java/lang/Thread"))
     ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
  (3 ("java/lang/Class" ("<name>" . "java/lang/String"))
     ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
  (4 ("java/lang/Class" ("<name>" . "java/lang/Class"))
     ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
  (5 ("java/lang/Class" ("<name>" . "Apprentice"))
     ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
  (6 ("java/lang/Class" ("<name>" . "Container"))
     ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
  (7 ("java/lang/Class" ("<name>" . "Job"))
     ("java/lang/Object" ("<monitor>" . 0) ("<mcount>" . 0)))
  (8 counter)
  (9 job1)
  (10 job2)
  (11 job3))
 (("java/lang/Object" NIL ()
                      NIL
                      NIL (("<init>:()V" NIL
                            (RETURN)))
                      (REF 0))
  ("[C" ("java/lang/Object")
           NIL
           NIL NIL NIL (REF 1))
  ("java/lang/Thread"
       ("java/lang/Object")
       NIL NIL NIL
       (("run:()V" NIL (RETURN))
        ("start:()V" NIL NIL)
        ("stop:()V" NIL NIL)
        ("<init>:()V" NIL
                  (ALOAD_0)
                  (INVOKESPECIAL "java/lang/Object" "<init>:()V" 0)
                  (RETURN)))
       (REF 2))
  ("java/lang/String"
       ("java/lang/Object")
       ("value:[C")
       NIL NIL
       (("<init>:()V" NIL (ALOAD_0)
                  (INVOKESPECIAL "java/lang/Object" "<init>:()V" 0)
                  (RETURN)))
       (REF 3))
  ("java/lang/Class"
       ("java/lang/Object")
       NIL NIL NIL
       (("<init>:()V" NIL (ALOAD_0)
                  (INVOKESPECIAL "java/lang/Object" "<init>:()V" 0)
                  (RETURN)))
       (REF 4))
  ("Apprentice" ("java/lang/Object")
                NIL NIL NIL
                (("<init>:()V" NIL (ALOAD_0)
                           (INVOKESPECIAL "java/lang/Object" "<init>:()V" 0)
                           (RETURN))
                 ("main:()V" NIL
;                 ("main:([Ljava/lang/String;)V" NIL
                         (NEW "Container")
                         (DUP)
                         (INVOKESPECIAL "Container" "<init>:()V" 0)
                         (ASTORE_1)
                         (NEW "Job")
                         (DUP)
                         (INVOKESPECIAL "Job" "<init>:()V" 0)
                         (ASTORE_2)
                         (ALOAD_2)
                         (ALOAD_1)
                         (INVOKEVIRTUAL "Job" "setref:(LContainer;)V" 1)
                         (ALOAD_2)
                         (INVOKEVIRTUAL "java/lang/Thread" "start:()V" 0)
                         (GOTO -17)))
                (REF 5))
  ("Container" ("java/lang/Object")
               ("counter:I")
               NIL NIL
               (("<init>:()V" NIL
                          (ALOAD_0)
                          (INVOKESPECIAL "java/lang/Object" "<init>:()V" 0)
                          (RETURN)))
               (REF 6))
  ("Job" ("java/lang/Thread" "java/lang/Object")
         ("objref:LContainer;")
         NIL NIL
         (("<init>:()V" NIL
                    (ALOAD_0)
                    (INVOKESPECIAL "java/lang/Thread" "<init>:()V" 0)
                    (RETURN))
          ("incr:()LJob;" NIL
                  (ALOAD_0)
                  (GETFIELD "Job" "objref:LContainer;")
                  (DUP)
                  (ASTORE_1)
                  (MONITORENTER)
                  (ALOAD_0)
                  (GETFIELD "Job" "objref:LContainer;")
                  (ALOAD_0)
                  (GETFIELD "Job" "objref:LContainer;")
                  (GETFIELD "Container" "counter:I")
                  (ICONST_1)
                  (IADD)
                  (PUTFIELD "Container" "counter:I")
                  (ALOAD_1)
                  (MONITOREXIT)
                  (GOTO 8)
                  (ASTORE_2)
                  (ALOAD_1)
                  (MONITOREXIT)
                  (ALOAD_2)
                  (ATHROW)
                  (ALOAD_0)
                  (ARETURN))
          ("setref:(LContainer;)V" NIL
                    (ALOAD_0)
                    (ALOAD_1)
                    (PUTFIELD "Job" "objref:LContainer;")
                    (RETURN))
          ("run:()V" NIL
                 (ALOAD_0)
                 (INVOKEVIRTUAL "Job" "incr:()LJob;" 0)
                 (POP)
                 (GOTO -5)))
         (REF 7)))))

(defmacro s (form) `(let ((s (@ s))) ,form))

; This program can be used to test whether good-state is invariant for
; a few steps

(defun test (sched s)
  (declare (xargs :mode :program))
  (cond ((good-state s)
         (cond ((endp sched) (list 'YES s))
               (t (test (cdr sched) (step (car sched) s)))))
        (t (list 'NO s))))

; This test runs 530 steps, leaves the counter at 15, and confirms
; that we are always in good-states during the run.

(defun repeat (th n)
  (if (zp n)
      nil
    (cons th (repeat th (- n 1)))))

(test (append (repeat 0 50)
              (repeat 1 10)
              (repeat 2 10)
              (repeat 1 20)
              (repeat 2 20)
              (repeat 1 10)
              (repeat 2 10)
              (repeat 1 20)
              (repeat 2 20)
              (repeat 1 10)
              (repeat 2 10)
              (repeat 1 20)
              (repeat 2 20)
              (repeat 1 10)
              (repeat 2 10)
              (repeat 1 20)
              (repeat 2 20)
              (repeat 1 10)
              (repeat 2 10)
              (repeat 1 20)
              (repeat 2 20)
              (repeat 1 10)
              (repeat 2 10)
              (repeat 1 20)
              (repeat 2 20)
              (repeat 1 10)
              (repeat 2 10)
              (repeat 1 20)
              (repeat 2 20)
              (repeat 1 10)
              (repeat 2 10)
              (repeat 1 20)
              (repeat 2 20))
        *a0*)
; jsm

; ----------------------------------------------------------------------------

|#
