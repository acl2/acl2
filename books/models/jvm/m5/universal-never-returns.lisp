#|
Certification:
(include-book "universal")
(certify-book "universal-never-returns" 1)
J Moore
Aug 2, 2002
|#
(in-package "M5")

; Some people leap to the conclusion that because ACL2 is a logic of
; total functions we can only deal with total programs.  That is, of
; course, a misunderstanding.

; In this book I prove that the universal program never terminates.
; This is not difficult and the only reason I prove it is to try to dispell
; the misunderstanding above.

; But the formalization raises problems.  What do we mean, "never
; terminates?"  I mean that once the universal program is invoked by a
; thread, th, then thread th forever stays in the universal program.
; By being "in the universal program" I mean that the program of the
; top frame of the thread is the universal one.

; The only sense in which this is a difficult proof is that we have to
; deal with the effects of arbitrarily many other threads running
; arbitrarily many other programs.  Can they do anything to mess up
; thread th?  Actually they can, e.g., they can run the native "stop"
; method on it.  That won't actually affect the program in the top
; frame of th, so our conjecture holds in the face of such an assault.

; But the most insideous thing another thread can do, it turns out, is
; to execute NEW on a class name that extends threads, in such a way
; that the new thread object created IS th.  This would change the top
; frame of th.  Of course, this cannot happen if th is an extant
; thread at the time the NEW was executed.  But it is for that reason
; that I have had to say that th is a legal thread identifier (a
; natural number less than the length of the thread-table) rather than
; leave it unrestricted.

(defthm len-bind
  (<= (len alist)
      (len (bind th v alist)))
  :rule-classes :linear)

(defun inside-universalp (th s)
  (and (integerp th)
       (<= 0 th)
       (< th (len (thread-table s)))
       (equal (program (top-frame th s))
              *universal-program*)))

; This proof takes a while (> 500 seconds) because it has to consider
; every possible step.  Note the x.

(defthm inside-universalp-step
  (implies (inside-universalp th s)
           (inside-universalp th (step x s)))
  :hints (("Goal"
           :in-theory (enable step))))

(in-theory (disable inside-universalp))

(defthm inside-universalp-run
  (implies (inside-universalp th s)
           (inside-universalp th (run sched s)))
  :hints (("Goal"
           :in-theory (enable run))))

; This is a technical lemma, needed because I've disabled inside-universalp.
; I need to prove that invoking the universal method puts you inside
; universal.

(defthm dumb-little-lemma
  (implies (and (integerp th)
                (<= 0 th)
                (< th (len (thread-table s))))
  (inside-universalp th
                     (MAKE-STATE
    (BIND
     TH
     (LIST
      (PUSH
       '(0 NIL NIL
           ((ICONST_0) (ICONST_1) (IADD) (GOTO -2))
           UNLOCKED "Universal")
       (PUSH (MAKE-FRAME
                  (+ 3
                     (PC (TOP (CADR (ASSOC-EQUAL TH (THREAD-TABLE S))))))
                  (LOCALS (TOP (CADR (ASSOC-EQUAL TH (THREAD-TABLE S)))))
                  (STACK (TOP (CADR (ASSOC-EQUAL TH (THREAD-TABLE S)))))
                  (PROGRAM (TOP (CADR (ASSOC-EQUAL TH (THREAD-TABLE S)))))
                  (SYNC-FLG (TOP (CADR (ASSOC-EQUAL TH (THREAD-TABLE S)))))
                  (CUR-CLASS (TOP (CADR (ASSOC-EQUAL TH (THREAD-TABLE S))))))
             (POP (CADR (ASSOC-EQUAL TH (THREAD-TABLE S))))))
      'SCHEDULED
      (CADDDR (ASSOC-EQUAL TH (THREAD-TABLE S))))
     (THREAD-TABLE S))
    (HEAP S)
    (CLASS-TABLE S))))
  :hints (("Goal" :in-theory (enable inside-universalp))))

(defthm poised-to-invoke-universal-never-returns
  (implies (and (poised-to-invoke-universal th s i)
                (integerp th)
                (<= 0 th)
                (< th (len (thread-table s))))
           (inside-universalp th (run (cons th sched) s))))

