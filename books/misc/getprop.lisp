; Copyright (C) 2013, Regents of the University of Texas
; Written by J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; In this sequence of events I define a linear-time no-duplicates
; function for lists of symbols, I prove its guards, I prove that it
; is equivalent to the quadratic time version (just to show that even
; though it uses private property lists it is a :logic mode function I
; can reason about), I define a timed version that prints the cpu time
; used, I prove it returns the correct Boolean answer (again, just to
; prove that it is a :logic mode function we can reason about even
; though it uses timers), and finally I demonstrate it on lists of
; length 20,000.  The time on a duplicate-free list is less than 2
; seconds on a 200 MHz machine.

(in-package "ACL2")

; Section 1.  The Definitions

; Here is my fast version of no-duplicatesp.  Props is a private ACL2
; property list world, different from the one we use.  I just mark
; every element of lst and see if I have ever seen it as I go.  The
; function extend-world "installs" the property list behind the scenes
; in Lisp in a way strictly analogous to ACL2 arrays.  It is logically
; the identity function but makes getprop go fast if everything is up
; to date.

(defun fast-no-duplicatesp1 (lst props)
  (declare (xargs :guard (and (symbol-listp lst)
                              (plist-worldp props))))
  (cond
   ((endp lst) t)
   ((getprop (car lst) 'mark nil 'fast-no-duplicatesp-world props)
    nil)
   (t (fast-no-duplicatesp1 (cdr lst)
                            (extend-world 'fast-no-duplicatesp-world
                                          (putprop (car lst)
                                                   'mark
                                                   t
                                                   props))))))

(defun fast-no-duplicatesp (lst)
  (declare (xargs :guard (symbol-listp lst)))
  (let ((ans (fast-no-duplicatesp1 lst nil)))
    (prog2$
     (retract-world 'fast-no-duplicatesp-world nil)
     ans)))

; The retract-world just undoes all the marks.

; Section 2. Proving It Correct

; Now I prove that fast-no-duplicatesp is equal to no-duplicatesp, the
; ACL2 function that does it in quadratic time.  Ignore all the lemmas
; until the last one of this section.  They just develop the necessary
; invariants.

(defthm sgetprop-means-fast-no-duplicatesp1-fails
  (implies (and (member e lst)
                (sgetprop e 'mark nil 'fast-no-duplicatesp-world props))
           (not (fast-no-duplicatesp1 lst props))))

(defun all-marked-t (props)
  (cond ((endp props) t)
        (t (and (eq (cadr (car props)) 'mark)
                (eq (cddr (car props)) t)
                (all-marked-t (cdr props))))))

(defthm sgetprop-means-in-strip-cars
  (implies (all-marked-t props)
           (iff (sgetprop x 'mark nil name props)
                (member x (strip-cars props)))))

(defthm member-append
  (iff (member e (append a b))
       (or (member e a)
           (member e b))))

(defthm duplicatesp-preserved-by-append
  (implies (no-duplicatesp (append x y))
           (and (no-duplicatesp x)
                (no-duplicatesp y))))

(defthm no-duplicatesp-append-cons
  (equal (no-duplicatesp (append a (cons e b)))
         (and (not (member e a))
              (not (member e b))
              (no-duplicatesp (append a b)))))

(defthm fast-no-duplicatesp1-is-no-duplicatesp-append
  (implies (and (no-duplicatesp (strip-cars props))
                (all-marked-t props))
           (equal (fast-no-duplicatesp1 lst props)
                  (no-duplicatesp (append (strip-cars props) lst)))))

; Isn't this pretty?

(defthm fast-no-duplicatesp-is-no-duplicatesp
  (equal (fast-no-duplicatesp lst)
         (no-duplicatesp lst)))

; Section 3.  The Timed Version

; Here is a version that prints the amount of time it takes.  It
; returns an ACL2 "error triple" (mv erp val state).  You don't really
; care.  But I prove that val is no-duplicatesp just to show that this
; is really a logic mode function even though it messes with state and
; timers.

(set-state-ok t)

(defun timed-fnd (lst state)

; This function answers the no-duplicatesp question for lst and prints
; the time it takes.

  (pprogn
   (set-timer 'fast-no-duplicatesp-time '(0) state)
   (let ((ans (fast-no-duplicatesp lst)))
     (pprogn
      (increment-timer 'fast-no-duplicatesp-time state)
      (print-timer 'fast-no-duplicatesp-time *standard-co* state)
      (princ$ " secs" *standard-co* state)
      (princ$ #\Newline *standard-co* state)
      (pop-timer 'fast-no-duplicatesp-time nil state)
      (value ans)))))

(defthm timed-fnd-is-no-duplicatesp
  (equal (mv-nth 1 (timed-fnd lst state))
         (no-duplicatesp lst))
  :hints (("Goal" :in-theory (disable print-rational-as-decimal))))

; Section 4. Benchmarking

; Now I show that I can answer the no-duplicatesp question for a list
; of 20,000 in about 2 seconds on my 200 MHz machine.

(defun make-temp-symbols (n acc)

; We make a list of n symbols, each of the form TEMPi.  We concatenate
; this list to acc.  The result is (TEMP1 ... TEMPn . acc).  Note that
; the list has no duplicates.  If you wish to produce a list with
; duplicates, initialize acc with '(TEMP1).

  (declare (xargs :mode :program))
  (cond
   ((zp n) acc)
   (t (make-temp-symbols (- n 1)
                         (cons (packn (list "TEMP" n)) acc)))))

(comp t)

; I build two lists, one containing 20,001 symbols whose first and
; last symbols are the same.  The other contains 20,001 distinct
; symbols.

(defconst *dup-list* (make-temp-symbols 20000 '(TEMP1)))

(defconst *no-dup-list* (cons 'TEMP0 (cdr *dup-list*)))

(make-event (er-progn (timed-fnd *dup-list* state)
                      (value '(value-triple :invisible))))

(make-event (er-progn (timed-fnd *no-dup-list* state)
                      (value '(value-triple :invisible))))

; The output of the two calls is shown below.

; ACL2 !>(timed-fnd *dup-list* state)
; [SGC for 38 ARRAY pages..(4725 writable)..(T=39).GC finished]
; [SGC for 38 ARRAY pages..(4725 writable)..(T=39).GC finished]
; [SGC for 38 ARRAY pages..(4725 writable)..(T=40).GC finished]
; 1.42 secs
;  NIL

; ACL2 !>(timed-fnd *no-dup-list* state)
; [SGC for 38 ARRAY pages..(4725 writable)..(T=37).GC finished]
; [SGC for 38 ARRAY pages..(4725 writable)..(T=38).GC finished]
; [SGC for 38 ARRAY pages..(4725 writable)..(T=39).GC finished]
; [SGC for 38 ARRAY pages..(4725 writable)..(T=40).GC finished]
; 1.75 secs
;  T
