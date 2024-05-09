; Copyright (C) 2022, ForrestHunt, Inc.
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Release approved by DARPA with "DISTRIBUTION STATEMENT A. Approved
; for public release. Distribution is unlimited."

(in-package "ACL2")

; This is the original definition of (all-pairs imax jmax) from Section 11 of
; the Loop$ Primer.

(defun make-pair (i j)
  (declare (xargs :guard t))
  (cons i j))

(defun all-pairs-helper2 (i j jmax)
  (declare (xargs :measure (nfix (- (+ (nfix jmax) 1) (nfix j)))
                  :guard (and (natp i) (natp j) (natp jmax))))
  (let ((j (nfix j))
        (jmax (nfix jmax)))
    (cond
     ((> j jmax) nil)
     (t (cons (make-pair i j)
              (all-pairs-helper2 i (+ 1 j) jmax))))))

(defun all-pairs-helper1 (i imax jmax)
  (declare (xargs :measure (nfix (- (+ (nfix imax) 1) (nfix i)))
                  :guard (and (natp i) (natp imax) (natp jmax))))
  (let ((i (nfix i))
        (imax (nfix imax)))
    (cond
     ((> i imax) nil)
     (t (append (all-pairs-helper2 i 1 jmax)
                (all-pairs-helper1 (+ 1 i) imax jmax))))))

(defun all-pairs (imax jmax)
  (declare (xargs :guard (and (natp imax) (natp jmax))))
  (all-pairs-helper1 1 imax jmax))

; This is the function in lp17.lisp that computes all-pairs another
; way.

(defun apdh2 (i j ans)
  (cond
   ((natp j)
    (cond ((< j 1) ans)
          (t (apdh2 i (- j 1) (cons (make-pair i j) ans)))))
   (t nil)))

(defun apdh1 (i jmax ans)
  (cond
   ((natp i)
    (cond ((< i 1) ans)
          (t (apdh1 (- i 1) jmax (apdh2 i jmax ans)))))
   (t nil)))

; In lp17.lisp we prove that a certain nested DO loop$ is equal to (apdh1 imax
; jmax nil).

; Our goal now is to prove that (apdh1 imax jmax nil) is equal to (all-pairs
; imax jmax).  That would allow us to conclude that the nested DO loop$ is
; equal to the original all-pairs.  Since (all-pairs imax jmax) is just
; (all-pairs-helper1 1 imax jmax) a more precise statement of our goal is to
; prove

;  (implies (and (natp imax)
;                (natp jmax))
;           (equal (apdh1 imax jmax nil)
;                  (all-pairs-helper1 1 imax jmax)))

; Obviously, we must prove the relation between apdh2 and all-pairs-helper2
; first and then deal with the theorem above.  Also obviously, we must
; generalize both theorems to accomodate the differences between the two
; algorithms.

; There are three differences to overcome.

; (1) the original all-pairs-helper functions count local variables i and j up
;     to imax and jmax, while the apdh functions count imax and jmax down.

; (2) the all-pairs-helper functions add new elements to the result of their
;     recursion, while the apdh functions have an accumulator and add new
;     elements before recursion.

; (3) the all-pairs-helper functions have fully adjustable bounds -- they count
;     from i to imax and from j to jmax, while the apdh functions have fixed
;     lower bounds -- they count from imax to 1 and jmax to 1.

; -----------------------------------------------------------------

; First we will fix the lower bounds problems by defining apd2 and apd1 with
; lower bounds j and i instead of 1 and 1.

(defun apd2 (i j jmax ans)
  (cond
   ((and (natp jmax)
         (natp j)
         (< 0 j))
    (cond ((< jmax j) ans)
          (t (apd2 i j (- jmax 1) (cons (make-pair i jmax) ans)))))
   (t nil)))

(defun apd1 (i imax jmax ans)
  (cond
   ((and (natp imax)
         (natp i)
         (< 0 i))
    (cond ((< imax i) ans)
          (t (apd1 i (- imax 1) jmax (apd2 imax 1 jmax ans)))))
   (t nil)))

; and we'll prove they apdh2 and apdh1 are equal to them when called with 1 as
; the bound.

(defthm apdh2-is-apd2
  (equal (apdh2 i jmax ans)
         (apd2  i 1 jmax ans)))

(defthm apdh1-is-apd1
  (equal (apdh1 imax jmax ans)
         (apd1  1 imax jmax ans)))

; -----------------------------------------------------------------

; Second, will prove apd2 is all-pairs-helper2, with appropriate accomodation
; of the accumulator.  We'll use the standard method of proving the equivalence
; of two (equivalent) functions that recur differently.  Of course, apd2 and
; all-pairs-helper2 are not really equivalent because of the differences
; discussed above.  So we have to generalize the standard method of proving two
; functions equivalent.

; The standard way to prove the equivalence of two (actually equivalent!)
; functions is to first prove a lemma that says one of the functions satisfies
; the definitional equation of the other.  Let's call this the ``Satisfies
; Lemma.''  This lemma the advantage of being a theorem about just one function
; so the induction is on that function's recursion.  That lemma then enables
; the equivalence proof to go through by induction on the other function
; because the Satisfies Lemma lets the first function open up in response to
; the induction by the other function's recursion.  See
; nats-up-is-nats-down.lisp for a simple example.  In our application of this
; general proof strategy we'll use apd2 as the ``first'' function and prove
; that it satisfies the equation of all-pairs-helper2.

(defthm apd2-satisfies-all-pairs-helper2
  (implies (and (natp j)
                (< 0 j)
                (natp jmax))
           (equal (apd2 i j jmax ans)
                  (let ((j (nfix j))
                        (jmax (nfix jmax)))
                    (cond
                     ((> j jmax) ans)
                     (t (cons (make-pair i j)
                              (apd2 i (+ 1 j) jmax ans)))))))
  :hints (("Subgoal *1/1'''"
           :expand ((APD2 I J J ANS)
                    (APD2 I J (+ -1 J)
                          (CONS (CONS I J) ANS)))))
  :rule-classes (:definition))

; Note the name below refers to apdh2 when in fact the lemma is about apd2.
; This lemma proves that apd2 ``is'' all-pairs-helper2.  But we've already
; proved that apdh2 is apd2 when j=1, so together those two facts establish
; what we called ``lemma2'' for apdh2 in our recipe for proving theorems about
; do loop$s.  So we give this lemma that name.

(defthm lp17-11-apdh2-lemma2
  (implies (and (natp j)
                (< 0 j)
                (natp jmax))
           (equal (apd2 i j jmax ans)
                  (append (all-pairs-helper2 i j jmax) ans)))
  :hints (("Goal" :induct (all-pairs-helper2 i j jmax))))

; -----------------------------------------------------------------
; Third, we repeat the same strategy for apd1 and all-pairs-helper1.
; But we have a bit more conventional work to do around the edges.

(defthm assoc-of-append
  (equal (append (append a b) c)
         (append a (append b c))))

(defthm apd1-append
  (implies (and (natp i)
                (< 0 i)
                (natp imax)
                (natp jmax))
           (equal (apd1 i imax jmax (append a b))
                  (append (apd1 i imax jmax a) b))))

(defthm apd1-nil
  (implies (and (syntaxp (not (equal b *nil*)))
                (natp i)
                (< 0 i)
                (natp imax)
                (natp jmax))
           (equal (apd1 i imax jmax b)
                  (append (apd1 i imax jmax nil) b))))


(defthm apd1-satisfies-all-pairs-helper1
  (implies (and (natp i)
                (< 0 i)
                (natp imax)
                (natp jmax))
           (equal (apd1 i imax jmax ans)
                  (let ((i (nfix i))
                        (imax (nfix imax)))
                    (cond
                     ((> i imax) ans)
                     (t (append (apd2 i 1 jmax nil)
                                (append (apd1 (+ 1 i) imax jmax nil)
                                        ans)))))))
  :hints (("Subgoal 2"
           :expand ((APD1 I IMAX JMAX NIL)))
          ("Subgoal 1"
           :expand ((:with apd1 (APD1 I IMAX JMAX NIL)))))
  :rule-classes (:definition))

; Again, we name this lemma after apdh1 instead of apd1.

(defthm lp17-11-apdh1-lemma2
  (implies (and (natp i)
                (< 0 i)
                (natp imax)
                (natp jmax))
           (equal (apd1 i imax jmax ans)
                  (append (all-pairs-helper1 i imax jmax) ans)))
  :hints (("Goal" :induct (all-pairs-helper1 i imax jmax))))

