; Copyright (C) 2024, J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
; Author: J Strother Moore

; Toy Comparator Sort: An Interesting Exercise in Generalization
; J Strother Moore
; December, 2024

; Abstract:

; This problem is based on the problem described in

; ``A Mechanically Checked Proof of a Comparator Sort Algorithm,'' Bishop Brock
; and J Strother Moore, in C. A. R. Hoare, D. Harel, and M. Broy (Eds.)
; Engineering Theories of Software Intensive Systems, Springer NATO Science
; Series, vol 195, pp. 141--175, 2005.

; In that paper we described the verification of a piece of microcode on a
; Motorola digital signal processor that scanned a sequence of inputs and
; collected the five highest values, and output them in order when stimulated
; on another input line.  The ACL2 solution to that problem may be found in
; books/misc/csort.lisp.

; This is a toy version of a similar problem.  I define a function that scans a
; list of inputs (integers and nils) and collects the minimal and the maximal
; values over the latest sequence of integers and outputs them, in order, when
; the sequence is broken by two nil (non-integers) inputs.  The toy
; formalization has two main modules, one called ``c'' (for ``circuit'') which
; processes a single input value, possibly writing to the output and possibly
; updating an internal state, and the other called ``driver'', which runs the
; circuit over each value in an arbitrarily long list and collects the outputs.
; In the original csort.lisp problem, the circuit was a comparator module and
; the driver was microcode.  The main problem presented by the formalization is
; that the state of the circuit is not visible from outside the driver.  The
; solution, both in csort.lisp and this toy version, is to define a function
; that makes the state visible and then to state a generalized theorem about
; it.

; Re-certification

; (certify-book "toy-csort")

(in-package "ACL2")

; This function, thought of as the ``circuit,'' takes a single input and the
; current state.  If the input is nil, it outputs the minimal element collected
; so far (or the maximal element if the minimal has already been output).
; Otherwise the input is expected to be an integer and is compared to the
; minimal and maximal collected so far and, possibly, replaces the values in
; the state with the input.  In this case the circuit outputs nothing.

(defun c (in st)
; This function returns two values, the output stimulated by this input
; and the new state.
  (if in                          ; in non-nil means in is an integer
      (if st                      ; st non-nil means st is (cons lo hi).
          (let* ((lo (car st))
                 (hi (cdr st))
                 (new-lo (min in (if lo lo in))) ; lo might be nil
                 (new-hi (max in hi)))
            (mv nil              ; no output
                (cons new-lo new-hi)))
          (mv nil (cons in in)))
      (if st
          (let* ((lo (car st))
                 (hi (cdr st))
                 (out (if lo lo hi)))
            (mv out
                (if lo
                    (cons nil hi)
                    nil)))
          (mv nil nil))))

(defun driver (lst st)
  (if (endp lst)
      nil
      (mv-let (out new-st)
        (c (car lst) st)
        (if out
            (cons out (driver (cdr lst) new-st))
            (driver (cdr lst) new-st)))))

(defthm example
  (equal (driver '(1 5 -3 4 7 2 nil nil) nil) '(-3 7)))

; Our goal: When called on a non-empty list of integers, lst, followed by two
; nils (given the initial state nil), driver outputs the minimal element of lst
; and then the maximal element.

; (defthm main
;   (implies (and (consp lst)
;                 (integer-listp lst))
;            (equal (driver (append lst '(nil nil))
;                           nil)
;                   (list (min* lst)
;                         (max* lst)))))

; where

(defun min* (lst)
  (if lst
      (if (cdr lst)
          (min (car lst) (min* (cdr lst)))
          (car lst))
      nil))

(defun max* (lst)
  (if lst
      (if (cdr lst)
          (max (car lst) (max* (cdr lst)))
          (car lst))
      nil))

; By the way, we'll need:

(defthm integerp-min*
  (implies (and lst
                (integer-listp lst))
           (integerp (min* lst))))

(defthm integerp-max*
  (implies (and lst
                (integer-listp lst))
           (integerp (max* lst))))

; Note that driver never exposes the state!  We need a function that does, so
; we can specify what happens on (driver (append a b) st).

(defun fin-st-driver (lst st) ; ``final state of driver''
  (if (endp lst)
      st
      (mv-let (out new-st)
        (c (car lst) st)
        (declare (ignore out))
        (fin-st-driver (cdr lst) new-st))))

; The trickiest aspect of this problem is that (car st) = nil is used to signal
; we have output the minimal and a subsequent nil input will output the
; maximal.  So c behaves unexpectedly if the next input is not nil (i.e., is an
; integer): it puts it into both components of state, as though we're back in
; the initial (nil) state.  So we break the problem of (driver (append lst
; '(nil nil)), where lst contains only integers into two parts, running over a
; list of integers starting in a ``full state,'' and then dealing with two nils
; in a row.  But how do we get into a full state?  The answer is that (driver
; lst nil) recurs to (driver (cdr lst) (cons (car lst) (car lst))), and that
; state is full.  So the lemma below applies.

(defun full-statep (st)
  (and (consp st)
       (integerp (car st))
       (integerp (cdr st))))

(defthm key-lemma
  (implies (and (integer-listp lst)
                (full-statep st))
           (equal (fin-st-driver lst st)
                  (cons (if lst
                            (min (min* lst) (car st))
                            (car st))
                        (if lst
                            (max (max* lst) (cdr st))
                            (cdr st))))))

; Note that the key-lemma, above, is about a function, fin-st-driver, that is
; not mentioned in the main theorem, and involves a generalization (in which
; the final state involves both lst and the initial state.

; This lemma motivated the need for fin-st-driver: how does (driver (append a
; b) st) decompose into terms about driver over a and driver over b?

(defthm driver-append
  (equal (driver (append a b) st)
         (append (driver a st)
                 (driver b (fin-st-driver a st)))))

; Of course, if a is just a list of integers, (driver a st) is nil.
(defthm driver-integer-listp
  (implies (integer-listp a)
           (equal (driver a st) nil)))

; And here's our main theorem.
(defthm main
  (implies (and (consp lst)
                (integer-listp lst))
           (equal (driver (append lst '(nil nil))
                          nil)
                  (list (min* lst)
                        (max* lst)))))

; The proof above generates 1,715 subgoals, including 40 forced hypotheses, and
; takes 0.44 seconds.  We could speed it up by first proving:

; (defthm main-driver-lemma
;   (implies (and (integer-listp a)
;                 (full-statep st))
;            (equal (driver (append a '(nil nil)) st)
;                   (list (if (consp a)
;                             (min (min* a) (car st))
;                             (car st))
;                         (if (consp a)
;                             (max (max* a) (cdr st))
;                             (cdr st))))))

; which generates 104 subgoals and takes 0.03 seconds.  If we then prove main,
; above, the proof generates 128 subgoals including 10 forced hypotheses, in
; 0.05 seconds.



