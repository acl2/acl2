#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

#| 

From http://en.wikipedia.org/wiki/FRACTRAN

FRACTRAN is a Turing-complete esoteric programming language invented
by the mathematician John Conway. A FRACTRAN program is an ordered
list of positive fractions together with an initial positive integer
input n. The program is run by updating the integer n as follows:

  1. For the first fraction f in the list for which nf is an integer,
     replace n by nf

  2. Repeat this rule until no fraction in the list produces an
     integer when multiplied by n, then halt.

|#

(include-book "coi/defung/defung" :dir :system)

(defun fstep (n list)
  (if (endp list) n
    (let ((f (* n (car list))))
      (if (integerp f) f
        (fstep n (cdr list))))))

(def::ung fractran (n list)
  (let ((r (fstep n list)))
    (if (= r n) n
      (fractran r list))))

#|

The simplest FRACTRAN program is a single instruction such as: (3/2)

Given an initial input of the form 2^a 3^b, this program will compute
the sequence 2^{a-1} 3^{b+1}, 2^{a-2} 3^{b+2}, etc, until eventually,
after a steps, no factors of 2 remain and the product with 3/2
no longer yields an integer; the machine then stops with a final
output of 3^{a + b} . It therefore adds two integers together.

|#

(defun add ()
  `(3/2))

(defthm fractran-adds
  (equal (fractran (* (expt 2 7) (expt 3 11)) (add))
         (expt 3 (+ 7 11))))

#|

A multiplier can be created by looping through the adder.

In this case, input of the form 2^a 3^b will result in
a value of the form 5^(a*b)

|#
(defun multiply ()
  `(455/33 11/13 1/11 3/7 11/2 1/3))

(defthm fractran-multiplies
  (equal (fractran (* (expt 2 7) (expt 3 11)) (multiply))
         (expt 5 (* 7 11))))
