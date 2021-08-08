; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

; The following macro defines the macro the-type-set so that
; (the-type-set x) expands to (the (integer 0 n) x).  It also declares
; the symbols listed below as defconsts whose values are the
; successive powers of 2.

; Warning:  The first seven entries *ts-zero* through
; *ts-complex-rational* are tied down to bit positions 0-6.  See, for
; example, our setting up of the +-alist entry.  Note however that in
; fact, we are wiring in the first seven entries as well, in our
; handling of *type-set-<-table*.  Since < is a function defined only
; on the rationals, the latter decision seems safe even given the
; possibility that we'll add additional numeric types in the future.

; WARNING: If new basic type-sets are added, update the function
; one-bit-type-setp below which enumerates all of the basic type-sets
; and also update *initial-type-set-inverter-rules* which must contain
; a rule for every primitive bit!

;; Historical Comment from Ruben Gamboa:
;; I added *ts-positive-non-ratio*, *ts-negative-non-ratio*, and
;; *ts-complex-non-rational*.

(def-basic-type-sets
  *ts-zero*
  *ts-one*
  *ts-integer>1*
  *ts-positive-ratio*
  #+:non-standard-analysis *ts-positive-non-ratio*
  *ts-negative-integer*
  *ts-negative-ratio*
  #+:non-standard-analysis *ts-negative-non-ratio*

; It is tempting to split the complex rationals into the positive and negative
; complex rationals (i.e., those with positive real parts and those with
; negative real parts).  See the ``Long comment on why we extend the
; true-type-alist to accommodate complex rationals'' in assume-true-false.
; For now, we'll resist that temptation.

  *ts-complex-rational*
  #+:non-standard-analysis *ts-complex-non-rational*
  *ts-nil*
  *ts-t*
  *ts-non-t-non-nil-symbol*
  *ts-proper-cons*
  *ts-improper-cons*
  *ts-string*
  *ts-character*)

; Notes on the Implementation of Type-Sets

; Suppose, contrary to truth but convenient for thinking, that there
; were only 3 ``regular'' type bits, say for cons, symbol, and
; character.  Then the length of the list on which def-basic-type-sets
; would be called would be 3.  Thus the integer 2^3-1 = 7 = ...0000111
; would be the type set that represented the set of all conses,
; symbols, and characters.  The type-set (lognot 7) = ....1111000 = -8
; would be the complement of that, i.e. the type set that consisted of
; everything but conses, symbols, and characters.  Were there only 3
; regular type bits, 7 and -8 would be the maximum and minimum type
; sets, considered as integers,

; Since, in fact, we name 14 regular type bits above, and 2^14 = 16384,
; the type-sets range from -16384 to +16383.

; It is important to note that even though there are only 14 regular
; type bits, type-sets are not exactly 14 bits wide.  A Common Lisp
; integer, when treated as a logical bit vector, can be thought of as
; a infinite series of bits which always concludes with an infinite
; series of 0's (for positive integers) or an infinite series of 1's
; (for negative integers).  We think of the bits in these two infinite
; series as standing for the ``irregular'' (non-ACL2) Common Lisp
; types.  Returning to the example above of 3 regular bits, and
; imagining that the irregular bits are for floats, arrays,
; pathnames, etc., then ...1111000 can be thought of as representing
; the set of all floats, complexes, arrays, pathnames, ..., etc.
; Since we there are an infinite number of these irregular bits the
; only way we can say this without the ``etc.''  is to say ``not
; conses, symbols, or characters.''

; When we first implemented ACL2 we did not use this approach.
; Instead we allocated one additional ``regular'' bit which we named
; *ts-other*, denoting all the ``irregular'' objects.  We cannot
; reconstruct exactly why we did this, though we believe it had to do
; with the misapprehension that use of the so-called ``sign bit'' (as
; in nqthm) would limit type sets to fixnums.  The fallacy of course
; is that in Common Lisp there is no sign bit, there is an infinite
; sequence of them.  In any case, the introduction of *ts-other* had
; several bad effects on our thinking, although it did not cause
; unsoundness.  The main effect was to lead us to pretend that
; type-sets could be thought of as masks of some fixed width, i.e.,
; 15.  But then consider two bit vectors that agree on their low order
; 15 bits but differ on the high order bits.  Are they the same type
; set or not?  Since we compare the type-sets with equality, they
; clearly are not the same.  What made our code correct was that such
; type sets could never arise: the setting of the *ts-other* bit was
; always equal to the setting of all the ``irregular'' bits.  Of
; course, this invariant would have been violated had we ever created
; a type-set by logioring *ts-other* into another type-set, but we
; never did that.  In any case, we now realize that the use of the
; infinite sequence of sign bits a la nqthm is really cleaner because
; it gives us no way to turn on the irregular bits except by
; complementing known bits.

(defconst *ts-positive-integer* (ts-union0 *ts-one*
                                           *ts-integer>1*))

(defconst *ts-non-negative-integer* (ts-union0 *ts-zero*
                                               *ts-positive-integer*))

(defconst *ts-non-positive-integer* (ts-union0 *ts-zero*
                                               *ts-negative-integer*))

(defconst *ts-integer* (ts-union0 *ts-positive-integer*
                                  *ts-zero*
                                  *ts-negative-integer*))

(defconst *ts-rational* (ts-union0 *ts-integer*
                                   *ts-positive-ratio*
                                   *ts-negative-ratio*))

;; Historical Comment from Ruben Gamboa:
;; I added the *ts-real* type, analogous to *ts-rational*.

#+:non-standard-analysis
(defconst *ts-real* (ts-union0 *ts-integer*
                               *ts-positive-ratio*
                               *ts-positive-non-ratio*
                               *ts-negative-ratio*
                               *ts-negative-non-ratio*))

;; Historical Comment from Ruben Gamboa:
;; I added *ts-complex* to include the complex-rationals and
;; non-rationals.

#+:non-standard-analysis
(defconst *ts-complex* (ts-union0 *ts-complex-rational*
                                  *ts-complex-non-rational*))

;; Historical Comment from Ruben Gamboa:
;; I changed the type *ts-acl2-number* to include the new reals
;; and complex numbers as well as the old rational numbers.  I added
;; the types *ts-rational-acl2-number* to stand for the old
;; *ts-acl2-number*, and I added *ts-non-rational-acl2-number* to
;; represent the new numbers.

(defconst *ts-acl2-number*
  #+:non-standard-analysis
  (ts-union0 *ts-real* *ts-complex*)
  #-:non-standard-analysis
  (ts-union0 *ts-rational* *ts-complex-rational*))

(defconst *ts-rational-acl2-number* (ts-union0 *ts-rational*
                                               *ts-complex-rational*))

#+:non-standard-analysis
(defconst *ts-non-rational-acl2-number* (ts-union0 *ts-positive-non-ratio*
                                                   *ts-negative-non-ratio*
                                                   *ts-complex-non-rational*))

(defconst *ts-negative-rational* (ts-union0 *ts-negative-integer*
                                            *ts-negative-ratio*))

(defconst *ts-positive-rational* (ts-union0 *ts-positive-integer*
                                            *ts-positive-ratio*))

(defconst *ts-non-positive-rational* (ts-union0 *ts-zero*
                                                *ts-negative-rational*))

(defconst *ts-non-negative-rational* (ts-union0 *ts-zero*
                                                *ts-positive-rational*))

(defconst *ts-ratio* (ts-union0 *ts-positive-ratio*
                                *ts-negative-ratio*))

(defconst *ts-bit* (ts-union0 *ts-zero* *ts-one*))

;; Historical Comment from Ruben Gamboa:
;; I added the types *ts-non-ratio*, *ts-negative-real*,
;; *ts-positive-real*, *ts-non-positive-real*, and
;; *ts-non-negative-real*, to mimic their *...-rational*
;; counterparts.

#+:non-standard-analysis
(progn

(defconst *ts-non-ratio* (ts-union0 *ts-positive-non-ratio*
                                    *ts-negative-non-ratio*))

(defconst *ts-negative-real* (ts-union0 *ts-negative-integer*
                                        *ts-negative-ratio*
                                        *ts-negative-non-ratio*))

(defconst *ts-positive-real* (ts-union0 *ts-positive-integer*
                                        *ts-positive-ratio*
                                        *ts-positive-non-ratio*))

(defconst *ts-non-positive-real* (ts-union0 *ts-zero*
                                            *ts-negative-real*))

(defconst *ts-non-negative-real* (ts-union0 *ts-zero*
                                            *ts-positive-real*))
)

(defconst *ts-cons* (ts-union0 *ts-proper-cons*
                               *ts-improper-cons*))

(defconst *ts-boolean* (ts-union0 *ts-nil* *ts-t*))

(defconst *ts-true-list* (ts-union0 *ts-nil* *ts-proper-cons*))

(defconst *ts-non-nil* (ts-complement0 *ts-nil*))

(defconst *ts-symbol* (ts-union0 *ts-nil*
                                 *ts-t*
                                 *ts-non-t-non-nil-symbol*))

(defconst *ts-true-list-or-string* (ts-union0 *ts-true-list* *ts-string*))

(defconst *ts-empty* 0)

(defconst *ts-unknown* -1)

;; Historical Comment from Ruben Gamboa:
;; In accordance with the comment above on adding new basic type
;; sets, I added *ts-positive-non-ratio*, *ts-negative-non-ratio*, and
;; *ts-complex-non-rational* to this recognizer.  I wonder if the
;; speed difference is still faster than logcount.  Seems like if it
;; was 75 times faster before, it probably ought to be.

(defun one-bit-type-setp (ts)

; Tests in AKCL (long before we added *ts-one* using one million iterations
; show that this function, as coded, is roughly 75 times faster than one based
; on logcount.  We do not currently use this function but it was once used in
; the double whammy heuristics and because we spent some time finding the best
; way to code it, we've left it for now.

  (or (= (the-type-set ts) *ts-zero*)
      (= (the-type-set ts) *ts-one*)
      (= (the-type-set ts) *ts-integer>1*)
      (= (the-type-set ts) *ts-positive-ratio*)
      #+:non-standard-analysis
      (= (the-type-set ts) *ts-positive-non-ratio*)
      (= (the-type-set ts) *ts-negative-integer*)
      (= (the-type-set ts) *ts-negative-ratio*)
      #+:non-standard-analysis
      (= (the-type-set ts) *ts-negative-non-ratio*)
      (= (the-type-set ts) *ts-complex-rational*)
      #+:non-standard-analysis
      (= (the-type-set ts) *ts-complex-non-rational*)
      (= (the-type-set ts) *ts-nil*)
      (= (the-type-set ts) *ts-t*)
      (= (the-type-set ts) *ts-non-t-non-nil-symbol*)
      (= (the-type-set ts) *ts-proper-cons*)
      (= (the-type-set ts) *ts-improper-cons*)
      (= (the-type-set ts) *ts-string*)
      (= (the-type-set ts) *ts-character*)))

; The following fancier versions of the ts functions and macros will serve us
; well below and in type-set-b.lisp.

;; Historical Comment from Ruben Gamboa:
;; I added here the new type sets that I had defined:
;; *ts-rational-acl2-number*, *ts-non-rational-acl2-number*,
;; *ts-real*, *ts-non-positive-real*, *ts-non-negative-real*,
;; *ts-negative-real*, *ts-positive-real*, *ts-non-ratio*,
;; *ts-complex*, *ts-positive-non-ratio*, *ts-negative-non-ratio*, and
;; *ts-complex-non-rational*.

(defconst *code-type-set-alist*

; This alist serves two distinct purposes.  The first is crucial to soundness:
; it maps each known type-set constant symbol to its value.  (Unsoundness would
; be introduced by mapping such a symbol to an incorrect value.)  Every
; declared type-set constant should be in this list; failure to include a
; symbol precludes its use in ts-union and other type-set building macros.
; Ordering of the alist is unimportant for these purposes.

; The second use is in decode-type-set, where we use it to convert a type-set
; into its symbolic form.  For those purposes it is best if the larger
; type-sets, the one containing more 1 bits, are listed first.  The heuristic
; for converting a type-set into symbolic form is to note whether the type-set
; contains as a subset one of the type-sets mentioned here and if so include
; the corresponding name in the output and delete from the numeric type-set the
; corresponding bits until all all bits are accounted for.

  (list (cons '*ts-unknown* *ts-unknown*)
        (cons '*ts-non-nil* *ts-non-nil*)
        (cons '*ts-acl2-number* *ts-acl2-number*)
        (cons '*ts-rational-acl2-number* *ts-rational-acl2-number*)

        #+:non-standard-analysis
        (cons '*ts-non-rational-acl2-number* *ts-non-rational-acl2-number*)
        #+:non-standard-analysis
        (cons '*ts-real* *ts-real*)

        (cons '*ts-rational* *ts-rational*)
        (cons '*ts-true-list-or-string* *ts-true-list-or-string*)
        (cons '*ts-symbol* *ts-symbol*)
        (cons '*ts-integer* *ts-integer*)

        #+:non-standard-analysis
        (cons '*ts-non-positive-real* *ts-non-positive-real*)
        #+:non-standard-analysis
        (cons '*ts-non-negative-real* *ts-non-negative-real*)

        (cons '*ts-non-positive-rational* *ts-non-positive-rational*)
        (cons '*ts-non-negative-rational* *ts-non-negative-rational*)

        #+:non-standard-analysis
        (cons '*ts-negative-real* *ts-negative-real*)
        #+:non-standard-analysis
        (cons '*ts-positive-real* *ts-positive-real*)

        (cons '*ts-negative-rational* *ts-negative-rational*)
        (cons '*ts-positive-rational* *ts-positive-rational*)
        (cons '*ts-non-negative-integer* *ts-non-negative-integer*)
        (cons '*ts-non-positive-integer* *ts-non-positive-integer*)
        (cons '*ts-positive-integer* *ts-positive-integer*)
        (cons '*ts-bit* *ts-bit*)
        (cons '*ts-ratio* *ts-ratio*)

        #+:non-standard-analysis
        (cons '*ts-non-ratio* *ts-non-ratio*)
        #+:non-standard-analysis
        (cons '*ts-complex* *ts-complex*)

        (cons '*ts-cons* *ts-cons*)
        (cons '*ts-boolean* *ts-boolean*)
        (cons '*ts-true-list* *ts-true-list*)
        (cons '*ts-integer>1* *ts-integer>1*)
        (cons '*ts-zero* *ts-zero*)
        (cons '*ts-one* *ts-one*)
        (cons '*ts-positive-ratio* *ts-positive-ratio*)

        #+:non-standard-analysis
        (cons '*ts-positive-non-ratio* *ts-positive-non-ratio*)

        (cons '*ts-negative-integer* *ts-negative-integer*)
        (cons '*ts-negative-ratio* *ts-negative-ratio*)

        #+:non-standard-analysis
        (cons '*ts-negative-non-ratio* *ts-negative-non-ratio*)
        #+:non-standard-analysis
        (cons '*ts-complex-non-rational* *ts-complex-non-rational*)

        (cons '*ts-complex-rational* *ts-complex-rational*)
        (cons '*ts-nil* *ts-nil*)
        (cons '*ts-t* *ts-t*)
        (cons '*ts-non-t-non-nil-symbol* *ts-non-t-non-nil-symbol*)
        (cons '*ts-proper-cons* *ts-proper-cons*)
        (cons '*ts-improper-cons* *ts-improper-cons*)
        (cons '*ts-string* *ts-string*)
        (cons '*ts-character* *ts-character*)
        (cons '*ts-empty* *ts-empty*)))

(defun logior-lst (lst ans)
  (cond
   ((null lst) ans)
   (t (logior-lst (cdr lst)
                  (logior (car lst) ans)))))

(defun logand-lst (lst ans)
  (cond
   ((null lst) ans)
   (t (logand-lst (cdr lst)
                  (logand (car lst) ans)))))

(mutual-recursion

(defun ts-complement-fn (x)
  (let ((y (eval-type-set x)))
    (if (integerp y)
        (lognot y)
      (list 'lognot (list 'the-type-set y)))))

(defun ts-union-fn (x)
  (cond ((null x) '*ts-empty*)
        ((null (cdr x)) (eval-type-set (car x)))
        (t (let ((lst (eval-type-set-lst x)))
             (cond
              ((integer-listp lst)
               (logior-lst lst *ts-empty*))
              (t
               (xxxjoin 'logior lst)))))))

(defun ts-intersection-fn (x)
  (cond ((null x) '*ts-unknown*)
        ((null (cdr x)) (eval-type-set (car x)))
        (t (let ((lst (eval-type-set-lst x)))
             (cond
              ((integer-listp lst)
               (logand-lst lst *ts-unknown*))
              (t
               (xxxjoin 'logand lst)))))))

(defun eval-type-set (x)
  (cond
   ((and (symbolp x)
         (legal-constantp1 x))
    (or (cdr (assoc-eq x *code-type-set-alist*))
        (er hard 'eval-type-set
            "The constant ~x0 appears as an argument to a ts- function but is ~
             not known to *code-type-set-alist*, whose current value ~
             is:~%~x1. You should redefine that constant or define your own ~
             ts- functions if you want to avoid this problem."
            x *code-type-set-alist*)))
   ((atom x) x)
   (t (case (car x)
            (quote (if (integerp (cadr x))
                       (cadr x)
                     x))
            (ts-union (ts-union-fn (cdr x)))
            (ts-intersection (ts-intersection-fn (cdr x)))
            (ts-complement (ts-complement-fn (cadr x)))
            (t x)))))

(defun eval-type-set-lst (x)

; This is an improved version of list-of-the-type-set.

  (cond ((consp x)
         (let ((y (eval-type-set (car x))))
           (cons (if (integerp y)
                     y
                   (list 'the-type-set y))
                 (eval-type-set-lst (cdr x)))))
        (t nil)))
)

(defmacro ts-complement (x)
  (list 'the-type-set (ts-complement-fn x)))

(defmacro ts-intersection (&rest x)
  (list 'the-type-set (ts-intersection-fn x)))

(defmacro ts-union (&rest x)
  (list 'the-type-set (ts-union-fn x)))

(defmacro ts-subsetp (ts1 ts2)
  (list 'let
        (list (list 'ts1 ts1)
              (list 'ts2 ts2))

; Warning: Keep the following type in sync with the definition of the-type-set
; in def-basic-type-sets.

        `(declare (type (integer ,*min-type-set* ,*max-type-set*)
                        ts1 ts2))
        '(ts= (ts-intersection ts1 ts2) ts1)))

;; Historical Comment from Ruben Gamboa:
;; I modified this to include cases for the irrationals and
;; complex numbers.

(defun type-set-binary-+-alist-entry (ts1 ts2)
  (ts-builder ts1
              (*ts-zero* ts2)
              (*ts-one*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-integer>1*)
                           (*ts-integer>1* *ts-integer>1*)
                           (*ts-negative-integer* *ts-non-positive-integer*)
                           (*ts-positive-ratio* *ts-positive-ratio*)
                           (*ts-negative-ratio* *ts-ratio*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-positive-non-ratio*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-non-ratio*)

                           (*ts-complex-rational* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-complex-non-rational*)
                           ))
              (*ts-integer>1*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-integer>1*)
                           (*ts-integer>1* *ts-integer>1*)
                           (*ts-negative-integer* *ts-integer*)
                           (*ts-positive-ratio* *ts-positive-ratio*)
                           (*ts-negative-ratio* *ts-ratio*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-positive-non-ratio*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-non-ratio*)

                           (*ts-complex-rational* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-complex-non-rational*)
                           ))
              (*ts-negative-integer*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-non-positive-integer*)
                           (*ts-integer>1* *ts-integer*)
                           (*ts-negative-integer* *ts-negative-integer*)
                           (*ts-positive-ratio* *ts-ratio*)
                           (*ts-negative-ratio* *ts-negative-ratio*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-non-ratio*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-negative-non-ratio*)

                           (*ts-complex-rational* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-complex-non-rational*)
                           ))
              (*ts-positive-ratio*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-positive-ratio*)
                           (*ts-integer>1* *ts-positive-ratio*)
                           (*ts-negative-integer* *ts-ratio*)
                           (*ts-positive-ratio* *ts-positive-rational*)
                           (*ts-negative-ratio* *ts-rational*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-positive-non-ratio*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-non-ratio*)

                           (*ts-complex-rational* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-complex-non-rational*)
                           ))
              (*ts-negative-ratio*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-ratio*)
                           (*ts-integer>1* *ts-ratio*)
                           (*ts-negative-integer* *ts-negative-ratio*)
                           (*ts-positive-ratio* *ts-rational*)
                           (*ts-negative-ratio* *ts-negative-rational*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-non-ratio*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-negative-non-ratio*)

                           (*ts-complex-rational* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-complex-non-rational*)
                           ))

              #+:non-standard-analysis
              (*ts-positive-non-ratio*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-positive-non-ratio*)
                           (*ts-integer>1* *ts-positive-non-ratio*)
                           (*ts-negative-integer* *ts-non-ratio*)
                           (*ts-positive-ratio* *ts-positive-non-ratio*)
                           (*ts-negative-ratio* *ts-non-ratio*)
                           (*ts-positive-non-ratio* *ts-positive-real*)
                           (*ts-negative-non-ratio* *ts-real*)
                           (*ts-complex-rational* *ts-complex-non-rational*)
                           (*ts-complex-non-rational* *ts-complex*)))
              #+:non-standard-analysis
              (*ts-negative-non-ratio*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-non-ratio*)
                           (*ts-integer>1* *ts-non-ratio*)
                           (*ts-negative-integer* *ts-negative-non-ratio*)
                           (*ts-positive-ratio* *ts-non-ratio*)
                           (*ts-negative-ratio* *ts-negative-non-ratio*)
                           (*ts-positive-non-ratio* *ts-real*)
                           (*ts-negative-non-ratio* *ts-negative-real*)
                           (*ts-complex-rational* *ts-complex-non-rational*)
                           (*ts-complex-non-rational* *ts-complex*)
                           ))
              (*ts-complex-rational*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-complex-rational*)
                           (*ts-integer>1* *ts-complex-rational*)
                           (*ts-negative-integer* *ts-complex-rational*)
                           (*ts-positive-ratio* *ts-complex-rational*)
                           (*ts-negative-ratio* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-complex-non-rational*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-complex-non-rational*)

                           (*ts-complex-rational* *ts-rational-acl2-number*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-non-rational-acl2-number*)
                           ))
              #+:non-standard-analysis
              (*ts-complex-non-rational*
               (ts-builder ts2
                           (*ts-zero* ts1)
                           (*ts-one* *ts-complex-non-rational*)
                           (*ts-integer>1* *ts-complex-non-rational*)
                           (*ts-negative-integer* *ts-complex-non-rational*)
                           (*ts-positive-ratio* *ts-complex-non-rational*)
                           (*ts-negative-ratio* *ts-complex-non-rational*)
                           (*ts-positive-non-ratio* *ts-complex*)
                           (*ts-negative-non-ratio* *ts-complex*)
                           (*ts-complex-rational* *ts-non-rational-acl2-number*)
                           (*ts-complex-non-rational* *ts-acl2-number*)))))

(defun type-set-binary-+-alist1 (i j lst)
  (cond ((< j 0) lst)
        (t (let ((x (type-set-binary-+-alist-entry i j)))
             (cond ((= x *ts-unknown*)
                    (type-set-binary-+-alist1 i (1- j) lst))
                   (t (type-set-binary-+-alist1 i (1- j)
                                         (cons (cons (cons i j) x)
                                               lst))))))))

(defun type-set-binary-+-alist (i j lst)
  (cond ((< i 0) lst)
        (t (type-set-binary-+-alist (1- i) j
                             (type-set-binary-+-alist1 i j lst)))))

;; Historical Comment from Ruben Gamboa:
;; I modified this to include cases for the irrationals and
;; complex numbers.

(defun type-set-binary-*-alist-entry (ts1 ts2)
  (ts-builder ts1
              (*ts-zero* *ts-zero*)
              (*ts-one* ts2)
              (*ts-integer>1*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-integer>1*)
                           (*ts-negative-integer* *ts-negative-integer*)
                           (*ts-positive-ratio* *ts-positive-rational*)
                           (*ts-negative-ratio* *ts-negative-rational*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-positive-non-ratio*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-negative-non-ratio*)

                           (*ts-complex-rational* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-complex-non-rational*)
                           ))
              (*ts-negative-integer*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-negative-integer*)
                           (*ts-negative-integer* *ts-positive-integer*)
                           (*ts-positive-ratio* *ts-negative-rational*)
                           (*ts-negative-ratio* *ts-positive-rational*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-negative-non-ratio*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-positive-non-ratio*)

                           (*ts-complex-rational* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-complex-non-rational*)
                           ))
              (*ts-positive-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-positive-rational*)
                           (*ts-negative-integer* *ts-negative-rational*)
                           (*ts-positive-ratio* *ts-positive-rational*)
                           (*ts-negative-ratio* *ts-negative-rational*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-positive-non-ratio*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-negative-non-ratio*)

                           (*ts-complex-rational* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-complex-non-rational*)
                           ))
              (*ts-negative-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-negative-rational*)
                           (*ts-negative-integer* *ts-positive-rational*)
                           (*ts-positive-ratio* *ts-negative-rational*)
                           (*ts-negative-ratio* *ts-positive-rational*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-negative-non-ratio*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-positive-non-ratio*)

                           (*ts-complex-rational* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-complex-non-rational*)
                           ))
              #+:non-standard-analysis
              (*ts-positive-non-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-positive-non-ratio*)
                           (*ts-negative-integer* *ts-negative-non-ratio*)
                           (*ts-positive-ratio* *ts-positive-non-ratio*)
                           (*ts-negative-ratio* *ts-negative-non-ratio*)
                           (*ts-positive-non-ratio* *ts-positive-real*)
                           (*ts-negative-non-ratio* *ts-negative-real*)
                           (*ts-complex-rational* *ts-complex-non-rational*)
                           (*ts-complex-non-rational* *ts-complex*)))
              #+:non-standard-analysis
              (*ts-negative-non-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-negative-non-ratio*)
                           (*ts-negative-integer* *ts-positive-non-ratio*)
                           (*ts-positive-ratio* *ts-negative-non-ratio*)
                           (*ts-negative-ratio* *ts-positive-non-ratio*)
                           (*ts-positive-non-ratio* *ts-negative-real*)
                           (*ts-negative-non-ratio* *ts-positive-real*)
                           (*ts-complex-rational* *ts-complex-non-rational*)
                           (*ts-complex-non-rational* *ts-complex*)))
              (*ts-complex-rational*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-complex-rational*)
                           (*ts-negative-integer* *ts-complex-rational*)
                           (*ts-positive-ratio* *ts-complex-rational*)
                           (*ts-negative-ratio* *ts-complex-rational*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-complex-non-rational*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-complex-non-rational*)

                           (*ts-complex-rational*
                            (ts-intersection0 *ts-rational-acl2-number*
                                              (ts-complement0 *ts-zero*)))

                           #+:non-standard-analysis
                           (*ts-complex-non-rational* *ts-non-rational-acl2-number*)))
              #+:non-standard-analysis
              (*ts-complex-non-rational*
               (ts-builder ts2
                           (*ts-zero* *ts-zero*)
                           (*ts-one* ts1)
                           (*ts-integer>1* *ts-complex-non-rational*)
                           (*ts-negative-integer* *ts-complex-non-rational*)
                           (*ts-positive-ratio* *ts-complex-non-rational*)
                           (*ts-negative-ratio* *ts-complex-non-rational*)
                           (*ts-positive-non-ratio* *ts-complex*)
                           (*ts-negative-non-ratio* *ts-complex*)
                           (*ts-complex-rational* *ts-non-rational-acl2-number*)
                           (*ts-complex-non-rational*
                            (ts-intersection0 *ts-acl2-number*
                                              (ts-complement0 *ts-zero*)))))))

(defun type-set-binary-*-alist1 (i j lst)
  (cond ((< j 0) lst)
        (t (let ((x (type-set-binary-*-alist-entry i j)))
             (cond ((= x *ts-unknown*)
                    (type-set-binary-*-alist1 i (1- j) lst))
                   (t (type-set-binary-*-alist1 i (1- j)
                                         (cons (cons (cons i j)
                                                     x)
                                               lst))))))))

(defun type-set-binary-*-alist (i j lst)
  (cond ((< i 0) lst)
        (t (type-set-binary-*-alist (1- i) j
                             (type-set-binary-*-alist1 i j lst)))))

;; Historical Comment from Ruben Gamboa:
;; I modified this to include cases for the irrationals and
;; complex numbers.

(defun type-set-<-alist-entry (ts1 ts2)
  (ts-builder ts1
              (*ts-zero*
               (ts-builder ts2
                           (*ts-zero* *ts-nil*)
                           (*ts-one* *ts-t*)
                           (*ts-integer>1* *ts-t*)
                           (*ts-negative-integer* *ts-nil*)
                           (*ts-positive-ratio* *ts-t*)
                           (*ts-negative-ratio* *ts-nil*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-t*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-nil*)))
              (*ts-one*
               (ts-builder ts2
                           (*ts-zero* *ts-nil*)
                           (*ts-one* *ts-nil*)
                           (*ts-integer>1* *ts-t*)
                           (*ts-negative-integer* *ts-nil*)
                           (*ts-positive-ratio* *ts-boolean*)
                           (*ts-negative-ratio* *ts-nil*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-boolean*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-nil*)))
              (*ts-integer>1*
               (ts-builder ts2
                           (*ts-zero* *ts-nil*)
                           (*ts-one* *ts-nil*)
                           (*ts-integer>1* *ts-boolean*)
                           (*ts-negative-integer* *ts-nil*)
                           (*ts-positive-ratio* *ts-boolean*)
                           (*ts-negative-ratio* *ts-nil*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-boolean*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-nil*)))
              (*ts-negative-integer*
               (ts-builder ts2
                           (*ts-zero* *ts-t*)
                           (*ts-one* *ts-t*)
                           (*ts-integer>1* *ts-t*)
                           (*ts-negative-integer* *ts-boolean*)
                           (*ts-positive-ratio* *ts-t*)
                           (*ts-negative-ratio* *ts-boolean*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-t*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-boolean*)))
              (*ts-positive-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-nil*)
                           (*ts-one* *ts-boolean*)
                           (*ts-integer>1* *ts-boolean*)
                           (*ts-negative-integer* *ts-nil*)
                           (*ts-positive-ratio* *ts-boolean*)
                           (*ts-negative-ratio* *ts-nil*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-boolean*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-nil*)))
              (*ts-negative-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-t*)
                           (*ts-one* *ts-t*)
                           (*ts-integer>1* *ts-t*)
                           (*ts-negative-integer* *ts-boolean*)
                           (*ts-positive-ratio* *ts-t*)
                           (*ts-negative-ratio* *ts-boolean*)

                           #+:non-standard-analysis
                           (*ts-positive-non-ratio* *ts-t*)
                           #+:non-standard-analysis
                           (*ts-negative-non-ratio* *ts-boolean*)))

              #+:non-standard-analysis
              (*ts-positive-non-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-nil*)
                           (*ts-one* *ts-boolean*)
                           (*ts-integer>1* *ts-boolean*)
                           (*ts-negative-integer* *ts-nil*)
                           (*ts-positive-ratio* *ts-boolean*)
                           (*ts-negative-ratio* *ts-nil*)
                           (*ts-positive-non-ratio* *ts-boolean*)
                           (*ts-negative-non-ratio* *ts-nil*)))
              #+:non-standard-analysis
              (*ts-negative-non-ratio*
               (ts-builder ts2
                           (*ts-zero* *ts-t*)
                           (*ts-one* *ts-t*)
                           (*ts-integer>1* *ts-t*)
                           (*ts-negative-integer* *ts-boolean*)
                           (*ts-positive-ratio* *ts-t*)
                           (*ts-negative-ratio* *ts-boolean*)
                           (*ts-positive-non-ratio* *ts-t*)
                           (*ts-negative-non-ratio* *ts-boolean*)))))

(defun type-set-<-alist1 (i j lst)
  (cond ((< j 0) lst)
        (t (let ((x (type-set-<-alist-entry i j)))
             (cond ((= x *ts-unknown*)
                    (type-set-<-alist1 i (1- j) lst))
                   (t (type-set-<-alist1 i (1- j)
                                         (cons (cons (cons i j) x)
                                               lst))))))))


(defun type-set-<-alist (i j lst)
  (cond ((< i 0) lst)
        (t (type-set-<-alist (1- i) j
                             (type-set-<-alist1 i j lst)))))

