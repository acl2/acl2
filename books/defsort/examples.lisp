; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>


; Defsort Examples.
;
; You do not need to load this book to use defsort; it is only here to show you
; some examples of using defsort.

(in-package "ACL2")
(include-book "defsort")
(include-book "misc/total-order" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)


;; The following defines (<-SORT X), which orders a list of rational numbers
;; in ascending order.

(defsort :comparablep rationalp
         :compare< <
         :prefix <
         :weak nil)

(assert! (equal (<-sort '(5 5 3 4 4)) '(3 4 4 5 5)))



;; We cannot define (>-SORT X) directly using >, because in ACL2 > is a macro
;; instead of a function.  So, we define a wrapper.

(defun greater-p (x y)
  (declare (xargs :guard (and (rationalp x)
                              (rationalp y))))
  (> x y))

(defsort :comparablep rationalp
         :compare< greater-p
         :prefix >
         :weak nil)

(assert! (equal (>-sort '(5 5 3 4 4)) '(5 5 4 4 3)))

;; new syntax with sort function name first
(defsort bigger-sort
  :comparablep rationalp
  :compare< (lambda (x y) (< y x))
  :prefix bigger
  :weak nil)

;; new syntax with sort function name and no prefix
(defsort littler-sort
  :comparablep rationalp
  :compare< (lambda (x y) (< x y))
  :weak nil)

;; We can define an arbitrary sort using <<.  This is almost the same as
;; SET::mergesort in the ordered sets library, except that defsorts are
;; always duplicate-preserving while SET::mergesort throws away identical
;; elements.

(defsort :compare< <<
         :prefix <<w)


;; If we prove that the negation of << is transitive, we can do this without
;; the :weak:

(defthm <<-negation-transitive
  (implies (and (not (<< x y))
                (not (<< y z)))
           (not (<< x z)))
  :hints (("goal" :use ((:instance <<-trichotomy
                         (x y) (y x)))
           :in-theory (disable <<-trichotomy))))

(defsort :compare< <<
         :prefix <<
         :weak nil)

(assert! (equal (<<-sort '(a c b 1 3 2 1/3 1/2 (1 . 2)))
                '(1/3 1/2 1 2 3 a b c (1 . 2))))

(defthm
  common-<<-sort-for-perms
  (implies (set-equiv x y)
           (equal (<<-sort (remove-duplicates-equal x))
                  (<<-sort (remove-duplicates-equal y))))
  :hints
  ((defsort-functional-inst
     common-sort-for-perms
     ((compare<-negation-transitive (lambda nil t))
      (compare<-strict (lambda nil t))
      (compare<-total (lambda nil t))
      (comparable-insert (lambda (elt x) (<<-insert elt x)))
      (comparable-insertsort (lambda (x) (<<-insertsort x)))
      (compare< (lambda (x y) (<< x y)))
      (comparablep (lambda (x) t))
      (comparable-listp (lambda (x) t))
      (element-list-final-cdr-p (lambda (x) t))
      (comparable-merge (lambda (x y) (<<-merge x y)))
      (comparable-orderedp (lambda (x) (<<-ordered-p x)))
      (comparable-merge-tr (lambda (x y acc)
                             (<<-merge-tr x y acc)))
      (fast-comparable-mergesort-fixnums (lambda (x len)
                                           (<<-mergesort-fixnum x len)))
      (fast-comparable-mergesort-integers
       (lambda (x len)
         (<<-mergesort-integers x len)))
      (comparable-mergesort (lambda (x) (<<-sort x))))))
  :rule-classes :congruence)

;; Sort with respect to an alist that maps each key to an integer.
(defun intval-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (integerp (cdar x))
         (intval-alistp (cdr x)))))

(encapsulate nil
  (local (defthm alistp-when-intval-alistp
           (implies (intval-alistp x)
                    (alistp x))))
  (local
   (defthm assoc-in-intval-alistp
     (implies (and (assoc k alist)
                   (intval-alistp alist))
              (and (consp (assoc k alist))
                   (integerp (cdr (assoc k alist)))
                   (real/rationalp (cdr (assoc k alist)))))))

  (defun intval-alist-< (x y alist)
    (Declare (xargs :guard (and (intval-alistp alist)
                                (assoc-equal x alist)
                                (assoc-equal y alist))))
    (< (cdr (assoc-equal x alist))
       (cdr (assoc-equal y alist))))

  (defsort intval-alist-sort
    :extra-args (alist)
    :extra-args-guard (intval-alistp alist)
    :comparablep (lambda (x alist) (consp (assoc-equal x alist)))
    :compare< intval-alist-<))

(encapsulate nil
  (local (defthm alistp-when-intval-alistp
           (implies (intval-alistp x)
                    (alistp x))))
  (local
   (defthm assoc-in-intval-alistp
     (implies (and (assoc k alist)
                   (intval-alistp alist))
              (consp (assoc k alist)))))

  (defun intval-alist-<2 (x y alist)
    (Declare (xargs :guard (and (intval-alistp alist)
                                ;; for demo purposes
                                (stringp x) (stringp y))))
    (< (ifix (cdr (assoc-equal x alist)))
       (ifix (cdr (assoc-equal y alist)))))

  ;; Testing both the new syntax, and a comparablep that ignores the extra-args
  (defsort intval-alist-sort2 (x alist)
    :extra-args-guard (intval-alistp alist)
    :comparablep (lambda (x alist) (stringp x))
    :compare< intval-alist-<2))





;; We can define a sort for strings.  String< is not appropriate because it
;; returns numbers instead of bools, so we define a little wrapper for it.
;; Furthermore, we need to prove the transitivity of string<, since this is
;; not yet known to ACL2.

(defun string-less-p (x y)
  (declare (xargs :guard (and (stringp x)
                              (stringp y))))
  (if (string< x y)
      t
    nil))

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (character-listp x)
                        (character-listp y)
                        (character-listp z)
                        (string<-l x y n)
                        (string<-l y z n))
                   (string<-l x z n))
          :hints(("Goal" :in-theory (enable string<-l)))))

 (defthm transitivity-of-string-less-p
   (implies (and (string< x y)
                 (string< y z))
            (string< x z))
   :hints(("Goal" :in-theory (enable string<)))))

(defsort :comparablep stringp
         :compare< string-less-p
         :prefix string)

(defsort :comparablep stringp
         :compare< string-less-p
         :prefix string2
         :comparable-listp string-listp
         :true-listp t)

(assert! (equal (string-sort '("z" "b" "foo" "bar" "aaa" "aaa"))
                '("aaa" "aaa" "b" "bar" "foo" "z")))



;; Imagine an alist of (number . string) pairs.  Below we can define
;; key and value sorts.

(defun entry-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (natp (car x))
       (stringp (cdr x))))

(defun entry-key< (x y)
  (declare (xargs :guard (and (entry-p x)
                              (entry-p y))))
  (< (car x) (car y)))

(defun entry-val< (x y)
  (declare (xargs :guard (and (entry-p x)
                              (entry-p y))))
  (string-less-p (cdr x) (cdr y)))

(defsort :comparablep entry-p
         :compare< entry-key<
         :prefix entry-key)

(defsort :comparablep entry-p
         :compare< entry-val<
         :prefix entry-val)

(assert! (equal (entry-key-sort '((1 . "z") (2 . "b") (1 . "y") (2 . "a")))
                '((1 . "z") (1 . "y") (2 . "b") (2 . "a"))))

(assert! (equal (entry-val-sort '((1 . "z") (2 . "b") (1 . "y") (2 . "a")))
                '((2 . "a") (2 . "b") (1 . "y") (1 . "z"))))


(local
 (encapsulate
   (((sortelt-p *) => *
     :formals (x)
     :guard t))

   (local (defun sortelt-p (x) (and x t)))

   (defthm type-of-sortelt-p
     (booleanp (sortelt-p x))
     :rule-classes :type-prescription)))

(local
 (encapsulate
   (((sortcmp * *) => *
     :formals (x y)
     :guard (and (sortelt-p x)
                 (sortelt-p y))))

   (local (defun sortcmp (x y) (< (nfix x) (nfix y))))

   (defthm type-of-sortcmp
     (booleanp (sortcmp x y))
     :rule-classes :type-prescription)

   (defthm sortcmp-transitive
     (implies (and (sortcmp x y)
                   (sortcmp y z))
              (sortcmp x z)))))


(local
 (encapsulate ()
   (local (defsort :prefix gensort
            :comparablep sortelt-p
            :compare< sortcmp
            :true-listp nil))
   (value-triple :test-true-listp-t-without-listp)))

(local
 (encapsulate ()
   (local (defun sorteltlist-p (x)
            (declare (xargs :guard t))
            (if (atom x)
                (not x)
              (and (sortelt-p (car x))
                   (sorteltlist-p (cdr x))))))
   (local (defsort :prefix gensort
            :comparablep sortelt-p
            :compare< sortcmp
            :true-listp t))

   (value-triple :test-true-listp-t-with-listp)))

(local
 (encapsulate ()
   (local (defun sorteltlist-p (x)
            (declare (xargs :guard t))
            (if (atom x)
                t
              (and (sortelt-p (car x))
                   (sorteltlist-p (cdr x))))))

   (local (defsort :prefix gensort
            :comparablep sortelt-p
            :compare< sortcmp))

   (value-triple :test-true-listp-nil-with-listp)))



#||

; Below are some performance comparisions.
; We do our timings on CCL on Lisp2.

(include-book ;; Line break fools dependency scanner.
 "std/osets/top" :dir :system)


:q

(ccl::set-lisp-heap-gc-threshold (expt 2 30))

(defparameter *integers*
  ;; A test vector of 10,000 integers which are the numbers 1 through 1000,
  ;; each repeated ten times.
  (loop for j from 1 to 10
        nconc
        (loop for i from 1 to 1000 collect i)))

(defparameter *strings*
  (loop for j from 1 to 10
        nconc
        (loop for i from 1 to 1000
              collect
              (concatenate 'string "string_number_"
                           (coerce (explode-atom i 10) 'string)))))


;; 9.13 seconds with 4.4 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (SET::mergesort (cons i *integers*))))
                     (declare (ignore result))
                     nil))))


;; 4.25 seconds with 1.5 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (<<-sort (cons i *integers*))))
                     (declare (ignore result))
                     nil))))


;; 2.71 seconds with 1.5 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (<-sort (cons i *integers*))))
                     (declare (ignore result))
                     nil))))


;; 2.97 seconds with 1.6 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (>-sort (cons i *integers*))))
                     (declare (ignore result))
                     nil))))

;; 25.4 seconds with 4.4 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (SET::mergesort (cons "foo" *strings*))))
                     (declare (ignore result))
                     nil))))

;; 18.8 seconds with 1.5 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (<<-sort (cons "foo" *strings*))))
                     (declare (ignore result))
                     nil))))

;; 11.7 seconds with 1.5 GB allocated
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (string-sort (cons "foo" *strings*))))
                     (declare (ignore result))
                     nil))))




(include-book ;; NOTE: not compatible with other includes
 "defexec/other-apps/qsort/programs" :dir :system)

;; 16.1 seconds with 240 MB allocated -- interesting
(progn (ccl::gc)
       (time (loop for i fixnum from 1 to 1000
                   do
                   (let ((result (qsort (cons i *integers*))))
                     (declare (ignore result))
                     nil))))



||#
