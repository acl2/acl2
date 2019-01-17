; Centaur Misc Books
; Copyright (C) 2008-2019 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc non-case-splitting-logic
  :parents (boolean-reasoning)
  :short "Boolean connectives that avoid case splits."
  :long "<p>Perhaps the most common reason that ACL2 proofs take a long time is
that they split into too many cases unnecessarily.  The alternative Boolean
operators @('iff*'), @('and*'), @('or*'), @('xor*'), and @('if*') can help to
avoid such case splits.</p>

<p>A small and abstract example: Suppose foo is a function that has the following shape:</p>

@({
 (defun foo (...)
   (cond (<exceptional-case1> ...)
         (<exceptional-case2> ...)
         ...
         (<exceptional-casen> ...)
         (t ...))) ;; default case
 })

<p>And suppose that each of the N exceptional cases is a conjunction of M
subterms.  How many cases will ACL2 typically split into in order to prove
something about foo?</p>

<p>The answer is on the order of @('M^N').  You can get the exact number via the following recurrence:</p>

@({
 (defun number-of-cases (n m)
    (if (zp n)
        1
      (+ 1 (* m (number-of-cases (- n 1) m)))))
 })

<p>This is because for each conjunction @('(and a b c') that may cause an
exceptional case, ACL2 considers the cases:</p>
@({
 (not a)
 (and a (not b))
 (and a b (not c))
 (and a b c)
 })

<p>In the first three cases, the conjunction is not true (this is where the
@('* m') in the recurrence comes from), and in the last case it is true (this
is where the @('+ 1') in the recurrence comes from).</p>

<p>This is where the alternative operators come in.  If we replace the
conjunctions above with @('and*') calls, then instead of splitting into
@('M^N') cases, we split into @('N+1') cases!  This usually works because when
we are in case K, we care that the conjuncts of @('<exceptional-casek>') were
true, but usually not which of the conjuncts of @('<exceptional-case0>')
through @('exceptional-casek-1') were untrue.</p>

")





;; IFF* is just like IFF, but doesn't automatically cause case splits.
(defsection iff*
  :parents (non-case-splitting-logic)
  :short "Non-case-splitting version of IFF."
  (defund iff* (x y)
    (iff x y))

  (local (in-theory (enable iff*)))

  (defequiv iff*)
  (defrefinement iff iff*)
  (defrefinement iff* iff)
  (defthm iff*-of-nonnils
    (implies (and x y)
             (equal (iff* x y) t))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))
  (defthm iff*-with-nil
    (and (equal (iff* x nil)
                (not x))
         (equal (iff* nil x)
                (not x))))

  (defthm iff*-when-other
    (implies y
             (and (iff (iff* x y) x)
                  (iff (iff* y x) x)))))

(defsection xor*
  :parents (non-case-splitting-logic)
  :short "Non-case-splitting version of XOR."
  (defund xor* (x y)
    (xor x y))

  (local (in-theory (enable xor*)))

  (defcong iff equal (xor* x y) 1)
  (defcong iff equal (xor* x y) 2)

  (defthm xor*-of-nonnils
    (implies (and x y)
             (equal (xor* x y) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))
  (defthm xor*-with-nil
    (and (iff (xor* x nil)
              x)
         (iff (xor* nil x)
              x)))

  (defthm xor*-when-other
    (implies y
             (and (equal (xor* x y) (not x))
                  (equal (xor* y x) (not x))))))



(defsection and*
  :parents (non-case-splitting-logic)
  :short "Non-case-splitting version of AND."
  (defun binary-and* (a b)
    (declare (xargs :guard t))
    (and a b))

  (defun and*-macro (lst)
    (if (atom lst)
        t
      (if (atom (cdr lst))
          (car lst)
        (list 'binary-and* (car lst)
              (and*-macro (cdr lst))))))

  (defmacro and* (&rest lst)
    (and*-macro lst))

  (add-binop and* binary-and*)

  (defcong iff equal (and* a b) 1)

  (defcong iff iff (and* a b) 2)

  (defthm and*-rem-first
    (implies a
             (equal (and* a b) b)))

  (defthm and*-rem-second
    (implies b
             (iff (and* a b) a)))

  (defthm and*-nil-first
    (equal (and* nil b) nil))

  (defthm and*-nil-second
    (equal (and* a nil) nil))

  (defthm and*-forward
    (implies (and* a b) (and a b))
    :rule-classes :forward-chaining)

  (defmacro and** (&rest lst)
    `(mbe :logic (and* . ,lst)
          :exec (and . ,lst)))

  (in-theory (disable and*)))


(defsection or*

  (defun binary-or* (a b)
    (declare (xargs :guard t))
    (or a b))

  (defun or*-macro (lst)
    (if (atom lst)
        nil
      (if (atom (cdr lst))
          (car lst)
        (list 'binary-or* (car lst)
              (or*-macro (cdr lst))))))

  (defmacro or* (&rest lst)
    (or*-macro lst))

  (add-binop or* binary-or*)

  (defcong iff iff (or* a b) 1)

  (defcong iff iff (or* a b) 2)

  (defthm or*-true-first
    (implies a
             (equal (or* a b) a)))

  (defthm or*-true-second
    (implies b
             (or* a b)))

  (defthm or*-nil-first
    (equal (or* nil b) b))

  (defthm or*-nil-second
    (equal (or* a nil) a))

  (defthm or*-forward
    (implies (or* a b) (or a b))
    :rule-classes :forward-chaining)

  (defmacro or** (&rest lst)
    `(mbe :logic (or* . ,lst)
          :exec (or . ,lst)))

  (in-theory (disable or*)))




#||
(defstub cccc (casenum conjnum x) nil)
(defstub aaaa (casenum x) nil)

(defstub pppp (x) nil)

(defaxiom pppp-of-aaaa
  (pppp (aaaa n x)))

(defun m-conjs (i m casenum)
  (declare (xargs :mode :program))
  (if (eql i m)
      nil
    (let ((i (1+ i)))
      (cons `(cccc ,casenum ,i x)
            (m-conjs i m casenum)))))

(defun n-cases (i n m)
  (declare (xargs :mode :program))
  (if (eql i n)
      nil
    (let ((i (1+ i)))
      (cons `((and . ,(m-conjs 0 m i)) (aaaa ,i x))
            (n-cases i n m)))))

(defun foo-n-m-test-form (n m)
  (Declare (xargs :mode :program))
  (let* ((name (intern$
                (concatenate 'string
                             "FOO-"
                             (coerce (explode-atom n 10) 'string)
                             "-"
                             (coerce (explode-atom m 10) 'string))
                "ACL2"))
         (thm (intern$
               (concatenate 'string
                            "PPPP-OF-"
                            (symbol-name name))
               "ACL2")))
    `(encapsulate nil
       (local (defun ,name (x)
                (cond ,@(n-cases 0 n m)
                      (t (aaaa 0 x)))))
       (local (defthm ,thm
                (pppp (,name x)))))))

(defmacro foo-n-m-test (n m)
  (foo-n-m-test-form n m))

(defun n-cases* (i n m)
  (declare (xargs :mode :program))
  (if (eql i n)
      nil
    (let ((i (1+ i)))
      (cons `((and* . ,(m-conjs 0 m i)) (aaaa ,i x))
            (n-cases* i n m)))))

(defun foo-n-m-test*-form (n m)
  (Declare (xargs :mode :program))
  (let* ((name (intern$
                (concatenate 'string
                             "FOO-"
                             (coerce (explode-atom n 10) 'string)
                             "-"
                             (coerce (explode-atom m 10) 'string))
                "ACL2"))
         (thm (intern$
               (concatenate 'string
                            "PPPP-OF-"
                            (symbol-name name))
               "ACL2")))
    `(encapsulate nil
       (local (defun ,name (x)
                (cond ,@(n-cases* 0 n m)
                      (t (aaaa 0 x)))))
       (local (defthm ,thm
                (pppp (,name x)))))))

(defmacro foo-n-m-test* (n m)
  (foo-n-m-test*-form n m))

(foo-n-m-test 0 3) ;; 1
(foo-n-m-test 1 3) ;; 4
(foo-n-m-test 2 3) ;; 13
(foo-n-m-test 3 3) ;; 40
(foo-n-m-test 4 3) ;; 121
(foo-n-m-test 5 3) ;; 364


(foo-n-m-test* 0 3) ;; 1
(foo-n-m-test* 1 3) ;; 2
(foo-n-m-test* 2 3) ;; 3
(foo-n-m-test* 3 3) ;; 4
(foo-n-m-test* 4 3) ;; 5
(foo-n-m-test* 5 3) ;; 6


||#

