; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book is referenced in the ACL2 source code, in the comment entitled
; "Essay on Memoization with Partial Functions (Memoize-partial)".

(in-package "ACL2")

; This is the definition familiar from books/demos/memoize-partial-input.lsp:
(defun fib-limit (n limit)
  (declare (type (integer 0 *) limit)
           (type integer n))
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      0 ; any term is fine here
    (let ((limit (1- limit)))
      (if (or (= n 0) (= n 1))
          1
        (+ (fib-limit (- n 1) limit)
           (fib-limit (- n 2) limit))))))

(encapsulate
  ((lim () t))
  (local (defun lim () 0))
  (defthm natp-lim
    (natp (lim))
    :rule-classes :type-prescription))

(defun fib-limit2 (n limit)
  (declare (type (integer 0 *) limit))
  (declare (xargs :guard (integerp n)
                  :measure (nfix limit)))
  (if (zp limit)
      (fib-limit n (lim))
    (let ((limit (1- limit)))
      (if (or (= n 0) (= n 1))
          1
        (+ (fib-limit2 (- n 1) limit)
           (fib-limit2 (- n 2) limit))))))

(defthm fib-limit2-is-fib-limit
  (implies (and (natp limit)
                (natp n))
           (equal (fib-limit2 n limit)
                  (fib-limit n (+ limit (lim))))))

; This lemma is proved by computation:
(defthm fib-fact-lemma-1
  (equal (fib-limit2 5 7)
         8)
  :rule-classes nil)

; This lemma follows by from fib-fact-lemma-1 by applying
; fib-limit2-is-fib-limit:
(defthm fib-fact-lemma-2
  (equal (fib-limit 5 (+ 7 (lim)))
         8)
  :hints (("Goal"
           :use fib-fact-lemma-1
           :in-theory (disable fib-limit (:e fib-limit2))))
  :rule-classes nil)

; Now replace (lim) by lim in fib-fact-lemma-2:
(defthm fib-fact-lemma-3
  (implies (natp lim)
           (equal (fib-limit 5 (+ 7 lim))
                  8))
  :hints (("Goal"
           :use ((:functional-instance fib-fact-lemma-2
                                       (lim (lambda () (nfix lim)))))
           :in-theory (disable fib-limit (:e fib-limit))))
  :rule-classes nil)

; We conclude with a trivial consequence of the preceding lemma:
(defthm fib-fact
  (implies (and (natp limit)
                (<= 7 limit))
           (equal (fib-limit 5 limit)
                  8))
  :hints (("Goal"
           :use ((:instance fib-fact-lemma-3
                            (lim (- limit 7))))
           :in-theory (disable fib-limit (:e fib-limit))))
  :rule-classes nil)
