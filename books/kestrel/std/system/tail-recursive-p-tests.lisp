; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tail-recursive-p")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (tail-recursive-p 'nthcdr (w state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (tail-recursive-p 'take (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (defun fact (n)
   (declare (xargs :guard (natp n)))
   (if (zp n)
       1
     (* n (fact (1- n)))))

 (defun fact-tr (n acc)
   (declare (xargs :guard (and (natp n) (natp acc))))
   (if (zp n)
       acc
     (fact-tr (1- n) (* n acc))))

 (include-book "arithmetic/top-with-meta" :dir :system)

 (defthm fact-tr-correct-lemma
   (implies (natp acc)
            (equal (fact-tr n acc)
                   (* acc (fact n)))))

 (defthm fact-tr-correct
   (equal (fact-tr n 1)
          (fact n))
   :hints (("Goal" :in-theory (disable fact-tr fact))))

 (assert! (not (tail-recursive-p 'fact (w state))))

 (assert! (tail-recursive-p 'fact-tr (w state))))
