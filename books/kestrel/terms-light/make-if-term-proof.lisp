; Proof of make-if-term, etc.

; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/evaluators/if-eval" :dir :system)
(include-book "make-if-term")

(defthm if-eval-of-make-if-term
  (iff (if-eval (make-if-term test then else) a)
       (if (if-eval test a)
           (if-eval then a)
         (if-eval else a)))
  :hints (("Goal" :in-theory (enable make-if-term))))

(defthm if-eval-of-make-if-term-gen
  (iff (if-eval (make-if-term-gen test then else) a)
       (if (if-eval test a)
           (if-eval then a)
         (if-eval else a)))
  :hints (("Goal" :in-theory (enable make-if-term-gen))))
