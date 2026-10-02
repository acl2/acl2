; Proof of make-if-term, etc.

; Copyright (C) 2021-2026 Kestrel Institute
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

(defthm logic-termp-of-make-if-term
  (implies (and (logic-termp test w)
                (logic-termp then w)
                (logic-termp else w)
                (arities-okp '((if . 3)) w))
           (logic-termp (make-if-term test then else) w))
  :hints (("Goal" :in-theory (enable make-if-term logic-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm if-eval-of-make-if-term-gen
  (iff (if-eval (make-if-term-gen test then else) a)
       (if (if-eval test a)
           (if-eval then a)
         (if-eval else a)))
  :hints (("Goal" :in-theory (enable make-if-term-gen))))

(defthm logic-termp-of-make-if-term-gen
  (implies (and (logic-termp test w)
                (logic-termp then w)
                (logic-termp else w)
                (arities-okp '((if . 3)) w))
           (logic-termp (make-if-term-gen test then else) w))
  :hints (("Goal" :in-theory (enable make-if-term-gen logic-termp))))
