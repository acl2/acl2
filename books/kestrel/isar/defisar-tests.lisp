; Isar (Intelligible Semi-Automated Reasoning) Library
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defisar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  (((p *) => *)
   ((q *) => *)
   ((r *) => *))
  (local (defun p (x) (equal x x)))
  (local (defun q (x) (equal x x)))
  (local (defun r (x) (equal x x)))
  (defthmd p=>q (implies (p x) (q x)))
  (defthmd q=>r (implies (q x) (r x))))

(defisar p=>r
  (implies (p x) (r x))
  :proof
  ((:assume (:p (p x)))
   (:derive (:q (q x))
    :from (:p)
    :hints (("Goal" :use p=>q)))
   (:derive (:r (r x))
    :from (:q)
    :hints (("Goal" :use q=>r)))
   (:qed)))
