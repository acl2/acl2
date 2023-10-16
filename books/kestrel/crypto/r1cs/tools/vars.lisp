; Extracting variable from an R1CS
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R1CS")

(include-book "../sparse/r1cs")
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(local
 (defthm all->=-len-of-2-when-sparse-vectorp
   (implies (sparse-vectorp vec)
            (acl2::all->=-len vec 2))
   :hints (("Goal" :in-theory (enable sparse-vectorp
                                      acl2::all->=-len)))))

(defund r1cs-sparse-vector-vars (vec)
  (declare (xargs :guard (sparse-vectorp vec)))
  (remove '1 (acl2::strip-cadrs vec)))

(defthm symbol-listp-of-r1cs-sparse-vector-vars
  (implies (sparse-vectorp vec)
           (symbol-listp (r1cs-sparse-vector-vars vec)))
  :hints (("Goal" :in-theory (enable r1cs-sparse-vector-vars))))

(defund r1cs-constraint-vars (constraint)
  (declare (xargs :guard (r1cs-constraintp constraint)))
  (let ((a (r1cs-constraint->a constraint))
        (b (r1cs-constraint->b constraint))
        (c (r1cs-constraint->c constraint)))
    (union-eq (r1cs-sparse-vector-vars a)
              (r1cs-sparse-vector-vars b)
              (r1cs-sparse-vector-vars c))))

(defthm symbol-listp-of-r1cs-constraint-vars
  (implies (r1cs-constraintp constraint)
           (symbol-listp (r1cs-constraint-vars constraint)))
  :hints (("Goal" :in-theory (enable r1cs-constraint-vars))))
