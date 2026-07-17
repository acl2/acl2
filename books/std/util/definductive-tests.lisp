; Standard Utilities Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "definductive")

(include-book "std/testing/must-be-redundant" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (defstub r (* *) => *)

 (definductive refl-trans-closure
   :preds ((r* a b))
   :irules ((base ((r x y))
                  (r* x y))
            (refl ()
                  (r* x x))
            (trans ((r* x y) (r* y z))
                   (r* x z))))

 (must-be-redundant
  (defthm r*-base
    (implies (r x y)
             (r* x y))))

 (must-be-redundant
  (defthm r*-refl
    (implies (and)
             (r* x x))))

 (must-be-redundant
  (defthm r*-trans
    (implies (and (r* x y)
                  (r* y z))
             (r* x z))))

 (must-be-redundant
  (defthm r*-alt-when-r*
    (implies (and (r*-alt-base-p)
                  (r*-alt-refl-p)
                  (r*-alt-trans-p)
                  (r* a b))
             (r*-alt a b)))))
