; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "../finite/base")

(defun open-cover (c tp)
  (and (subset c tp)
       (equal (union c)
              (union tp))))

(defun-sk exists-finite-subcover (c tp)
  (exists c2
    (and (equal (union c2) (union tp))
         (subset c2 c)
         (finite c2))))

(defun-sk compact (tp)
  (forall c
    (implies (open-cover c tp)
             (exists-finite-subcover c tp)))
  :rewrite :direct)

(in-theory (disable compact))
