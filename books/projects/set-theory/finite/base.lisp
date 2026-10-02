; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ZF")

(include-book "../base")

(defun-sk finite (s)
  (exists f (and (funp f)
                 (natp (domain f))
                 (subset s (image f)))))

(defthmz subset-preserves-finite
  (implies (and (finite s1)
                (subset s2 s1))
           (finite s2)))

(in-theory (disable finite))
