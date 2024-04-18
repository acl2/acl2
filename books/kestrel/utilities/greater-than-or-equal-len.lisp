; A lightweight book about the built-in function >=-len.
;
; Copyright (C) 2015-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable >=-len))

(defthm >=-len-rewrite
  (implies (natp n)
           (equal (>=-len x n)
                  (>= (len x) n)))
  :hints (("Goal" :in-theory (enable >=-len))))
