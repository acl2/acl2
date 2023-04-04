; A lightweight book about the built-in function >=-len.
;
; Copyright (C) 2015-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm >=-len-rewrite
  (implies (natp n)
           (equal (>=-len x n)
                  (>= (len x) n))))
