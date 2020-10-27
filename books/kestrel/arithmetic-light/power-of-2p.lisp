; A recognizer for a power of 2
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;dup
;define in terms of lg?
(defund power-of-2p (x)
  (declare (xargs :guard t))
  (and (natp x) ;otherwise, this would count 1/2 but not 1/4
       (= x (expt 2 (+ -1 (integer-length x))))))
