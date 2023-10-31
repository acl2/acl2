; Material about fixnums
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Evaluating most-positive-fixnum on CCL and SBCL gives 2^60-1 and 2^62-1, respectively.
(defconst *max-fixnum* (+ -1 (expt 2 60)))

;; Evaluating most-negative-fixnum on CCL and SBCL gives -(2^60) and -(2^62), respectively.
(defconst *min-fixnum* (- (expt 2 60)))
