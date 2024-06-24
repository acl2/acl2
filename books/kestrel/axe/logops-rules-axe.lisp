; Axe rules about logops
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2021 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book collections logops rules only needed by Axe (e.g., things that
;; ACL2 already "knows").

(include-book "ihs/basic-definitions" :dir :system) ; for logmask$inline
(include-book "kestrel/utilities/def-constant-opener" :dir :system)

(defthmd integerp-of-logand (integerp (logand x y)))
(defthmd integerp-of-logior (integerp (logior x y)))
(defthmd integerp-of-logxor (integerp (logxor x y)))

(def-constant-opener logmask$inline)
(def-constant-opener binary-logand)
