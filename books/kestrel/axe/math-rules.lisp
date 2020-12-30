; Arithmetic rules
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

;; TODO: Move these to a more generic library (which one?)

(include-book "kestrel/utilities/polarity" :dir :system)
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))

(defthm strengthen-<-of-constant-when-not-equal
  (implies (and (syntaxp (quotep k))
                (syntaxp (want-to-strengthen (< x k)))
                (not (equal x k2)) ;k2 is a free var
                (syntaxp (quotep k2))
                (equal k2 (+ -1 k)) ;gets computed
                (integerp k) ;gets computed
                (integerp x) ;only works for integers
                )
           (equal (< x k)
                  (< x (+ -1 k)))))
