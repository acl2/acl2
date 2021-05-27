; More rules about the built-in function pseudo-termp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book includes rules that mix pseudo-termp with non-built-in functions.

(include-book "kestrel/utilities/polarity" :dir :system)

(defthm pseudo-termp-strengthen-when-not-consp-cheap
  (implies (and (syntaxp (want-to-strengthen (pseudo-termp term)))
                (not (consp term)))
           (equal (pseudo-termp term)
                  (symbolp term)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 0))))
