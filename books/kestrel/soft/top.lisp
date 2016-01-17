; SOFT ('Second-Order Functions and Theorems')
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file provides SOFT ('Second-Order Functions and Theorems'),
; a tool to mimic second-order functions and theorems
; in the first-order logic of ACL2.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "implementation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc soft

  :parents (kestrel-books macro-libraries)

  :short
  "SOFT (&lsquo;Second-Order Functions and Theorems&rsquo;),
  a tool to mimic second-order functions and theorems
  in the first-order logic of ACL2."

  :long
  "<p>
  See the
  <a href='http://eptcs.web.cse.unsw.edu.au/paper.cgi?ACL22015.3'
  >ACL2 Workshop 2015 paper on SOFT</a> for documentation.
  </p>")
