; Unicode Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The types of the data of the two conformance tests
; of the Unicode Bidirectional Algorithm,
; which are in ../data/bidi/.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "UNICODE")

(include-book "../bidi-resolved-levels")

(local (include-book "std/lists/top" :dir :system)) ; for more DEFLIST theorems

(acl2::controlled-configuration)

(local (in-theory (enable nfix natp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-test-input-list
  :short "Fixtype of lists of strings that hold the inputs
          of a group of test cases."
  :elt-type string
  :true-listp t
  :elementp-of-nil nil
  :pred bidi-test-input-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod bidi-test-group
  :short "Fixtype of groups of lines of the conformance test
          on bidirectional classes."
  ((levels bidi-level-option-list)
   (order nat-list)
   (directions nat)
   (inputs bidi-test-input-list))
  :pred bidi-test-group-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-test-group-list
  :short "Fixtype of lists of groups of lines of the conformance test
          on bidirectional classes."
  :elt-type bidi-test-group
  :true-listp t
  :elementp-of-nil nil
  :pred bidi-test-group-listp)

;;;;;;;;;;;;;;;;;;;;

(fty::defprod bidi-character-test-group
  :short "Fixtype of groups of lines of the conformance test
          on characters."
  ((direction nat)
   (paragraph-level nat)
   (levels bidi-level-option-list)
   (order nat-list)
   (inputs bidi-test-input-list))
  :pred bidi-character-test-group-p)

;;;;;;;;;;;;;;;;;;;;

(fty::deflist bidi-character-test-group-list
  :short "Fixtype of lists of groups of lines of the conformance test
          on characters."
  :elt-type bidi-character-test-group
  :true-listp t
  :elementp-of-nil nil
  :pred bidi-character-test-group-listp)
