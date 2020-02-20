; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc common-concepts
  :parents (apt)
  :short "Concepts that are common to different APT transformations.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc redundancy
  :parents (common-concepts)
  :short "Notion of redundancy for APT transformations."
  :long
  (xdoc::topstring
   (xdoc::p
    "A call of an APT transformation is redundant if and only if
     it is identical to a previous successful call of the same transformation
     whose @(':show-only') input is not @('t'),
     except that the two calls may differ in
     their @(':print') and @(':show-only') inputs.
     These options do not affect the generated events,
     and thus they are ignored for the purpose of redundancy.")
   (xdoc::p
    "A call of an APT transformation whose @(':show-only') input is @('t')
     does not generate any event.
     No successive call may be redundant with such a call.")))
