; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "implementation-environments/versions")

(include-book "std/util/defval" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ punctuators
  :parents (language)
  :short "Punctuators of C."
  :long
  (xdoc::topstring
   (xdoc::p
    "These depend on the "
    (xdoc::seetopic "versions" "C version")
    ", but they are all readily representable as ACL2 strings.")
   (xdoc::p
    "We introduce lists of ACL2 strings representing C punctuators,
     parameterized over the C version."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *punctuators-c17*
  :short "List of the C17 punctuators [C17:6.4.6/1]."
  '("["
    "]"
    "("
    ")"
    "{"
    "}"
    "."
    "->"
    "++"
    "--"
    "&"
    "*"
    "+"
    "-"
    "~"
    "!"
    "/"
    "%"
    "<<"
    ">>"
    "<"
    ">"
    "<="
    ">="
    "=="
    "!="
    "^"
    "|"
    "&&"
    "||"
    "?"
    ":"
    ";"
    "..."
    "="
    "*="
    "/="
    "%="
    "+="
    "-="
    "<<="
    ">>="
    "&="
    "^="
    "|="
    ","
    "#"
    "##"
    "<:"
    ":>"
    "<%"
    "%>"
    "%:"
    "%:%:")
  ///
  (assert-event (string-listp *punctuators-c17*))
  (assert-event (no-duplicatesp-equal *punctuators-c17*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *punctuators-c23*
  :short "List of C23 punctuators [C23:6.4.2]."
  :long
  (xdoc::topstring
   (xdoc::p
    "The only difference with @(tsee *punctuators-c17*)
     is the addition of @('::')."))
  '("["
    "]"
    "("
    ")"
    "{"
    "}"
    "."
    "->"
    "++"
    "--"
    "&"
    "*"
    "+"
    "-"
    "~"
    "!"
    "/"
    "%"
    "<<"
    ">>"
    "<"
    ">"
    "<="
    ">="
    "=="
    "!="
    "^"
    "|"
    "&&"
    "||"
    "?"
    ":"
    "::"
    ";"
    "..."
    "="
    "*="
    "/="
    "%="
    "+="
    "-="
    "<<="
    ">>="
    "&="
    "^="
    "|="
    ","
    "#"
    "##"
    "<:"
    ":>"
    "<%"
    "%>"
    "%:"
    "%:%:")
  ///
  (assert-event (string-listp *punctuators-c23*))
  (assert-event (no-duplicatesp-equal *punctuators-c23*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define punctuators-for ((version versionp))
  :returns (list string-listp)
  :short "List of keywords according to the C version."
  :long
  (xdoc::topstring
   (xdoc::p
    "This does not depend on the GCC or Clang extensions,
     but just on the C standard."))
  (cond ((version-std-c17p version) *punctuators-c17*)
        ((version-std-c23p version) *punctuators-c23*))

  ///

  (more-returns
   (list no-duplicatesp-equal)))
