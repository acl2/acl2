; The following copyright/license is perhaps unimportant, since this is a
; trivial file.  But I'll include it for completeness.

; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann, January, 2015.
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we include all books in this directory.  By including this book in
; books/doc/top.lisp, we ensure that this directory's documentation is included
; in the combined manual.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc data-structures
  :parents (macro-libraries)
  :short "The @('books/data-structures') library"
  :long "<p>Also see @(see std).  The @('books/data-structures') library is
 much older, much smaller, and less maintained than the @('std') library.</p>")

(include-book "alist-defthms")
(include-book "alist-defuns")
(include-book "alist-theory")
(include-book "array1")
(include-book "defalist")
(include-book "deflist")
(include-book "list-defthms")
(include-book "list-defuns")
(include-book "list-theory")
(include-book "no-duplicates")
(include-book "number-list-defthms")
(include-book "number-list-defuns")
(include-book "number-list-theory")
(include-book "portcullis")
(include-book "set-defthms")
(include-book "set-defuns")
(include-book "set-theory")
(include-book "structures")
(include-book "utilities")
