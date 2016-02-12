; Kestrel Books
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains the top-level documentation for the Kestrel Books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "general/top")
(include-book "soft/top")
(include-book "system/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc kestrel-books

  :parents (software-verification)

  :short
  "A collection of ACL2 books contributed by Kestrel Institute."

  :long
  "<img src='res/kestrel/kestrel-logo.png'/>
  <p>
  The <b>Kestrel Books</b> are a collection of ACL2 books
  contributed by <a href='http://www.kestrel.edu'>Kestrel Institute</a>.
  The Kestrel Books are freely available under a liberal license.
  Specific copyright, author, and license information
  is provided in the individual files and subdirectories.
  </p>
  <p>
  As they become more stable,
  parts of the Kestrel Books may be moved
  to other locations in the
  <see topic='@(url community-books)'>Community Books</see>.
  For example, <see topic='@(url std)'>STD</see>
  includes some Kestrel contributions.
  </p>")

(xdoc::add-resource-directory "kestrel" "images")
