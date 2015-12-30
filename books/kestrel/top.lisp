; Kestrel Books
;
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains the top-level documentation for the Kestrel Books.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "general/top")
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
  </p>")

(xdoc::add-resource-directory "kestrel" "images")
