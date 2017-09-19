; Kestrel Books
;
; Copyright (C) 2015-2017 Kestrel Institute (http://www.kestrel.edu)
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "abnf/top")
(include-book "abnf/examples") ; they have XDOC topics for the manual
(include-book "apt/top")
(include-book "soft/top")
(include-book "utilities/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc kestrel-books

  :parents (software-verification)

  :short "A collection of ACL2 books contributed mainly by Kestrel Institute."

  :long
  "<img src='res/kestrel/kestrel-logo.png'/>
   <p>
   The <b>Kestrel Books</b> are a collection of ACL2 books
   contributed mainly by <a href='http://www.kestrel.edu'>Kestrel Institute</a>.
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
