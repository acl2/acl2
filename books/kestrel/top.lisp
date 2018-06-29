; Kestrel Books
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "abnf/top")
(include-book "abnf/examples") ; they have XDOC topics for the manual
(include-book "apt/top")
(include-book "auto-termination/top") ; omits some books (see file for why)
(include-book "ethereum/top")
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
   For example,
   <see topic='@(url std)'>STD</see> and
   <see topic='@(url x86isa)'>X86ISA</see>
   include some Kestrel contributions.
   </p>
   <p>
   The Kestrel Books build upon, and are meant to extend and be compatible with,
   the ACL2 system code
   and various existing libraries such as
   <see topic='@(url std)'>STD</see>,
   <see topic='@(url fty)'>FTY</see>,
   <see topic='@(url seq)'>Seq</see>,
   and others.
   </p>")

(xdoc::add-resource-directory "kestrel" "images")
