; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc show-books
  :parents (kestrel-utilities books include-book)
  :short "Return a tree representing the included @(see books)."
  :long "
 @({
 General Forms:
 (show-books) ; Return a tree representing the included books,
              ; in a format described below
 (show-books :sysfile :default) ; Same as above
 (show-books :sysfile t)   ; Same as above but using sysfiles when possible
 (show-books :sysfile nil) ; Same as above but using strings only
 })

 <p>The form @('(show-books)') evaluates to a tree whose leaves consist of
 exactly one entry per book included in the current ACL2 session using @(tsee
 include-book) (either explicitly or by way of @('include-book') forms within
 included books).  The result thus has the following structure, which actually
 will probably be pretty obvious when you run @('show-books').</p>

 @({
 result     ::= entry-list
 entry-list ::= nil | (entry . entry-list)
 entry      ::= (book-representation . entry-list)
 })

 <p>The @(':sysfile') keyword controls the @('book-representation') values in
 the result.  When @(':sysfile') is omitted or has value @(':default'), the
 books will be represented using their full pathnames except as follows.  When
 a book is in the @(see community-books), it is represented as
 @('\"[books]/pathname\"') where @('\"pathname\"') is the book's pathname
 relative to the community-books directory.  The only other exception can occur
 when you have set the @(see project-dir-alist), in which case sysfile notation
 will be used for books residing under project directories; see @(see
 sysfile).</p>

 <p>The other legal values of @(':sysfile') are @('t') and @('nil').  With
 value @('t'), sysfile notation will be used for all books residing in project
 directories, including the community books.  With value @('nil'), the
 full (absolute) pathname will be used for all books.</p>

 <p>Note that each book will be listed only once.  If it was included by way of
 an @(tsee include-book) form within an included book, then it will be a child
 of the book that included it non-@(see redundant)ly.</p>"

)
