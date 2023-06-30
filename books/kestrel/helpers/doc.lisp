; Documentation for the helpers/ dir.
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/defmacrodoc" :dir :system) ;todo: reduce
(include-book "improve-book")
(include-book "kestrel/utilities/xdoc-paras" :dir :system)

(defxdoc helpers :short "Tools for finding, improving, and repairing proofs and books.")

(defxdoc-for-macro improve-book
  :parents (helpers)
  :short "Suggest improvements for a book."
  :description
  (xdoc::topparas "@('Improve-book') tries many things to improve a book and its contents.  It prints suggestions for the user to consider.

@('Improve-book') should be invoked in a fresh ACL2 session (except for including the @('improve-book') tool itself), usually while connected to the directory of the book to be improved.

Improvements at the book level include including dropping @(tsee include-book)s and @(tsee local) events.

Improvements to @(tsee defthm)s include dropping @(':hints'), dropping or weaking hypotheses, and disabling slow rules.

Improvements to defuns include various things checked by our Linter tool.

Support for additional kinds of events, such as @('define'), @('mutual-recursion'), and nested events, is in-progress.

Note that all suggestions made by @('improve-book') are independent.  There is no guarantee that multiple suggested changes can be made together.")
  :arg-descriptions ((bookname "The name of the book to improve.")
                     (dir "The directory of the book, where @(':cbd') indicates the @('cbd').")
                     (print "How much to print: @('nil'), @(':brief'), @('t'), or @(':verbose').")))

(defxdoc-for-macro improve-books
  :parents (helpers improve-book)
  :short "Suggest improvements for all books in a directory, but not in subdirectories."
  :description "@('Improve-books') runs @(tsee improve-book) on all books in the current directory.  Books in subdirectories are not processed, but see @(tsee improve-books-in-subtree)."
  :arg-descriptions ((print "How much to print: @('nil'), @(':brief'), @('t'), or @(':verbose').")))

(defxdoc-for-macro improve-books-in-subtree
  :parents (helpers improve-book improve-books)
  :short "Suggest improvements for all books in a directory, including subdirectories."
  :arg-descriptions ((print "How much to print: @('nil'), @(':brief'), @('t'), or @(':verbose').")))

;; TODO: Document the Linter
