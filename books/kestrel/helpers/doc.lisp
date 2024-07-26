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

;; TODO: Document the Linter (and move it to this dir)

(defxdoc helpers :short "Tools for finding, improving, and repairing proofs and books."
  :parents (kestrel-books))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc-for-macro improve-book
  :parents (helpers)
  :short "Suggest improvements for a book."
  :description
  (xdoc::topparas "@('Improve-book') tries many things to improve a book and its contents.  It prints suggestions for the user to consider, but does not actually change the book.

To apply @('improve-book') to some book FOO, start ACL2 in the directory that contains FOO.  The ACL2 session should contain as few events as possible.  FOO may need to be certified so that @('improve-book') can load its @(tsee portcullis) commands.  Then do:

@('(include-book \"kestrel/helpers/improve-book\" :dir :system)')
@('(improve-book \"FOO\")')

Improvements at the book level include including dropping @(tsee include-book)s and @(tsee local) events.

Improvements to @(tsee defthm)s include dropping @(':hints'), dropping or weaking hypotheses, and disabling slow rules.

Improvements to defuns include various things checked by our Linter tool.

Support for additional kinds of events, such as @('define'), @('mutual-recursion'), and nested events, is in-progress.

Note that all suggestions made by @('improve-book') are independent.  There is no guarantee that multiple suggested changes can be made together.")
  :arg-descriptions ((bookname "The name of the book to improve, with or without the @('.lisp') extension.")
                     (dir "The directory of the book, where @(':cbd') indicates the @(tsee cbd).")
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc-for-macro speed-up-event
  :parents (helpers improve-book)
  :short "Suggest ways to speed up an event."
  :description "Wrapping an event in a call of @('speed-up-event') causes attempts to be made to speed it up (e.g., by deleting hints).  Currently, only @(tsee defthm) and @(tsee defrule) events are supported."
  :arg-descriptions ((form "The entire event to speed up (e.g., a @('defthm') form).")
                     (print "How much to print (should satisfy print-levelp).")
                     (synonym-alist "A symbol-symbol-alist mapping from synonyms to known event types (e.g., you can declare foo to be treated like defthm by the speed-up tool).")))
