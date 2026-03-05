; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ positions
  :parents (concrete-syntax)
  :short "Positions of characters in files."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce data structures that describe
     positions of character in files."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod position
  :short "Fixtype of positions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A position within a file is normally specified by
     a combination of a line number and column number.
     We number lines from 1,
     which is consistent with [C17:6.10.4/2]:
     since the characters in the first line
     have 0 preceding new-line characters,
     the number of the first line is 1 plus 0, i.e. 1.
     We number columns from 0,
     but we could change that to 1.
     Numbering lines from 1 and columns from 0
     is also consistent with Emacs."))
  ((line pos)
   (column nat))
  :pred positionp
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-position
  :short "An irrelevant position."
  :type positionp
  :body (make-position :line 1 :column 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist position-list
  :short "Fixtype of lists of positions."
  :elt-type position
  :true-listp t
  :elementp-of-nil nil
  :pred position-listp

  ///

  (defruled position-listp-of-resize-list
    (implies (and (position-listp poss)
                  (positionp default))
             (position-listp (resize-list poss length default)))
    :induct t
    :enable resize-list)

  (defruled position-listp-of-update-nth-strong
    (implies (position-listp poss)
             (equal (position-listp (update-nth i pos poss))
                    (and (positionp pos)
                         (<= (nfix i) (len poss)))))
    :induct t
    :enable (update-nth nfix zp len)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-init ()
  :returns (pos positionp)
  :short "Initial position in a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is at line 1 and column 0."))
  (make-position :line 1 :column 0)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-inc-column ((columns natp) (pos positionp))
  :returns (new-pos positionp)
  :short "Increment a position by a number of columns."
  :long
  (xdoc::topstring
   (xdoc::p
    "The line number is unchanged."))
  (change-position pos :column (+ (the unsigned-byte (position->column pos))
                                  (the unsigned-byte columns)))
  :inline t
  :hooks nil

  ///

  (fty::deffixequiv position-inc-column
    :args ((pos positionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-inc-line ((lines posp) (pos positionp))
  :returns (new-pos positionp)
  :short "Increment a position by a number of lines."
  :long
  (xdoc::topstring
   (xdoc::p
    "The column is reset to 0."))
  (make-position :line (+ (the (integer 1 *) (position->line pos))
                          (the (integer 1 *) lines))
                 :column 0)
  :inline t
  :hooks nil

  ///

  (fty::deffixequiv position-inc-line
    :args ((pos positionp))))
