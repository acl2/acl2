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
     positions of characters in files."))
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
     is also consistent with Emacs.")
   (xdoc::p
    "We also include an indication of the file that the position refers to,
     for now represented as a string, which we use for a file path.
     Although generally each file is (pre)procesed individually
     (so that the file in question is contextually known),
     the preprocessing directive @('#line') [C17:6.10.4]
     can change the `presumed' line number and file name.
     We could consider more ``sparse'' representations of the `presumed' file,
     compared to adding it to every position,
     but in memory it is just a pointer, repeated in every position,
     and it supports better execution speed,
     at the cost of a little extra memory usage."))
  ((file string)
   (line pos)
   (column nat))
  :pred positionp
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-position
  :short "An irrelevant position."
  :type positionp
  :body (make-position :file "" :line 1 :column 0))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-init ((file stringp))
  :returns (pos positionp)
  :short "Initial position in a file."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is at line 1 and column 0.")
   (xdoc::p
    "The file information is passed as input."))
  (make-position :file file :line 1 :column 0)
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
  (change-position pos
                   :line (+ (the (integer 1 *) (position->line pos))
                            (the (integer 1 *) lines))
                   :column 0)
  :inline t
  :hooks nil

  ///

  (fty::deffixequiv position-inc-line
    :args ((pos positionp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-to-msg ((pos positionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a position as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in user-oriented error messages.
     It consists of file, line, and column, separated by colons."))
  (msg "~s0:~x1:~x2:"
       (position->file pos)
       (position->line pos)
       (position->column pos)))
