; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/defirrelevant" :dir :system)

(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ positions
  :parents (syntax-for-tools)
  :short "Positions in source texts, as lines and columns."
  :long
  (xdoc::topstring
   (xdoc::p
    "A place in a source text is an offset:
     the number of code points of the text that come before it.
     Tokens and syntax trees refer to the text by offsets
     (see @(see spans)).
     For a person, a place is a line and a column.
     We introduce positions, which are pairs of a line and a column,
     and the function that gives the position of an offset in a text.
     So positions are not stored with the tokens:
     they are computed from offsets, where a message needs them.")
   (xdoc::p
    "A line ends with a line feed, which is its last character.
     Every other code point takes one column, a carriage return too:
     in a source text, a carriage return is not part of a line ending
     (see @(see input-format))."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod position
  :short "Fixtype of positions."
  :long
  (xdoc::topstring
   (xdoc::p
    "A position is a line number and a column number.
     We number lines from 1 and columns from 0.
     (For error messages, rustc displays both lines and columns from 1;
     any such adjustment belongs in message formatting, not here.)
     Columns count code points."))
  ((line pos)
   (column nat))
  :pred positionp
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-position
  :short "A position witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see rust::irr-edition) for
     the purpose of these witnesses."))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-init ()
  :returns (pos positionp)
  :short "Position of the start of a text."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is at line 1 and column 0."))
  (make-position :line 1 :column 0)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-inc-column ((columns posp) (pos positionp))
  :returns (new-pos positionp)
  :short "Increment a position by a number of columns."
  :long
  (xdoc::topstring
   (xdoc::p
    "The line number is unchanged."))
  (change-position pos :column (+ (the unsigned-byte (position->column pos))
                                  (the unsigned-byte (lposfix columns))))
  :inline t)

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
                            (the (integer 1 *) (lposfix lines)))
                   :column 0)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-advance ((nat natp) (pos positionp))
  :returns (new-pos positionp)
  :short "Advance a position over one code point."
  :long
  (xdoc::topstring
   (xdoc::p
    "A line feed moves to the next line;
     every other code point advances the column by one.
     (Like rustc, we do not treat
     a carriage return as a line terminator:
     rustc normalizes CRLF to LF before lexing,
     and any other carriage return is
     a whitespace character like a space or a tab,
     not a line break.)"))
  (if (eql (lnfix nat) #x0a)
      (position-inc-line 1 pos)
    (position-inc-column 1 pos)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-advance-over ((count natp) (nats nat-listp) (pos positionp))
  :returns (new-pos positionp)
  :short "Advance a position over the first code points of a list."
  :long
  (xdoc::topstring
   (xdoc::p
    "The position is advanced over @('count') code points,
     or over all of them if there are fewer."))
  (b* ((count (lnfix count))
       (nats (nat-list-fix nats))
       ((when (or (equal count 0) (endp nats))) (position-fix pos)))
    (position-advance-over (1- count)
                           (cdr nats)
                           (position-advance (car nats) pos)))
  :measure (nfix count))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-of-offset ((offset natp) (text nat-listp))
  :returns (pos positionp)
  :short "Position of an offset in a text."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the line and the column of the code point at that offset,
     or of the end of the text if the offset is its length:
     the line is 1 more than the number of line feeds before the offset,
     and the column is the number of code points
     between the last of those line feeds and the offset.
     An offset beyond the end of the text
     gives the position of the end of the text."))
  (position-advance-over offset text (position-init)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define position-to-msg ((pos positionp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a position as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in user-oriented error messages.
     It consists of line and column, separated by a colon."))
  (msg "~x0:~x1"
       (position->line pos)
       (position->column pos)))
