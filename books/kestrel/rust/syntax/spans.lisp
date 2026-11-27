; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST$")

(include-book "positions")

(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ spans
  :parents (syntax-for-tools)
  :short "Spans of constructs in source texts."
  :long
  (xdoc::topstring
   (xdoc::p
    "A Rust construct, such as a token or an expression,
     is written as a sequence of contiguous characters.
     Its span says where:
     it is a pair of offsets into a source text,
     the offset of its first code point
     and the offset just after its last one.
     An offset is a number of code points,
     counted from the start of the source text
     (see @(see input-format) for what a source text is).
     Here we introduce a data type for spans,
     and some operations on spans.")
   (xdoc::p
    "Every token carries a span from the moment it is lexed,
     and spans are propagated through
     token trees, abstract syntax, and later pipeline stages,
     so that messages at every stage can refer to source locations;
     this parallels rustc, where nearly every structure carries a span.")
   (xdoc::p
    "A span refers to the text of a source unit
     (see @(see source-units)), not to a file:
     the file can change after it is read,
     and the source unit keeps the text that the span is about.
     A span does not say which source unit it refers to;
     the tokens of a source unit refer to the text of that unit.
     The line and the column of an offset are not stored either:
     they are computed from the text (see @(see positions)).")
   (xdoc::p
    "rustc's spans also have a start and an exclusive end,
     as offsets into the text after the byte order mark is removed
     and the line endings are normalized;
     its offsets count bytes, where ours count code points."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod span
  :short "Fixtype of spans."
  :long
  (xdoc::topstring
   (xdoc::p
    "A span consists of two offsets into a source text,
     which characterize a sequence of contiguous code points:
     the start is the offset of the first one,
     and the end is the offset just after the last one.
     So the ending offset of a span is exclusive,
     and the number of code points is the difference of the two.")
   (xdoc::p
    "The start of a span is normally not after its end.
     However, our data structure for spans allows it;
     the spans produced by the tokenizer are well-formed in this sense."))
  ((start nat)
   (end nat))
  :pred spanp
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-span
  :short "A span witness."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see rust::irr-edition) for
     the purpose of these witnesses."))
  :type spanp
  :body (make-span :start 0 :end 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption span-option
  span
  :short "Fixtype of optional spans."
  :pred span-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist span-list
  :short "Fixtype of lists of spans."
  :elt-type span
  :true-listp t
  :elementp-of-nil nil
  :pred span-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define span-length ((span spanp))
  :returns (length natp)
  :short "Number of code points of a span."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is 0 if the start is after the end."))
  (nfix (- (span->end span) (span->start span))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define span-join ((span1 spanp) (span2 spanp))
  :returns (span spanp)
  :short "Join two spans."
  :long
  (xdoc::topstring
   (xdoc::p
    "The first span must come before the second one.
     We return a new span that goes
     from the start of the first span to the end of the second span."))
  (make-span :start (span->start span1)
             :end (span->end span2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define span-text ((span spanp) (text nat-listp))
  :returns (nats true-listp :rule-classes :type-prescription)
  :short "Code points of a text at a span."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the code points of the text
     from the start of the span to its end, exclusive.
     The span should be within the text:
     its end should be at most the length of the text.
     (If it is not, the result has @('nil')
     for each offset beyond the text.)"))
  (take (span-length span)
        (nthcdr (span->start span) (nat-list-fix text))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define span-to-msg ((span spanp) (text nat-listp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a span as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in user-oriented messages.
     It shows the positions, in the text that the span refers to,
     of the start of the span and of its end, which is exclusive."))
  (msg "[~@0 to ~@1)"
       (position-to-msg (position-of-offset (span->start span) text))
       (position-to-msg (position-of-offset (span->end span) text))))
