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

(local (include-book "std/lists/top" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ spans
  :parents (syntax-for-tools)
  :short "Spans of constructs in files."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on the fact that characters have @(see positions),
     Rust constructs, such as tokens and expressions,
     which are formed by sequences of contiguous characters,
     have spans, i.e. pairs of positions, starting and ending.
     Here we introduce a data type for spans,
     and some operations on spans.")
   (xdoc::p
    "Every token carries a span from the moment it is lexed,
     and spans are propagated through
     token trees, abstract syntax, and later pipeline stages,
     so that messages at every stage can refer to source locations;
     this parallels rustc, where nearly every structure carries a span."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod span
  :short "Fixtype of spans."
  :long
  (xdoc::topstring
   (xdoc::p
    "A span consists of two positions,
     which characterize a sequence of contiguous characters.
     The ending position of a span is inclusive.")
   (xdoc::p
    "The positions of a span normally have the same file component,
     i.e. the span is within a file.
     However, our data structure for spans allows for
     positions with different files;
     well-formed spans produced by the lexer are within one file."))
  ((start position)
   (end position))
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
  :body (make-span :start (irr-position) :end (irr-position)))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define span-to-msg ((span spanp))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp character-alistp))))
  :short "Represent a span as a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used in user-oriented messages."))
  (msg "[~@0 to ~@1]"
       (position-to-msg (span->start span))
       (position-to-msg (span->end span))))
