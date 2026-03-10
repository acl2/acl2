; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "positions")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ spans
  :parents (concrete-syntax)
  :short "Spans of constructs in files."
  :long
  (xdoc::topstring
   (xdoc::p
    "Based on the fact that characters have @(see positions),
     C constructs, such as tokens and expressions,
     which are formed by sequences of contiguous characters,
     have spans, i.e. pair of positions, starting and ending.
     Here we introduce a data type for spans,
     and some operations on spans."))
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
     However, our data structure for spans allow for
     positions with different files.
     Indeed, this may be the case for constructs
     within which there is a @('#line') directive [C17:6.10.4]."))
  ((start position)
   (end position))
  :pred spanp
  :layout :fulltree)

;;;;;;;;;;;;;;;;;;;;

(defirrelevant irr-span
  :short "An irrelevant span."
  :type spanp
  :body (make-span :start (irr-position) :end (irr-position)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption span-option
  span
  :short "Fixtype of optional spans."
  :pred span-optionp)

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
