; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "identifiers")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ locations
  :parents (dynamic-semantics)
  :short "Leo locations."
  :long
  (xdoc::topstring
   (xdoc::p
    "During execution, Leo reads and writes values in variables.
     These values may be primitive or aggregate:
     the latter consist of parts that can be individually read and written;
     these parts may in turn have sub-parts, recursively.")
   (xdoc::p
    "These individually readable and writable parts are locations.
     A location may be a variable,
     or a component of a tuple location,
     or a component of a struct location;
     this notion will be extended as more kinds of aggregate values
     (besides tuples and structs) are added to Leo,
     most likely arrays.
     That is, a location consists of a variable (always the starting point)
     followed by zero or more ``sub-part selectors''.
     The term `location' is appropriate because
     these are abstract memory locations.")
   (xdoc::p
    "As a point of comparison, the Java Language Specification
     uses the term `variable' to denote what we call `locations' here;
     in Java, a variable is not just a named variable,
     e.g. it may be an array component.
     In our Leo formalization, we reserve the term `variable'
     for the named locations at the top level."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum location
  :short "Fixtype of Leo locations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is either a variable name,
     or a tuple component of a location;
     the latter is denoted via a numeric index."))
  (:var ((name identifier)))
  (:tuple-comp ((tuple location)
                (index nat)))
  (:struct-comp ((struct location)
                  (name identifier)))
  :pred locationp)
