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

(include-book "values")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ screens
  :parents (dynamic-environments)
  :short "Screens where console printing goes."
  :long
  (xdoc::topstring
   (xdoc::p
    "Leo provides console print statements,
     which are not represented in the zero-knowledge circuits
     but are executed as part of the calculation of outputs from inputs:
     in the course of this execution,
     console print statements print things on the screen.")
   (xdoc::p
    "In order to formally model this aspect of Leo'd dynamic semantics,
     we introduce a notion of screen as a collection of printed messages.
     The screen is initially empty,
     and it is extended with messages as console print statements are executed.
     This represents not the totality of the screen as one might think of,
     but just the portion that is relevant to one run of a Leo program."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deftagsum screen-message
  :short "Fixtype of screen messages."
  :long
  (xdoc::topstring
   (xdoc::p
    "We introduce a notion of screen message as the thing printed by
     a single console print statement.
     This should be a sequence of characters,
     obtained by combining the format strings
     with the values obtained from the expressions (if any).
     However, for now we do not carry out this combination (but we plan to),
     and instad define a screen message as consisting of
     a format string
     (the characters from the format string in the console print statement)
     and a list of zero or more values
     (resulting from evaluating the expressions in the console print statement).
     We also label the message with an indication of
     the kind of print statement."))
  (:error ((string char-list)
           (values value-list)))
  (:log ((string char-list)
         (values value-list)))
  :pred screen-messagep)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist screen-message-list
  :short "Fixtype of lists of screen messages."
  :elt-type screen-message
  :true-listp t
  :elementp-of-nil nil
  :pred screen-message-listp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod screen
  :short "Fixtype of screens."
  :long
  (xdoc::topstring
   (xdoc::p
    "We model a screen as a list of screen messages.
     We wrap the list into this product fixtype
     to facilitate possible future extensions
     and to create a layer of abstraction."))
  ((messages screen-message-list))
  :tag :screen
  :pred screenp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define init-screen ()
  :returns (screen screenp)
  :short "Initial screen."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is empty."))
  (screen nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define print-message-to-screen ((message screen-messagep) (screen screenp))
  :returns (new-screen screenp)
  :short "Extend a screen with a message."
  :long
  (xdoc::topstring
   (xdoc::p
    "We append the message to the end of the list."))
  (screen (append (screen->messages screen)
                  (list message)))
  :hooks (:fix))
