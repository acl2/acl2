((:FILES "
.:
ccg.lisp
"
)
 (:TITLE    "CCG Termination Analysis")
 (:AUTHOR/S "Daron Vroon and Pete Manolios")
 (:KEYWORDS ; non-empty list of keywords, case-insensitive
   "book contributions" "contributed books"
   "termination" "termination analysis"
   "automated termination proofs"
   )
 (:ABSTRACT
"Automated termination analysis based on Calling Context Graphs,
developed as part of ACL2 Sedan. 

To use this book, use the event form shown at the bottom.
CCG is configured by calling set-termination-method with a single
parameter, which must be one of these:

    :ccg - CCG analysis only (no measure-based proof attempt)
    :measure - no CCG analysis (measure-based proofs only) 

Regardless of this or other settings, ACL2's built-in method will be
used if an explicit measure is specified.

Of course, any termination analysis is necessarily incomplete and
eventually users may come across terminating functions that CCG
analysis cannot prove terminating. When that happens, CCG analysis
will construct a function that is as simple as possible, includes a
subset of the looping behavior of the submitted function, and which
CCG analysis cannot prove terminating. This function, along with
several suggestions of how to help CCG analysis prove termination,
will be presented to the user.

Our CCG termination analysis is highly customizable and includes many
features not mentioned here. For detailed documentation please refer
to :doc ccg from inside a session.

")
 (:PERMISSION ; author/s permission for distribution and copying:
"Copyright (C) 2010 Daron Vroon, Pete Manolios.
License: A 3-clause BSD license.  
See the LICENSE file distributed with ACL2.
"))

#|
(duplicated here from README)
To enable CCG termination analysis:
(include-book "ccg"  :ttags ((:ccg)) :load-compiled-file nil)
(ld "ccg-settings.lsp")

|#