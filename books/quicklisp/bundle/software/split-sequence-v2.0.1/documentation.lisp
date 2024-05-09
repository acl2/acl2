;;;; -*- Mode: Lisp; indent-tabs-mode: nil -*-

(in-package :split-sequence)

(setf (documentation 'split-sequence 'function)
      "Return a list of subsequences in seq delimited by delimiter.
If :remove-empty-subseqs is NIL, empty subsequences will be included
in the result; otherwise they will be discarded.  All other keywords
work analogously to those for CL:SUBSTITUTE.  In particular, the
behaviour of :from-end is possibly different from other versions of
this function; :from-end values of NIL and T are equivalent unless
:count is supplied. :count limits the number of subseqs in the main
resulting list. The second return value is an index suitable as an
argument to CL:SUBSEQ into the sequence indicating where processing
stopped.")

(setf (documentation 'split-sequence-if 'function)
      "Return a list of subsequences in seq delimited by items satisfying
predicate.
If :remove-empty-subseqs is NIL, empty subsequences will be included
in the result; otherwise they will be discarded.  All other keywords
work analogously to those for CL:SUBSTITUTE-IF.  In particular, the
behaviour of :from-end is possibly different from other versions of
this function; :from-end values of NIL and T are equivalent unless
:count is supplied. :count limits the number of subseqs in the main
resulting list. The second return value is an index suitable as an
argument to CL:SUBSEQ into the sequence indicating where processing
stopped.")

(setf (documentation 'split-sequence-if-not 'function)
      "Return a list of subsequences in seq delimited by items satisfying
\(CL:COMPLEMENT predicate).
If :remove-empty-subseqs is NIL, empty subsequences will be included
in the result; otherwise they will be discarded.  All other keywords
work analogously to those for CL:SUBSTITUTE-IF-NOT.  In particular,
the behaviour of :from-end is possibly different from other versions
of this function; :from-end values of NIL and T are equivalent unless
:count is supplied. :count limits the number of subseqs in the main
resulting list. The second return value is an index suitable as an
argument to CL:SUBSEQ into the sequence indicating where processing
stopped.")
