; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defun fms!-lst (lst chan state)
  (declare (xargs :stobjs state
                  :mode :program
                  :guard ; incomplete guard
                  (and (open-output-channel-p chan :character state)
                       (true-listp lst))))
  (cond ((endp lst) state)
        (t (pprogn (fms! "~X01"
                         (list (cons #\0 (car lst))
                               (cons #\1 nil))
                         chan state nil)
                   (fms!-lst (cdr lst) chan state)))))

(defxdoc fms!-lst
  :parents (kestrel-utilities io)
  :short "Write each object in a list to a character output channel."
  :long "
 @({
 General Form:

 (fms!-lst list channel state)
 })

 <p>where list is an arbitrary list that is null-terminated &mdash; that is,
 satisfies @(tsee true-listp) &mdash; @('channel') is an open character output
 channel (see @(see io)), and @('state') is the ACL2 @(see state).  This
 function simply prints each form in the given list, in order, without
 evisceration (see @(see evisc-tuple)), where each is printed with @(tsee fms!)
 as shown below.</p>

 @(def fms!-lst)")
