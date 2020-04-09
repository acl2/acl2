; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file, which is submitted to ACL2 by write-td-cands.sh, creates the file
; td-cands.lisp, which supports the use of defunt.  For more information, see
; the README in this directory.

(in-package "ACL2")

(ld '(

; Include a lot of books.
(include-book "doc/top-slow" :dir :system) ; probably takes several minutes

; The following three forms probably speed things up.
(set-gc-strategy :egc)
(gc-verbose t) ; or (gc-verbose t t) to see many ephemeral GC messages
(ld '((unmemoize 'translate11)
      (unmemoize 'translate11-call)
      (unmemoize 'translate11-lst)
      (unmemoize 'macroexpand1-cmp)
      (unmemoize 'normalize-lst)
      (unmemoize 'normalize)
      (unmemoize 'remove-guard-holders1-lst)
      (unmemoize 'remove-guard-holders1)
      (unmemoize 'remove-guard-holders)
      (unmemoize 'remove-guard-holders-weak)
      (unmemoize 'ffnnamep-mod-mbe-lst)
      (unmemoize 'all-vars1-lst)
      (unmemoize 'all-vars1)
      (unmemoize 'all-fnnames1)))

(clear-memoize-statistics) ; perhaps unnecessary
(reset-prehistory) ; perhaps unnecessary

; Initialize the termination database, i.e., the td stobj.
(include-book "termination-database")

; The values 10 and 100 below, for :fns-limit 10 :clause-size-limit (resp.),
; are somewhat arbitrary.  But some experiments on 6/28/2018 suggest that these
; might be reasonable limits for now.  See to-do.txt.
(td-init :fns-limit 10 :clause-size-limit 1000)

; Write out the file of "termination database (td) candidates" for subsuming
; proposed termination theorems.
(time$ (write-td "td-cands"))

)

:ld-pre-eval-print t)
