; An evaluator for x86 code lifting
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../evaluator-basic")

(include-book "projects/x86isa/machine/application-level-memory" :dir :system) ;for canonical-address-p$inline

(defconst *axe-evaluator-x86-fns-and-aliases*
  (append '(x86isa::canonical-address-p$inline ; unguarded
            ;; todo: X86ISA::PREFIXES->OPR$INLINE, logbitp
            )
          *axe-evaluator-basic-fns-and-aliases*))

;; Makes the evaluator (also checks that each alias given is equivalent to its function):
(make-evaluator-simple x86 *axe-evaluator-x86-fns-and-aliases*)
