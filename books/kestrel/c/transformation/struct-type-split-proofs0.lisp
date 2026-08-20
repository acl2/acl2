; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "struct-type-split")

(include-book "kestrel/c/syntax/input-files" :dir :system)
(include-book "kestrel/c/syntax/output-files" :dir :system)
(include-book "kestrel/c/syntax/abstract-syntax-formal-mapping-direct" :dir :system)

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file applies the STS (Struct Type Split) transformation
; to a simple example, in order to experiment with proofs (in other files).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Read the code to transform.
(c$::input-files :files '("gso.c")
                 :base-dir "tests/struct-type-split"
                 :const *old*)

; Transform the code.
(struct-type-split *old*
                   *new*
                   :struct-tag "s"
                   :right-members ("b")
                   :new-tag "s2")

; Write the transformed code.
(c$::output-files :const *new*
                  :base-dir "tests/struct-type-split/new")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Check that the old code is in the formal subset.
(assert-event (c$::trans-ensemble-formalp
               (c$::code-ensemble->trans-units *old*)))

; Check that the new code is in the formal subset.
(assert-event (c$::trans-ensemble-formalp
               (c$::code-ensemble->trans-units *new*)))

; AST of the old code in the language formalization.
(defconst *oldf*
  (b* (((mv & tuens)
        (c$::ldm-trans-ensemble (c$::code-ensemble->trans-units *old*))))
    tuens))

; AST of the new code in the language formalization.
(defconst *newf*
  (b* (((mv & tuens)
        (c$::ldm-trans-ensemble (c$::code-ensemble->trans-units *new*))))
    tuens))
