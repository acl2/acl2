; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C2C")

(include-book "../../struct-type-split-proofs")

(include-book "../../../syntax/input-files")
(include-book "../../../syntax/output-files")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(c$::input-files :files '("gso.c")
                 :const *old*)

(struct-type-split *old*
                   *new*
                   :struct-tag "s"
                   :right-members ("b")
                   :new-tag "s2")

(c$::output-files :const *new*
                  :base-dir "new")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct-type-split-proofs *old*
                          *new*
                          :struct-tag "s"
                          :new-tag "s2"
                          :right-members ("b"))
