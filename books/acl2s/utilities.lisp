#|$ACL2s-Preamble$;
; Copyright (C) 2018, Northeastern University
; Written by Pete Manolios
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t);$ACL2s-Preamble$|#

(in-package "ACL2S")

(include-book "kestrel/utilities/proof-builder-macros" :dir :system)

(defxdoc acl2-pc::repeat-until-done
  :parents (proof-builder-commands)
  :short "(macro)
Repeat the given instructions until all goals have been proved"
  :long "@({
 Example:
 (repeat-until-done induct (repeat bash))

 General Form:
 (repeat-until-done instr1 ... instrk)
 })

 <p>where each @('instri') is a proof-builder instruction.</p>")

(define-pc-macro repeat-until-done (&rest instrs)
  (value
   `(repeat (do-all
             ,@(append instrs 
                       `((negate (when-not-proved fail))))))))
