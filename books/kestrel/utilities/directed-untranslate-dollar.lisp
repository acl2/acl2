; A simpler interface to directed-untranslate
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "directed-untranslate")
(include-book "translate")

;; TODO: Consider passing in iff-flg and ctx
;;Example: (directed-untranslate$ '(if x y 'nil) '(and x y) (w state))
(defun directed-untranslate$ (term ;the term to untranslate
                              guide-form ;an untranslated term to try to match
                              wrld)
  (declare (xargs :mode :program
                  :guard (pseudo-termp term)))
  (directed-untranslate guide-form
                        (translate-term guide-form 'directed-untranslate$ wrld)
                        term
                        nil ;iff-flg
                        nil ;stobjs-out
                        wrld))
