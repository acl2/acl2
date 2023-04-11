; Utilities that translate terms
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)

;; Returns a list of the free variabls in TERM, an untranslated term.  This
;; translates TERM using WRLD, so all functions in TERM must have entries
;; (perhaps fake) in WRLD.
;; TODO: Make this one the primary one, but note that it requires the world.
(defun free-vars-in-untranslated-term$ (term wrld)
  (declare (xargs :guard (plist-worldp wrld)
                  :mode :program))
  (let ((translated-term (translate-term term 'free-vars-in-untranslated-term$ wrld)))
    (free-vars-in-term translated-term)))

(defun free-vars-in-untranslated-term-list$ (terms wrld)
  (declare (xargs :guard (and (true-listp terms)
                              (plist-worldp wrld))
                  :mode :program))
  (if (endp terms)
      nil
    (union-eq (free-vars-in-untranslated-term$ (first terms) wrld)
              (free-vars-in-untranslated-term-list$ (rest terms) wrld))))
