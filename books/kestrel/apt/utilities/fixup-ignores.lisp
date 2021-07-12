; Utilities to fix up ignore declares
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/fake-worlds" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "kestrel/utilities/translate" :dir :system)
(include-book "kestrel/utilities/declares0" :dir :system)

;; Fixup the ignore declarations to ignore exactly those formals not mentioned in the body.
;; A fake-wrld is required so we can translate the BODY during the process (though we try to keep the result untranslated).
;; Note that irrelevant params may have to be dealt with separately.
;; Returns the new declares.
(defun fixup-ignores-with-fake-world (declares
                                      formals
                                      body ; untranslated
                                      fake-wrld ; must assign arities to all functions in BODY, even those that are not yet defined
                                      )
  (declare (xargs :guard (and (symbol-listp formals)
                              (all-declarep declares)
                              (plist-worldp fake-wrld))
                  :mode :program))
  (b* (((mv ctx msg-or-translated-body)
        (translate-term-with-defaults body 'fixup-ignores2 fake-wrld) ;pass a better context
        )
       ((when ctx) ;; check for translation error
        (er hard? 'fixup-ignores2 "Failed to translate ~x0. ~@1." body msg-or-translated-body))
       (translated-body msg-or-translated-body)
       (formals-mentioned (free-vars-in-term translated-body))
       (ignored-formals (set-difference-eq formals formals-mentioned))
       (declares (remove-declares 'ignore declares))
       ;; Also remove any ignorable declares, since we are setting the ignore to be exactly what we need:
       (declares (remove-declares 'ignorable declares))
       (declares (if ignored-formals
                     (add-declare-arg `(ignore ,@ignored-formals) declares)
                   declares)))
    declares))

(defun fixup-ignores2 (declares
                       formals
                       body ; untranslated
                       function-renaming
                       wrld)
  (declare (xargs :guard (and (symbol-listp formals)
                              (all-declarep declares)
                              (plist-worldp wrld))
                  :mode :program))
  (let* ((new-fns-arity-alist (pairlis$ (strip-cdrs function-renaming)
                                        (fn-arities (strip-cars function-renaming) wrld)))
         ;; New fns from the renaming may appear in TERM, but they are not yet
         ;; in the world, so we make this fake world:
         (fake-wrld (add-fake-fns-to-world new-fns-arity-alist wrld))
         )
    (fixup-ignores-with-fake-world declares
                                   formals
                                   body ; untranslated
                                   fake-wrld ; must assign arities to all functions in BODY, even those that are not yet defined
                                   )))
