; Utilities to fix up ignore declares
;
; Copyright (C) 2014-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fake-worlds")
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(include-book "translate")
(include-book "declares0")
(include-book "mutual-recursion-forms")

;; TODO: Move this file to ../../utilities

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
                  :mode :program ;; because we call translate-term-with-defaults
                  ))
  (b* (((mv ctx msg-or-translated-body)
        (translate-term-with-defaults body 'fixup-ignores-with-fake-world fake-wrld) ;pass a better context
        )
       ((when ctx) ;; check for translation error
        (er hard? 'fixup-ignores-with-fake-world "Failed to translate ~x0. ~@1." body msg-or-translated-body))
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

;; The name-arity-alist supports translating the BODY by assigning arities to
;; functions that may appear but are not already defined.
;; Returns the new declares.
(defun fixup-ignores-with-name-arity-alist (declares
                                            formals
                                            body ; untranslated
                                            name-arity-alist
                                            wrld)
  (declare (xargs :guard (and (all-declarep declares)
                              (symbol-listp formals)
                              (symbol-alistp name-arity-alist)
                              (nat-listp (strip-cdrs name-arity-alist))
                              (plist-worldp wrld))
                  :mode :program ;; because this does translation
                  ))
  (let ((fake-wrld (add-fake-fns-to-world name-arity-alist wrld)))
    (fixup-ignores-with-fake-world declares
                                   formals
                                   body
                                   fake-wrld)))

;; ;; This variant takes a function-renaming and uses it to construct a fake world.
;; ;; Returns the new declares.
;; (defun fixup-ignores2 (declares
;;                        formals
;;                        body ; untranslated
;;                        function-renaming
;;                        wrld)
;;   (declare (xargs :guard (and (symbol-listp formals)
;;                               (all-declarep declares)
;;                               (plist-worldp wrld))
;;                   :mode :program))
;;   (let* (;; New fns from the renaming may appear in TERM, but they are not yet
;;          ;; in the world, so we make a fake world using this alist:
;;          (new-fns-arity-alist (pairlis$ (strip-cdrs function-renaming)
;;                                         (fn-arities (strip-cars function-renaming) wrld))))
;;     (fixup-ignores-with-name-arity-alist declares
;;                                          formals
;;                                          body ; untranslated
;;                                          new-fns-arity-alist
;;                                          wrld)))

;; Returns the new defun-form.
(defun fixup-ignores-in-defun-form (defun-form
                                     name-arity-alist ; has entries for all undefined functions called in DEFUN-FORM (except rec calls)
                                     wrld)
  (declare (xargs :guard (and (defun-formp defun-form)
                              (symbol-alistp name-arity-alist)
                              (nat-listp (strip-cdrs name-arity-alist))
                              (plist-worldp wrld))
                  :mode :program))
  (let* ((name (get-name-from-defun defun-form))
         (formals (get-formals-from-defun defun-form))
         (arity (len formals))
         (declares (get-declares-from-defun defun-form))
         (body (get-body-from-defun defun-form))
         ;; In case the function is recursive:
         (name-arity-alist (acons name arity name-arity-alist))
         (new-declares (fixup-ignores-with-name-arity-alist declares
                                                            formals
                                                            body ; untranslated
                                                            name-arity-alist
                                                            wrld)))
    (replace-declares-in-defun defun-form new-declares)))

;; Returns the new defun-forms.
(defun fixup-ignores-in-defun-forms (defun-forms name-arity-alist wrld)
  (declare (xargs :guard (and (all-defun-formp defun-forms)
                              (true-listp defun-forms)
                              (symbol-alistp name-arity-alist)
                              (nat-listp (strip-cdrs name-arity-alist))
                              (plist-worldp wrld))
                  :mode :program))
  (if (endp defun-forms)
      nil
    (cons (fixup-ignores-in-defun-form (first defun-forms) name-arity-alist wrld)
          (fixup-ignores-in-defun-forms (rest defun-forms) name-arity-alist wrld))))

;; Returns the new mutual-recursion.
(defun fixup-ignores-in-mutual-recursion-form (mut-rec wrld)
  (declare (xargs :guard (and (mutual-recursion-formp mut-rec)
                              (plist-worldp wrld))
                  :mode :program))
  `(mutual-recursion ,@(fixup-ignores-in-defun-forms
                        (cdr mut-rec)
                        (get-name-arity-list-from-mutual-recursion mut-rec)
                        wrld)))
