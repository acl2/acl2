; Utilities that translate terms
;
; Copyright (C) 2014-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "tables")
(local (include-book "read-acl2-oracle"))

(local (in-theory (disable w)))

;; Returns (mv ctx msg-or-val), a context-message-pair.  When CTX is nil,
;; translation succeeded and msg-or-val is the result.  When CTX is non-nil,
;; translation failed and msg-or-val is a msgp indicating the error.
(defun translate-term-with-defaults (term ctx wrld)
  (declare (xargs :mode :program
                  ;; todo: guard
                  ))
  (translate-cmp term
                 t ;stobjs-out, don't enforce stobj restrictions
                 t ;logic-modep ;; means :program mode cannot be involved (TRANSLATE-CMP explicitly checks for that).
                 t ;known-stobjs
                 ctx
                 wrld
                 (default-state-vars nil)))

;; Translates a term (by expanding macros, quoting constants, turning lets into
;; lambdas, etc.).  Returns the translation of TERM, or throws an informative
;; hard error if something is wrong.  I think this is based on something Matt
;; K. wrote.  See also check-user-term.
;; See also translate-term-allowing-ignored-vars.
(defun translate-term (term ctx wrld)
  (declare (xargs :mode :program
                  ;; todo: guard
                  ))
  (mv-let (ctx msg-or-val)
    (translate-term-with-defaults term ctx wrld)
    (if ctx
        (er hard! ctx "Failed to translate term ~x0. ~@1" term msg-or-val)
      msg-or-val)))

;; Translate a list of terms.
;; Compare to TRANSLATE-TERM-LST?
(defun translate-terms (terms ctx wrld)
  (declare (xargs :mode :program))
  (if (endp terms)
      nil
    (cons (translate-term (first terms) ctx wrld)
          (translate-terms (rest terms) ctx wrld))))

;; Checks whether UNTRANSLATED-TERM can be translated in world WRLD.
(defun translatable-termp (untranslated-term wrld)
  (declare (xargs :mode :program
                  :guard (plist-worldp wrld)))
  (mv-let (ctx msg-or-val)
    (translate-term-with-defaults untranslated-term 'translatable-termp wrld)
    (declare (ignore msg-or-val)) ; ignore the translation
    (not ctx) ; ctx means an error occurred
    ))

;; Checks whether all of the UNTRANSLATED-TERMS can be translated in world WRLD.
(defun translatable-term-listp (untranslated-terms wrld)
  (declare (xargs :mode :program
                  :guard (and (true-listp untranslated-terms)
                              (plist-worldp wrld))))
  (if (endp untranslated-terms)
      t
    (and (translatable-termp (first untranslated-terms) wrld)
         (translatable-term-listp (rest untranslated-terms) wrld))))

;; Returns the translation of TERM (or throws an error)
(defun translate-term-allowing-ignored-vars (term ctx wrld)
  (declare (xargs :mode :program
                  ;; xb:guard (plist-worldp wrld)
                  ))
  (let ((wrld (table-programmatic 'acl2-defaults-table :ignore-ok t wrld)))
    (translate-term term ctx wrld)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp translated-term state).
(defund translate-term-in-logic-mode (term ctx state)
  (declare (xargs :stobjs state
                  ;; todo: guard?
                  ))
  (let ((wrld (w state)))
    (mv-let (erp translated-term state)
      (in-logic-mode (translate-term term ctx wrld) state)
      (if erp
          (mv erp nil state)
        (if (not ;; (termp translated-term wrld) ; todo: use this, but what about the guard
                 (pseudo-termp translated-term)
                 )
            ;; should never happen:
            (prog2$ (er hard? 'translate-term-in-logic-mode "Bad result of translation: ~x0." translated-term)
                    (mv :bad-result-of-translation nil state))
          (mv nil ; no error
              translated-term
              state))))))

(defthm pseudo-termp-of-mv-nth-1-of-translate-term-in-logic-mode
  (pseudo-termp (mv-nth 1 (translate-term-in-logic-mode term ctx state)))
  :hints (("Goal" :in-theory (enable translate-term-in-logic-mode))))

(defthm w-of-mv-nth-1-of-translate-term-in-logic-mode
  (equal (w (mv-nth 2 (translate-term-in-logic-mode term ctx state)))
         (w state))
  :hints (("Goal" :in-theory (enable translate-term-in-logic-mode))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp translated-terms state).
(defund translate-terms-in-logic-mode (terms ctx state)
  (declare (xargs :stobjs state
                  :guard (true-listp terms) ;; todo: what else?
                  ))
  (if (endp terms)
      (mv nil nil state)
    (mv-let (erp translated-first state)
      (translate-term-in-logic-mode (first terms) ctx state)
      (if erp
          (mv erp nil state)
        (mv-let (erp translated-rest state)
          (translate-terms-in-logic-mode (rest terms) ctx state)
          (if erp
              (mv erp nil state)
            (mv nil (cons translated-first translated-rest) state)))))))

(defthm pseudo-term-listp-of-mv-nth-1-of-translate-terms-in-logic-mode
  (pseudo-term-listp (mv-nth 1 (translate-terms-in-logic-mode terms ctx state)))
  :hints (("Goal" :in-theory (enable translate-terms-in-logic-mode))))

(defthm w-of-mv-nth-1-of-translate-terms-in-logic-mode
  (equal (w (mv-nth 2 (translate-terms-in-logic-mode terms ctx state)))
         (w state))
  :hints (("Goal" :in-theory (enable translate-terms-in-logic-mode))))
