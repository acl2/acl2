; Copyright (C) 2022, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book defines the function defthm-symbol-table in support of file
; patch.lsp in this directory.  Its purpose is to return an alist mapping
; symbols used in a defthm event to their sources, where a source can be an
; included book, :builtin, or (otherwise) the book under certification.  Each
; such book name ends in ".lisp", and should start with "[books]" to abbreviate
; the absolute pathname to the system books directory -- unless the book isn't
; under that directory, but we don't expect that to happen except in testing,
; e.g., the test*.lisp books in this directory.

; We only grab the low-hanging fruit in the case of hints.  For example, we
; don't collect symbols used in substitutions provided for :use hints.  Also
; note that we mainly consider only translated terms (with some exceptions,
; e.g., for :in-theory (enable ...) and similarly for disable and e/d), so
; macros are generally not included in the symbol-table.

(in-package "ACL2")

(include-book "kestrel/utilities/book-of-event" :dir :system)
(include-book "remove-hint-setting-checkpoints") ; for rmh-keys-equal

(program) ; since book-of-event is in :program mode

(defun event-source (name current-book wrld)
  (if (acl2-system-namep name wrld)
      :builtin
    (let ((book (book-of-event name wrld)))
      (if (or (stringp book)
              (sysfile-p book))
          book
        current-book))))

(defun event-names-to-book-alist (fns current-book wrld acc)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp wrld))))
  (cond ((endp fns) acc)
        (t (event-names-to-book-alist
            (cdr fns) current-book wrld
            (acons (car fns)
                   (event-source (car fns) current-book wrld)
                   acc)))))

(defun runes-and-symbols-to-symbols (lst acc)
  (cond ((endp lst) acc)
        (t (runes-and-symbols-to-symbols
            (cdr lst)
            (cons (let ((x (car lst)))
                    (cond ((symbolp x) x)
                          ((keywordp (car x))
                           (cadr x))
                          (t (assert$ ; (foo) for (:e foo)
                              (and (consp x)
                                   (null (cdr x))
                                   (symbolp (car x)))
                              (car x)))))
                  acc)))))

(defun in-theory-hint-setting-symbols (uval acc)

; As noted above, we gather only low-hanging fruit here.

  (cond ((symbolp uval) ; presumably a constant
         (cons uval acc))
        ((atom uval) ; impossible?
         acc)
        ((member-eq (car uval) '(enable disable enable* disable*))
         (runes-and-symbols-to-symbols (cdr uval) acc))
        ((member-eq (car uval) '(e/d e/d*))
         (runes-and-symbols-to-symbols
          (cadr uval)
          (runes-and-symbols-to-symbols (caddr uval) acc)))
        ((quotep uval)
         (runes-and-symbols-to-symbols (cadr uval) acc))
        ((eq (car uval) 'theory)
         (assert$ (consp (cdr uval))
                  (cond ((quotep (cadr uval))
                         (let ((sym (unquote (cadr uval))))
                           (if (symbolp sym) ; always true?
                               (cons sym acc)
                             acc)))
                        ((symbolp (cadr uval)) ; must be a defined constant
                         (cons (cadr uval) acc))
                        (t acc))))
        ((member-eq (car uval)
                    '(set-difference-theories
                      union-theories
                      intersection-theories))

; This doesn't include function symbols called in the theory expression.  We'd
; have to translate uval to get those.  Note that the translated in-theory hint
; is just a list of runes.

         (runes-and-symbols-to-symbols
          (and (quotep (cadr uval)) (unquote (cadr uval)))
          (runes-and-symbols-to-symbols
           (and (quotep (caddr uval)) (unquote (caddr uval)))
           acc)))
        (t acc)))

(defun lmi-symbol (lmi wrld acc)

; Lmi is an untranslated lemma-instance (as provided to translate-lmi, or see
; :DOC lemma-instance).  Note: At this point we only include the lmi names,
; ignoring substitutions and theorems.

  (cond ((atom lmi)
         (assert$ (symbolp lmi)
                   (cons lmi acc)))
        (t (case (car lmi)
             ((:guard-theorem :termination-theorem :termination-theorem!)
              (cons (cadr lmi) acc))
             (:theorem nil) ; would need translated value
             ((:instance :functional-instance)
              (lmi-symbol (cadr lmi) wrld acc))
             (t ; rune
              (assert$ (runep lmi wrld)
                       (cons (base-symbol lmi) acc)))))))

(defun lmi-lst-symbols (uval wrld acc)
  (cond ((endp uval) acc)
        (t (lmi-lst-symbols (cdr uval)
                            wrld
                            (lmi-symbol (car uval) wrld acc)))))

(defun expand-lst-symbols (expand-hint-lst acc)
  (cond ((endp expand-hint-lst) acc)
        (t (expand-lst-symbols
            (cdr expand-hint-lst)
            (if (eq (car expand-hint-lst) :lambdas)
                acc
              (all-ffn-symbs (access expand-hint (car expand-hint-lst)
                                     :pattern)
                             acc))))))

(defun hands-off-symbols (lst acc)
  (cond ((endp lst) acc)
        (t (hands-off-symbols
            (cdr lst)
            (let ((fn (car lst)))
              (if (symbolp fn)
                  (cons fn acc)
                (all-ffn-symbs (lambda-body fn) acc)))))))

(defun hint-settings-symbols (uhint-settings thint-settings wrld acc)

; It's OK if the result has duplicates.

  (cond
   ((endp uhint-settings)
    (assert$ (null thint-settings)
             acc))
   (t
    (assert$
     (and (consp thint-settings)
          (consp (car thint-settings))
          (eq (car uhint-settings)
              (caar thint-settings)))
     (let ((syms
            (let ((kwd (car uhint-settings))
                  (uval (cadr uhint-settings))
                  (tval (cdar thint-settings)))
              (case kwd
                (:in-theory (in-theory-hint-setting-symbols uval acc))
                (:use (lmi-lst-symbols
; See translate-use-hint.
                       (cond ((atom uval) (list uval))
                             ((or (member-eq (car uval)
                                             '(:instance
                                               :functional-instance
                                               :theorem
                                               :termination-theorem
                                               :termination-theorem!
                                               :guard-theorem))
                                  (runep uval wrld))
                              (list uval))
                             (t uval))
                       wrld
                       acc))
                (:by (lmi-symbol uval wrld acc))
                (:expand (expand-lst-symbols tval acc))
                (:restrict (strip-cars uval))
                (:hands-off (hands-off-symbols tval acc))
                (:induct (all-ffn-symbs tval acc))
                (:clause-processor (all-ffn-symbs (access clause-processor-hint
                                                          tval
                                                          :term)
                                                  acc))
                (:cases (all-ffn-symbs-lst tval acc))
                (t nil)))))
       (hint-settings-symbols
        (cddr uhint-settings) (cdr thint-settings) wrld
        (append syms acc)))))))

(defun hints-symbols (uhints thints wrld)

; Since we only remove "Goal" hint-settings, we only collect symbols from
; "Goal" hint-settings.

  (let* ((thint-settings
          (cdr (assoc-equal *initial-clause-id* thints)))
         (uhint-settings
          (and thint-settings
               (alistp uhints)
               (cdr (assoc-string-equal "goal" uhints)))))
    (and uhint-settings
         (keyword-value-listp uhint-settings)
         (rmh-keys-equal uhint-settings thint-settings)
         (hint-settings-symbols uhint-settings thint-settings wrld
                                nil))))

(defun defthm-symbol-table (term rune-alist uhints thints wrld state)

; Warning: This function should only be called when a book is under
; certification.  (See the assert$ call below.)

; This doesn't include rule-classes, because I don't think the effort to find
; symbols in corollaries (and other places?) is sufficiently relevant to the
; intended application.

  (declare (xargs :stobjs state))
  (let* ((info (f-get-global 'certify-book-info state))
         (current-book
          (assert$
           info
           (access certify-book-info info :full-book-name)))
         (term-symbols (all-fnnames term)) ; no duplicates
         (rune-alist-symbols (strip-base-symbols (strip-cars rune-alist)))
         (hints-symbols (hints-symbols uhints thints wrld))
         (symbols (strict-merge-symbol<
                   (merge-sort-symbol< term-symbols)
                   (strict-merge-symbol<
                    (strict-merge-sort-symbol< rune-alist-symbols)
                    (strict-merge-sort-symbol< hints-symbols)
                    nil)
                   nil)))
    (event-names-to-book-alist symbols current-book wrld nil)))
