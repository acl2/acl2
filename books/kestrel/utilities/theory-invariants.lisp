; Utilities related to theory-invariants
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; Extends ACC with a list of all the names declared to be incompatible with any of the RUNES.
;; NOTE: This only deals with theory-invariants defined using INCOMPATIBLE.
(defund runes-incompatible-with-runes (runes theory-invariant-table-alist acc)
  (declare (xargs :guard (and (true-listp runes)
                              (alistp theory-invariant-table-alist))))
  (if (endp theory-invariant-table-alist)
      acc
    (let* ((entry (first theory-invariant-table-alist))
           (inv-rec (cdr entry)))
      (if (not (weak-theory-invariant-record-p inv-rec))
          (er hard? 'runes-incompatible-with-runes "Ill-formed theory invariant record: ~x0.")
        (let ((form (access theory-invariant-record inv-rec :untrans-term)))
          (if (and (true-listp form)
                   (consp form)
                   (eq 'incompatible (car form))
                   (equal 3 (len form)))
              ;; form is (incompatible rune1 rune2).  If rune1 is among the runes,
              ;; and rune2 as incompatible, and vice versa.
              (runes-incompatible-with-runes runes
                                             (rest theory-invariant-table-alist)
                                             (append
                                              (if (member-equal (cadr form) runes)
                                                  (list (caddr form))
                                                nil)
                                              (if (member-equal (caddr form) runes)
                                                  (list (cadr form))
                                                nil)
                                              acc))
            ;; TODO: Add support for other cases:
            (runes-incompatible-with-runes runes (rest theory-invariant-table-alist)
                                           acc)))))))

;; Returns a list of all the names declared to be incompatible with NAME-OR-RUNE.
;; NOTE: This only deals with theory-invariants defined using INCOMPATIBLE.
(defund incompatible-runes (name-or-rune wrld)
  (declare (xargs :guard (and (plist-worldp wrld)
                              (or (and (symbolp name-or-rune)
                                       (alistp (fgetprop name-or-rune
                                                         'runic-mapping-pairs
                                                         nil wrld)))
                                  (consp name-or-rune))
                              (alistp (fgetprop 'theory-invariant-table
                                                'table-alist
                                                nil wrld)))))
  (let ((runes (if (consp name-or-rune) ; checks if it is a rune
                   (list name-or-rune)
                 ;; it's a symbol:
                 (strip-cdrs (fgetprop name-or-rune 'runic-mapping-pairs nil wrld)))))
    (if (not runes)
        (er hard? 'incompatible-runes "Can't find any runes for ~x0." name-or-rune)
      (runes-incompatible-with-runes runes (table-alist 'theory-invariant-table wrld) nil))))

;; Extends ACC with a list of all the names declared to be incompatible with any of the names-or-runes.
;; NOTE: This only deals with theory-invariants actually defined using INCOMPATIBLE.
(defund incompatible-runes-lst-aux (names-or-runes wrld acc)
  (declare (xargs :guard (and (true-listp names-or-runes)
                              (plist-worldp wrld)
                              (alistp (fgetprop 'theory-invariant-table
                                                'table-alist
                                                nil wrld)))))
  (if (endp names-or-runes)
      acc
    (let ((name-or-rune (first names-or-runes)))
      (if ;; for guards:
          (not (or (and (symbolp name-or-rune)
                        (alistp (fgetprop name-or-rune
                                          'runic-mapping-pairs
                                          nil wrld)))
                   (consp name-or-rune)))
          (er hard? 'incompatible-runes-lst-aux "Bad name or rune: ~x0.")
        (incompatible-runes-lst-aux (rest names-or-runes) wrld (incompatible-runes name-or-rune wrld))))))

;; Returns a list of all the names declared to be incompatible with any of the NAMES-OR-RUNES.
;; NOTE: This only deals with theory-invariants actually defined using INCOMPATIBLE.
(defund incompatible-runes-lst (names-or-runes wrld)
  (declare (xargs :guard (and (true-listp names-or-runes)
                              (plist-worldp wrld)
                              ;; todo: consider strengthening this, using the table guard from "(table theory-invariant-table nil nil" in other-events.lisp
                              (alistp (fgetprop 'theory-invariant-table
                                                'table-alist
                                                nil wrld)))))
  (incompatible-runes-lst-aux names-or-runes wrld nil))
