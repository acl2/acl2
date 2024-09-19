; Utilites about runes (rule names)
;
; Copyright (C) 2014-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

(include-book "system/pseudo-good-worldp" :dir :system) ;for pseudo-runep

(defconst *fake-rule-classes*
  (strip-cars *fake-rune-alist*))

;filter out fake runes like (:FAKE-RUNE-FOR-TYPE-SET NIL)
(defun drop-fake-runes (runes)
  (declare (xargs :guard t ;;(pseudo-or-fake-rune-listp runes)
                  ))
  (if (atom runes)
      nil
    (let ((rune (first runes)))
      (if (and (consp rune)
               (member-eq (first rune) *fake-rule-classes*))
          (drop-fake-runes (rest runes))
        (cons rune (drop-fake-runes (rest runes)))))))

;; TODO: Are there any more?
(defconst *non-fake-rule-classes*
  '(:executable-counterpart
    :rewrite
    :built-in-clause
    :clause-processor
    :compound-recognizer
    :congruence
    :definition
    :elim
    :equivalence
    :forward-chaining
    :generalize
    :induction
    :linear
    :meta
    :refinement
    :tau-system
    :type-prescription
    :type-set-inverter
    :well-founded-relation))

;; Unlike runep, this does not take wrld.  This recognizes "fake" runes.
(defun fake-runep (rune)
  (declare (xargs :guard t))
  (and (consp rune)
       (member-eq (car rune) *fake-rule-classes*)
       (consp (cdr rune))
       (null (cadr rune)) ; the second arg must always be nil (see the Essay on Fake Runes)
       (null (cdr (cdr rune)))))

(defun pseudo-or-fake-runep (rune)
  (declare (xargs :guard t))
  (or (pseudo-runep rune)
      (fake-runep rune)))

(defun pseudo-or-fake-rune-listp (runes)
  (declare (xargs :guard t))
  (if (not (consp runes))
      (null runes)
    (and (pseudo-or-fake-runep (first runes))
         (pseudo-or-fake-rune-listp (rest runes)))))
