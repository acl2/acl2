(in-package "ACL2")

(include-book "system/pseudo-good-worldp" :dir :system) ;for pseudo-runep

;; TODO: Are there any more?
(defconst *fake-rule-classes*
  '(:fake-rune-for-type-set
    :fake-rune-for-linear))

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

;; Unlike runep, this does not take wrld.  This includes "fake" runes.
(defun fake-runep (rune)
  (declare (xargs :guard t))
  (and (consp rune)
       (member-eq (car rune) *fake-rule-classes*)
       (consp (cdr rune))
       (null (cadr rune)) ; the second arg must always be nil?
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

;filter out fake runes like (:FAKE-RUNE-FOR-TYPE-SET NIL)
(defun drop-fake-runes (runes)
  (declare (xargs :guard (pseudo-or-fake-rune-listp runes)))
  (if (endp runes)
      nil
    (let ((rune (first runes)))
      (if (member-eq (first rune) *non-fake-rule-classes*)
          (cons rune (drop-fake-runes (rest runes)))
        (drop-fake-runes (rest runes))))))
