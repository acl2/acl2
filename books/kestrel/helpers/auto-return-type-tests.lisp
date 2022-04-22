; Tests for auto-return-type
;
; Copyright (C) 2020-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "auto-return-type")
(include-book "kestrel/utilities/deftest" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example where one branch returns a param, so the tool guesses that the
;; return type of the function is the same as the param:
(deftest
  (defund skip-json-whitespace (chars)
    (declare (xargs :guard (character-listp chars)))
    (if (endp chars)
        nil
      (if (member (first chars) '(#\tab #\newline #\return #\space))
          (skip-json-whitespace (rest chars))
        chars)))

  (submit-auto-return-type skip-json-whitespace)

  ;; Expected result:
  (must-be-redundant
   (defthm character-listp-of-skip-json-whitespace
     (implies (character-listp chars)
              (character-listp (skip-json-whitespace chars)))
     :hints (("Goal" :in-theory (enable skip-json-whitespace))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example where in one branch the function conses the car of a formal onto
;; something, so the tool guesses that the return type is the type of that
;; formal:
;; TODO: Try this but with an intervening LET.
(deftest
  (defun filter-evens (nats)
    (declare (xargs :guard (nat-listp nats)))
    (if (endp nats)
        nil
      (if (evenp (first nats))
          (cons (first nats) (filter-evens (rest nats)))
        (filter-evens (rest nats)))))

  (submit-auto-return-type filter-evens)

  ;; Expected result:
  (must-be-redundant
   (defthm nat-listp-of-filter-evens
     (implies (nat-listp nats)
              (nat-listp (filter-evens nats)))
     :hints (("Goal" :in-theory (enable filter-evens))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ;; Example where in one branch the function returns the car of a formal, so
;; ;; the tool guesses that the return type is a list of the type of that
;; ;; formal:
;; ;; TODO: Get this to work, but note that the function can return nil.
;; (deftest
;;   (defun find-even (nats)
;;     (declare (xargs :guard (nat-listp nats)))
;;     (if (endp nats)
;;         nil
;;       (if (evenp (first nats))
;;           (first nats)
;;         (find-even (rest nats)))))

;;   (submit-auto-return-type find-even)

;;   ;; Expected result:
;;   (must-be-redundant
;;    ...
;;      :hints (("Goal" :in-theory (enable filter-evens))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Example where in one branch the function returns the car of a formal.
;; Variant of the above where the base case is a nat, so the return type
;; is unconditional.
(deftest
  (defun find-even (nats)
    (declare (xargs :guard (nat-listp nats)))
    (if (endp nats)
        0
      (if (evenp (first nats))
          (first nats)
        (find-even (rest nats)))))

  (submit-auto-return-type find-even)

  ;; Expected result:
  (must-be-redundant
   (DEFTHM NATP-OF-FIND-EVEN
     (IMPLIES (NAT-LISTP NATS)
              (NATP (FIND-EVEN NATS)))
     :HINTS (("Goal" :IN-THEORY (ENABLE FIND-EVEN))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test the variant that does not submit the generated theorems:
(deftest
  (defund skip-json-whitespace (chars)
    (declare (xargs :guard (character-listp chars)))
    (if (endp chars)
        nil
      (if (member (first chars) '(#\tab #\newline #\return #\space))
          (skip-json-whitespace (rest chars))
        chars)))

  (assert!-stobj (mv-let (erp res state)
                   (auto-return-type skip-json-whitespace)
                   (mv (and (eq (erp-nil) erp)
                            (equal res
                                   '(progn (defthm character-listp-of-skip-json-whitespace
                                             (implies (character-listp chars)
                                                      (character-listp (skip-json-whitespace chars)))
                                             :hints (("Goal" :in-theory (enable skip-json-whitespace)))))))
                       state))
                 state))

(deftest
  ;; without the suffix, the theorem is redundant (built into the tool)
  (submit-auto-return-type extract-branches :suffix test)

  ;; Expected result:
  (must-be-redundant
   (defthm pseudo-term-listp-of-extract-branches-test
     (implies (pseudo-termp term)
              (pseudo-term-listp (extract-branches term)))
     :hints (("Goal" :in-theory (enable extract-branches))))))

(deftest
  ;; without the suffix, the theorem is redundant (built into the tool)
  (submit-auto-return-type remove-calls-to :suffix test)

  ;; Expected result:
  (must-be-redundant
   (defthm pseudo-term-listp-of-remove-calls-to-test
     (implies (pseudo-term-listp terms)
              (pseudo-term-listp (remove-calls-to fn terms)))
     :hints (("Goal" :in-theory (enable remove-calls-to))))))

(deftest
  ;; without the suffix, the theorem is redundant (built into the tool)
  (submit-auto-return-type guard-conjunct-for-formal :suffix test)

  ;; Expected result:
  (must-be-redundant
   (defthm pseudo-termp-of-guard-conjunct-for-formal-test
     (implies (pseudo-term-listp guard-conjuncts)
              (pseudo-termp (guard-conjunct-for-formal guard-conjuncts formal)))
     :hints (("Goal" :in-theory (enable guard-conjunct-for-formal))))))


(deftest
  ;; without the suffix, the theorem is redundant (built into the tool)
  (submit-auto-return-type get-conjuncts :suffix test)

  ;; Expected result:
  (must-be-redundant
   (defthm pseudo-term-listp-of-get-conjuncts-test
     (implies (pseudo-termp term)
              (pseudo-term-listp (get-conjuncts term)))
     :hints (("Goal" :in-theory (enable get-conjuncts))))))


;;todo:
;; (submit-auto-return-type get-conjuncts-list) -- need to notice that we are appending onto a recursive call, so look for the type of the thing being appended
