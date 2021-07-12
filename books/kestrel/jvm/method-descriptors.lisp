; Utilities dealing with method descriptors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; Utilities dealing with method-descriptors

(include-book "descriptors")
(local (include-book "kestrel/utilities/mv-nth" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

;;;
;;; parse-descriptors-from-front
;;;

;; Parse as many complete descriptors as possible from the front of chars.
;; Returns (mv parsed-descriptors remaining-chars).
(defund parse-descriptors-from-front (chars)
  (declare (xargs :guard (character-listp chars)
                  :measure (len chars)))
  (mv-let (parsed-descriptor remaining-chars)
    (parse-descriptor-from-front chars)
    (if (not parsed-descriptor)
        (mv nil chars)
      (mv-let (parsed-descriptors remaining-chars)
        (parse-descriptors-from-front remaining-chars)
        (mv (cons parsed-descriptor parsed-descriptors)
            remaining-chars)))))

(defthm character-listp-of-mv-nth-1-of-parse-descriptors-from-front
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-descriptors-from-front chars))))
  :hints (("Goal" :in-theory (enable parse-descriptors-from-front SKIP-DESCRIPTOR-AT-FRONT))))

(defthm all-typep-of-mv-nth-0-of-parse-descriptors-from-front
  (all-typep (mv-nth 0 (parse-descriptors-from-front chars)))
  :hints (("Goal" :in-theory (enable parse-descriptors-from-front))))

(defthm true-listp-of-mv-nth-0-of-parse-descriptors-from-front
  (true-listp (mv-nth 0 (parse-descriptors-from-front chars)))
  :hints (("Goal" :in-theory (enable parse-descriptors-from-front))))

;;;
;;; skip-descriptors-at-front
;;;

;; Skip as many complete descriptors as possible at the front of chars.
;; Returns the remaining-chars.
(defund skip-descriptors-at-front (chars)
  (declare (xargs :guard (character-listp chars)
                  :measure (len chars)
                  :hints (("Goal" :in-theory (enable skip-descriptor-at-front)))))
  (mv-let (starts-with-descriptorp remaining-chars)
    (skip-descriptor-at-front chars)
    (if (not starts-with-descriptorp)
        chars
      (skip-descriptors-at-front remaining-chars))))

(defthm character-listp-of-skip-descriptors-at-front
  (implies (character-listp chars)
           (character-listp (skip-descriptors-at-front chars)))
  :hints (("Goal" :in-theory (enable skip-descriptors-at-front))))

(local
 (defthm skip-descriptors-at-front-correct
   (equal (skip-descriptors-at-front chars)
          (mv-nth 1 (parse-descriptors-from-front chars)))
   :hints (("Goal" :in-theory (enable skip-descriptors-at-front
                                      parse-descriptors-from-front
                                      skip-descriptor-at-front-correct-1
                                      skip-descriptor-at-front-correct-2)))))


;;;
;;; parse-return-type-from-front
;;;

;; Returns (mv parsed-return-type chars) where parsed-return-type is nil if we
;; could not parse a return type from the front of CHARS.
(defund parse-return-type-from-front (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (equal (first chars) #\V)
      (mv :void (rest chars))
    (parse-descriptor-from-front chars)))

(defthm return-typep-of-mv-nth-0-parse-return-type-from-front
  (iff (return-typep (mv-nth 0 (parse-return-type-from-front chars)))
       (mv-nth 0 (parse-return-type-from-front chars)))
  :hints (("Goal" :in-theory (enable parse-return-type-from-front
                                     return-typep))))

;;;
;;; skip-return-type-at-front
;;;

;; Returns (mv foundp remaining-chars).
(defund skip-return-type-at-front (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (equal (first chars) #\V)
      (mv t (rest chars))
    (skip-descriptor-at-front chars)))

(defthm character-listp-of-mv-nth-1-of-skip-return-type-at-front
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (skip-return-type-at-front chars))))
  :hints (("Goal" :in-theory (enable skip-return-type-at-front))))

;dups
(defconst *right-paren* #\))
(defconst *left-paren* #\()

;;;
;;; parse-method-descriptor-from-front
;;;

;; Returns (mv foundp param-types return-type remaining-chars).  Example: (B[[IBB)V.
(defund parse-method-descriptor-from-front (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (not (and (consp chars)
                (eql (first chars) *left-paren*)))
      (mv nil nil nil chars)
    (mv-let (parsed-param-descriptors remaining-chars)
      (parse-descriptors-from-front (rest chars)) ;skip the left paren
      (if (not (and (consp remaining-chars)
                    (eql (first remaining-chars) *right-paren*)))
          (mv nil parsed-param-descriptors nil chars)
        (mv-let (parsed-return-type remaining-chars)
          (parse-return-type-from-front (rest remaining-chars)) ;skip the right paren
          (if parsed-return-type
              (mv t parsed-param-descriptors parsed-return-type remaining-chars)
            (mv nil parsed-param-descriptors nil chars)))))))

(defthm all-typep-of-mv-nth-1-of-parse-method-descriptor-from-front
  (implies (mv-nth 0 (parse-method-descriptor-from-front chars))
           (all-typep (mv-nth 1 (parse-method-descriptor-from-front chars))))
  :hints (("Goal" :in-theory (enable parse-method-descriptor-from-front))))

(defthm true-listp-of-mv-nth-1-of-parse-method-descriptor-from-front
  (implies (mv-nth 0 (parse-method-descriptor-from-front chars))
           (true-listp (mv-nth 1 (parse-method-descriptor-from-front chars))))
  :hints (("Goal" :in-theory (enable parse-method-descriptor-from-front))))

(defthm return-typep-of-mv-nth-2-of-parse-method-descriptor-from-front
  (implies (mv-nth 0 (parse-method-descriptor-from-front chars))
           (return-typep (mv-nth 2 (parse-method-descriptor-from-front chars))))
  :hints (("Goal" :in-theory (enable parse-method-descriptor-from-front))))

;;;
;;; skip-method-descriptor-at-front
;;;

;; Returns (mv foundp remaining-chars).  Example: (B[[IBB)V.
(defund skip-method-descriptor-at-front (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (not (and (consp chars)
                (eql (first chars) *left-paren*)))
      (mv nil chars)
    (let ((remaining-chars (skip-descriptors-at-front (rest chars)))) ;skip the paren
      (if (not (and (consp remaining-chars)
                    (eql (first remaining-chars) *right-paren*)))
          (mv nil chars)
        (mv-let (foundp remaining-chars)
          (skip-return-type-at-front (rest remaining-chars)) ;skip the paren
          (if foundp
              (mv t remaining-chars)
            (mv nil chars)))))))

;;;
;;; parse-method-descriptor-chars
;;;

;; Returns (mv erp param-types return-type).  ERP is non-nil if CHARS is not an encoded method descriptor.
(defund parse-method-descriptor-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (foundp param-types return-type remaining-chars)
    (parse-method-descriptor-from-front chars)
    (if (not foundp)
        ;; error:
        (mv (list "Failed to parse a method-descriptor from." chars) param-types return-type)
      (if (consp remaining-chars)
          ;; error:
          (mv (list "Extra chars found after method-descriptor." chars) param-types return-type)
        (mv nil ;no error
            param-types return-type)))))

(defthm all-typep-of-mv-nth-1-of-parse-method-descriptor-chars
  (implies (not (mv-nth 0 (parse-method-descriptor-chars chars)))
           (all-typep (mv-nth 1 (parse-method-descriptor-chars chars))))
  :hints (("Goal" :in-theory (enable parse-method-descriptor-chars))))

(defthm true-listp-of-mv-nth-1-of-parse-method-descriptor-chars
  (implies (not (mv-nth 0 (parse-method-descriptor-chars chars)))
           (true-listp (mv-nth 1 (parse-method-descriptor-chars chars))))
  :hints (("Goal" :in-theory (enable parse-method-descriptor-chars))))

(defthm return-typep-of-mv-nth-2-of-parse-method-descriptor-chars
  (implies (not (mv-nth 0 (parse-method-descriptor-chars chars)))
           (return-typep (mv-nth 2 (parse-method-descriptor-chars chars))))
  :hints (("Goal" :in-theory (enable parse-method-descriptor-chars))))


;;;
;;; parse-method-descriptor
;;;

;; Returns (mv erp param-types return-type).  Throws an error if STR is not a method descriptor.
(defund parse-method-descriptor (str)
  (declare (xargs :guard (stringp str)))
  (parse-method-descriptor-chars (coerce str 'list)))

(defthm true-listp-of-mv-nth-1-parse-method-descriptor
  (implies (not (mv-nth 0 (parse-method-descriptor str)))
           (true-listp (mv-nth 1 (parse-method-descriptor str))))
  :hints (("Goal" :in-theory (enable parse-method-descriptor))))

(defthm all-typep-of-mv-nth-1-parse-method-descriptor
  (implies (not (mv-nth 0 (parse-method-descriptor str)))
           (all-typep (mv-nth 1 (parse-method-descriptor str))))
  :hints (("Goal" :in-theory (enable parse-method-descriptor))))

(defthm return-typep-of-mv-nth-2-parse-method-descriptor
  (implies (not (mv-nth 0 (parse-method-descriptor str)))
           (return-typep (mv-nth 2 (parse-method-descriptor str))))
  :hints (("Goal" :in-theory (enable parse-method-descriptor))))

;(parse-method-descriptor "()V")

;;;
;;; method-descriptor-charsp
;;;

;; Check whether CHARS represents a single method-descriptor.
(defun method-descriptor-charsp (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (starts-with-method-descriptorp remaining-chars)
    (skip-method-descriptor-at-front chars)
    (and starts-with-method-descriptorp
         (not (consp remaining-chars)))))

;;;
;;; is-method-descriptorp
;;;

;; Check whether STR represents a single method-descriptor
(defun is-method-descriptorp (str)
  (declare (xargs :guard (stringp str)))
  (method-descriptor-charsp (coerce str 'list)))

;;;
;;; method-descriptorp
;;;

;; Recognize a single method-descriptor
(defund method-descriptorp (desc)
  (declare (xargs :guard t))
  (and (stringp desc)
       (is-method-descriptorp desc)))

;;;
;;; param-types-from-method-descriptor
;;;

;; Returns a list of typeps. Can throw an error.  We could just call
;; parse-method-descriptor but that would waste time parsing the return type.
(defund param-types-from-method-descriptor (descriptor)
  (declare (xargs :guard (stringp descriptor)))
  (let ((chars (coerce descriptor 'list)))
    (if (not (and (consp chars)
                  (eql (first chars) *left-paren*)))
        (prog2$ (er hard? 'param-types-from-method-descriptor "Failed to parse a method-descriptor from ~x0." descriptor)
                nil ;; empty list of descriptors
                )
      (mv-let (parsed-descriptors remaining-chars)
        (parse-descriptors-from-front (rest chars)) ;skip the left-paren
        (declare (ignore remaining-chars))
        parsed-descriptors))))

(local (in-theory (disable mv-nth)))

(local
 (defthm param-types-from-method-descriptor-correct
   (equal (param-types-from-method-descriptor descriptor)
          (mv-nth 1 (parse-method-descriptor descriptor)))
   :hints (("Goal" :in-theory (enable param-types-from-method-descriptor
                                      parse-method-descriptor
                                      parse-method-descriptor-chars
                                      parse-method-descriptor-from-front)))))

;;;
;;; return-type-from-method-descriptor
;;;

;; Returns a typep or :void.  Can throw an error.  We could just call
;; parse-method-descriptor but that would waste time parsing the param types.
(defund return-type-from-method-descriptor (descriptor)
  (declare (xargs :guard (stringp descriptor)))
  (let ((chars (coerce descriptor 'list)))
    (if (not (and (consp chars)
                  (eql (first chars) *left-paren*)))
        (prog2$ (er hard? 'return-type-from-method-descriptor "Failed to parse a method-descriptor from ~x0." descriptor)
                nil ;; match what parse-method-descriptor returns
                )
      (let ((remaining-chars (skip-descriptors-at-front (rest chars)))) ;skip the left paren
        (if (not (and (consp remaining-chars)
                      (eql (first remaining-chars) *right-paren*)))
            nil ;; match what parse-method-descriptor returns
          (mv-let (parsed-return-type remaining-chars)
            (parse-return-type-from-front (rest remaining-chars)) ;skip the right paren
            (declare (ignore remaining-chars))
            parsed-return-type))))))


(local
 (defthm return-type-from-method-descriptor-correct
   (equal (return-type-from-method-descriptor descriptor)
          (mv-nth 2 (parse-method-descriptor descriptor)))
   :hints (("Goal" :in-theory (enable return-type-from-method-descriptor
                                      parse-method-descriptor
                                      parse-method-descriptor-chars
                                      parse-method-descriptor-from-front)))))
