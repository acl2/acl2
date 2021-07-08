; Utilities dealing with (field) descriptors
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; Utilities dealing with descriptors, which are strings representing the
;; types of fields, method params, etc, (JVM spec, section 4.3).

;; TODO: Rename to field-descriptors.lisp?

(include-book "types") ;  because parsing a descriptor yields a type
(local (include-book "kestrel/utilities/mv-nth" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

;dup
(defund turn-slashes-into-dots-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (substitute #\. #\/ chars))

;dup
(defthm character-listp-of-turn-slashes-into-dots-chars
  (implies (character-listp chars)
           (character-listp (turn-slashes-into-dots-chars chars)))
  :hints (("Goal" :in-theory (enable turn-slashes-into-dots-chars))))

;;;
;;; read-chars-through-terminator
;;;

;; Search the CHARS for the TERMINATOR, returning the chars-before-terminator and the rest of the chars (not including the terminator).
;; Returns (mv foundp chars-before-terminator rest-chars) where if the TERMINATOR does not appear, foundp=nil and rest-chars=chars.
(defund read-chars-through-terminator (chars terminator)
  (declare (xargs :measure (len chars)
                  :guard (and (character-listp chars)
                              (characterp terminator))))
  (if (endp chars)
      (mv nil nil chars)
    (if (eql (first chars) terminator)
        (mv t nil (rest chars)) ;return the empty char list and consume the terminator
      (mv-let (foundp chars-before-terminator rest-chars)
        (read-chars-through-terminator (rest chars) terminator)
        (if foundp
            (mv t (cons (first chars) chars-before-terminator) rest-chars)
          (mv nil nil chars))))))

(defthm character-listp-of-mv-nth-1-of-read-chars-through-terminator
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (read-chars-through-terminator chars terminator))))
  :hints (("Goal" :in-theory (enable read-chars-through-terminator))))

(defthm character-listp-of-mv-nth-2-of-read-chars-through-terminator
  (implies (character-listp chars)
           (character-listp (mv-nth 2 (read-chars-through-terminator chars terminator))))
  :hints (("Goal" :in-theory (enable read-chars-through-terminator))))

(defthm <-of-len-of-mv-nth-2-of-read-chars-through-terminator
  (implies (mv-nth 0 (read-chars-through-terminator chars terminator))
           (< (len (mv-nth 2 (read-chars-through-terminator chars terminator)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable read-chars-through-terminator))))

;;;
;;; skip-chars-through-terminator
;;;

;; Returns (mv foundp rest-chars) where if the terminator does not appear, foundp=nil and rest-chars=chars.
;; This is like read-chars-through-terminator except we don't bother to return the chars before the terminator.
(defund skip-chars-through-terminator (chars terminator)
  (declare (xargs :measure (len chars)
                  :guard (and (character-listp chars)
                              (characterp terminator))))
  (if (endp chars)
      (mv nil chars)
    (if (eql (first chars) terminator)
        (mv t (rest chars)) ;return the empty char list and consume the terminator
      (mv-let (foundp rest-chars)
        (skip-chars-through-terminator (rest chars) terminator)
        (if foundp
            (mv t rest-chars)
          (mv nil chars))))))

(defthm character-listp-of-mv-nth-1-of-skip-chars-through-terminator
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (skip-chars-through-terminator chars terminator))))
  :hints (("Goal" :in-theory (enable skip-chars-through-terminator))))

(defthmd skip-chars-through-terminator-correct-1
  (equal (mv-nth 0 (skip-chars-through-terminator chars terminator))
         (mv-nth 0 (read-chars-through-terminator chars terminator)))
  :hints (("Goal" :in-theory (enable skip-chars-through-terminator
                                     read-chars-through-terminator))))

(defthmd skip-chars-through-terminator-correct-2
  (equal (mv-nth 1 (skip-chars-through-terminator chars terminator))
         (mv-nth 2 (read-chars-through-terminator chars terminator)))
  :hints (("Goal" :in-theory (enable skip-chars-through-terminator
                                     read-chars-through-terminator
                                     skip-chars-through-terminator-correct-1))))

(defthm <-of-len-of-mv-nth-1-of-skip-chars-through-terminator
  (implies (mv-nth 0 (skip-chars-through-terminator chars terminator))
           (< (len (mv-nth 1 (skip-chars-through-terminator chars terminator)))
              (len chars)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable skip-chars-through-terminator))))

;;;
;;; parse-descriptor-from-front
;;;

;; Returns (mv parsed-descriptor remaining-chars) where parsed-descriptor is nil
;; if the CHARS do not start with the parsed reprentation of a descriptor (in
;; that case, the REMAINING-CHARS returned are equal to CHARS).
(defund parse-descriptor-from-front (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      (mv nil chars)
    (let* ((firstchar (first chars)))
      (if (eql firstchar #\B)
          (mv :byte (rest chars))
        (if (eql firstchar #\C)
            (mv :char (rest chars))
          (if (eql firstchar #\D)
              (mv :double (rest chars))
            (if (eql firstchar #\F)
                (mv :float (rest chars))
              (if (eql firstchar #\I)
                  (mv :int (rest chars))
                (if (eql firstchar #\J)
                    (mv :long (rest chars))
                  (if (eql firstchar #\S)
                      (mv :short (rest chars))
                    (if (eql firstchar #\Z)
                        (mv :boolean (rest chars))
                      (if (eql firstchar #\[) ;; an array
                          (mv-let (rest-descriptor remaining-chars)
                            (parse-descriptor-from-front (rest chars))
                            (if rest-descriptor
                                (mv (list :array rest-descriptor)
                                    remaining-chars)
                              (mv nil chars)))
                        (if (eql firstchar #\L)
                            (mv-let (foundp classname-chars remaining-chars)
                              (read-chars-through-terminator (rest chars) #\;)
                              (if foundp
                                  (mv (coerce (turn-slashes-into-dots-chars classname-chars) 'string)
                                      remaining-chars)
                                (mv nil chars)))
                          (mv nil chars))))))))))))))

(defthm typep-of-mv-nth-0-of-parse-descriptor-from-front
  (implies (mv-nth 0 (parse-descriptor-from-front chars))
           (typep (mv-nth 0 (parse-descriptor-from-front chars))))
  :hints (("Goal" :in-theory (enable parse-descriptor-from-front typep))))

(defthm character-listp-of-mv-nth-1-of-parse-descriptor-from-front
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-descriptor-from-front chars))))
  :hints (("Goal" :in-theory (enable parse-descriptor-from-front))))

(defthm <-of-len-of-mv-nth-1-of-parse-descriptor-from-front
  (implies (mv-nth 0 (parse-descriptor-from-front chars))
           (< (len (mv-nth 1 (parse-descriptor-from-front chars)))
              (len chars)))
  :hints (("Goal" :in-theory (enable parse-descriptor-from-front))))

;;;
;;; skip-descriptor-at-front
;;;

;; Returns (mv starts-with-descriptorp remaining-chars)
(defund skip-descriptor-at-front (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (not (consp chars))
      (mv nil chars)
    (let ((firstchar (first chars)))
      (if (member firstchar '(#\B #\C #\D #\F #\I #\J #\S #\Z))
          (mv t (rest chars))
        (if (eql firstchar #\[)
            (mv-let (rest-starts-with-descriptorp remaining-chars)
              (skip-descriptor-at-front (rest chars))
              (if rest-starts-with-descriptorp
                  (mv t remaining-chars)
                (mv nil chars)))
          (if (eql firstchar #\L)
              (mv-let (foundp remaining-chars)
                (skip-chars-through-terminator (rest chars) #\;)
                (if foundp
                    (mv t remaining-chars)
                  (mv nil chars)))
            (mv nil chars)))))))

(defthm character-listp-of-mv-nth-1-of-skip-descriptor-at-front
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (skip-descriptor-at-front chars))))
  :hints (("Goal" :in-theory (enable skip-descriptor-at-front))))

(defthmd skip-descriptor-at-front-correct-1
  (iff (mv-nth 0 (skip-descriptor-at-front chars))
       (mv-nth 0 (parse-descriptor-from-front chars)))
  :hints (("Goal" :in-theory (enable skip-descriptor-at-front
                                     parse-descriptor-from-front
                                     skip-chars-through-terminator-correct-1))))

(defthmd skip-descriptor-at-front-correct-2
  (equal (mv-nth 1 (skip-descriptor-at-front chars))
         (mv-nth 1 (parse-descriptor-from-front chars)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable skip-descriptor-at-front
                              parse-descriptor-from-front
                              skip-descriptor-at-front-correct-1
                              skip-chars-through-terminator-correct-1
                              skip-chars-through-terminator-correct-2
                              ))))

;;;
;;; parse-descriptor-chars
;;;

;; Attempt to parse the CHARS as a single descriptor.
;; Returns (mv erp parsed-descriptor).  Can throw an error.
(defund parse-descriptor-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (parsed-descriptor remaining-chars)
    (parse-descriptor-from-front chars)
    (if (not parsed-descriptor)
        (prog2$ (er hard? 'parse-descriptor-chars "Failed to parse a descriptor from ~X01." chars nil)
                (mv :failed-to-parse-descriptor nil))
      (if (consp remaining-chars)
          (prog2$ (er hard? 'parse-descriptor-chars "Extra chars found after descriptor in ~X01." chars nil)
                  (mv :extra-chars-after-descriptor nil))
        (mv nil ; no error
            parsed-descriptor)))))

(defthm typep-of-mv-nth-1-of-parse-descriptor-chars
  (implies (not (mv-nth 0 (jvm::parse-descriptor-chars chars)))
           (jvm::typep (mv-nth 1 (jvm::parse-descriptor-chars chars))))
  :hints (("Goal" :in-theory (enable jvm::parse-descriptor-chars))))

;;;
;;; parse-descriptor
;;;

;; Returns (mv erp parsed-descriptor).
;; Can throw an error.
(defund parse-descriptor (str)
  (declare (xargs :guard (stringp str)))
  (parse-descriptor-chars (coerce str 'list)))

(defthm typep-of-mv-nth-1-of-parse-descriptor
  (implies (not (mv-nth 0 (jvm::parse-descriptor str)))
           (jvm::typep (mv-nth 1 (jvm::parse-descriptor str))))
  :hints (("Goal" :in-theory (enable jvm::parse-descriptor))))

;;;
;;; descriptor-charsp
;;;

;; Check whether CHARS represents a single descriptor
(defund descriptor-charsp (chars)
  (declare (xargs :guard (character-listp chars)))
  (mv-let (starts-with-descriptorp remaining-chars)
    (skip-descriptor-at-front chars)
    (and starts-with-descriptorp
         (not (consp remaining-chars)))))

;;;
;;; is-descriptorp
;;;

;; Check whether STR represents a single descriptor
(defund is-descriptorp (str)
  (declare (xargs :guard (stringp str)))
  (descriptor-charsp (coerce str 'list)))

;;;
;;; descriptorp
;;;

;; Recognize a single descriptor
(defund descriptorp (desc)
  (declare (xargs :guard t))
  (and (stringp desc)
       (is-descriptorp desc)))
