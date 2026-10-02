; Material on Java strings.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; TODO: Add Unicode support.

(include-book "types")
(include-book "java-types")
(include-book "kestrel/bv/bvchop-def" :dir :system)
(local (include-book "kestrel/bv/bvchop" :dir :system))

(in-theory (disable mv-nth))

;; Recognizes a true-list of 16-bit Java chars.
(defund java-char-listp (chars)
  (declare (xargs :guard t))
  (if (atom chars)
      (null chars)
    (and (acl2::java-charp (first chars))
         (java-char-listp (rest chars)))))

(defthm java-char-listp-of-cdr
  (implies (java-char-listp chars)
           (java-char-listp (cdr chars)))
  :hints (("Goal" :in-theory (enable java-char-listp))))

(defthm java-char-listp-of-cons
  (equal (java-char-listp (cons char chars))
         (and (acl2::java-charp char)
              (java-char-listp chars)))
  :hints (("Goal" :in-theory (enable java-char-listp))))

(defthm java-char-listp-of-append
  (equal (java-char-listp (append chars1 chars2))
         (and (java-char-listp (true-list-fix chars1))
              (java-char-listp chars2)))
  :hints (("Goal" :in-theory (enable java-char-listp))))

(defthm java-char-listp-of-nthcdr
  (implies (java-char-listp chars)
           (java-char-listp (nthcdr n chars)))
  :hints (("Goal" :in-theory (enable java-char-listp nthcdr))))



;; Converts a list of Java chars into a list of ACL2 characters (chops down any char > 255).
;todo use defmap
(defun code-char-list (chars)
  (declare (xargs :guard (java-char-listp chars)
                  :guard-hints (("Goal" :expand ((java-char-listp chars))
                                 :in-theory (enable java-char-listp acl2::java-charp unsigned-byte-p)))))
  (if (endp chars)
      nil
    (cons (code-char (bvchop 8 (first chars))) ;;TTODO: Drop the bvchop (actually, use Alessandro's representation of Java strings?)
          (code-char-list (rest chars)))))

(defun char-list-to-string (java-chars)
  (declare (xargs :guard (java-char-listp java-chars)))
  (let ((acl2-characters (code-char-list java-chars)))
    (coerce acl2-characters 'string)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo use defmap, or rename map-char-code
(defun char-code-list (characters)
  (declare (xargs :guard (character-listp characters)
                  :guard-hints (("Goal" :in-theory (enable character-listp)))
                  ))
  (if (endp characters)
      nil
    (cons (char-code (first characters))
          (char-code-list (rest characters)))))

(defthm char-code-list-iff
  (iff (char-code-list characters)
       (not (endp characters))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;Convert an ACL2 string to a list of Java chars (unsigned 16-bit integers)
;FIXME What about unicode?
(defun string-to-char-list (string)
  (declare (xargs :guard (stringp string)))
  (let ((characters (coerce string 'list)))
    (char-code-list characters)))

;move
(defthm equal-nil-string-to-char-list-helper
  (implies (and (equal nil (coerce string 'list))
                (stringp string))
           (equal "" string))
  :hints (("Goal" :use (:instance coerce-inverse-2 (acl2::x string))))
  :rule-classes nil)

(defthm equal-nil-string-to-char-list
  (equal (equal nil (string-to-char-list string))
         (or (not (stringp string))
             (equal "" string)))
  :hints (("Goal" :use (:instance equal-nil-string-to-char-list-helper))))

(defthm code-char-list-of-char-code-list
  (implies (character-listp lst)
           (equal (code-char-list (char-code-list lst))
                  lst))
  :hints (("Goal" :in-theory (enable code-char-list
                                     char-code-list
                                     unsigned-byte-p))))

(defthm char-list-to-string-of-string-to-char-list
  (implies (stringp str)
           (equal (char-list-to-string (string-to-char-list str))
                  str))
  :hints (("Goal" :in-theory (enable string-to-char-list))))
