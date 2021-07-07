; Material on Java strings.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

;; TODO: Add Unicode support.

(include-book "kestrel/jvm/types" :dir :system)
(include-book "kestrel/jvm/java-types" :dir :system)
(include-book "kestrel/bv/bvchop" :dir :system)

;todo: change to JVM package
(defun acl2::all-java-charp (x)
  (declare (xargs :guard t))
  (if (atom x)
      t
      (and (acl2::java-charp (first x))
           (acl2::all-java-charp (rest x)))))

;todo use defmap
(defun code-char-list (characters)
  (declare (xargs :guard (and (true-listp characters)
                              (acl2::all-java-charp characters))
                  :guard-hints (("Goal" :expand ((ACL2::ALL-JAVA-CHARP CHARACTERS))
                                 :in-theory (enable acl2::all-java-charp ACL2::JAVA-CHARP UNSIGNED-BYTE-P)))
                  ))
  (if (endp characters)
      nil
    (cons (code-char (acl2::bvchop 8 (first characters))) ;;TTODO: Drop the bvchop (actually, use Alessandro's representation of Java strings)
          (code-char-list (rest characters)))))

(defun char-list-to-string (java-chars)
  (declare (xargs :guard (and (true-listp java-chars)
                              (acl2::all-java-charp java-chars))))
  (let ((acl2-characters (code-char-list java-chars)))
    (coerce acl2-characters 'string)))

;todo use defmap
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

;Convert an ACL2 string to a list of Java chars (unsigned 16-bit integers)
;FIXME What about unicode?
(defun string-to-char-list (string)
  (declare (xargs :guard (stringp string)))
  (let ((characters (coerce string 'list)))
    (char-code-list characters)))

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
