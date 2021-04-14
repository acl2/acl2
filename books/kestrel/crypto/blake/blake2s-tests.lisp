; Tests for BLAKE2s
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

(include-book "blake2s")
(include-book "kestrel/json-parser/parse-json-file" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/testing/assert-bang-stobj" :dir :system)

(in-theory (disable ACL2::REVAPPEND-REMOVAL)) ;todo: bad.  comes in via file-io

;; Returns (mv erp val)
(defund hex-char-to-val (char)
  (declare (xargs :guard (characterp char)))
  (let ((code (char-code char)))
    (if (and (<= 48 code)
             (<= code 57))
        ;; digit 0-9
        (mv nil (- code 48))
      (if (and (<= 65 code)
               (<= code 70))
          ;; capital A-F
          (mv nil (+ 10 (- code 65)))
        (if (and (<= 97 code)
                 (<= code 102))
            ;; lowercase a-f
            (mv nil (+ 10 (- code 97)))
          (mv :bad-digit 0))))))

(defthm natp-of-mv-nth-1-of-hex-char-to-val
  (natp (mv-nth 1 (hex-char-to-val char)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable hex-char-to-val))))

(defthm <-16-of-mv-nth-1-of-hex-char-to-val
  (< (mv-nth 1 (hex-char-to-val char)) 16)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable hex-char-to-val))))

;; Returns (mv erp val)
(defund hex-chars-to-bytes (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (true-listp acc))))
  (if (endp chars)
      (mv nil (reverse acc))
    (if (endp (rest chars))
        (mv :odd-number-of-chars nil)
      (b* ((first-char (first chars))
           (second-char (second chars))
           ((mv erp first-char-value)
            (hex-char-to-val first-char))
           ((when erp) (mv erp nil))
           ((mv erp second-char-value)
            (hex-char-to-val second-char))
           ((when erp) (mv erp nil))
           (byte (+ (* 16 first-char-value)
                    second-char-value)))
        (hex-chars-to-bytes (rest (rest chars))
                            (cons byte acc))))))

(defthm all-unsigned-byte-p-of-mv-nth-1-of-hex-chars-to-bytes
  (implies (all-unsigned-byte-p 8 acc)
           (all-unsigned-byte-p 8 (mv-nth 1 (hex-chars-to-bytes chars acc))))
  :hints (("Goal" :in-theory (enable hex-chars-to-bytes unsigned-byte-p))))

(defthm true-listp-of-mv-nth-1-of-hex-chars-to-bytes
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (hex-chars-to-bytes chars acc))))
  :hints (("Goal" :in-theory (enable hex-chars-to-bytes))))

;; Returns (mv erp val)
(defund hex-string-to-bytes (s)
  (declare (xargs :guard (stringp s)))
  (let ((chars (coerce s 'list)))
    (hex-chars-to-bytes chars nil)))

(defthm all-unsigned-byte-p-of-mv-nth-1-of-hex-string-to-bytes
  (all-unsigned-byte-p 8 (mv-nth 1 (hex-string-to-bytes s)))
  :hints (("Goal" :in-theory (enable hex-string-to-bytes))))

(defthm true-listp-of-mv-nth-1-of-hex-string-to-bytes
  (true-listp (mv-nth 1 (hex-string-to-bytes s)))
  :hints (("Goal" :in-theory (enable hex-string-to-bytes))))

;; Returns result where result is :pass, :fail, or :error
(defund run-parsed-blake2s-test (test)
  (declare (xargs :guard t))
  (if (not (and (acl2::call-of :object test)
                (= 1 (len (acl2::fargs test)))))
      :error
    (let ((alist (acl2::farg1 test)))
      (if (not (and (alistp alist)
                    (equal '("hash" "in" "key" "out") (strip-cars alist))))
          :error
        (let ((hash (acl2::lookup-equal "hash" alist)))
          (if (not (equal hash "blake2s"))
              (progn$ (cw "Skipping test for ~x0.~%" hash)
                      :pass)
            (let ((in (acl2::lookup-equal "in" alist))
                  (key (acl2::lookup-equal "key" alist))
                  (out (acl2::lookup-equal "out" alist)))
              (b* (((when (not (and (stringp in)
                                    (stringp key)
                                    (stringp out))))
                    :error)
                   ((mv erp in-bytes) (hex-string-to-bytes in))
                   ((when erp) :error)
                   ((when (not (< (len in-bytes) (- *blake2s-max-data-byte-length* 64)) ;todo
                               ))
                    (cw "ERROR: Test input too long.")
                    :error)
                   ((mv erp key-bytes) (hex-string-to-bytes key))
                   ((when erp) :error)
                   ((mv erp out-bytes) (hex-string-to-bytes out))
                   ((when erp) :error)
                   (kk (len key-bytes))
                   ((when (< 32 kk))
                    (cw "ERROR: Key input too long.")
                    :error)
                   (nn (len out-bytes)) ;desired length of hash
                   ((when (< nn 1))
                    (cw "ERROR: Test output too short.")
                    :error)
                   ((when (< 32 nn))
                    (cw "ERROR: Test output too long.")
                    :error)
                   (test-result (blake2s in-bytes key-bytes nn)))
                (if (equal test-result out-bytes)
                    (progn$ (cw "Test passed.~%")
                            :pass)
                  (progn$ (cw "Test failed.~%In: ~x0.~%Key: ~x1.~%Expected result:~x2.~%Actual Result: ~x3." in key out-bytes test-result)
                          :fail))))))))))

;; Returns result, which is is :pass, :fail, or :error.
(defund run-parsed-blake2s-tests (tests)
  (declare (xargs :guard t))
  (if (atom tests)
      :pass
    (let ((result (run-parsed-blake2s-test (first tests))))
      (if (eq :error result)
          :error
        (if (eq :fail result)
            :fail
          (run-parsed-blake2s-tests (rest tests)))))))

;; Returns (mv result acl2::state) where result is :pass, :fail, or :error
(defun run-blake2s-tests (acl2::state)
  (declare (xargs :stobjs acl2::state))
  (b* (((mv parsed-tests acl2::state)
        (acl2::parse-file-as-json "blake2-kat.json" acl2::state))
       ((when (not (and (acl2::call-of :array parsed-tests)
                        (= 1 (len (acl2::fargs parsed-tests))))))
        (mv :error acl2::state))
       (result (run-parsed-blake2s-tests (acl2::farg1 parsed-tests))))
    (mv result acl2::state)))

(acl2::assert!-stobj (mv-let (res acl2::state)
                       (run-blake2s-tests acl2::state)
                       (mv (equal :pass res) acl2::state))
                     acl2::state)
