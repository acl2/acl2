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
(include-book "kestrel/utilities/hex-string-to-bytes" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/testing/assert-bang-stobj" :dir :system)

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
                   ((mv erp in-bytes) (acl2::hex-string-to-bytes in))
                   ((when erp) :error)
                   ((when (not (< (len in-bytes) (- *blake2s-max-data-byte-length* 64)) ;todo
                               ))
                    (cw "ERROR: Test input too long.")
                    :error)
                   ((mv erp key-bytes) (acl2::hex-string-to-bytes key))
                   ((when erp) :error)
                   ((mv erp out-bytes) (acl2::hex-string-to-bytes out))
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
