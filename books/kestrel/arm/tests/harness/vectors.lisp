; Test vector data structure for the ARM32 model
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; A test vector describes the state before one instruction and the expected
;; state after it.  It is a keyword-value list with these keys:
;;
;;   :id      a string naming the test
;;   :arch    the architecture version, 4 to 7 (default 7)
;;   :pc      the address of the instruction to execute
;;   :code    a list of 32-bit instruction words, stored from :pc upward
;;   :regs    an alist from register numbers to initial values (others are 0)
;;   :apsr    the initial APSR (default 0)
;;   :mem     a list of (address size value) triples to store, little-endian
;;   :expect  a keyword-value list describing the state after one step:
;;     :error     the expected error value; when non-nil nothing else is checked
;;     :pc        the expected program counter
;;     :regs      an alist of expected register values; a register not listed
;;                here must be unchanged from its initial value
;;     :apsr      the expected APSR (default 0), compared under :apsr-mask
;;     :apsr-mask which APSR bits to compare (default #xF0000000, that is,
;;                the N, Z, C, and V flags)
;;     :mem       a list of (address size value) triples expected in memory
;;
;; Vectors contain only keywords, numbers, and strings, so the package in which
;; they are read does not matter.  See smoke.lisp for examples.
;;
;; The recognizers below also check what the harness needs no guard for:
;; each key is one of those above and appears at most once, and :expect gives
;; a :pc unless it gives an :error.  A misspelled key would otherwise make its
;; check silently vanish.

(include-book "../../memory") ; for addressp
(include-book "kestrel/bv-lists/unsigned-byte-listp-def" :dir :system)

;; Looks up KEY in the keyword-value list VEC, returning DEFAULT if absent.
;; Kept disabled so that guard proofs below match the recognizers below
;; syntactically instead of case-splitting on which keys are present.
(defund vec-get (key vec default)
  (declare (xargs :guard (and (keywordp key)
                              (keyword-value-listp vec))))
  (let ((tail (assoc-keyword key vec)))
    (if tail (cadr tail) default)))

;; An alist from register numbers (0 to 15) to 32-bit values.
(defun reg-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (consp (car x))
         (natp (caar x))
         (<= (caar x) 15)
         (unsigned-byte-p 32 (cdar x))
         (reg-alistp (cdr x)))))

;; A list of (address size value) triples.
(defun mem-triple-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (let ((triple (car x)))
      (and (true-listp triple)
           (= 3 (len triple))
           (addressp (first triple))
           (posp (second triple))
           (unsigned-byte-p (* 8 (second triple)) (third triple))
           (mem-triple-listp (cdr x))))))

(defconst *test-vector-keys* '(:id :arch :pc :code :regs :apsr :mem :expect))

(defconst *expect-keys* '(:error :pc :regs :apsr :apsr-mask :mem))

;; Recognizes the :expect part of a test vector.
(defun expectp (x)
  (declare (xargs :guard t))
  (and (keyword-value-listp x)
       (subsetp-eq (evens x) *expect-keys*)
       (no-duplicatesp-equal (evens x))
       (or (vec-get :error x nil)
           (addressp (vec-get :pc x nil)))
       (reg-alistp (vec-get :regs x nil))
       (unsigned-byte-p 32 (vec-get :apsr x 0))
       (unsigned-byte-p 32 (vec-get :apsr-mask x #xF0000000))
       (mem-triple-listp (vec-get :mem x nil))))

(defun test-vectorp (x)
  (declare (xargs :guard t))
  (and (keyword-value-listp x)
       (subsetp-eq (evens x) *test-vector-keys*)
       (no-duplicatesp-equal (evens x))
       (stringp (vec-get :id x ""))
       (let ((arch (vec-get :arch x 7)))
         (and (integerp arch) (<= 4 arch) (<= arch 7)))
       (addressp (vec-get :pc x 0))
       (acl2::unsigned-byte-listp 32 (vec-get :code x nil))
       (reg-alistp (vec-get :regs x nil))
       (unsigned-byte-p 32 (vec-get :apsr x 0))
       (mem-triple-listp (vec-get :mem x nil))
       (expectp (vec-get :expect x nil))))

(defun test-vector-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (test-vectorp (car x))
         (test-vector-listp (cdr x)))))
