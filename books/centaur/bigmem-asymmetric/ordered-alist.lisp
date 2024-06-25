; Ordered Alists
; Copyright (C) 2024, Intel Corporation

; For development:
; (ld "ordered-alist.lisp" :ld-pre-eval-print t)

; Contact
;   ACL2 Formal Verification Group
;   Intel Corporation
;   1300 South MoPac Expy,  Austin, TX  78746, USA
;   https://www.intel.com/

; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

;   Original Author(s): "Warren A. Hunt, Jr." <warren.hunt@intel.com>

(in-package "BIGMEM-ASYMMETRIC")

; "xdoc/top" appears to be included by the "std/util/define" book.
(include-book "xdoc/top"         :dir :system)
(include-book "std/util/define"  :dir :system)

; Should be removed
; (include-book "misc/disassemble" :dir :system :ttags (:disassemble$))


(defxdoc ordered-bytes
  :parents (bigmem-asymmetric)
  :short "Alists with ordered keys."

  :long "<p>The @('ordered-list') library is simply the definition
  of an alist where the key-value entries are ordered by their keys.</p>

  <p>This book defines a recognizer for alists whose key-value pairs are kept
  with ordered keys.  A default value of 0 is returned when such an ordered
  alist has no associated key.  Our initial use for this package is to model
  sparse memories while maintaining memory-style access and update functions.</p>")


; Recognizer of AList with ordered natural number keys with non-zero (byte)
; values less than 256.

(defun nat-bytep (x)
  "Nat-Bytep: natural-number, ordered-key AList with no value bound to 0."
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (let ((pair (car x))
          (rest (cdr x)))
      (and (consp pair)
           (let ((key (car pair))
                 (val (cdr pair)))
             (and (natp key)
                  (unsigned-byte-p 8 val)
                  (not (= val 0))
                  ;; Check REST for syntatic structure
                  (nat-bytep rest)
                  (if (atom rest)
                      (null rest)
                      ;; Check key ordering on the way "out"
                    (< key (caar rest)))))))))

(defun nat-byte-alst (x)
  "Syntax of AList with natural-number keys and non-zero byte values."
  (declare (xargs :guard (alistp x)))
  (or (atom x)
      (let ((k (caar x))
            (v (cdar x)))
        (and (natp k)
             (unsigned-byte-p 8 v)
             (not (= v 0))
             (nat-byte-alst (cdr x))))))

(defun ord-keys (x)
  "AList with ordered keys."
  (declare (xargs :guard (and (alistp x)
                              (nat-byte-alst x))))
  (or (atom x)
      (atom (cdr x))
      (and (< (caar x)
              (caar (cdr x)))
           (ord-keys (cdr x)))))

(defun nbp (x)
  "NBPs: natural-number, ordered-key AList with no value bound to 0."
  (declare (xargs :guard t))
  (and (alistp x)
       (nat-byte-alst x)
       (ord-keys x)))

(defthmd nbp-is-nat-bytep
  (equal (nat-bytep x)
         (nbp x)))

(defthm nat-bytep-forward
  (implies (nat-bytep x)
           (and (alistp x)
                (nat-byte-alst x)
                (ord-keys x)))
  ;; :rule-classes :forward-chaining
  :rule-classes NIL)


; Properties about natural-number, ordered-keys, AList

(defun all-keys-as-big (minimum oal)
  (declare (xargs :guard (and (natp minimum)
                              (nat-bytep oal))))
  (if (atom oal)
      T
    (and (<= minimum (caar oal))
         (all-keys-as-big minimum (cdr oal)))))

(defun first-key-as-big (minimum oal)
  (declare (xargs :guard (and (natp minimum)
                              (nat-bytep oal))))
  (if (atom oal)
      T
    (<= minimum (caar oal))))

(defthm first-key-as-big-implies-all-keys-as-big
  (implies (and (nat-bytep oal)
                (first-key-as-big minimum oal))
           (all-keys-as-big minimum oal)))


; Membership function.

(defun mbr-kv (k x)
  "If key K exists, return alist value; otherwise, return 0."
  (declare (xargs :guard (and (natp k)
                              (nat-bytep x))
                  :verify-guards nil))
  (if (atom x)
      0
    (let* ((pair (car x))
           (key (car pair)))
      (mbe :logic
           (if (= k key)
               (cdr pair)
             (mbr-kv k (cdr x)))
           :exec
           (if (< k key) ;; Ordered-keys optimization
               0
             (if (= k key)
                 (cdr pair)
               (mbr-kv k (cdr x))))))))

(defthm mbr-kv-is-0-when-e-<-caar-x
  (implies (and (nat-bytep x)
                (or (atom x)
                    (< k (caar x))))
           (equal (mbr-kv k x) 0))
  :hints
  (("Goal" :induct (mbr-kv k x))))

(verify-guards mbr-kv)

(defthm natp-mbr-kv
  (implies (nat-bytep x)
           (natp (mbr-kv k x)))
  :hints
  (("Goal" :induct (mbr-kv k x)))
  :rule-classes :type-prescription)

(defthm integerp-mbr-kv
  (implies (nat-bytep x)
           (integerp (mbr-kv k x))))

(defthm in-range-mbr-kv
  (implies (nat-bytep x)
           (and (<= 0 (mbr-kv a x))
                (< (mbr-kv a x) 256)))
  :hints
  (("Goal" :induct (nat-bytep x)))
  :rule-classes :linear)

(in-theory (disable mbr-kv))


; Deletion function.

(defun del-kv (k x)
  "Delete key K and its value from memory X; otherwise, return X."
  (declare (xargs :guard (and (natp k)
                              (nat-bytep x))
                  :verify-guards nil))
  (if (atom x)
      NIL
    (let* ((pair (car x))
           (key (car pair))
           (rest (cdr x)))
      (mbe :logic
           (if (= k key)
               rest
             (cons pair
                   (del-kv k rest)))
           :exec
           (if (< k key)
               x
             (if (= k key)
                 rest
               (cons pair
                     (del-kv k rest))))))))

(defthm k-<-caar-x
  (implies (and (nat-bytep x)
                (or (atom x)
                    (< k (caar x))))
           (equal (del-kv k x) x))
  :hints
  (("Goal" :induct (del-kv k x))))

(verify-guards del-kv)

(defthm nat-bytep-del-kv
  (implies (nat-bytep x)
           (nat-bytep (del-kv k x))))

; Lemmas about insertion and deletion functions.

(defthm del-kv-del-kv
  ;; This lemma is true for any two distinct addresses -- even symbols,
  ;; characters, string, and numbers other than naturals.
  (implies (and (not (equal a1 a2))
                (nat-bytep x))
           ;; !!! Warning.  See: LOOP-STOPPER
           (equal (del-kv a1 (del-kv a2 x))
                  (del-kv a2 (del-kv a1 x)))))

(defthm mbr-kv-del-kv
  (implies (and (equal a1 a2)
                (nat-bytep x))
           (equal (mbr-kv a1 (del-kv a2 x))
                  0))
  :hints
  (("Goal" :in-theory (e/d (mbr-kv)))))

(defthm mbr-kv-del-kv-different-address
  (implies (and (not (equal a1 a2))
                (nat-bytep x))
           (equal (mbr-kv a1 (del-kv a2 x))
                  (mbr-kv a1 x)))
  :hints
  (("Goal" :in-theory (e/d (mbr-kv) ()))))

(defthm del-kv-when-zero
  (implies (and (nat-bytep x)
                (= (mbr-kv k x) 0))
           (equal (del-kv k x)
                  x))
  :hints
  (("Goal" :in-theory (e/d (mbr-kv) ()))))

(defthm all-keys-as-big-del-kv
  (implies (and (nat-bytep x)
                (all-keys-as-big minimum x))
           (all-keys-as-big minimum (del-kv k x))))

(in-theory (disable del-kv))


; Non-zero-value, key-value insertion function.

(defun insrt-kv-not-0 (k v x)
  "Insert non-zero V at K into ordered alist X."
  (declare (xargs :guard (and (natp k)
                              (posp v)
                              (unsigned-byte-p 8 v)
                              (nat-bytep x))))
  (if (atom x)
      (list (cons k v))
    (let* ((pair (car x))
           (key (car pair)))
      (if (< k key)
          (cons (cons k v)
                x)
        (if (= k key)
            (cons (cons k v)
                  (cdr x))
          (cons pair
                (insrt-kv-not-0 k v (cdr x))))))))

(defthm nat-bytep-insrt-kv-not-0
  (implies (and (natp k)
                (unsigned-byte-p 8 v)
                (not (= v 0))
                (nat-bytep x))
           (nat-bytep (insrt-kv-not-0 k v x)))
  :hints
  (("Goal" :induct (insrt-kv-not-0 k v x))))

(defthm all-keys-as-big-insrt-kv-not-0
  (implies (and (nat-bytep x)
                (<= minimum k)
                (all-keys-as-big minimum x))
           (all-keys-as-big minimum (insrt-kv-not-0 k v x))))

(defthm insrt-kv-not-0-insrt-kv-not-0-same-address
  (implies (and (equal a1 a2)
                (nat-bytep x))
           (equal (insrt-kv-not-0 a1 v1 (insrt-kv-not-0 a2 v2 x))
                  (insrt-kv-not-0 a1 v1 x))))

(defthm insrt-kv-not-0-insrt-kv-not-0
  ;; This lemma is not valid when test is: (not (equal a1 a2)).  For example,
  ;; (< <sym1> <sym2>) is always NIL.  The definition of INSRT-KV-NOT-0 could
  ;; be generalized by using LEXORDER instead of <, but we only have natural
  ;; number key (addresses).
  (implies (and (not (equal (nfix a1) (nfix a2)))
                (nat-bytep x))
           ;; !!! Warning.  See: LOOP-STOPPER
           (equal (insrt-kv-not-0 a2 v2 (insrt-kv-not-0 a1 v1 x))
                  (insrt-kv-not-0 a1 v1 (insrt-kv-not-0 a2 v2 x)))))

(defthm mbr-kv-insrt-kv-not-0
  (implies (nat-bytep x)
           (equal (mbr-kv k (insrt-kv-not-0 k v x))
                  v))
  :hints
  (("Goal" :induct (insrt-kv-not-0 k v x)
           :in-theory (e/d (mbr-kv) ()))))

(defthm mbr-kv-insrt-kv-not-0-different-addresses
  (implies (and (not (equal a1 a2))
                (nat-bytep x))
           (equal (mbr-kv a1 (insrt-kv-not-0 a2 v x))
                  (mbr-kv a1 x)))
  :hints
  (("Goal" :in-theory (e/d (mbr-kv) ()))))

(defthm insrt-kv-not-0-del-kv-same-address
  (implies (and (equal a1 a2)
                (nat-bytep x))
           (equal (insrt-kv-not-0 a1 v (del-kv a2 x))
                  (insrt-kv-not-0 a1 v x)))
  :hints
  (("Goal" :in-theory (e/d (del-kv) ()))))

(defthm insrt-kv-not-0-del-kv-different-addresses
  (implies (and (not (equal (nfix a1) (nfix a2)))
                (nat-bytep x))
           (equal (insrt-kv-not-0 a2 v (del-kv a1 x))
                  (del-kv a1 (insrt-kv-not-0 a2 v x))))
  :hints
  (("Goal" :induct (del-kv a1 x)
           :in-theory (e/d (del-kv)
                           (integer-range-p
                            unsigned-byte-p)))))

(defthm insrt-kv-not-0-with-mbr-kv
  (implies (and (nat-bytep x)
                (not (= (mbr-kv k x) 0)))
           (equal (insrt-kv-not-0 k (mbr-kv k x) x)
                  x))
  :hints
  (("Goal" :in-theory (e/d (mbr-kv) ()))))

(defthm del-kv-insrt-kv-not-0
  (implies (nat-bytep x)
           (equal (del-kv k (insrt-kv-not-0 k v x))
                  (del-kv k x)))
  :hints
  (("Goal" :in-theory (e/d (del-kv) ()))))

(in-theory (disable insrt-kv-not-0))


; Key-value insertion function.

(defun insrt-kv (k v x)
  "Insert V at K into ordered alist X."
  (declare (xargs :guard (and (natp k)
                              (unsigned-byte-p 8 v)
                              (nat-bytep x))))
  (if (= v 0)
      (del-kv k x)
    (insrt-kv-not-0 k v x)))

(defthm nat-bytep-insrt-kv
  (implies (and (natp k)
                (unsigned-byte-p 8 v)
                (nat-bytep x))
           (nat-bytep (insrt-kv k v x))))

(defthm all-keys-as-big-insrt-kv
  (implies (and (nat-bytep x)
                (<= minimum k)
                (all-keys-as-big minimum x))
           (all-keys-as-big minimum (insrt-kv k v x))))

(defthm mbr-kv-insrt-kv-same-address
  (implies (and (equal a1 a2)
                (nat-bytep x))
           (equal (mbr-kv a1 (insrt-kv a2 v x))
                  v)))

(defthm mb-kv-insrt-kv-different-addresses
  (implies (and (not (equal (nfix a1) (nfix a2)))
                (nat-bytep x))
           (equal (mbr-kv a1 (insrt-kv a2 v x))
                  (mbr-kv a1 x))))


; The following four lemmas are required for a memory.

(defthm mbr-kv-a1-a2-insrt-kv
  ;; nth-!nth
  ;; Read-over-Write; redundant with built-in lemma NTH-UPDATE-NTH
  (implies (nat-bytep x)
           (equal (mbr-kv a1 (insrt-kv a2 v x))
                  (if (equal a1 a2)
                      v
                    (mbr-kv a1 x)))))

(defthm insrt-kv-mbr-kv
  ;; !nth-nth
  ;; Write-over-Read; A read "off the end" is 0, but a non-zero write extends X
  (implies (and (equal a1 a2)
                (nat-bytep x))
           (equal (insrt-kv a1 (mbr-kv a2 x) x)
                  x)))

(defthm insrt-kv-insrt-kv-same-address
  ;; !nth-!nth-same-address
  ;; Write-over-write; memory at a specific address reflects last value written
  (implies (and (nat-bytep x)
                (equal a1 a2))
           (equal (insrt-kv a1 v (insrt-kv a2 w x))
                  (insrt-kv a1 v x))))

(defthm insrt-kv-insrt-kv-different-addresses
  ;; !nth-!nth-different-addresses
  ;; Order of writes to different memory locations is irrelavant
  (implies (and (nat-bytep x)
                (not (equal (nfix a1) (nfix a2))))
           ;; !!! Warning.  See: LOOP-STOPPER
           (equal (insrt-kv a1 v1 (insrt-kv a2 v2 x))
                  (insrt-kv a2 v2 (insrt-kv a1 v1 x)))))

(in-theory (disable insrt-kv))

(in-theory
 ;; Most definitions are already disabled.
 ;; Disable all lemmas other than last four lemmas.
 (disable first-key-as-big-implies-all-keys-as-big
          mbr-kv-is-0-when-e-<-caar-x
          ;; natp-mbr-kv
          integerp-mbr-kv
          ;; in-range-mbr-kv
          k-<-caar-x
          nat-bytep-del-kv
          del-kv-del-kv
          mbr-kv-del-kv
          mbr-kv-del-kv-different-address
          del-kv-when-zero
          all-keys-as-big-del-kv
          nat-bytep-insrt-kv-not-0
          all-keys-as-big-insrt-kv-not-0
          insrt-kv-not-0-insrt-kv-not-0-same-address
          insrt-kv-not-0-insrt-kv-not-0
          mbr-kv-insrt-kv-not-0
          mbr-kv-insrt-kv-not-0-different-addresses
          insrt-kv-not-0-del-kv-same-address
          insrt-kv-not-0-del-kv-different-addresses
          insrt-kv-not-0-with-mbr-kv
          del-kv-insrt-kv-not-0
          nat-bytep-insrt-kv
          all-keys-as-big-insrt-kv
          mbr-kv-insrt-kv-same-address
          mb-kv-insrt-kv-different-addresses

          ;; The significant lemmas remain enabled

          ;; mbr-kv-a1-a2-insrt-kv
          ;; insrt-kv-mbr-kv
          ;; insrt-kv-insrt-kv-same-address
          ;; insrt-kv-insrt-kv-different-addresses

          ))
