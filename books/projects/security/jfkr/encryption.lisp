; Copyright David Rager 2006

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

(in-package "CRYPTO")


;;;;;;;;;;;;;;;;;;;;
;;; Typing rules ;;;
;;;;;;;;;;;;;;;;;;;;

(defun keyp (x)
  (declare (xargs :guard t))
  (integerp x))

(defun encryptable-listp (x)
  (declare (xargs :guard t))
  (integer-listp x))

(defun decryptable-listp (x)
  (declare (xargs :guard t))
  (integer-listp x))

#|
; I don't use these theorems, because we will probably never disable
; encryptable-listp and decryptable list-p.  I leave them as a possible level
; of indirection in case we change what we can encrypt and decrypt later.

(defthm encryptable-listp-implies-integer-listp
  (iff (encryptable-listp x)
       (integer-listp x))
  :rule-classes :compound-recognizer)

(defthm decryptable-listp-implies-integer-listp
  (iff (decryptable-listp x)
       (integer-listp x))
  :rule-classes :compound-recognizer)

(in-theory (disable encryptable-listp decryptable-listp))

(thm
 (implies (integer-listp (foo x))  (encryptable-lisp (foo x)))
 :rule-classes :type-prescription)

(defthm encryptable-listp-implies-integer-listp
  (implies (integer-listp x)
           (encryptable-listp x)))

(defthm encryptable-listp-implies-integer-listp2
  (implies (encryptable-listp x)
           (integer-listp x)))
|#


;;;;;;;;;;;;;;;;;;;;;;;;;;
;; symmetric encryption ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun encrypt-symmetric-list (lst key)
  (declare (xargs :guard (and (keyp key)
                              (encryptable-listp lst))))
  (if (atom lst)
      nil
    (cons (+ (car lst) key)
          (encrypt-symmetric-list (cdr lst) key))))


(defun decrypt-symmetric-list (lst key)
  (declare (xargs :guard (and (keyp key)
                              (decryptable-listp lst))))
  (if (atom lst)
      nil
    (cons (- (car lst) key)
          (decrypt-symmetric-list (cdr lst) key))))

(defthm encrypt-symmetric-list-returns-decryptable-listp
  (implies (and (force (encryptable-listp lst))
                (force (keyp key)))
           (decryptable-listp (encrypt-symmetric-list lst key))))


(defthm decrypt-of-encrypt-symmetric-equals-plaintext
  (implies (force (encryptable-listp lst))
           (equal (decrypt-symmetric-list (encrypt-symmetric-list lst key)
                                          key)
                  lst)))

(defthm decrypt-of-encrypt-symmetric-needs-key
  (implies (and (encryptable-listp lst)
                (not (null lst))
                (keyp keyA)
                (keyp keyB)
                (not (equal keyA keyB)))
           (not (equal (decrypt-symmetric-list (encrypt-symmetric-list lst keyA)
                                               keyB)
                       lst))))

(in-theory (disable encrypt-symmetric-list decrypt-symmetric-list))


;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; asymmetric encryption ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun public-private-key-pairp (x y)
  (declare (xargs :guard (and (keyp x)
                              (keyp y))))
  (equal x (- y)))

(defun encrypt-asymmetric-list (lst key)
  (declare (xargs :guard (and (keyp key)
                              (encryptable-listp lst))))
  (if (atom lst)
      nil
    (cons (+ (car lst) key) ; maybe make operation * in future
          (encrypt-asymmetric-list (cdr lst) key))))

(defun decrypt-asymmetric-list (lst key)
  (declare (xargs :guard (and (keyp key)
                              (decryptable-listp lst))))
  (if (atom lst)
      nil
    (cons (+ (car lst) key)
          (decrypt-asymmetric-list (cdr lst) key))))


(defthm decrypt-of-encrypt-asymmetric-equals-plaintext
  (implies (and (encryptable-listp lst)
                (public-private-key-pairp key1 key2))
           (and (equal (decrypt-asymmetric-list
                        (encrypt-asymmetric-list lst key1)
                        key2)
                       lst)
                (equal (decrypt-asymmetric-list
                        (encrypt-asymmetric-list lst key2)
                        key1)
                       lst))))

(defthm decrypt-of-encrypt-asymmetric-needs-key
  (implies (and (encryptable-listp lst)
                (not (null lst))
                (keyp keyA)
                (keyp keyB)
                (not (public-private-key-pairp keyA keyB)))
           (not (equal (decrypt-asymmetric-list (encrypt-asymmetric-list lst keyA)
                                                keyB)
                       lst))))

(in-theory (disable encrypt-asymmetric-list decrypt-asymmetric-list))

;;;;;;;;;;;;;;;;
;; signatures ;;
;;;;;;;;;;;;;;;;

(defun sum (lst)
  (declare (xargs :guard (integer-listp lst)))
  (if (endp lst)
      0
    (+ (car lst) (sum (cdr lst)))))

; we use forward-chaining whenever we want to rewrite hypothesizes
(defthm sum-integerp
  (implies (force (integer-listp lst))
           (integerp (sum lst)))
  :rule-classes :forward-chaining)

(in-theory (disable sum))

(defun compute-signature-list (lst key)
  (declare (xargs :guard (and (keyp key)
                              (encryptable-listp lst))))
  (- (sum lst) key))

(defun verify-signature-list (lst key)
  (declare (xargs :guard (and (keyp key)
                              (encryptable-listp lst))))
  (+ (sum lst) key))

(defthm verify-of-signature-verifies
  (implies (and (force (encryptable-listp lst))
                (force (public-private-key-pairp public-key private-key)))
           (equal (compute-signature-list lst private-key)
                  (verify-signature-list lst public-key))))

(defthm verify-of-signature-needs-key
  (implies (and (force (encryptable-listp lst))
                (force (not (null lst)))
                (force (keyp public-key))
                (force (keyp private-key))
                (force (not (public-private-key-pairp public-key private-key))))
           (not (equal (compute-signature-list lst private-key)
                       (verify-signature-list lst public-key)))))

(defthm computed-signature-integerp
  (implies (and (force (encryptable-listp lst))
                (force (keyp key)))
           (integerp (compute-signature-list lst key)))
  :rule-classes :forward-chaining)

(defthm verified-signature-integerp
  (implies (and (force (encryptable-listp lst))
                (force (keyp key)))
           (integerp (verify-signature-list lst key)))
  :rule-classes :forward-chaining)

(in-theory (disable compute-signature-list verify-signature-list
                    public-private-key-pairp))


;;;;;;;;;;;;
;; hashes ;;
;;;;;;;;;;;;

(defun compute-keyed-hash (lst key)
  ;; All that matters is that this operation is irreverisble.  The
  ;; implementation is hidden later anyway.
  (declare (xargs :guard (and (keyp key)
                              (encryptable-listp lst))))
  (+ (sum lst) key))

(defthm compute-keyed-hash-returns-int
  (implies (and (force (keyp key))
                (force (encryptable-listp lst)))
           (integerp (compute-keyed-hash lst key)))
  :rule-classes (:type-prescription :forward-chaining))

(defthm compute-keyed-hash-requires-key-to-duplicate-for-a-given-lst
  (implies (and (encryptable-listp lst)
                (keyp keyA)
                (keyp keyB)
                (not (equal keyA keyB)))
           (not (equal (compute-keyed-hash lst keyA)
                       (compute-keyed-hash lst keyB)))))

(in-theory (disable compute-keyed-hash encryptable-listp keyp))
