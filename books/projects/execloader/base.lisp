; EXLD (execloader) Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>

; [Shilpi Goel] This book is a generalized version of older books
; present in [books]/projects/x86isa/tools/execution/exec-loaders.

;; ----------------------------------------------------------------------

(in-package "EXLD")
(include-book "std/lists/take" :dir :system)
(include-book "std/lists/nthcdr" :dir :system)
(include-book "kestrel/fty/byte-list" :dir :system)
(include-book "centaur/bitops/merge" :dir :system)

(local (xdoc::set-default-parents execloader))

;; ----------------------------------------------------------------------

(define bytes->charlist ((bytes byte-listp))
  :short "Convert a list of bytes to a list of characters."
  :returns (lst character-listp :hyp (byte-listp bytes))
  (if (endp bytes)
      nil
    (cons (code-char (car bytes))
          (bytes->charlist (cdr bytes)))))

(define charlist->bytes ((charlist character-listp))
  :short "Convert a list of characters to a list of bytes."
  :returns (bl byte-listp :hyp :guard)
  :prepwork ((local (in-theory (e/d (acl2::bytep) ()))))
  (if (endp charlist)
      nil
    (cons (char-code (car charlist))
          (charlist->bytes (cdr charlist))))
  ///
  (defret same-length-of-byte-and-character-lists
    (implies (character-listp charlist)
             (equal (len bl) (len charlist)))))

(define string->bytes ((str stringp))
  :short "Convert a string to a list of bytes."
  :returns (bl byte-listp :hyp :guard
               :hints (("Goal"
                        :in-theory (e/d () (str::coerce-to-list-removal)))))
  (charlist->bytes (coerce str 'LIST)))

(define bytes->string ((bytes byte-listp))
  :short "Convert a list of bytes to a string."
  :returns (str stringp :hyp :guard)
  (coerce (bytes->charlist bytes) 'STRING))

(define take-till-zero ((bytes byte-listp))
  :short "Return all initial elements of @('bytes') until a @('0')
  element is encountered or the end of @('bytes') is reached,
  whichever happens first."
  :returns (bs byte-listp :hyp :guard)
  (if (endp bytes)
      nil
    (if (equal (car bytes) 0)
        nil
      (cons (car bytes) (take-till-zero (cdr bytes))))))

;; ----------------------------------------------------------------------

(define merge-bytes ((bytes byte-listp))
  :short "Concatenates @('bytes') (least-significant byte appears
  first) to form a single natural number"
  :returns (merged natp :rule-classes :type-prescription)
  (bitops::merge-unsigneds 8 (acl2::reverse bytes))
  ///
  (local (in-theory (e/d () (unsigned-byte-p))))
  (defret width-of-<fn>
    (implies (and (<= (* 8 (len bytes)) m) (natp m))
             (unsigned-byte-p m merged))))

(define split-bytes ((n natp)
                     (bytes byte-listp))
  :short "Split @('bytes') into two lists, where first part has @('n') elements"
  :returns (mv (one byte-listp :hyp (byte-listp bytes))
               (two byte-listp :hyp (byte-listp bytes)))
  (b* ((rest (nthcdr n bytes))
       ((unless (<= n (len bytes)))
        (prog2$
         (raise "Not enough bytes to split into two by ~x0! (len bytes): ~x1" n (len bytes))
         (mv (make-list n :initial-element 0) rest)))
       (first (take n bytes)))
    (mv first rest))
  ///
  (defret len-of-mv-nth-0-<fn>
    (equal (len one) (nfix n)))

  (defret len-of-mv-nth-1-<fn>
    (equal (len two) (nfix (- (len bytes) (nfix n))))))

(define merge-first-split-bytes ((n natp)
                                 (bytes byte-listp))
  :short "Merge first @('n') bytes (least-significant byte first) from
  @('bytes'); return remaining bytes"
  :returns (mv (merged-num natp :rule-classes :type-prescription)
               (rest byte-listp :hyp (byte-listp bytes)))
  (b* (((mv first rest) (split-bytes n bytes)))
    (mv (merge-bytes first) rest))
  ///
  (local (in-theory (e/d () (unsigned-byte-p))))

  (defret width-of-mv-nth-0-<fn>
    (implies (and (equal m (* 8 n)) (natp n))
             (unsigned-byte-p m merged-num))
    :hints (("Goal" :do-not-induct t
             :use ((:instance len-of-mv-nth-0-split-bytes (n n) (bytes bytes))
                   (:instance width-of-merge-bytes
                              (m (* 8 n))
                              (bytes (mv-nth 0 (split-bytes n bytes)))))
             :in-theory (e/d ()
                             (len-of-mv-nth-0-split-bytes
                              width-of-merge-bytes)))))

  (defret len-of-mv-nth-1-<fn>
    (equal (len rest) (nfix (- (len bytes) (nfix n))))))

;; ----------------------------------------------------------------------
