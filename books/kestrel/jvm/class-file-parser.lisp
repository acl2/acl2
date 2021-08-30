; A parser for Java class files (passed in as sequences of bytes)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book parses the bytes representing a JVM class (e.g., from a .class
;; file) into an s-expression format (uses alists and lists).

;; See also read-and-parse-class-file.lisp, for a version that reads the bytes
;; from a file.

;; This tool operates in two steps: First we parse the bytes to create a
;; raw-parsed-class, then we create a class-info (and perhaps defconsts for
;; constant fields) from that.  The first step is separable from the second and
;; could be used for other purposes.

(include-book "kestrel/bv/bvcat2" :dir :system)
(include-book "floats")
(include-book "descriptors")
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(include-book "kestrel/lists-light/len-at-least" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "classes") ; this brings in defforall
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system)) ;for EQUAL-OF-BOOLEANS
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/lists-light/first-n-ac" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "kestrel/lists-light/last" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/alists-light/acons" :dir :system))
(local (include-book "kestrel/alists-light/strip-cars" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
;(local (include-book "kestrel/bv-lists/unsigned-byte-listp" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))

(local
 (defthm memberp-iff
   (iff (memberp a x)
        (member-equal a x))
   :hints (("Goal" :in-theory (enable memberp member-equal)))))

(local
 (defthm keyword-listp-forward-to-true-listp
   (implies (keyword-listp x)
            (true-listp x))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable keyword-listp)))))

(in-theory (disable true-listp))

(local
 (defthm symbolp-of-lookup-equal-when-symbol-listp-of-strip-cdrs
   (implies (symbol-listp (strip-cdrs alist))
            (symbolp (lookup-equal key alist)))
   :hints (("Goal" :in-theory (enable lookup-equal assoc-equal strip-cdrs)))))

(defthm equal-of-len-of-cdr-lemma
  (equal (equal (len (cdr bytes)) (len bytes))
         (atom bytes)))

;dup, except the guard
(defund map-code-char2 (codes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 codes)
                              (true-listp codes))
                  :guard-hints (("Goal" :in-theory (enable unsigned-byte-p)))
                  ))
  (if (endp codes)
      nil
    (cons (code-char (first codes))
          (map-code-char2 (rest codes)))))

(defthm character-listp-of-map-code-char2
  (character-listp (map-code-char2 code))
  :hints (("Goal" :in-theory (enable map-code-char2))))

;; (defthm character-listp-of-reverse-list
;;   (implies (character-listp l)
;;            (character-listp (reverse-list l)))
;;   :hints (("Goal" :in-theory (enable reverse-list))))

;; (defthm character-listp-of-substitute-ac
;;   (implies (and (characterp new)
;;                 (characterp old)
;;                 (character-listp seq)
;;                 (character-listp acc))
;;            (character-listp (substitute-ac new old seq acc))))

;; (defthm memberp-when-last-elem
;;   (implies (and (equal (last-elem x) a)
;;                 (or a
;;                     (consp x)))
;;            (memberp a x))
;;   :hints (("Goal" :in-theory (enable last-elem memberp))))

;; (defund check-field-infop (field-info)
;;   (declare (xargs :guard t))
;;   (if (not (jvm::field-infop field-info))
;;       (prog2$ (er hard? 'check-field-infop "Invalid field info: ~x0.~%" field-info)
;;               field-info)
;;     field-info))

;; (defund check-method-infop (method-info)
;;   (declare (xargs :guard t))
;;   (if (not (jvm::method-infop method-info))
;;       (prog2$ (er hard? 'check-method-infop "Invalid method info: ~x0.~%" method-info)
;;               method-info)
;;     method-info))

;acons key to val in alist except don't bother if val is nil.
(defund maybe-acons (key val alist)
  (declare (xargs :guard (alistp alist)))
  (if val
      (acons key val alist)
    alist))

(defthm alistp-of-maybe-acons
  (implies (alistp alist)
           (alistp (maybe-acons key val alist)))
  :hints (("Goal" :in-theory (enable maybe-acons))))

(defthm lookup-equal-of-maybe-acons
  (equal (lookup-equal key1 (maybe-acons key2 val alist))
         (if (equal key1 key2)
             (if val
                 val
               (lookup-equal key1 alist))
           (lookup-equal key1 alist)))
  :hints (("Goal" :in-theory (enable maybe-acons))))

(defthm strip-cars-of-maybe-acons
  (equal (strip-cars (maybe-acons key val alist))
         (if val
             (cons key (strip-cars alist))
           (strip-cars alist)))
  :hints (("Goal" :in-theory (enable maybe-acons))))

; helps in backchaining
;for termination of parse-fieldtype
(local
 (defthm if-hack-99
  (equal (< (if (< x y) y x) x)
         nil)))

;dup:
;(defforall all-unsigned-byte-p (size lst) (unsigned-byte-p size lst) :fixed size :declares ((type t size lst)))


;(local (in-theory (disable NTHCDR-OF-1)))

;(in-theory (disable decrement-positive-unsigned-byte)) ;yuck ;bad rule when applied to constants

(local
 (defthm cancel-hack
  (equal (< (+ a b c) c)
         (< (+ a b) 0))
  :hints (("Goal" :in-theory (enable)))))


;; FIXME What version of the JVM spec should we target?

;Notes:
;I tried having the book for a class include the books for all of the classes that it mentioned, but there seemed to be circularities.
;We now store only the direct superclass of a class, meaning we can don't have to parse class C's ancestors during (or before) the parsing of class C.

;Some of these functions could probably be in :logic mode instead?

;fixme - doesn't handle unicode (we assume all utf8 strings are just ascii!)

; might we need the constant pool if there are attributes that reference it and that we can't translate yet?

;now supports wide

;doesn't always translate all data in the class file (some numbers may need to be sign extended, some info from the instruction stream may need to be looked up) - maybe that sort of pre-processing is gross and the JVM model should just handle the constant pool, etc.
;May need to handle other attributes (but does handle local variable tables and line number tables).
;LDC (etc.) are currently handled differently from what m5 does - m5 returns a much smaller CP,reindexed...

;(in-theory (disable UNSIGNED-BYTE-P-RESOLVER)) ;trying
;(in-theory (disable UNSIGNED-BYTE-PROMOTE)) ;my rule is better?
;(in-theory (disable APPEND-TO-APP)) ;yuck! gone in ACL2 6.2

;; Returns an unsigned-byte-p 16
(defund 2bytes-to-int (highbyte lowbyte)
  (declare (type (unsigned-byte 8) highbyte lowbyte))
  (bvcat 8 highbyte 8 lowbyte))

(defthm unsigned-byte-p-of-2bytes-to-int
  (unsigned-byte-p 16 (2bytes-to-int highbyte lowbyte))
  :hints (("Goal" :in-theory (enable 2bytes-to-int))))

;; Returns an unsigned-byte-p 32
(defund 4bytes-to-int (highbyte highmidbyte lowmidbyte lowbyte)
  (declare (type (unsigned-byte 8) highbyte highmidbyte lowmidbyte lowbyte))
  (bvcat2 8 highbyte 8 highmidbyte 8 lowmidbyte 8 lowbyte)
  ;kill: (bvcat 24 (bvcat 16 (bvcat 8 highbyte 8 highmidbyte) 8 lowmidbyte) 8 lowbyte)
  )

;; Return (mv erp val remaining-bytes) where val is an unsigned-byte-p 8.
(defund readu1 (bytes)
  (declare (xargs :guard (all-unsigned-byte-p 8 bytes)))
  (if (consp bytes)
      (mv (erp-nil) (first bytes) (rest bytes))
    (mv :not-enough-bytes 0 nil)))

(defthm true-listp-of-mv-nth-2-of-readu1
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (readu1 bytes))))
  :hints (("Goal" :in-theory (enable readu1))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-readu1
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (readu1 bytes))))
  :hints (("Goal" :in-theory (enable readu1))))

(defthm natp-of-mv-nth-1-of-readu1
  (implies (all-unsigned-byte-p 8 bytes)
           (natp (mv-nth 1 (readu1 bytes))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable readu1))))

;; Returns (mv erp val remaining-bytes) where val is an unsigned-byte-p 16.
(defund readu2 (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes))))
  (if (consp (rest bytes))
      (mv (erp-nil)
          (2bytes-to-int (first bytes) (second bytes))
          (rest (rest bytes)))
    (mv :not-enough-bytes 0 nil)))

(defthm natp-of-mv-nth-1-of-readu2
  (natp (mv-nth 1 (readu2 bytes)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable readu2))))

(defthm unsigned-byte-p-of-mv-nth-1-of-readu2
  (unsigned-byte-p 16 (mv-nth 1 (readu2 bytes)))
  :hints (("Goal" :in-theory (enable readu2))))

(defthm true-listp-of-mv-nth-2-of-readu2
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (readu2 bytes))))
  :hints (("Goal" :in-theory (enable readu2))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-readu2
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (readu2 bytes))))
  :hints (("Goal" :in-theory (enable readu2))))

(defthm len-of-mv-nth-2-of-readu2
  (implies (not (mv-nth 0 (readu2 bytes)))
           (equal (len (mv-nth 2 (readu2 bytes)))
                  (+ -2 (len bytes))))
  :hints (("Goal" :in-theory (enable readu2))))

;; Returns (mv erp val remaining-bytes) where val is an unsigned-byte-p 32.
(defund readu4 (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes))))
  (if (consp (rest (rest (rest bytes))))
      (mv (erp-nil)
          (4bytes-to-int (first bytes) (second bytes) (third bytes) (fourth bytes))
          (rest (rest (rest (rest bytes)))))
    (mv :not-enough-bytes 0 nil)))

(defthm natp-of-mv-nth-1-of-readu4
  (natp (mv-nth 1 (readu4 bytes)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable readu4))))

(defthm true-listp-of-mv-nth-2-of-readu4
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (readu4 bytes))))
  :hints (("Goal" :in-theory (enable readu4))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-readu4
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (readu4 bytes))))
  :hints (("Goal" :in-theory (enable readu4))))

(defthm len-of-mv-nth-2-of-readu4
  (implies (not (mv-nth 0 (readu4 bytes)))
           (equal (len (mv-nth 2 (readu4 bytes)))
                  (+ -4 (len bytes))))
  :hints (("Goal" :in-theory (enable readu4))))

;; Returns (mv erp val remaining-bytes) where val is an signed-byte-p 32.
(defund read-signed-4-byte-quantity (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes))))
  (b* (((mv erp u4 bytes) (readu4 bytes))
       ((when erp) (mv erp 0 nil)))
    (mv (erp-nil)
        (logext 32 u4)
        bytes)))

(defthm true-listp-of-mv-nth-2-of-read-signed-4-byte-quantity
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (read-signed-4-byte-quantity bytes))))
  :hints (("Goal" :in-theory (enable read-signed-4-byte-quantity))))

(defthm integerp-of-mv-nth-1-of-read-signed-4-byte-quantity
  (integerp (mv-nth 1 (read-signed-4-byte-quantity bytes)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-signed-4-byte-quantity))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-read-signed-4-byte-quantity
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (read-signed-4-byte-quantity bytes))))
  :hints (("Goal" :in-theory (enable read-signed-4-byte-quantity))))

;; Returns (mv erp n-bytes remaining-bytes).
(defund readnbytes (n bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (natp n))))
  (if (len-at-least n bytes)
      (mv (erp-nil) (firstn n bytes) (nthcdr n bytes))
    (mv :not-enough-bytes nil nil)))

(defthm true-listp-of-mv-nth-1-of-readnbytes
  (true-listp (mv-nth 1 (readnbytes n bytes)))
  :hints (("Goal" :in-theory (enable readnbytes))))

(defthm all-unsigned-byte-p-8-of-mv-nth-1-of-readnbytes
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 1 (readnbytes n bytes))))
  :hints (("Goal" :in-theory (enable readnbytes))))

(defthm true-listp-of-mv-nth-2-of-readnbytes
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (readnbytes n bytes))))
  :hints (("Goal" :in-theory (enable readnbytes))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-readnbytes
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (readnbytes n bytes))))
  :hints (("Goal" :in-theory (enable readnbytes))))

(defthm readnbytes-len-bound
  (<= (len (mv-nth 2 (readnbytes n bytes)))
      (len bytes))
  :hints (("Goal" :in-theory (enable readnbytes)))
  :rule-classes (:linear))

;; Returns (mv erp u2s remaining-bytes).
(defund readu2s (number-of-u2s bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (natp number-of-u2s))
                  :guard-hints (("Goal" :in-theory (enable readu2)))))
  (if (zp number-of-u2s)
      (mv (erp-nil) nil bytes)
    (b* (((mv erp val bytes) (readu2 bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp rest bytes) (readu2s (+ -1 number-of-u2s) bytes))
         ((when erp) (mv erp nil nil)))
      (mv (erp-nil)
          (cons val rest)
          bytes))))

;; ;move?
;; (local
;;  (defthm NAT-LISTP-when-ALL-UNSIGNED-BYTE-P
;;    (IMPLIES (AND (ALL-UNSIGNED-BYTE-P 8 BYTES)
;;                  (TRUE-LISTP BYTES))
;;             (NAT-LISTP BYTES))
;;    :hints (("Goal" :in-theory (enable nat-listp all-unsigned-byte-p)))))

(defthm nat-listp-of-mv-nth-1-of-readu2s
  (nat-listp (mv-nth 1 (readu2s number-of-u2s bytes)))
  :hints (("Goal" :in-theory (enable readu2s))))

(defthm true-listp-of-mv-nth-2-of-readu2s
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (readu2s number-of-u2s bytes))))
  :hints (("Goal" :in-theory (enable readu2s))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-readu2s
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (readu2s number-of-u2s bytes))))
  :hints (("Goal" :in-theory (enable readu2s))))

;; Returns (mv erp u4s remaining-bytes).
(defund readu4s (number-of-u4s bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (natp number-of-u4s))
                  :guard-hints (("Goal" :in-theory (enable readu4)))))
  (if (zp number-of-u4s)
      (mv (erp-nil) nil bytes)
    (b* (((mv erp val bytes) (readu4 bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp rest bytes) (readu4s (+ -1 number-of-u4s) bytes))
         ((when erp) (mv erp nil nil))
         )
      (mv (erp-nil)
          (cons val rest)
          bytes))))

;; Returns (mv erp vals remaining-bytes).
(defund read-signed-4-byte-quantities (number-of-quantities bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (natp number-of-quantities)
                              )
                  :guard-hints (("Goal" :in-theory (enable readu4)))))
  (if (zp number-of-quantities)
      (mv (erp-nil) nil bytes)
    (b* (((mv erp val bytes) (read-signed-4-byte-quantity bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp rest bytes) (read-signed-4-byte-quantities (+ -1 number-of-quantities) bytes))
         ((when erp) (mv erp nil nil)))
      (mv (erp-nil)
          (cons val rest)
          bytes))))

(defthm true-listp-of-mv-nth-1-of-read-signed-4-byte-quantities
  (true-listp (mv-nth 1 (read-signed-4-byte-quantities number-of-quantities bytes)))
  :hints (("Goal" :in-theory (enable read-signed-4-byte-quantities))))

(defthm true-listp-of-mv-nth-2-of-read-signed-4-byte-quantities
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (read-signed-4-byte-quantities number-of-quantities bytes))))
  :hints (("Goal" :in-theory (enable read-signed-4-byte-quantities))))

;FFIXME this doesn't handle utf8's that aren't ascii compliant!
(defund bytelist-to-string (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes))))
  (coerce (map-code-char2 bytes) 'string))

(defund turn-slashes-into-dots-chars (chars)
  (declare (xargs :guard (character-listp chars)))
  (substitute #\. #\/ chars))

(defthm character-listp-of-turn-slashes-into-dots-chars
  (implies (character-listp chars)
           (character-listp (turn-slashes-into-dots-chars chars)))
  :hints (("Goal" :in-theory (enable turn-slashes-into-dots-chars))))

(defund turn-slashes-into-dots (str)
  (declare (xargs :guard (stringp str)))
  (substitute #\. #\/ str))

(defthm stringp-of-turn-slashes-into-dots
  (implies (stringp str)
           (stringp (turn-slashes-into-dots str)))
  :hints (("Goal" :in-theory (enable turn-slashes-into-dots))))

;(in-theory (disable STR::COERCE-TO-LIST-REMOVAL STR::COERCE-TO-STRING-REMOVAL)) ;todo new

;; (defthm equal-of-length-and-0
;;   (IMPLIES (stringp str) ;backchain limit? ;gen
;;            (equal (EQUAL (LENGTH STR) 0)
;;                   (equal str "")))
;;   :hints (("Goal" :in-theory (enable length))))

;; (defthm length-of-subseq-suffix ;gen
;;   (implies (and (posp start)
;;                 (not (equal str ""))
;;                 (stringp str))
;;            (< (length (subseq str start (length str)))
;;               (length str)))
;;   :hints (("Goal" :in-theory (enable subseq length))))

;; (defthm val1-of-READTHROUGHTERMINATOR-AUX
;;   (IMPLIES (and ;(MEMBERP #\; chars)
;;         ;        (character-listp chars)
;;                 )
;;            (EQUAL (MV-NTH 1 (READTHROUGHTERMINATOR-AUX chars #\;))
;;                   (DISCARD-UP-THROUGH-FIRST-MATCH #\; chars)))
;;   :hints (("Goal" :in-theory (enable READTHROUGHTERMINATOR-AUX DISCARD-UP-THROUGH-FIRST-MATCH))))

;; ;todo: move to library
;; ;is this needed?
;; (defun string-length (str)
;;   (declare (type string str))
;;   (mbe :exec (length str)
;;        :logic (len (coerce str 'list))))

;; (defthm string-of-mv-nth-1-of-READTHROUGHTERMINATOR
;;   (STRINGP (MV-NTH 1 (READTHROUGHTERMINATOR str char)))
;;   :hints (("Goal" :in-theory (enable READTHROUGHTERMINATOR))))

;; (defun unparse-descriptor (item)
;;   (if (equal :byte item)
;;       "B"
;;     (if (equal :char item)
;;         "C"
;;       (if (equal :double item)
;;           "D"
;;         (if (equal :float item)
;;             "F"
;;           (if (equal :int item)
;;               "I"
;;             (if (equal :long item)
;;                 "J"
;;               (if (equal :short item)
;;                   "S"
;;                 (if (equal :boolean item)
;;                     "Z"
;;                   (if (and (consp item)
;;                            (equal :array (car item)))
;;                       (string-append "[" (unparse-descriptor (cadr item)))
;;                     (if (and (consp item)
;;                              (equal :reference (car item))) test stringp - :reference is deprecated
;;                         (concatenate 'string
;;                                      "L"
;;                                      (cadr item) ;should be a string
;;                                      ";")
;;                       (er hard? 'unparse-descriptor "Trying to unparse the unrecognized signature item ~x0." item))))))))))))

;; ;drop?
;; (defun unparse-descriptors (signature)
;;   (if (endp signature)
;;       ""
;;     (string-append (unparse-descriptor (car signature))
;;                    (unparse-descriptors (cdr signature)))))

;; (thm
;;  (implies (stringp str)
;;           (equal (EQUAL (LENGTH STR) 0)
;;                  (equal str "")))
;;  :hints (("Goal" :in-theory (enable length))))

;; (defthm equal-of-string-length-and-0
;;   (implies (stringp str)
;;            (equal (equal (string-length str) 0)
;;                   (equal str "")))
;;   :hints (("Goal" :in-theory (enable string-length))))

;; (defthm string-length-of-coerce
;;   (implies (character-listp chars)
;;            (equal (string-length (coerce chars 'string))
;;                   (len chars)))
;;   :hints (("Goal" :in-theory (enable string-length))))

;; (defthm string-length-of-mv-nth-1-of-readthroughterminator-bound
;;   (<= (string-length (mv-nth 1 (readthroughterminator str terminator)))
;;       (string-length str))
;;   :hints (("Goal" :in-theory (enable readthroughterminator string-length))))

;fixme reconcile these notions with descriptorp

;(in-theory (disable string-length)) ;fixme

;; (defthm mv-nth-1-of-readthroughterminator-aux
;;   (implies (and (memberp terminator chars)
;;                 (character-listp chars)
;; ;                (characterp terminator)
;;                 )
;;            (equal (mv-nth 1 (readthroughterminator-aux chars terminator))
;;                   (nthcdr (+ 1 (position-equal terminator chars)) chars)))
;;   :hints (("Goal" :in-theory (e/d (readthroughterminator-aux position-equal POSITION-EQUAL2
;;                                                              ) (;memberp
;;                                                                 nthcdr)))))

;; (defthm equal-of-coerce-string-and-coerce-string
;;   (implies (and (character-listp chars1)
;;                 (character-listp chars2))
;;            (equal (equal (coerce chars1 'string) (coerce chars2 'string))
;;                   (equal chars1 chars2)))
;;   :hints (("Goal" :in-theory (disable coerce-inverse-1-forced coerce-inverse-1)
;;            :use ((:instance coerce-inverse-1 (x chars1))
;;                  (:instance coerce-inverse-1 (x chars2))))))

;string version of nthcdr

;; (defun strnthcdr (n str)
;;   (declare (xargs :guard (and (natp n)
;;                               (stringp str))))
;;   (coerce (nthcdr n (coerce str 'list)) 'string))

;; (defthm mv-nth-1-of-readthroughterminator
;;   (implies (and (memberp terminator (coerce str 'list))
;;                 (stringp str))
;;            (equal (mv-nth 1 (readthroughterminator str terminator))
;;                   (strnthcdr (+ 1 (position-equal terminator str)) str)))
;;   :hints (("Goal"
;;            :use (:instance take-does-nothing (n  (+ -1 (len (coerce str 'list))
;;                                                         (- (position-equal2 terminator (coerce str 'list)))))
;;                            (lst (nthcdr (position-equal2 terminator (coerce str 'list))
;;                                         (coerce str 'list))))
;;            :in-theory (e/d (readthroughterminator subseq position-equal)
;;                            (len-of-coerce-of-strcdr ;looped
;;                             take-does-nothing
;;                             )))))

;; (defthm member-of-cdr-when-not-car
;;   (implies (not (equal item (car lst)))
;;            (equal (MEMBERP item (cdr lst))
;;                   (MEMBERP item lst))))

;; ;fixme slow?
;; (defthm memberp-when-equal-car-last
;;   (IMPLIES (AND (CONSP CHARS)
;;                 (EQUAL (CAR (LAST (CDR CHARS))) #\;))
;;            (MEMBERP #\; CHARS))
;;   :hints (("Goal" :in-theory (enable memberp last))))

;; The order here matches "Table 4.4-A. Constant pool tags (by section)"
(defconst *CONSTANT_Class* 7)
(defconst *CONSTANT_Fieldref* 9)
(defconst *CONSTANT_Methodref* 10)
(defconst *CONSTANT_InterfaceMethodref* 11)
(defconst *CONSTANT_String* 8)
(defconst *CONSTANT_Integer* 3)
(defconst *CONSTANT_Float* 4)
(defconst *CONSTANT_Long* 5)
(defconst *CONSTANT_Double* 6)
(defconst *CONSTANT_NameAndType* 12)
(defconst *CONSTANT_Utf8* 1)
(defconst *CONSTANT_MethodHandle* 15)
(defconst *CONSTANT_MethodType* 16)
(defconst *CONSTANT_Dynamic* 17)
(defconst *CONSTANT_InvokeDynamic* 18)
(defconst *CONSTANT_Module* 19)
(defconst *CONSTANT_Package* 20)

;; TODO: Add more checks
(defund constant-pool-entryp (entry)
  (declare (xargs :guard t))
  (or (null entry) ; still a symbol-alist
      (and (symbol-alistp entry)
           (let ((tag (lookup-eq 'tag entry)))
             (and (symbolp tag)
                  (cond
                   ((eq tag :constant-class)
                    (and (natp (lookup-eq 'name_index entry))))
                   (t t ;todo: switch to nil when we've covered all cases
                      ))
                  ))
           )))

(defthm constant-pool-entryp-forward-to-alistp
  (implies (constant-pool-entryp entry)
           (alistp entry))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable constant-pool-entryp))))

;; Introduces constant-poolp
;; TODO: Also introduce an invaraint over the constant pool, saying that the information in it is well-typed.
(defstobj constant-pool
  (entries :type (array (satisfies constant-pool-entryp) (0)) ; initially empty
           :initially nil
           :resizable t))

(in-theory (disable update-entriesi entriesi entriesp entries-length constant-poolp resize-entries))

(defthm entriesp-of-update-nth
  (implies (and (entriesp entries)
                (natp n)
                (< n (len entries))
                (constant-pool-entryp val))
           (entriesp (update-nth n val entries)))
  :hints (("Goal" :in-theory (enable entriesp update-nth))))

(defthm alistp-of-nth-when-entriesp
  (implies (and (entriesp entries)
                (natp n)
                (< n (len entries)))
           (alistp (nth n entries)))
  :hints (("Goal" :in-theory (e/d (entriesp nth) (NTH-OF-CDR)))))

(defthm entries-length-of-update-entriesi
  (implies (and (natp index)
                (force (< index (entries-length constant-pool))))
           (equal (entries-length (update-entriesi index val constant-pool))
                  (entries-length constant-pool)))
  :hints (("Goal" :in-theory (enable entries-length update-entriesi))))

(defthm entries-length-of-resize-entries
  (implies (natp len)
           (equal (entries-length (resize-entries len constant-pool))
                  len))
  :hints (("Goal" :in-theory (enable entries-length resize-entries))))

(defthm entriesp-of-nth-when-constant-poolp
  (implies (constant-poolp constant-pool)
           (entriesp (nth *entriesi* constant-pool)))
  :hints (("Goal" :in-theory (enable constant-poolp))))

(defthm alistp-of-entriesi
  (implies (and (natp index)
                (force (< index (entries-length constant-pool)))
                (constant-poolp constant-pool))
           (alistp (entriesi index constant-pool)))
  :hints (("Goal" :in-theory (enable entries-length entriesi))))

(defthm constant-poolp-of-update-entriesi
  (implies (and (natp index)
                (< index (entries-length constant-pool))
                (constant-pool-entryp val)
                (constant-poolp constant-pool))
           (constant-poolp (update-entriesi index val constant-pool)))
  :hints (("Goal" :in-theory (e/d (entries-length update-entriesi constant-poolp entriesp)
                                  ()))))


;; (defthmd alistp-of-lookup-equal-when-constant-poolp
;;   (implies (constant-poolp cp)
;;            (alistp (lookup-equal key cp)))
;;   :hints (("Goal" :in-theory (enable constant-poolp lookup-equal))))

;; (local (in-theory (enable alistp-of-lookup-equal-when-constant-poolp)))

;; ;todo: expensive?
;; (defthmd alistp-when-constant-poolp
;;   (implies (constant-poolp cp)
;;            (alistp cp))
;;   :hints (("Goal" :in-theory (enable constant-poolp))))

;; (local (in-theory (enable alistp-when-constant-poolp)))

;; (defthmd eqlable-alistp-when-constant-poolp
;;   (implies (constant-poolp cp)
;;            (eqlable-alistp cp))
;;   :hints (("Goal" :in-theory (enable constant-poolp))))

;; (local (in-theory (enable eqlable-alistp-when-constant-poolp)))

;; TODO: Avoid setting the 'tag entries here that we never check:
;returns (mv erp entryinfo numentries bytes)
;numentries is the number of entries accounted for by the call to this function (constants of type double and long take two entries, other things take 1)
;; TODO: Some of the 'tags here are not used, so we don't need to cons them on
(defund parse-constant-pool-entry (bytes)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes))))
  (b* (((mv erp tag bytes) (readu1 bytes))
       ((when erp) (mv erp nil 0 bytes)))
    (cond ((= tag *CONSTANT_Class*) ;todo: use case?
           (b* (((mv erp name_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'name_index name_index
                        (acons 'tag :CONSTANT_Class nil))
                 1
                 bytes)))
          ((= tag *CONSTANT_Fieldref*)
           (b* (((mv erp class_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp name_and_type_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'class_index class_index
                        (acons 'name_and_type_index name_and_type_index
                               (acons 'tag :CONSTANT_Fieldref nil)))
                 1
                 bytes)))
          ((= tag *CONSTANT_Methodref*)
           (b* (((mv erp class_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp name_and_type_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'class_index class_index
                        (acons 'name_and_type_index name_and_type_index
                               (acons 'tag :CONSTANT_Methodref nil)))
                 1
                 bytes)))
          ((= tag *CONSTANT_InterfaceMethodref*)
           (b* (((mv erp class_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp name_and_type_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'class_index class_index
                        (acons 'name_and_type_index name_and_type_index
                               (acons 'tag :CONSTANT_InterfaceMethodref nil)))
                 1
                 bytes)))
          ((= tag *CONSTANT_String*)
           (b* (((mv erp string_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'string_index string_index (acons 'tag :CONSTANT_String nil))
                 1
                 bytes)))
          ((= tag *CONSTANT_Integer*)
           (b* (((mv erp val bytes) (readu4 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             ;; The integer is stored as a bit vector
             (mv (erp-nil)
                 (acons 'bytes val
                        (acons 'tag :CONSTANT_Integer nil))
                 1
                 bytes)))
          ((= tag *CONSTANT_Float*)
           (b* (((mv erp val bytes) (readu4 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil) (acons 'bytes val (acons 'tag :CONSTANT_Float nil))
                 1
                 bytes)))
          ((= tag *CONSTANT_Long*)
           (b* (((mv erp high_bytes bytes) (readu4 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp low_bytes bytes) (readu4 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             ;;we used to store high and low bytes separately
             (mv (erp-nil)
                 (acons 'bytes (bvcat 32 high_bytes 32 low_bytes)
                        (acons 'tag :CONSTANT_Long nil))
                 2 ;note that long constants take two entries
                 bytes)))
          ((= tag *CONSTANT_Double*)
           (b* (((mv erp high_bytes bytes) (readu4 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp low_bytes bytes) (readu4 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'bytes (bvcat 32 high_bytes 32 low_bytes)
                        (acons 'tag :CONSTANT_Double nil))
                 2 ;note that double constants take two entries
                 bytes)))
          ((= tag *CONSTANT_NameAndType*)
           (b* (((mv erp name_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp descriptor_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'name_index name_index
                        (acons 'descriptor_index descriptor_index
                               (acons 'tag :CONSTANT_NameAndType nil)))
                 1
                 bytes)))
          ((= tag *CONSTANT_Utf8*)
           (b* (((mv erp length bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp val bytes) (readnbytes length bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv
              (erp-nil)
              (acons 'bytes ;todo: bytes is a bad name for this
                     ;; TODO: In some cases (e.g., for descriptors) we might rather have chars here than a string
                     (bytelist-to-string val) ;FFFFIXME doesn't handle non-ascii - add unicode support!  ;fixme: just turn this into a char-list?  since often this just gets unstringified anyway((when erp) (mv erp nil 0 bytes)).
                     (acons 'tag :CONSTANT_Utf8 nil))
              1
              bytes)))
          ((= tag *CONSTANT_MethodHandle*)
           (b* (((mv erp reference_kind bytes) (readu1 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp reference_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'reference_kind reference_kind
                        (acons 'reference_index reference_index
                               (acons 'tag :CONSTANT_MethodHandle nil)))
                 1
                 bytes)))
          ((= tag *CONSTANT_MethodType*)
           (b* (((mv erp descriptor_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes))
                )
             (mv (erp-nil)
                 (acons 'descriptor_index descriptor_index
                        (acons 'tag :CONSTANT_MethodType nil))
                 1
                 bytes)))
          ((= tag *CONSTANT_Dynamic*)
           (b* (((mv erp bootstrap_method_attr_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp name_and_type_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'bootstrap_method_attr_index bootstrap_method_attr_index
                        (acons 'name_and_type_index name_and_type_index
                               (acons 'tag :CONSTANT_Dynamic nil)))
                 1
                 bytes)))
          ((= tag *CONSTANT_InvokeDynamic*)
           (b* (((mv erp bootstrap_method_attr_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes))
                ((mv erp name_and_type_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'bootstrap_method_attr_index bootstrap_method_attr_index
                        (acons 'name_and_type_index name_and_type_index
                               (acons 'tag :CONSTANT_InvokeDynamic nil)))
                 1
                 bytes)))
          ;; only allowed for classes with the ACC_MODULE attribute (we could check for that):
          ((= tag *CONSTANT_Module*)
           (b* (((mv erp name_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'name_index name_index
                        (acons 'tag :CONSTANT_Module nil))
                 1
                 bytes)))
          ;; only allowed for classes with the ACC_MODULE attribute (we could check for that):
          ((= tag *CONSTANT_Package*)
           (b* (((mv erp name_index bytes) (readu2 bytes))
                ((when erp) (mv erp nil 0 bytes)))
             (mv (erp-nil)
                 (acons 'name_index name_index
                        (acons 'tag :CONSTANT_Package nil))
                 1
                 bytes)))
          (t (prog2$
              (er hard? 'parse-constant-pool-entry "Found an unknown tag, ~x0, for a constant pool entry" tag)
              (mv :unknown-tag nil 0 bytes))))))

(defthm posp-of-mv-nth-2-of-parse-constant-pool-entry
  (implies (not (mv-nth 0 (parse-constant-pool-entry bytes)))
           (posp (mv-nth 2 (parse-constant-pool-entry bytes))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-constant-pool-entry))))

(defthm alistp-of-mv-nth-1-of-parse-constant-pool-entry
  (alistp (mv-nth 1 (parse-constant-pool-entry bytes)))
  :hints (("Goal" :in-theory (enable parse-constant-pool-entry))))

(defthm true-listp-of-mv-nth-3-of-parse-constant-pool-entry
  (implies (true-listp bytes)
           (true-listp (mv-nth 3 (parse-constant-pool-entry bytes))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-constant-pool-entry))))

(defthm all-unsigned-byte-p-8-of-nth-3-of-parse-constant-pool-entry
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 3 (parse-constant-pool-entry bytes))))
  :hints (("Goal" :in-theory (enable parse-constant-pool-entry))))

(defthm constant-pool-entryp-of-mv-nth-1-of-parse-constant-pool-entry
  (implies (not (mv-nth 0 (parse-constant-pool-entry bytes)))
           (constant-pool-entryp (mv-nth 1 (parse-constant-pool-entry bytes))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable parse-constant-pool-entry
                                     constant-pool-entryp))))

;; Returns (mv erp constant-pool bytes-remaining).
;; acc accumulates info on the entries.
;; The result is in reverse order by entry number, but that shouldn't matter
;; since each entry is looked up by number.
(defund parse-constant-pool-entries (index
                                     max-index
                                     bytes
                                     constant-pool)
  (declare (xargs :measure (nfix (+ 1 (- max-index index)))
                  :guard (and (posp index)
                              (natp max-index)
                              (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (< max-index (entries-length constant-pool)))
                  :stobjs constant-pool))
  (if (or (not (mbt (and (natp index)
                         (natp max-index))))
          (< max-index index))
      (mv (erp-nil) constant-pool bytes)
    (b* (((mv erp entry numentries bytes) (parse-constant-pool-entry bytes))
         ((when erp) (mv erp constant-pool nil))
         ((when (< max-index (+ -1 index numentries)))
          (mv :too-many-cp-entries-consumed constant-pool nil))
         (constant-pool (update-entriesi index entry constant-pool)))
      (progn$
       ;; (cw "Constant pool entry number ~x0 is: ~x1.~%" (+ 1 totalentries (- entriesleft)) entry)
       (parse-constant-pool-entries (+ numentries index)
                                    max-index
                                    bytes
                                    constant-pool)))))

(defthm true-listp-of-mv-nth-2-of-parse-constant-pool-entries
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (parse-constant-pool-entries index max-index bytes acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable parse-constant-pool-entries))))

(defthm all-unsigned-byte-p-8-of-nth-2-of-parse-constant-pool-entries
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (parse-constant-pool-entries index max-index bytes acc))))
  :hints (("Goal" :in-theory (enable parse-constant-pool-entries))))

(defthm entries-length-of-nth-1-of-parse-constant-pool-entries
  (implies (and (not (mv-nth 0 (parse-constant-pool-entries index max-index bytes constant-pool)))
                (natp index)
                (natp max-index)
                (< max-index (entries-length constant-pool))
;                (<= index max-index)
                (constant-poolp constant-pool))
           (equal (entries-length (mv-nth 1 (parse-constant-pool-entries index max-index bytes constant-pool)))
                  (entries-length constant-pool)))
  :hints (("Goal" :expand (PARSE-CONSTANT-POOL-ENTRIES INDEX INDEX BYTES CONSTANT-POOL)
           :in-theory (enable parse-constant-pool-entries))))

(defthm constant-poolp-of-nth-1-of-parse-constant-pool-entries
  (implies (and (natp index)
                (natp max-index)
                (< max-index (entries-length constant-pool))
;                (<= index max-index)
                (constant-poolp constant-pool))
           (constant-poolp (mv-nth 1 (parse-constant-pool-entries index max-index bytes constant-pool))))
  :hints (("Goal" :in-theory (enable parse-constant-pool-entries))))

(defund getarraytype (int)
  (declare (xargs :guard (natp int)))
  (cond ((= int 4)  :boolean)
        ((= int 5)  :char)
        ((= int 6)  :float)
        ((= int 7)  :double)
        ((= int 8)  :byte)
        ((= int 9)  :short)
        ((= int 10) :int)
        ((= int 11) :long)
        (t (er hard? 'getarraytype "Found a call to newarray with an unrecognized array type."))))

;; Parse a class name as it appears in a symbolic reference to a class.  Array
;; classes have a different representation than normal classes/interfaces.  See
;; JVMS 5.1 (The Run-Time Constant Pool).
;; Returns (mv erp parsed-class-name).
(defund parse-class-name (str)
  (declare (xargs :guard (stringp str)))
  (if (= 0 (length str))
      (prog2$ (er hard? 'parse-class-name "Empty class name encountered.")
              (mv :empty-class-name nil))
    ;; Now check whether it is an array class:
    (let* ((firstchar (char str 0)))
      (if (eql firstchar #\[)
          ;; It is an array class, so it must be a descriptor:
          (jvm::parse-descriptor str)
        ;; A non-array class/interface name.  Does not start with L and end in
        ;; semicolon, but does have slashes that must be turned into dots:
        (mv (erp-nil)
            (turn-slashes-into-dots str))))))

;todo: it might be a parsed array class name!
;; (defthm class-namep-of-mv-nth-1-of-parse-class-name
;;   (implies (not (mv-nth 0 (parse-class-name str)))
;;            (jvm::class-namep (mv-nth 1 (parse-class-name str))))
;;   :hints (("Goal" :in-theory (enable parse-class-name))))

;; Returns (mv erp entry).
(defund lookup-in-constant-pool (index constant-pool)
  (declare (xargs :guard (natp index)
                  :stobjs constant-pool))
  (if (not (< index (entries-length constant-pool)))
      (mv `(:bad-cp-index ,index) nil)
    (mv (erp-nil) (entriesi index constant-pool))))

(defthm alistp-of-mv-nth-1-of-lookup-in-constant-pool
  (implies (and (constant-poolp constant-pool)
                (natp index))
           (alistp (mv-nth 1 (lookup-in-constant-pool index constant-pool))))
  :hints (("Goal" :in-theory (enable lookup-in-constant-pool))))

;; Returns (mv erp res).
;; Returns a reference-typep.  This can sometimes be an array type.
(defund get-class-name-from-src (symbolic-reference-to-class constant-pool)
  (declare (xargs :guard (and (natp symbolic-reference-to-class)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp cp-entry) (lookup-in-constant-pool symbolic-reference-to-class constant-pool))
       ((when erp) (mv erp nil))
       (name_index (lookup-eq-safe 'name_index cp-entry))
       ((mv erp class-name-entry) (lookup-in-constant-pool (nfix name_index) constant-pool)) ;todo: drop the nfix
       ((when erp) (mv erp nil))
       (class-name (lookup-eq-safe 'bytes class-name-entry))
       ((when (not (stringp class-name)))
        (er hard? 'get-class-name-from-src "Bad string.")
        (mv :bad-string nil))
       ((mv erp parsed-class-name) (parse-class-name class-name))
       ((when erp) (mv erp nil)))
    (mv (erp-nil) parsed-class-name)))

;; not true if array class?
;; (defthm class-namep-of-mv-nth-1-of-get-class-name-from-src
;;   (implies (not (mv-nth 0 (get-class-name-from-src symbolic-reference-to-class constant-pool)))
;;            (jvm::class-namep (mv-nth 1 (get-class-name-from-src symbolic-reference-to-class constant-pool))))
;;   :hints (("Goal" :in-theory (enable get-class-name-from-src))))

;; Returns (mv erp res).
;fixme does this handle symbolic refs to interfaces also?
(defund get-class-names-from-srcs (symbolic-reference-to-class-lst constant-pool)
  (declare (xargs :guard (nat-listp symbolic-reference-to-class-lst)
                  :stobjs constant-pool))
  (if (atom symbolic-reference-to-class-lst)
      (mv (erp-nil) nil)
    (b* (((mv erp res1) (get-class-name-from-src (car symbolic-reference-to-class-lst) constant-pool))
         ((when erp) (mv erp nil))
         ((mv erp res2) (get-class-names-from-srcs (cdr symbolic-reference-to-class-lst) constant-pool))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons res1 res2)))))

(defthm true-listp-of-mv-nth-1-of-get-class-names-from-srcs
  (true-listp (mv-nth 1 (get-class-names-from-srcs symbolic-reference-to-class-lst constant-pool)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable get-class-names-from-srcs))))

;; (defthm all-class-namesp-of-mv-nth-1-of-get-class-names-from-srcs
;;   (implies (not (mv-nth 0 (get-class-names-from-srcs symbolic-reference-to-class-lst constant-pool)))
;;            (JVM::ALL-CLASS-NAMESP (mv-nth 1 (get-class-names-from-srcs symbolic-reference-to-class-lst constant-pool))))
;;   :hints (("Goal" :in-theory (enable get-class-names-from-srcs))))

;; Returns (mv erp class-name field-name descriptor).
(defund get-info-from-srf (index constant-pool)
  (declare (xargs :guard (and (natp index)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp srf) (lookup-in-constant-pool index constant-pool))
       ((when erp) (mv erp nil nil nil))
       (class_index (lookup-eq-safe 'class_index srf))
       ((when (not (natp class_index)))
        (er hard? 'get-info-from-srf "Bad index for class: ~x0." class_index)
        (mv :bad-index-for-class nil nil nil))
       ((mv erp class-type) (get-class-name-from-src class_index constant-pool))
       ((when erp) (mv erp nil nil nil))
       ((when (not (jvm::class-or-interface-namep class-type)))
        (er hard? 'get-info-from-srf "Surprised to see an array class, ~x0, in an SRF." class-type)
        (mv :unexpected-array-class nil nil nil))
       (name_and_type_index (nfix (lookup-eq-safe 'name_and_type_index srf)))
       ((mv erp name_and_type) (lookup-in-constant-pool name_and_type_index constant-pool))
       ((when erp) (mv erp nil nil nil))
       (name_index (nfix (lookup-eq-safe 'name_index name_and_type)))
       ((mv erp field-name-entry) (lookup-in-constant-pool name_index constant-pool))
       ((when erp) (mv erp nil nil nil))
       (field-name (lookup-eq-safe 'bytes field-name-entry))
       (descriptor_index (nfix (lookup-eq-safe 'descriptor_index name_and_type)))
       ((mv erp field-descriptor-entry) (lookup-in-constant-pool descriptor_index constant-pool))
       ((when erp) (mv erp nil nil nil))
       (field-descriptor (lookup-eq-safe 'bytes field-descriptor-entry)))
    (mv (erp-nil) class-type field-name field-descriptor)))

;; Returns (mv erp class-name method-name method-descriptor param-types interfacep)
;; The class-name returned is a reference-typep (sometimes be an array type).
(defund get-info-from-srm (index constant-pool)
  (declare (xargs :guard (and (natp index)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp srm) (lookup-in-constant-pool index constant-pool))
       ((when erp) (mv erp nil nil nil nil nil))
       (class_index (lookup-eq-safe 'class_index srm))
       (name_and_type_index (nfix (lookup-eq-safe 'name_and_type_index srm)))
       (tag (lookup-eq-safe 'tag srm))

       ((when (not (natp class_index)))
        (er hard? 'get-class-name-from-srm "Bad index for class: ~x0." class_index)
        (mv :bad-index-for-class nil nil nil nil nil))
       ((mv erp class-name) (get-class-name-from-src class_index constant-pool))
       ((when erp) (mv erp nil nil nil nil nil))
       ((mv erp name_and_type) (lookup-in-constant-pool name_and_type_index constant-pool))
       ((when erp) (mv erp nil nil nil nil nil))
       (name_index (nfix (lookup-eq-safe 'name_index name_and_type)))
       ((mv erp method-name-entry) (lookup-in-constant-pool name_index constant-pool))
       ((when erp) (mv erp nil nil nil nil nil))
       (method-name (lookup-eq-safe 'bytes method-name-entry))
       (descriptor_index (nfix (lookup-eq-safe 'descriptor_index name_and_type)))
       ((mv erp method-descriptor-entry) (lookup-in-constant-pool descriptor_index constant-pool))
       ((when erp) (mv erp nil nil nil nil nil))
       (method-descriptor (lookup-eq-safe 'bytes method-descriptor-entry))
       ((when (not (stringp method-descriptor))) ;todo: should not happen
        (er hard? 'get-info-from-srm "Bad method-descriptor")
        (mv :bad-method-descriptor nil nil nil nil nil))
       (param-types (jvm::param-types-from-method-descriptor method-descriptor))

       (interfacep (eq tag :CONSTANT_InterfaceMethodref)))
    (mv (erp-nil) class-name method-name method-descriptor param-types interfacep)))

;; Returns (mv erp parsed-names bytes).
(defund get-class-names-for-indices (count bytes constant-pool)
  (declare (xargs :guard (and (natp count)
                              (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (if (zp count)
      (mv (erp-nil) nil bytes)
    (b* (((mv erp index bytes) (readu2 bytes))
         ((when erp)
          (er hard? 'get-class-names-for-indices "Ran out of data.")
          (mv erp nil nil))
         ((mv erp rest-names bytes)
          (get-class-names-for-indices (+ -1 count) bytes constant-pool))
         ((when erp) (mv erp nil nil))
         ((mv erp class-name) (get-class-name-from-src index constant-pool))
         ((when erp) (mv erp nil nil)))
      (mv (erp-nil)
          (cons class-name rest-names)
          bytes))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-get-class-names-for-indices
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (get-class-names-for-indices count bytes constant-pool))))
  :hints (("Goal" :in-theory (enable get-class-names-for-indices))))

(defthm len-bound-for-get-class-names-for-indices
  (<= (len (mv-nth 2 (get-class-names-for-indices count bytes constant-pool)))
      (len bytes))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable get-class-names-for-indices))))

(defthm true-listp-of-mv-nth-2-of-get-class-names-for-indices
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (get-class-names-for-indices count bytes constant-pool))))
  :hints (("Goal" :in-theory (enable get-class-names-for-indices))))

;; Should work for a method or a field (but perhaps not if we change this to parse the descriptor)
;; Returns (mv erp get-name-and-type-from-cp-entry).
(defund get-name-and-type-from-cp-entry (name_and_type_index constant-pool)
  (declare (xargs :guard (and (natp name_and_type_index)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp name_and_type) (lookup-in-constant-pool name_and_type_index constant-pool))
       ((when erp) (mv erp nil))
       (name_index (nfix (lookup-eq-safe 'name_index name_and_type)))
       (descriptor_index (nfix (lookup-eq-safe 'descriptor_index name_and_type)))

       ((mv erp name-entry) (lookup-in-constant-pool name_index constant-pool))
       ((when erp) (mv erp nil))
       (name (lookup-eq-safe 'bytes name-entry))

       ((mv erp descriptor-entry) (lookup-in-constant-pool descriptor_index constant-pool))
       ((when erp) (mv erp nil))
       (descriptor (lookup-eq-safe 'bytes descriptor-entry)) ;todo: maybe parse
       )
    (mv (erp-nil)
        (acons :name name (acons :descriptor descriptor nil)))))

;; Returs (mv erp constant).
(defun get-ldc-constant (index constant-pool)
  (declare (xargs :guard (and (natp index)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp entry) (lookup-in-constant-pool index constant-pool))
       ((when erp) (mv erp nil))
       (tag (lookup-eq-safe 'tag entry)))
    (if (eq tag :CONSTANT_Integer)
        (mv (erp-nil) (lookup-eq-safe 'bytes entry)) ;an (untagged) BV32
      (if (eq tag :CONSTANT_Float)
          (let ((val (lookup-eq-safe 'bytes entry)))
            (if (not (unsigned-byte-p 32 val))
                (mv :bad-float-constant nil)
              (mv (erp-nil) (parse-float val)))) ;this will be a java-floatp and so will have a tag of :float
        (if (eq tag :CONSTANT_string)
            (b* ((string_index (nfix (lookup-eq-safe 'string_index entry)))
                 ((mv erp string_index-entry) (lookup-in-constant-pool string_index constant-pool))
                 ((when erp) (mv erp nil))
                 (string-bytes (lookup-eq-safe 'bytes string_index-entry)) ;will be an ACL2 string (fixme what about unicode?)
                 )
              (mv (erp-nil) string-bytes))
          ;;There seems to be another case for class_info. for example, see this snippet from javap:
          ;; 12: ldc_w #95=<Class [C>
          ;; this seems to be related to java 1.5 class literals
          ;;FFFIXME Handle this correctly.  Print a warning until I do?
          (if (eq tag :CONSTANT_Class)
              (b* ((name_index (nfix (lookup-eq-safe 'name_index entry)))
                   ((mv erp name_index-entry) (lookup-in-constant-pool name_index constant-pool))
                   ((when erp) (mv erp nil))
                   (string-bytes (lookup-eq-safe 'bytes name_index-entry))) ;will be an ACL2 string (fixme what about unicode?)
                (if (not (stringp string-bytes)) ;rename string-bytes and the 'bytes field
                    (mv :bad-string nil)
                  (mv (erp-nil) (list :class (turn-slashes-into-dots string-bytes))) ;the :class tag distinguishes this from the string case.
                  ))
            (mv :unrecognized-stuff-for-ldc-or-ldc_w nil)))))))

;; Returns (mv erp constant).
;; This version is for longs/doubles only
(defun get-ldc2_w-constant (index constant-pool)
  (declare (xargs :guard (and (natp index)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp entry) (lookup-in-constant-pool index constant-pool))
       ((when erp) (mv erp nil))
       (tag (lookup-eq-safe 'tag entry)))
    (if (eq tag :CONSTANT_Long)
        (mv (erp-nil) (lookup-eq-safe 'bytes entry)) ;an (untagged) BV64
      (if (eq tag :CONSTANT_Double)
          (let ((val (lookup-eq-safe 'bytes entry))) ;an (untagged) BV64
            (if (not (unsigned-byte-p 64 val))
                (mv `(:bad-double-constant ,val) nil)
              (mv (erp-nil) (parse-double val)))) ;this will be a java-doublep and so will have a tag of :double
        (mv :unrecognized-stuff-for-ldc2_w nil)))))

;this usually needs to consume more bytes than just the opcode, so we pass in bytes and return extrabytecount
;FFIXME for some instructions, translation of the stuff after the opcode needs to be done (e.g., looking stuff up in the constant pool)
; Returns (mv erp instr extrabytecount) where extrabytecount is the number of extra bytes occupied by the instruction (not counting the opcode byte)
(defund translate-instruction (opcode-name
                               byte-number-of-opcode
                               bytes ;the stream of bytes following the instruction
                               constant-pool)
  (declare (xargs :guard (and (symbolp opcode-name)
                              (natp byte-number-of-opcode)
                              (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (cond
   ;; WIDE modifies the instruction that comes after it.  Note that
   ;; once we translate the instruction, it would not be clear that
   ;; there was a WIDE (so you couldn't tell from the parsed
   ;; instruction how many bytes it takes), so we now store the length
   ;; explicitly in the instruction.
   ;; TODO: test the parsing of WIDE
   ((eq ':wide opcode-name)
    (b* (((when (not (consp bytes)))
          (mv :not-enough-bytes nil 0))
         (opcode-after-wide (first bytes))
         (opcode-after-wide-name (lookup opcode-after-wide *opcode-to-name-table*)))
      (if (member-eq opcode-after-wide-name '(:iload
                                              :fload
                                              :aload
                                              :lload
                                              :dload
                                              :istore
                                              :fstore
                                              :astore
                                              :lstore
                                              :dstore
                                              :ret))
          ;;Format 1:
          (if (not (consp (rest (rest bytes))))
              (mv :not-enough-bytes nil 0)
            (mv (erp-nil)
                (list opcode-after-wide-name
                      (2bytes-to-int (second bytes) (third bytes))
                      4 ;the total length of the instruction
                      )
                3 ;one byte for the opcode-after-wide, two bytes for the index
                ))
        (if (eq opcode-after-wide-name ':iinc)
            (if (not (consp (rest (rest (rest (rest bytes))))))
                (mv :not-enough-bytes nil 0)
              ;;Format 2:
              (mv (erp-nil)
                  (list opcode-after-wide-name
                        (2bytes-to-int (second bytes) (third bytes))
                        (logext 16 (2bytes-to-int (fourth bytes) (fifth bytes)))
                        6 ;the total length of the instruction
                        )
                  5 ;one byte for the iinc, 4 bytes for the two indices (each of 2 bytes)
                  ))
          (prog2$ (er hard? 'translate-instruction "unknown opcode (~x0) after wide.~%" opcode-after-wide)
                  (mv :unknown-instruction 'error 0))))))
   ((eq opcode-name ':tableswitch)
    (b* ((bytes-of-padding (- 3 (mod byte-number-of-opcode 4)))
         (bytes (nthcdr bytes-of-padding bytes)) ;could check that the skipped bytes are in fact 0's
         ((mv erp default-offset bytes) (read-signed-4-byte-quantity bytes))
         ((when erp) (mv erp nil 0))
         ((mv erp low bytes) (read-signed-4-byte-quantity bytes))
         ((when erp) (mv erp nil 0))
         ((mv erp high bytes) (read-signed-4-byte-quantity bytes))
         ((when erp) (mv erp nil 0))
         ((when (< high low))
          (mv :error-in-tableswitch nil 0))
         ((mv erp jump-offsets &) (read-signed-4-byte-quantities (+ 1 high (- low)) bytes))
         ((when erp) (mv erp nil 0)))
      (mv (erp-nil)
          (list opcode-name
                default-offset ;signed
                low            ;signed
                high           ;signed
                jump-offsets   ;all are signed
                )
          (+ bytes-of-padding
             4                        ;for default
             4                        ;for low
             4                        ;for high
             (* 4 (+ 1 high (- low))) ;for the jump offsets
             ))))
   ((eq opcode-name ':lookupswitch)
    (let* ((bytes-of-padding (- 3 (mod byte-number-of-opcode 4)))
           (bytes (nthcdr bytes-of-padding bytes)) ;could check that the skipped bytes are in fact 0's
           )
      (b* (((mv erp default-value bytes) (read-signed-4-byte-quantity bytes))
           ((when erp) (mv erp nil 0))
           ((mv erp npairs bytes) (read-signed-4-byte-quantity bytes))
           ((when erp) (mv erp nil 0))
           ((when (not (<= 0 npairs)))
            (mv :bad-npairs-in-lookupswitch nil 0))
           ((mv erp matches-and-offsets &) (read-signed-4-byte-quantities (* 2 npairs) bytes))
           ((when erp) (mv erp nil 0))
           (extra-byte-count (+ bytes-of-padding
                                4 ;for default value
                                4 ;for npairs value
                                (* 4 2 npairs) ;we have npairs pairs, each of which has two, four-byte quantities
                                ))
           ;;(inst-len (+ 1 extra-byte-count))
           )
        (mv (erp-nil)
            (list opcode-name
                  (pairlis$ (evens matches-and-offsets) (odds matches-and-offsets)) ;make the alist
                  default-value
                  ;; inst-len ;I guess we don't need this
                  )
            extra-byte-count))))
   ((member-eq opcode-name jvm::*one-byte-ops*)
    (mv (erp-nil) (list opcode-name) 0))
   ((eq opcode-name ':bipush)
    (if (not (consp bytes))
        (mv :not-enough-bytes nil 0)
      (mv (erp-nil)
          (list ':bipush (logext 8 (first bytes)))
          1)))
   ((eq opcode-name ':sipush)
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (mv (erp-nil)
          (list ':sipush (logext 16 (2bytes-to-int (first bytes) (second bytes))))
          2)))

   ;; LDC and variants (we look up the data from the constant pool right here):
   ((eq opcode-name ':ldc)
    (if (not (consp bytes))
        (mv :not-enough-bytes nil 0)
      (b* (((mv erp val) (get-ldc-constant (first bytes) constant-pool))
           ((when erp) (mv erp nil 0)))
        (mv (erp-nil)
            (list opcode-name val)
            1))))
   ;;this variant takes 2 bytes and uses them to assemble a 16-bit unsigned index into the constant pool
   ((eq opcode-name ':LDC_W)
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (b* (((mv erp val) (get-ldc-constant (2bytes-to-int (first bytes) (second bytes)) constant-pool))
           ((when erp) (mv erp nil 0)))
        (mv (erp-nil)
            (list opcode-name val)
            2))))
   ;;this variant handles longs/doubles
   ((eq opcode-name ':LDC2_W)
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (b* (((mv erp val) (get-ldc2_w-constant (2bytes-to-int (first bytes) (second bytes)) constant-pool))
           ((when erp) (mv erp nil 0)))
        (mv (erp-nil)
            (list opcode-name val)
            2))))

   ;;these take a single unsigned byte (if they are modified by a WIDE, they are handled when the WIDE opcode is processed)
   ((member-eq opcode-name '(:ILOAD :LLOAD :FLOAD
                                    :DLOAD :ALOAD :ISTORE
                                    :LSTORE
                                    :FSTORE :DSTORE
                                    :ASTORE :RET))
    (if (not (consp bytes))
        (mv :not-enough-bytes nil 0)
      (mv (erp-nil)
          (list opcode-name (first bytes)
                2 ;total length of the instruction (in this case, it was not preceded by WIDE)
                )
          1)))
   ((eq opcode-name ':NEWARRAY)
    (if (not (consp bytes))
        (mv :not-enough-bytes nil 0)
      (mv (erp-nil)
          (list opcode-name (getarraytype (first bytes)))
          1)))
   ;;these take 2 bytes and use them to assemble a 16-bit unsigned value
   ((member-eq opcode-name '(:NEW))
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (b* (((mv erp class-name) (get-class-name-from-src (2bytes-to-int (first bytes) (second bytes)) constant-pool))
           ((when erp) (mv erp nil 0)))
        (mv (erp-nil)
            (list opcode-name class-name)
            2))))

   ;;these take 2 bytes and use them to assemble a 16-bit unsigned value
   ((member-eq opcode-name '(:CHECKCAST :ANEWARRAY :INSTANCEOF))
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (b* (((mv erp class-name) (get-class-name-from-src (2bytes-to-int (first bytes) (second bytes)) constant-pool))
           ((when erp) (mv erp nil 0)))
        (mv (erp-nil)
            (list opcode-name class-name)
            2))))

   ((eq opcode-name :INVOKEVIRTUAL)
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (b* ((srm-index (2bytes-to-int (first bytes) (second bytes)))
           ((mv erp class-name method-name method-descriptor param-types &) ;; interfacep is not used
            (get-info-from-srm srm-index constant-pool))
           ((when erp) (mv erp nil 0)))
        (mv (erp-nil)
            (list opcode-name
                  class-name ;; This can be a (parsed) array class, at least for :invokevirtual.
                  method-name
                  ;;should we parse this?:
                  method-descriptor
                  ;;we precompute these and stick them in the instruction:
                  param-types)
            2))))

   ((member-eq opcode-name '(:INVOKESTATIC :INVOKESPECIAL))
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (b* ((srm-index (2bytes-to-int (first bytes) (second bytes)))
           ((mv erp class-name method-name method-descriptor param-types interfacep)
            (get-info-from-srm srm-index constant-pool))
           ((when erp) (mv erp nil 0)))
        (mv (erp-nil)
            (list opcode-name
                  class-name ;; This can be a (parsed) array class, at least for :invokevirtual.
                  method-name
                  ;;should we parse this?:
                  method-descriptor
                  ;;we precompute these and stick them in the instruction:
                  param-types
                  interfacep)
            2))))

   ;;this one is special.. FFIXME deref in constant pool
   ((eq opcode-name ':INVOKEINTERFACE)
    (if (not (consp (rest (rest (rest bytes)))))
        (mv :not-enough-bytes nil 0)
      (b* ((srm-index (2bytes-to-int (first bytes) (second bytes)))
           ((mv erp class-name method-name method-descriptor param-types &) ;; interfacep is not used
            (get-info-from-srm srm-index constant-pool))
           ((when erp) (mv erp nil 0)))
        (mv (erp-nil)
            (list opcode-name
                  ;; todo: these next steps are inefficient:
                  class-name
                  method-name
                  method-descriptor
                  param-types
;this must always be zero? check Java 8
;              (third bytes) ;count (could omit this.  the spec says its redundant.)
;                                              srm (third bytes) (fourth bytes))
                  )
            4))))
   ((eq opcode-name ':INVOKEDYNAMIC)
    (if (not (consp (rest (rest (rest bytes)))))
        (mv :not-enough-bytes nil 0)
      (mv (erp-nil)
          (list opcode-name
                (2bytes-to-int (first bytes) (second bytes)) ;fixme look this up in the constant pool
                ;; todo: call get-info-from-srm
                ;;(get-class-name-from-srm (2bytes-to-int (first bytes) (second bytes)) constant-pool)
                ;;(get-method-name-from-srm (2bytes-to-int (first bytes) (second bytes)) constant-pool)
                ;;(get-method-descriptor-from-srm (2bytes-to-int (first bytes) (second bytes)) constant-pool)
                ;;(get-method-param-types-from-srm (2bytes-to-int (first bytes) (second bytes)) constant-pool)

;this must always be zero? check Java 8
;              (third bytes) ;count (could omit this.  the spec says its redundant.)
;                                              (2bytes-to-int (first bytes) (second bytes)) (third bytes) (fourth bytes))
                )
          4)))
   ((member-eq opcode-name '(:GETFIELD :PUTFIELD :GETSTATIC :PUTSTATIC))
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (b* ((srf-index (2bytes-to-int (first bytes) (second bytes)))
           ((mv erp class-name field-name descriptor)
            (get-info-from-srf srf-index constant-pool))
           ((when erp) (mv erp nil 0))
           ((when (not (stringp descriptor))) ;for guards, can this be dropped?
            (mv :bad-descriptor nil 0))
           ((when (not (jvm::field-namep field-name))) ;for guards, can this be dropped?
            (mv :bad-field-name nil 0))
           ((mv erp type) (jvm::parse-descriptor descriptor))
           ((when erp) (mv erp nil 0))
           (field-id (jvm::make-field-id field-name type))
           (long-flag (if (member-equal type
                                        '(:long ;long integer
                                          :double ;double float (hope this is right)
                                          ))
                          t
                        nil)))
        (mv (erp-nil)
            (list opcode-name
                  class-name ; should not be an array class (checked in get-info-from-srf)
                  field-id
                  long-flag)
            2))))
   ;;this one is special because it takes a signed value
   ;; (if IINC is modified by a WIDE it is handled when the WIDE opcode is processed)
   ((eq opcode-name ':IINC)
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (mv (erp-nil)
          (list opcode-name (first bytes) (logext 8 (second bytes))
                3 ;total length of the instruction (in this case, it was not preceded by WIDE)
                )
          2)))
   ;;these take 2 bytes and use them to assemble a 16-bit signed value
   ((member-eq opcode-name '(:IFEQ :IFNE :IFLT
                                   :IFGE :IFGT :IFLE
                                   :IF_ICMPEQ :IF_ICMPNE
                                   :IF_ICMPLT :IF_ICMPGE
                                   :IF_ICMPGT :IF_ICMPLE
                                   :IF_ACMPEQ :IF_ACMPNE
                                   :GOTO :JSR :IFNULL
                                   :IFNONNULL))
    (if (not (consp (rest bytes)))
        (mv :not-enough-bytes nil 0)
      (mv (erp-nil)
          (list opcode-name (logext 16 (2bytes-to-int (first bytes) (second bytes))))
          2)))
   ;;this one is special...
   ((eq opcode-name ':MULTIANEWARRAY)
    (if (not (consp (rest (rest bytes))))
        (mv :not-enough-bytes nil 0)
      (b* (((mv erp class-name) (get-class-name-from-src (2bytes-to-int (first bytes) (second bytes)) constant-pool))
           ((when erp) (mv erp nil 0)))
        (mv (erp-nil)
            (list opcode-name
                  class-name
                  (third bytes) ;number of dimensions
                  )
            3))))
   ((member-eq opcode-name '(:GOTO_W :JSR_W))
    (if (not (consp (rest (rest (rest bytes)))))
        (mv :not-enough-bytes nil 0)
      (mv (erp-nil)
          (list opcode-name (logext 32 (4bytes-to-int (first bytes) (second bytes) (third bytes) (fourth bytes))))
          4)))
   (t (mv :unhandled-opcode
          (er hard? 'translate-instruction "Found an unhandled opcode: ~x0." opcode-name)
          0))))

(defthm natp-of-mv-nth-2-of-translate-instruction
  (implies (integerp byte-number-of-opcode)
           (natp (mv-nth 2 (translate-instruction opcode-name byte-number-of-opcode bytes constant-pool))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable translate-instruction))))

;; (thm
;;  (implies (not (MV-NTH 0 (translate-instruction opcode-name byte-number-of-opcode bytes constant-pool)))
;;           (JVM::JVM-INSTRUCTION-OKAYP (MV-NTH 1 (translate-instruction opcode-name byte-number-of-opcode bytes constant-pool))
;;                                       BYTE-NUMBER-OF-OPCODE
;;                                       (CONS BYTE-NUMBER-OF-OPCODE
;;                                             (STRIP-CARS ACC))))

;this is now tail recursive
;byte-number-of-opcode is the byte number of the opcode of the instruction (numbering with the first opcode in the method as 0)
;; Returns (mv erp program) where the program is an alist from pcs to instructions.
(defund translate-code-bytes-aux (bytes byte-number-of-opcode constant-pool acc)
  (declare (xargs :measure (+ 1 (len bytes))
                  :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              (natp byte-number-of-opcode)

                              (true-listp acc))
                  :stobjs constant-pool))
  (if (endp bytes)
      (mv (erp-nil) (reverse acc))
    (b* (((when (not (consp bytes)))
          (mv :not-enough-bytes nil))
         (opcode (first bytes))
         (bytes (rest bytes))
         (opcode-name (lookup opcode *opcode-to-name-table*))
         ((when (not opcode-name))
          (er hard? 'translate-code-bytes-aux "Unknown opcode: ~x0." opcode)
          (mv :bad-opcode nil))
         ((mv erp parsed-instruction extrabytecount)
          (translate-instruction opcode-name byte-number-of-opcode bytes constant-pool))
         ((when erp) (mv erp nil)))
      (translate-code-bytes-aux (nthcdr extrabytecount bytes) ;we already did the cdr for the opcode
                                (+ 1                          ;for the opcode
                                   extrabytecount
                                   byte-number-of-opcode)
                                constant-pool
                                (cons (cons byte-number-of-opcode parsed-instruction) ;big change!  programs are now alists from pcs to instructions!
                                      acc)))))

(defthm alistp-of-mv-nth-1-of-translate-code-bytes-aux
  (implies (and ;(not (mv-nth 0 (translate-code-bytes-aux bytes byte-number-of-opcode constant-pool acc)))
                (alistp acc))
           (alistp (mv-nth 1 (translate-code-bytes-aux bytes byte-number-of-opcode constant-pool acc))))
  :hints (("Goal" :in-theory (enable translate-code-bytes-aux
                                     all-pcp))))

(defthm all-pcp-of-strip-cars-of-mv-nth-1-of-translate-code-bytes-aux
  (implies (and (not (mv-nth 0 (translate-code-bytes-aux bytes byte-number-of-opcode constant-pool acc)))
                (all-pcp (strip-cars acc))
                (true-listp acc)
                (natp byte-number-of-opcode))
           (all-pcp (strip-cars (mv-nth 1 (translate-code-bytes-aux bytes byte-number-of-opcode constant-pool acc)))))
  :hints (("Goal" :in-theory (enable translate-code-bytes-aux
                                     all-pcp))))

(defthm car-of-car-of-mv-nth-1-of-translate-code-bytes-aux
  (implies (and (not (mv-nth 0
                             (translate-code-bytes-aux bytes byte-number-of-opcode constant-pool acc)))
                (natp byte-number-of-opcode)
                (consp (mv-nth 1
                               (translate-code-bytes-aux bytes byte-number-of-opcode constant-pool acc)))
                (true-listp acc))
           (equal (car (car (mv-nth 1 (translate-code-bytes-aux bytes byte-number-of-opcode constant-pool acc))))
                  (if acc
                      (car (car (last acc)))
                    byte-number-of-opcode)))
  :hints (("Goal" :in-theory (e/d (translate-code-bytes-aux) (reverse)))))

;todo
;; (defthm increasing-pcsp-of-strip-cars-of-mv-nth-1-of-translate-code-bytes-aux
;;   (implies (and (not (mv-nth 0 (translate-code-bytes-aux bytes byte-number-of-opcode constant-pool acc)))
;;                 (jvm::increasing-pcsp (strip-cars (reverse acc)) prev-pc)
;;                 (true-listp acc)
;;                 (natp byte-number-of-opcode)
;;                 (<= prev-pc byte-number-of-opcode))
;;            (jvm::increasing-pcsp (strip-cars (mv-nth 1 (translate-code-bytes-aux bytes byte-number-of-opcode constant-pool acc)))
;;                                  prev-pc))
;;   :hints (("Goal" :in-theory (enable translate-code-bytes-aux
;;                                      jvm::increasing-pcsp))))

;; Returns (mv erp program) where the program as an alist from pcs to instructions.
(defund translate-code-bytes (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp program) (translate-code-bytes-aux bytes 0 constant-pool nil))
       ((when erp) (mv erp program)))
    (if (not (consp program))
        (mv :empty-program nil)
      (let ((pcs (strip-cars program)))
        (if (and (jvm::jvm-instructions-okayp program pcs) ;todo: avoid the strip-cars?
                 (JVM::INCREASING-PCSP (REST PCS) 0) ;todo: drop!
                 )
            (mv (erp-nil) program)
          (mv `(:instructions-not-all-ok ,program) nil))))))

(defthm method-programp-of-mv-nth-1-of-translate-code-bytes
  (implies (not (mv-nth 0 (translate-code-bytes bytes constant-pool)))
           (jvm::method-programp (mv-nth 1 (translate-code-bytes bytes constant-pool))))
  :hints (("Goal" ;:expand (translate-code-bytes-aux bytes 0 constant-pool nil)
           :in-theory (enable jvm::method-programp
                              translate-code-bytes))))

;this puts the start_pc before the line_number in each pair, to facilitate looking up the line of a given pc
;this is the opposite of how javap prints it
;are the pcs necessarily in order?
;probably safest, when looking up the line number for a pc, to find the largest start-pc <= the target pc and use that entry
;; Returns (mv erp table bytes).
(defun parse-linenumbertable (line_number_table_length bytes acc)
  (declare (xargs :guard (and (natp line_number_table_length)
                              (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              (true-listp acc))))
  (if (zp line_number_table_length)
      (mv (erp-nil) (reverse acc) bytes)
    (b* (((mv erp start_pc bytes) (readu2 bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp line_number bytes) (readu2 bytes))
         ((when erp) (mv erp nil nil)))
      (parse-linenumbertable (+ -1 line_number_table_length) bytes (cons (list start_pc line_number) acc)))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-parse-linenumbertable
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (parse-linenumbertable line_number_table_length bytes acc))))
  :hints (("Goal" :in-theory (enable parse-linenumbertable))))

(defthm true-listp-of-mv-nth-2-of-parse-linenumbertable
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (parse-linenumbertable line_number_table_length bytes acc))))
  :hints (("Goal" :in-theory (enable parse-linenumbertable))))

(defthm <=-of-len-of-mv-nth-2-of-parse-linenumbertable
  (<= (len (mv-nth 2 (parse-linenumbertable line_number_table_length bytes acc)))
      (len bytes))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-linenumbertable))))

;ffixme can there be more that one linenumbertable attribute for a given method??
;; Returns (mv erp table bytes).
(defun parse-linenumbertable-attribute (bytes)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))))
  (b* (((mv erp line_number_table_length bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil)))
    (parse-linenumbertable line_number_table_length bytes nil)))

;first compare the local slot number, then compare by start-pc
;could perhaps just use acl2's total order?
(defund smaller-local-variable-table-entry (entry1 entry2)
  (declare (xargs :guard (and (jvm::local-variable-table-entryp entry1)
                              (jvm::local-variable-table-entryp entry2))
                  :guard-hints (("Goal" :in-theory (enable jvm::local-variable-table-entryp)))))
  (let ((index1 (nth 0 entry1))
        (index2 (nth 0 entry2)))
    (if (< index1 index2)
        entry1
      (if (< index2 index1)
          entry2
        (let ((start-pc1 (nth 1 entry1))
              (start-pc2 (nth 1 entry2)))
          (if (< start-pc1 start-pc2)
              entry1
            (if (< start-pc2 start-pc1)
                entry2
              (prog2$ (er hard? 'smaller-local-variable-table-entry "Two local variable table entries found with the same local slot number and start PC.") ;or is this legal if they are identical?
                      entry1)))))))) ;return a valid entry even in this case

(defthm local-variable-table-entryp-of-smaller-local-variable-table-entry
  (implies (and (jvm::local-variable-table-entryp entry1)
                (jvm::local-variable-table-entryp entry2))
           (jvm::local-variable-table-entryp (smaller-local-variable-table-entry entry1 entry2)))
  :hints (("Goal" :in-theory (enable smaller-local-variable-table-entry))))

(defund smallest-local-variable-table-entry (smallest-so-far entries)
  (declare (xargs :guard (and (jvm::local-variable-table-entryp smallest-so-far)
                              (true-listp entries)
                              (jvm::all-local-variable-table-entryp entries))))
  (if (endp entries)
      smallest-so-far
    (let ((smallest-so-far (smaller-local-variable-table-entry (first entries) smallest-so-far)))
      (smallest-local-variable-table-entry smallest-so-far (rest entries)))))

(defthm member-equal-of-smallest-local-variable-table-entry
  (or (equal (smallest-local-variable-table-entry smallest-so-far entries) smallest-so-far)
      (member-equal (smallest-local-variable-table-entry smallest-so-far entries)
                    entries))
  :hints (("Goal" :in-theory (enable smallest-local-variable-table-entry
                                     smaller-local-variable-table-entry))))

(defthm local-variable-table-entryp-of-smallest-local-variable-table-entry
  (implies (and (jvm::all-local-variable-table-entryp entries)
                (jvm::local-variable-table-entryp smallest-so-far))
           (jvm::local-variable-table-entryp (smallest-local-variable-table-entry smallest-so-far entries)))
  :hints (("Goal" :in-theory (enable smallest-local-variable-table-entry))))

(defund sort-local-variable-table-entries (entries)
  (declare (xargs :guard (and (true-listp entries)
                              (jvm::all-local-variable-table-entryp entries))
                  :measure (len entries)
                  :hints (("Goal" :in-theory (e/d (smaller-local-variable-table-entry)
                                                  (member-equal-of-smallest-local-variable-table-entry))
                           :use (:instance member-equal-of-smallest-local-variable-table-entry
                                           (smallest-so-far (car entries))
                                           (entries (cdr entries)))))))
  (if (endp entries)
      nil
    (let ((smallest-entry (smallest-local-variable-table-entry (first entries) (rest entries))))
      (cons smallest-entry
            (sort-local-variable-table-entries (remove-equal smallest-entry entries))))))

;move
(defthm local-variable-tablep-of-cons
  (equal (jvm::local-variable-tablep (cons a x))
         (and (jvm::local-variable-table-entryp a)
              (jvm::local-variable-tablep x)))
  :hints (("Goal" :in-theory (enable jvm::local-variable-tablep))))

(defthm all-local-variable-table-entryp-of-sort-local-variable-table-entries
  (implies (jvm::all-local-variable-table-entryp entries)
           (jvm::all-local-variable-table-entryp (sort-local-variable-table-entries entries)))
  :hints (("Goal" :in-theory (enable sort-local-variable-table-entries jvm::local-variable-tablep))))

;; (thm
;;  (implies (TRUE-LISTP ENTRIES)
;;           (equal (JVM::LOCAL-VARIABLE-TABLEP (SORT-LOCAL-VARIABLE-TABLE-ENTRIES entries))
;;                  (JVM::LOCAL-VARIABLE-TABLEP entries)))
;;  :hints (("Goal" :in-theory (enable SORT-LOCAL-VARIABLE-TABLE-ENTRIES JVM::LOCAL-VARIABLE-TABLEP))))


;; Returns (mv erp localvariabletable bytes).
(defun parse-localvariabletable (local_variable_table_length bytes constant-pool acc)
  (declare (xargs :guard (and (natp local_variable_table_length)
                              (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)

                              (true-listp acc)
                              (jvm::local-variable-tablep acc))
                  :stobjs constant-pool
                  :guard-hints (("Goal" :in-theory (enable jvm::local-variable-table-entryp jvm::pcp)))))
  (if (zp local_variable_table_length)
      (mv (erp-nil)
          (sort-local-variable-table-entries (reverse acc))
          bytes)
    (b* (((mv erp start_pc bytes) (readu2 bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp length bytes) (readu2 bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp name_index bytes) (readu2 bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp name-entry) (lookup-in-constant-pool name_index constant-pool))
         (name (lookup-eq-safe 'bytes name-entry))
         ((when erp) (mv erp nil nil))
         ((when (not (stringp name))) ;drop?
          (mv :bad-name nil nil))
         ((mv erp descriptor_index bytes) (readu2 bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp descriptor-entry) (lookup-in-constant-pool descriptor_index constant-pool))
         ((when erp) (mv erp nil nil))
         (descriptor (lookup-eq-safe 'bytes descriptor-entry))
         ((when (not (stringp descriptor))) ;drop?
          (mv :bad-descriptor nil nil))
         ((mv erp parsed-descriptor) (jvm::parse-descriptor descriptor)) ;new!
         ((when erp) (mv erp nil nil))
         ((mv erp index bytes) (readu2 bytes))
         ((when erp) (mv erp nil nil))
         ;; I have seen entries with 0 length, in which case the end will be
         ;; one less than the start
         )
      (parse-localvariabletable (+ -1 local_variable_table_length)
                                bytes
                                constant-pool
                                ;; a local-variable-table-entry:
                                (cons (list index ;this is the local slot
                                            start_pc
                                            (+ start_pc length -1) ;end pc or -1 (inclusive)
                                            name
                                            parsed-descriptor)
                                      acc)))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-parse-localvariabletable
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (parse-localvariabletable local_variable_table_length bytes constant-pool acc))))
  :hints (("Goal" :in-theory (enable parse-localvariabletable))))

(defthm true-listp-of-mv-nth-2-of-parse-localvariabletable
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (parse-localvariabletable local_variable_table_length bytes constant-pool acc))))
  :hints (("Goal" :in-theory (enable parse-localvariabletable))))

(defthm <=-of-len-of-mv-nth-2-of-parse-localvariabletable
  (<= (len (mv-nth 2 (parse-localvariabletable local_variable_table_length bytes constant-pool acc)))
      (len bytes))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-localvariabletable))))

(defthm local-variable-tablep-of-mv-nth-1-of-parse-localvariabletable
  (implies (and (not (mv-nth 0 (parse-localvariabletable local_variable_table_length bytes constant-pool acc)))
                ;;(natp local_variable_table_length)
                ;; (true-listp bytes)
                ;; (all-unsigned-byte-p 8 bytes)
                ;; (constant-poolp constant-pool)
                ;;(true-listp acc)
                (jvm::local-variable-tablep acc)
                )
           (jvm::local-variable-tablep (mv-nth 1 (parse-localvariabletable local_variable_table_length bytes constant-pool acc))))
  :hints (("Goal" :in-theory (enable jvm::local-variable-table-entryp
                                     jvm::pcp))))

;; Returns (mv erp localvariabletable bytes).
(defun parse-localvariabletable-attribute (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp local_variable_table_length bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil)))
    (parse-localvariabletable local_variable_table_length bytes constant-pool nil)))

;; Return (mv erp entry bytes)
(defund parse-exception-table-entry (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))
                  :stobjs constant-pool))
  (b* (((mv erp start_pc bytes) (readu2 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp end_pc bytes) (readu2 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp handler_pc bytes) (readu2 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp catch_type bytes) (readu2 bytes))
       ((when erp) (mv erp nil bytes))
       ((mv erp catch-type)
        (if (= 0 catch_type)
            (mv (erp-nil) :any) ; means to handle all exceptions
          (b* (((mv erp catch-type-entry) (lookup-in-constant-pool catch_type constant-pool))
               ((when erp) (mv erp nil))
               ((mv erp name-entry) (lookup-in-constant-pool (nfix (lookup-eq-safe 'name_index catch-type-entry))
                                                             constant-pool))
               ((when erp) (mv erp nil))
               (exception-class (lookup-eq-safe 'bytes name-entry))
               ((when (not (jvm::class-namep exception-class)))
                (mv `(:bad-exception-class-in-exception-table ,exception-class)
                    nil)))
            (mv (erp-nil)
                exception-class))))
       ((when erp) (mv erp nil bytes)))
    (mv (erp-nil)
        (list start_pc end_pc handler_pc catch-type)
        bytes)))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-parse-exception-table-entry
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (parse-exception-table-entry bytes constant-pool))))
  :hints (("Goal" :in-theory (enable parse-exception-table-entry))))

(defthm true-listp-of-mv-nth-2-of-parse-exception-table-entry
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (parse-exception-table-entry bytes constant-pool))))
  :hints (("Goal" :in-theory (enable parse-exception-table-entry))))

(defthm exception-table-entryp-of-mv-nth-1-of-parse-exception-table-entry
  (implies (not (mv-nth 0 (parse-exception-table-entry bytes constant-pool)))
           (jvm::exception-table-entryp (mv-nth 1 (parse-exception-table-entry bytes constant-pool))))
  :hints (("Goal" :in-theory (enable parse-exception-table-entry))))

;; Returns (mv erp exception-table).
;; the order of the entries matters!
(defund parse-exception-table (exception-table-length
                               bytes ;a list of 8*exception-table-length bytes ; todo: add that to guard and reuce checks?
                               constant-pool)
  (declare (xargs :guard (and (natp exception-table-length)
                              (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes))
                  :stobjs constant-pool))
  (if (zp exception-table-length)
      (mv (erp-nil) nil)
    (b* (((mv erp res1 bytes)
          (parse-exception-table-entry bytes constant-pool))
         ((when erp) (mv erp nil))
         ((mv erp res2) (parse-exception-table (+ -1 exception-table-length)
                                               bytes
                                               constant-pool))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons res1 res2)))))

(defthm exception-tablep-of-mv-nth-1-of-parse-exception-table
  (implies (and (not (mv-nth 0 (parse-exception-table exception-table-length bytes constant-pool)))
                ;(natp exception-table-length)
                ;;(true-listp bytes)
                ;;(all-unsigned-byte-p 8 bytes)
                )
           (jvm::exception-tablep (mv-nth 1 (parse-exception-table exception-table-length bytes constant-pool))))
  :hints (("Goal" :in-theory (e/d (jvm::exception-tablep parse-exception-table) (natp)))))

;; Returns (mv erp parsed-names bytes).  Assumes we have already parsed the
;; attribute_name_index and the attribute_length.
(defund parse-exceptions-attribute (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp number_of_exceptions bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil)))
    (get-class-names-for-indices number_of_exceptions bytes constant-pool)))

;; Returns (mv erp parsed-names bytes).  Assumes we have already parsed the
;; attribute_name_index and the attribute_length.
(defund parse-nestmembers-attribute (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp number_of_classes bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil)))
    (get-class-names-for-indices number_of_classes bytes constant-pool)))

;; Returns (mv erp parsed-name bytes).  Assumes we have already parsed the
;; attribute_name_index and the attribute_length.
(defund parse-nesthost-attribute (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp host_class_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp class-name) (get-class-name-from-src host_class_index constant-pool))
       ((when erp) (mv erp nil nil)))
    (mv (erp-nil) class-name bytes)))

;; Returns (mv erp source-file bytes).  Assumes we have already parsed the
;; attribute_name_index and the attribute_length.
(defund parse-sourcefile-attribute (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp sourcefile_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp source-file-entry) (lookup-in-constant-pool sourcefile_index constant-pool))
       ((when erp) (mv erp nil nil)))
    (mv (erp-nil)
        (lookup-eq-safe 'bytes source-file-entry)
        bytes)))

;; Returns (mv erp signature bytes).  Assumes we have already parsed the
;; attribute_name_index and the attribute_length.
(defund parse-signature-attribute (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp signature_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp signature-entry) (lookup-in-constant-pool signature_index constant-pool))
       ((when erp) (mv erp nil nil)))
    (mv (erp-nil)
        (lookup-eq-safe 'bytes signature-entry)
        bytes)))

;; Returns (mv erp info bytes).  Assumes we have already parsed the
;; attribute_name_index and the attribute_length.
(defund parse-enclosingmethod-attribute (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp class_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp method_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp class-name) (get-class-name-from-src class_index constant-pool))
       ((when erp) (mv erp nil nil))
       ((mv erp name-and-type)
        (if (= 0 method_index)
            (mv (erp-nil) :none)
          (get-name-and-type-from-cp-entry method_index constant-pool)))
       ((when erp) (mv erp nil nil)))
    (mv (erp-nil)
        (acons :class class-name
               (acons :method
                      name-and-type
                      nil))
        bytes)))

;; Returns (mv erp val bytes).  Assumes we have already parsed the
;; attribute_name_index and the attribute_length.
(defund parse-constantvalue-attribute (bytes constant-pool)
  (declare (xargs :guard (and (true-listp bytes)
                              (all-unsigned-byte-p 8 bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp constantvalue_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp val-entry) (lookup-in-constant-pool constantvalue_index constant-pool))
       ((when erp) (mv erp nil nil))
       (val-tag (lookup-eq-safe 'tag val-entry)))
    (if (equal val-tag :CONSTANT_String)
        (b* ((string_index (nfix (lookup-eq-safe 'string_index val-entry)))
             ((mv erp string_index-entry) (lookup-in-constant-pool string_index constant-pool))
             ((when erp) (mv erp nil nil))
             (string-bytes (lookup-eq-safe 'bytes string_index-entry)))
          (mv (erp-nil) string-bytes bytes))
      (mv (erp-nil) (lookup-eq-safe 'bytes val-entry) bytes))))

(defund code-attributep (code-attribute)
  (declare (xargs :guard t))
  (and (alistp code-attribute)
       ;; implies a code-attribute cannot be nil:
       (natp (lookup-equal :max_locals code-attribute))
       (jvm::exception-tablep (lookup-equal :exception_table code-attribute))
       (alistp (lookup-equal :attributes code-attribute))
       (jvm::local-variable-tablep (lookup-equal "LocalVariableTable" (lookup-equal :attributes code-attribute)))
       ;; code length must be > 0, and method-programp disallows an empty program
       (jvm::method-programp (lookup-equal :code code-attribute))))

(mutual-recursion
 ;; We've already read the attribute_name_index and attribute_length fields.
 ;; Returns (mv erp info bytes).
 (defun parse-code-attribute (bytes constant-pool)
   (declare (xargs
             :measure (make-ord (+ 1 (len bytes)) 1 0) ;not sure about these measures
             :verify-guards nil ;; done below
             :guard (and (true-listp bytes)
                         (all-unsigned-byte-p 8 bytes)
                         )
             :stobjs constant-pool
             :hints (("Goal" :in-theory (enable readu2 readu4)
                      ;;:expand (PARSE-ATTRIBUTE-INFO-ENTRY BYTES CONSTANT-POOL) ;todo: illegal
                      ))))
   (if (endp bytes) ;for termination, could strengthen this check
       (mv :ran-out-of-bytes nil bytes)
     (b* (((mv erp max_stack bytes) (readu2 bytes))
          ((when erp) (mv erp nil nil))
          (info nil)
          (info (acons :max_stack max_stack info))
          ((mv erp max_locals bytes) (readu2 bytes))
          ((when erp) (mv erp nil nil))
          (info (acons :max_locals max_locals info))
          ((mv erp code_length bytes) (readu4 bytes))
          ((when erp) (mv erp nil nil))
          ((mv erp code bytes) (readnbytes code_length bytes))
          ((when erp) (mv erp nil nil))
          ((mv erp program) (translate-code-bytes code constant-pool))
          ((when erp) (mv erp nil nil))
          (info (acons :code program info))
          ((mv erp exception_table_length bytes) (readu2 bytes))
          ((when erp) (mv erp nil nil))
          ((mv erp exception_table bytes) (readnbytes (* 8 exception_table_length) bytes))
          ((when erp) (mv erp nil nil))
          ((mv erp exception-table)
           (parse-exception-table exception_table_length
                                  exception_table
                                  constant-pool))
          ((when erp) (mv erp nil nil))
          (info (acons :exception_table exception-table info))
          ((mv erp attributes_count bytes) (readu2 bytes))
          ((when erp) (mv erp nil nil))
          ((mv erp attributes bytes)
           (parse-attribute-info-entries
            attributes_count
            bytes
            nil ;initial accumulator
            constant-pool))
          ((when erp) (mv erp nil nil))
          (info (acons :attributes attributes info)))
       (mv (erp-nil) info bytes))))

 ;; Returns (mv erp attribute-name attribute-value bytes).
 (defun parse-attribute-info-entry (bytes constant-pool)
   (declare (xargs :measure (make-ord (+ 1 (len bytes)) 1 0)
                   :guard (and (true-listp bytes)
                               (all-unsigned-byte-p 8 bytes)
                               )
                   :stobjs constant-pool))
   (if (endp bytes)          ;for termination, could strengthen this check
       (mv :ran-out-of-bytes ;(er hard? 'parse-attribute-info-entry "Ran out of bytes")
           nil nil bytes)
     (b* (((mv erp attribute_name_index bytes) (readu2 bytes))
          ((when erp) (mv erp nil nil nil))
          ((mv erp attribute_length bytes) (readu4 bytes))
          ((when erp) (mv erp nil nil nil))
          ((mv erp attribute-entry) (lookup-in-constant-pool attribute_name_index constant-pool))
          ((when erp) (mv erp nil nil nil))
          (attribute_name (lookup-eq-safe 'bytes attribute-entry)))
       (cond ((equal "Code" attribute_name)
              (mv-let (erp info bytes)
                (parse-code-attribute bytes constant-pool)
                (mv erp attribute_name info bytes)))
             ;;FIXME multiple LineNumberTables may exist?  spec seems to indicate so (and so they must be combined?)
             ;;same for Local var tables?
             ((equal "LineNumberTable" attribute_name)
              (mv-let (erp info bytes)
                (parse-linenumbertable-attribute bytes)
                (mv erp attribute_name info bytes)))
             ((equal "LocalVariableTable" attribute_name)
              (mv-let (erp info bytes)
                (parse-localvariabletable-attribute bytes constant-pool)
                (mv erp attribute_name info bytes)))
             ((equal "SourceFile" attribute_name)
              (mv-let (erp source-file bytes)
                (parse-sourcefile-attribute bytes constant-pool)
                (mv erp attribute_name source-file bytes)))
             ((equal "Signature" attribute_name)
              (mv-let (erp signature bytes)
                (parse-signature-attribute bytes constant-pool)
                (mv erp attribute_name signature bytes)))
             ((equal "Exceptions" attribute_name)
              (mv-let (erp parsed-names bytes)
                (parse-exceptions-attribute bytes constant-pool)
                (mv erp attribute_name parsed-names bytes)))
             ((equal "ConstantValue" attribute_name)
              (mv-let (erp val bytes)
                (parse-constantvalue-attribute bytes constant-pool)
                (mv erp attribute_name val bytes)))
             ((equal "NestHost" attribute_name)
              (mv-let (erp parsed-name bytes)
                (parse-nesthost-attribute bytes constant-pool)
                (mv erp attribute_name parsed-name bytes)))
             ((equal "NestMembers" attribute_name)
              (mv-let (erp parsed-names bytes)
                (parse-nestmembers-attribute bytes constant-pool)
                (mv erp attribute_name parsed-names bytes)))
             ((equal "EnclosingMethod" attribute_name)
              (mv-let (erp info bytes)
                (parse-enclosingmethod-attribute bytes constant-pool)
                (mv erp attribute_name info bytes)))
             (t
              (prog2$
               ;; TODO: Handle these:
               ;; TOOD: Are there any more of these?
               (and (not (member-equal attribute_name '("StackMap" ;; This does seem to be used but is not in the main list of pre-defined attributes.
                                                        "StackMapTable"
                                                        "Signature"
                                                        "LocalVariableTypeTable"
                                                        "InnerClasses"
                                                        "Deprecated"
                                                        "RuntimeInvisibleAnnotations"
                                                        "RuntimeVisibleAnnotations"
                                                        "RuntimeInvisibleParameterAnnotations"
                                                        "RuntimeVisibleParameterAnnotations"
                                                        "RuntimeVisibleTypeAnnotations"
                                                        "RuntimeInvisibleTypeAnnotations"
                                                        "AnnotationDefault"
                                                        "Synthetic"
                                                        "InconsistentHierarchy"
                                                        "MissingTypes"
                                                        "SourceDebugExtension"
                                                        "BootstrapMethods"
                                                        "MethodParameters"
                                                        "NestMembers" ;todo
                                                        )))
                    (cw "Note: Unknown attribute: ~x0.~%" attribute_name))
               (b* (((mv erp info bytes) (readnbytes attribute_length bytes))
                    ((when erp) (mv erp nil nil nil)))
                 (mv (erp-nil)
                     attribute_name
                     ;;these are raw bytes:
                     info
                     bytes))))))))

 ;; returns (mv erp val bytes) where val is an "alist" from attribute names to their values - except that some keys may appear multiple times!
 ;; can't use a record/map since attribute names are not unique in general
 (defun parse-attribute-info-entries (numentries bytes acc constant-pool)
   (declare (xargs :measure (make-ord (+ 1 (len bytes)) 1 (nfix numentries))
                   :guard (and (natp numentries)
                               (true-listp bytes)
                               (all-unsigned-byte-p 8 bytes)
                               (alistp acc)
                               )
                   :stobjs constant-pool))
   (if (zp numentries)
       (mv (erp-nil) acc bytes)
     (b* (((mv erp attribute-name attribute-info bytes2)
           (parse-attribute-info-entry bytes constant-pool))
          ((when erp) (mv erp nil nil)))
       (if (mbt (< (len bytes2) (len bytes))) ;for termination
           (progn$
            ;; (cw "Attribute entry number ~x0 is: ~x1.~%" numentries entry)
            (parse-attribute-info-entries (+ -1 numentries) bytes2 (acons attribute-name attribute-info acc) constant-pool))
         (mv :parse-attribute-info-entries-did-not-consume-any-bytes ;(er hard? 'parse-attribute-info-entries "Did not consume any bytes.")
             nil
             nil))))))

(make-flag parse-code-attribute
           :hints (("Goal" :in-theory (enable readu2 readu4)
                    ;;:expand (PARSE-ATTRIBUTE-INFO-ENTRY BYTES CONSTANT-POOL) ;todo: illegal
                    )))

(defthm-flag-parse-code-attribute
  (defthm all-unsigned-byte-p-8-of-mv-nth-2-of-parse-code-attribute
    (implies (and ;(true-listp bytes)
              (all-unsigned-byte-p 8 bytes))
             (all-unsigned-byte-p 8 (mv-nth 2 (parse-code-attribute bytes constant-pool))))
    :flag parse-code-attribute)
  (defthm all-unsigned-byte-p-8-of-mv-nth-3-of-parse-attribute-info-entry
    (implies (and ;(true-listp bytes)
              (all-unsigned-byte-p 8 bytes))
             (all-unsigned-byte-p 8 (mv-nth 3 (parse-attribute-info-entry bytes constant-pool))))
    :flag parse-attribute-info-entry)
  (defthm all-unsigned-byte-p-8-of-mv-nth-2-of-parse-attribute-info-entries
    (implies (and ;(true-listp bytes)
              (all-unsigned-byte-p 8 bytes))
             (all-unsigned-byte-p 8 (mv-nth 2 (parse-attribute-info-entries numentries bytes acc constant-pool))))
    :flag parse-attribute-info-entries)
  :hints (("Goal" :expand (parse-code-attribute bytes constant-pool)
           :in-theory (enable parse-constantvalue-attribute
                              parse-enclosingmethod-attribute
                              parse-nestmembers-attribute
                              parse-exceptions-attribute
                              parse-sourcefile-attribute
                              parse-signature-attribute
                              parse-nesthost-attribute))))

(defthm-flag-parse-code-attribute
  (defthm true-listp-of-mv-nth-2-of-parse-code-attribute
    (implies (true-listp bytes)
             (true-listp (mv-nth 2 (parse-code-attribute bytes constant-pool))))
    :flag parse-code-attribute)
  (defthm true-listp-of-mv-nth-3-of-parse-attribute-info-entry
    (implies (true-listp bytes)
             (true-listp (mv-nth 3 (parse-attribute-info-entry bytes constant-pool))))
    :flag parse-attribute-info-entry)
  (defthm true-listp-of-mv-nth-2-of-parse-attribute-info-entries
    (implies (true-listp bytes)
             (true-listp (mv-nth 2 (parse-attribute-info-entries numentries bytes acc constant-pool))))
    :flag parse-attribute-info-entries)
  :hints (("Goal" :expand (parse-code-attribute bytes constant-pool)
           :in-theory (enable parse-constantvalue-attribute
                                     parse-enclosingmethod-attribute
                                     parse-nestmembers-attribute
                                     parse-exceptions-attribute
                                     parse-sourcefile-attribute
                                     parse-signature-attribute
                                     parse-nesthost-attribute))))

(defthm-flag-parse-code-attribute
  (defthm <=-of-len-of-mv-nth-2-of-parse-code-attribute
    (<= (len (mv-nth 2 (parse-code-attribute bytes constant-pool)))
        (len bytes))
    :rule-classes :linear
    :flag parse-code-attribute)
  (defthm <=-of-len-of-mv-nth-3-of-parse-attribute-info-entry
    (<= (len (mv-nth 3 (parse-attribute-info-entry bytes constant-pool)))
        (len bytes))
    :rule-classes :linear
    :flag parse-attribute-info-entry)
  (defthm <=-of-len-of-mv-nth-2-of-parse-attribute-info-entries
    (<= (len (mv-nth 2 (parse-attribute-info-entries numentries bytes acc constant-pool)))
        (len bytes))
    :rule-classes :linear
    :flag parse-attribute-info-entries)
  :hints (("Goal" :expand (parse-code-attribute bytes constant-pool)
           :in-theory (enable parse-constantvalue-attribute
                                     parse-enclosingmethod-attribute
                                     parse-nestmembers-attribute
                                     parse-exceptions-attribute
                                     parse-sourcefile-attribute
                                     parse-signature-attribute
                                     parse-nesthost-attribute))))

(defund attribute-info-entries-okp (entries)
  (declare (xargs :guard (alistp entries)))
  (and (or (null (lookup-equal "LocalVariableTable" entries))
           (jvm::local-variable-tablep (lookup-equal "LocalVariableTable" entries)))
       (or (null (lookup-equal "Code" entries))
           (code-attributep (lookup-equal "Code" entries)))))

(defthm code-attributep-of-lookup-equal-of-code
  (implies (attribute-info-entries-okp entries)
           (iff (code-attributep (lookup-equal "Code" entries))
                (lookup-equal "Code" entries)))
  :hints (("Goal" :in-theory (enable attribute-info-entries-okp))))

(defthm-flag-parse-code-attribute
  (defthm code-attributep-of-mv-nth-1-of-parse-code-attribute
    (implies (not (mv-nth 0 (parse-code-attribute bytes constant-pool)))
             (code-attributep (mv-nth 1 (parse-code-attribute bytes constant-pool))))
    :flag parse-code-attribute)
  (defthm mv-nth-2-of-parse-attribute-info-entry-correct
    (implies (not (mv-nth 0 (parse-attribute-info-entry bytes constant-pool)))
             (and (implies (equal "Code" (mv-nth 1 (parse-attribute-info-entry bytes constant-pool)))
                           (code-attributep (mv-nth 2 (parse-attribute-info-entry bytes constant-pool))))
                  (implies (equal "LocalVariableTable" (mv-nth 1 (parse-attribute-info-entry bytes constant-pool)))
                           (jvm::local-variable-tablep (mv-nth 2 (parse-attribute-info-entry bytes constant-pool))))))
    :flag parse-attribute-info-entry)
  (defthm mv-nth-1-of-parse-attribute-info-entries-correct
    (implies (and (not (mv-nth 0 (parse-attribute-info-entries numentries bytes acc constant-pool)))
                  (attribute-info-entries-okp acc)
                  (alistp acc))
             (and (alistp (mv-nth 1 (parse-attribute-info-entries numentries bytes acc constant-pool)))
                  (attribute-info-entries-okp (mv-nth 1 (parse-attribute-info-entries numentries bytes acc constant-pool)))))
    :flag parse-attribute-info-entries)
  :hints (("Goal" :in-theory (enable ATTRIBUTE-INFO-ENTRIES-OKP)
           :expand ((:free (key val alist)
                           (CODE-ATTRIBUTEP (acons key val alist)))
                    (PARSE-CODE-ATTRIBUTE (MV-NTH 2 (READU4 (MV-NTH 2 (READU2 BYTES))))
                                          CONSTANT-POOL)
                    (PARSE-ATTRIBUTE-INFO-ENTRIES NUMENTRIES BYTES ACC CONSTANT-POOL)))))



(defthm bound-on-parse-attribute-info-entry
  (implies (not (mv-nth 0 (parse-attribute-info-entry bytes constant-pool)))
           (< (len (mv-nth 3 (parse-attribute-info-entry bytes constant-pool)))
              (len bytes)))
  :hints (("Goal" :expand (PARSE-ATTRIBUTE-INFO-ENTRY BYTES CONSTANT-POOL)
           :in-theory (enable parse-attribute-info-entry
                              parse-constantvalue-attribute
                              parse-enclosingmethod-attribute
                              parse-nestmembers-attribute
                              parse-exceptions-attribute
                              parse-sourcefile-attribute
                              parse-signature-attribute
                              parse-nesthost-attribute))))


(defthm-flag-parse-code-attribute
  (defthm alistp-of-mv-nth-1-of-parse-code-attribute
    (alistp (mv-nth 1 (parse-code-attribute bytes constant-pool)))
    :flag parse-code-attribute)
  (defthm alistp-of-mv-nth-2-of-parse-attribute-info-entry
    (implies (equal "Code" (mv-nth 1 (parse-attribute-info-entry bytes constant-pool)))
             (alistp (mv-nth 2 (parse-attribute-info-entry bytes constant-pool))))
    :flag parse-attribute-info-entry)
  (defthm alistp-of-lookup-equal-code-of-mv-nth-1-of-parse-attribute-info-entries
    (implies (and ;(true-listp bytes)
              (alistp acc)
              (alistp (LOOKUP-EQUAL "Code" acc)))
             (and (alistp (mv-nth 1 (parse-attribute-info-entries numentries bytes acc constant-pool)))
                  (alistp (LOOKUP-EQUAL "Code" (mv-nth 1 (parse-attribute-info-entries numentries bytes acc constant-pool))))))
    :flag parse-attribute-info-entries)
  :hints (("Goal"  :expand (parse-code-attribute bytes constant-pool)
           :in-theory (enable parse-constantvalue-attribute
                                     parse-enclosingmethod-attribute
                                     parse-nestmembers-attribute
                                     parse-exceptions-attribute
                                     parse-sourcefile-attribute
                                     parse-signature-attribute
                                     parse-nesthost-attribute))))

(verify-guards parse-code-attribute)

(defund maybe-add-flag (flag yesno flags)
  (declare (xargs :guard t))
  (if yesno
      (cons flag flags)
    flags))

(defthm member-equal-of-maybe-add-flag
  (equal (member-equal a (maybe-add-flag b yesno flags))
         (if (and yesno
                  (equal a b))
             (cons b flags)
           (member-equal a flags)))
  :hints (("Goal" :in-theory (enable maybe-add-flag))))

(defthm true-listp-of-maybe-add-flag
  (implies (true-listp flags)
           (true-listp (maybe-add-flag b yesno flags)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable maybe-add-flag))))

(defthm keyword-listp-of-maybe-add-flag
  (implies (and (keyword-listp flags)
                (keywordp flag))
           (keyword-listp (maybe-add-flag flag yesno flags)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable maybe-add-flag))))

(defthm subsetp-equal-of-maybe-add-flag-iff
  (iff (subsetp-equal (maybe-add-flag flag yesno flags) lst)
       (if yesno
           (and (member-equal flag lst)
                (subsetp-equal flags lst))
         (subsetp-equal flags lst)))
  :hints (("Goal" :in-theory (enable maybe-add-flag))))

(defthm no-duplicatesp-equal-of-maybe-add-flag
  (implies (and (not (member-equal flag flags))
                (no-duplicatesp-equal flags))
           (no-duplicatesp-equal (maybe-add-flag flag yesno flags)))
  :hints (("Goal" :in-theory (enable maybe-add-flag))))

(defund raw-field-infop (raw-field-info)
  (declare (xargs :guard t))
  (and (alistp raw-field-info)
       (jvm::field-namep (lookup-equal :name raw-field-info))
       (alistp (lookup-equal :attributes raw-field-info))
       (keyword-listp (lookup-equal :access_flags raw-field-info))
       (no-duplicatesp-equal (lookup-equal :access_flags raw-field-info))
       (subsetp-equal (lookup-equal :access_flags raw-field-info)
                      '(:acc_public :acc_private :acc_protected
                                    :acc_static :acc_final
                                    :acc_volatile :acc_transient
                                    :acc_synthetic :acc_enum))
       (jvm::typep (lookup-equal :descriptor raw-field-info))))

(defund raw-field-infosp (raw-field-infos)
  (declare (xargs :guard t))
  (if (atom raw-field-infos)
      (null raw-field-infos)
    (and (raw-field-infop (first raw-field-infos))
         (raw-field-infosp (rest raw-field-infos)))))

(defthm raw-field-infosp-of-revappend
  (implies (and (raw-field-infosp x)
                (raw-field-infosp y))
           (raw-field-infosp (revappend x y)))
  :hints (("Goal" :in-theory (enable revappend raw-field-infosp))))

;; Returns a list of keywords representing the flags.
(defund parse-class-access-flags (uint16)
  (declare (type (unsigned-byte 16) uint16))
  (let* ((flags nil)
         (flags (maybe-add-flag :ACC_PUBLIC (logbitp 0 uint16) flags))
         (flags (maybe-add-flag :ACC_FINAL (logbitp 4 uint16) flags))
         (flags (maybe-add-flag :ACC_SUPER (logbitp 5 uint16) flags))
         (flags (maybe-add-flag :ACC_INTERFACE (logbitp 9 uint16) flags))
         (flags (maybe-add-flag :ACC_ABSTRACT (logbitp 10 uint16) flags))
         (flags (maybe-add-flag :ACC_SYNTHETIC (logbitp 12 uint16) flags))
         (flags (maybe-add-flag :ACC_ANNOTATION (logbitp 13 uint16) flags))
         (flags (maybe-add-flag :ACC_ENUM (logbitp 14 uint16) flags)))
    flags))

(defthm keyword-listp-of-parse-class-access-flags
  (keyword-listp (parse-class-access-flags uint16))
  :hints (("Goal" :in-theory (enable parse-class-access-flags))))

(defthm no-duplicatesp-equal-of-parse-class-access-flags
  (no-duplicatesp-equal (parse-class-access-flags uint16))
  :hints (("Goal" :in-theory (enable parse-class-access-flags))))

(defthm subsetp-equal-of-parse-class-access-flags
  (subsetp-equal (parse-class-access-flags uint16)
                 '(:acc_public :acc_final
                               :acc_super :acc_interface
                               :acc_abstract :acc_synthetic
                               :acc_annotation :acc_enum))
  :hints (("Goal" :in-theory (enable parse-class-access-flags))))

;; Returns a list of keywords representing the flags.
;It might be more clear to use the masks here that are used in Table 4.6-A,
;instead of using logbitp.  Returns a list of the flags whose bits are set.
(defund parse-method-access-flags (uint16)
  (declare (type (unsigned-byte 16) uint16))
  (let* ((flags nil)
         (flags (maybe-add-flag :ACC_PUBLIC (logbitp 0 uint16) flags))
         (flags (maybe-add-flag :ACC_PRIVATE (logbitp 1 uint16) flags))
         (flags (maybe-add-flag :ACC_PROTECTED (logbitp 2 uint16) flags))
         (flags (maybe-add-flag :ACC_STATIC (logbitp 3 uint16) flags))
         (flags (maybe-add-flag :ACC_FINAL (logbitp 4 uint16) flags))
         (flags (maybe-add-flag :ACC_SYNCHRONIZED (logbitp 5 uint16) flags))
         (flags (maybe-add-flag :ACC_BRIDGE (logbitp 6 uint16) flags))
         (flags (maybe-add-flag :ACC_VARARGS (logbitp 7 uint16) flags))
         (flags (maybe-add-flag :ACC_NATIVE (logbitp 8 uint16) flags))
         (flags (maybe-add-flag :ACC_ABSTRACT (logbitp 10 uint16) flags))
         (flags (maybe-add-flag :ACC_STRICT (logbitp 11 uint16) flags))
         (flags (maybe-add-flag :ACC_SYNTHETIC (logbitp 12 uint16) flags)))
    flags))

(defthm keyword-listp-of-parse-method-access-flags
  (keyword-listp (parse-method-access-flags uint16))
  :hints (("Goal" :in-theory (enable parse-method-access-flags))))

(defthm no-duplicatesp-equal-of-parse-method-access-flags
  (no-duplicatesp-equal (parse-method-access-flags uint16))
  :hints (("Goal" :in-theory (enable parse-method-access-flags))))

(defthm subsetp-equal-of-parse-method-access-flags
  (subsetp-equal (parse-method-access-flags uint16)
                 '(:ACC_PUBLIC :ACC_PRIVATE
                               :ACC_PROTECTED :ACC_STATIC
                               :ACC_FINAL :ACC_SYNCHRONIZED
                               :ACC_BRIDGE :ACC_VARARGS
                               :ACC_NATIVE :ACC_ABSTRACT
                               :ACC_STRICT :ACC_SYNTHETIC))
  :hints (("Goal" :in-theory (enable parse-method-access-flags))))


;; Returns a list of keywords representing the flags.
(defund parse-field-access-flags (uint16)
  (declare (type (unsigned-byte 16) uint16))
  (let* ((flags nil)
         (flags (maybe-add-flag :ACC_PUBLIC (logbitp 0 uint16) flags))
         (flags (maybe-add-flag :ACC_PRIVATE (logbitp 1 uint16) flags))
         (flags (maybe-add-flag :ACC_PROTECTED (logbitp 2 uint16) flags))
         (flags (maybe-add-flag :ACC_STATIC (logbitp 3 uint16) flags))
         (flags (maybe-add-flag :ACC_FINAL (logbitp 4 uint16) flags))
         (flags (maybe-add-flag :ACC_VOLATILE (logbitp 6 uint16) flags))
         (flags (maybe-add-flag :ACC_TRANSIENT (logbitp 7 uint16) flags))
         (flags (maybe-add-flag :ACC_SYNTHETIC (logbitp 12 uint16) flags))
         (flags (maybe-add-flag :ACC_ENUM (logbitp 14 uint16) flags)))
    flags))

(defthm keyword-listp-of-parse-field-access-flags
  (keyword-listp (parse-field-access-flags uint16))
  :hints (("Goal" :in-theory (enable parse-field-access-flags))))

(defthm no-duplicatesp-equal-of-parse-field-access-flags
  (no-duplicatesp-equal (parse-field-access-flags uint16))
  :hints (("Goal" :in-theory (enable parse-field-access-flags))))

(defthm subsetp-equal-of-parse-field-access-flags
  (subsetp-equal (parse-field-access-flags uint16)
                 '(:acc_public :acc_private :acc_protected
                               :acc_static :acc_final
                               :acc_volatile :acc_transient
                               :acc_synthetic :acc_enum))
  :hints (("Goal" :in-theory (enable parse-field-access-flags))))

;; Returns (mv erp field-info bytes).
(defund parse-field-info-entry (bytes constant-pool)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              )
                  :stobjs constant-pool))
  (b* (((mv erp access_flags bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp name_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp name-entry) (lookup-in-constant-pool name_index constant-pool))
       ((when erp) (mv erp nil nil))
       (name (lookup-eq-safe 'bytes name-entry))
       ((when (not (jvm::field-namep name))) ;todo: prove this can't happen
        (mv :bad-field-name nil bytes))
       ((mv erp descriptor_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp descriptor-entry) (lookup-in-constant-pool descriptor_index constant-pool))
       ((when erp) (mv erp nil nil))
       (descriptor (lookup-eq-safe 'bytes descriptor-entry))
       ((when (not (stringp descriptor)))
        (mv :bad-descriptor nil nil))
       ((mv erp type) (jvm::parse-descriptor descriptor))
       ((when erp) (mv erp nil nil))
       ((mv erp attributes_count bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp attributes bytes)
        (parse-attribute-info-entries attributes_count
                                      bytes
                                      nil ;initial accumulator
                                      constant-pool
                                      ))
       ((when erp) (mv erp nil nil)))
    (mv (erp-nil)
        (acons :name name
               (acons :descriptor type ;todo change the key to 'type
                      (acons :access_flags (parse-field-access-flags access_flags)
                             (acons :attributes attributes nil))))
        bytes)))

(defthm raw-field-infop-of-mv-nth-1-of-parse-field-info-entry
  (implies (not (mv-nth 0 (parse-field-info-entry bytes constant-pool)))
           (raw-field-infop (mv-nth 1 (parse-field-info-entry bytes constant-pool))))
  :hints (("Goal" :in-theory (enable raw-field-infop parse-field-info-entry))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-parse-field-info-entry
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (parse-field-info-entry bytes constant-pool))))
  :hints (("Goal" :in-theory (enable parse-field-info-entry))))

(defthm true-listp-of-mv-nth-2-of-parse-field-info-entry
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (parse-field-info-entry bytes constant-pool))))
  :hints (("Goal" :in-theory (enable parse-field-info-entry))))

;; Returns (mv erp field-info bytes).
(defund parse-field-info-entries (numentries bytes acc constant-pool)
  (declare (xargs :guard (and (natp numentries)
                              (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (true-listp acc)
                              )
                  :stobjs constant-pool))
  (if (zp numentries)
      (mv (erp-nil) (reverse acc) bytes)
    (b* (((mv erp entry bytes)
          (parse-field-info-entry bytes constant-pool))
         ((when erp) (mv erp nil nil))
         ;; (- (cw "Field entry number ~x0 is: ~x1.~%" numentries entry))
         )
      (parse-field-info-entries (+ -1 numentries) bytes (cons entry acc) constant-pool))))

(defthm raw-field-infosp-of-mv-nth-1-of-parse-field-info-entries
  (implies (raw-field-infosp acc)
           (raw-field-infosp (mv-nth 1 (parse-field-info-entries numentries bytes acc constant-pool))))
  :hints (("Goal" :in-theory (enable raw-field-infosp parse-field-info-entries))))

(defthm true-listp-of-mv-nth-2-of-parse-field-info-entries
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (parse-field-info-entries numentries bytes acc constant-pool))))
  :hints (("Goal" :in-theory (enable parse-field-info-entries))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-parse-field-info-entries
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (parse-field-info-entries numentries bytes acc constant-pool))))
  :hints (("Goal" :in-theory (enable parse-field-info-entries))))

(defund raw-method-infop (raw-method-info)
  (declare (xargs :guard t))
  (and (alistp raw-method-info)
       (stringp (lookup-equal :name raw-method-info))
       (jvm::method-descriptorp (lookup-equal :descriptor raw-method-info))
       (let ((access-flags (lookup-equal :access_flags raw-method-info))
             (parameter-types (lookup-equal :parameter-types raw-method-info))
             (return-type (lookup-equal :return-type raw-method-info))
             (attributes (lookup-equal :attributes raw-method-info)))
         (and
          (keyword-listp access-flags)
          (no-duplicatesp-equal access-flags)
          (acl2::subsetp-eq access-flags
                            '(:acc_public
                              :acc_private
                              :acc_protected
                              :acc_static
                              :acc_final
                              :acc_synchronized
                              :acc_bridge
                              :acc_varargs
                              :acc_native
                              :acc_abstract
                              :acc_strict
                              :acc_synthetic))
          (jvm::all-typep parameter-types)
          (true-listp parameter-types)
          (jvm::return-typep return-type)
          (alistp attributes)
          (let ((code-attribute (lookup-equal "Code" attributes)))
            (and (or (null code-attribute) ;todo: maybe use :none?
                     (code-attributep code-attribute))
                 ;; TODO: Check this wrt 4.7.3 of the spec:
                 (implies (and (not (member-eq :acc_abstract access-flags))
                               (not (member-eq :acc_native access-flags)))
                          (code-attributep code-attribute))))))))

(defund raw-method-infosp (raw-method-infos)
  (declare (xargs :guard t))
  (if (atom raw-method-infos)
      (null raw-method-infos)
    (and (raw-method-infop (first raw-method-infos))
         (raw-method-infosp (rest raw-method-infos)))))

;Returns (mv erp raw-method-info bytes).
(defund parse-method-info-entry (bytes constant-pool)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              )
                  :guard-hints (("Goal" :in-theory (enable alistp)))
                  :stobjs constant-pool))
  (b* (((mv erp access_flags bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp name_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp name-entry) (lookup-in-constant-pool name_index constant-pool))
       ((when erp) (mv erp nil nil))
       (name (lookup-eq-safe 'bytes name-entry))
       ((when (not (stringp name))) (mv `(:bad-name ,name) nil nil))
       ((mv erp descriptor_index bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp descriptor-entry) (lookup-in-constant-pool descriptor_index constant-pool))
       ((when erp) (mv erp nil nil))
       (descriptor (lookup-eq-safe 'bytes descriptor-entry))
       ((when (not (jvm::method-descriptorp descriptor)))
        (mv :bad-descriptor nil nil))
       ((mv erp parameter-types return-type)
        (jvm::parse-method-descriptor descriptor))
       ((when erp) (mv erp nil nil))
       ((mv erp attributes_count bytes) (readu2 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp attributes bytes)
        (parse-attribute-info-entries
         attributes_count
         bytes
         nil ;initial accumulator
         constant-pool))
       ((when erp) (mv erp nil nil))
       (access-flags (parse-method-access-flags access_flags))
       (code-attribute (lookup-equal "Code" attributes))
       ((when (not (iff (or (member-eq :acc_abstract access-flags)
                            (member-eq :acc_native access-flags))
                        (not (consp (lookup-equal :code code-attribute))))))
        ;; method has code but shouldn't because it is native or abstract, or vice versa:
        (mv :bad-method
            nil
            bytes)))
    (mv (erp-nil)
        (acons :name name
               (acons :descriptor descriptor
                      (acons :access_flags access-flags
                             (acons :parameter-types parameter-types
                                    (acons :return-type return-type
                                           (acons :attributes attributes nil))))))
        bytes)))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-parse-method-info-entry
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (parse-method-info-entry bytes constant-pool))))
  :hints (("Goal" :in-theory (enable parse-method-info-entry))))

(defthm true-listp-of-mv-nth-2-of-parse-method-info-entry
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (parse-method-info-entry bytes constant-pool))))
  :hints (("Goal" :in-theory (enable parse-method-info-entry))))

(defthm raw-method-infop-of-mv-nth-1-of-parse-method-info-entry
  (implies (not (mv-nth 0 (parse-method-info-entry bytes constant-pool))) ;no error
           (raw-method-infop (mv-nth 1 (parse-method-info-entry bytes constant-pool))))
  :hints (("Goal" :in-theory (enable raw-method-infop parse-method-info-entry))))

;; Returns (mv erp raw-method-infos bytes).
(defund parse-method-info-entries (numentries bytes acc constant-pool)
  (declare (xargs :guard (and (natp numentries)
                              (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes)
                              (true-listp acc)
                              )
                  :stobjs constant-pool))
  (if (zp numentries)
      (mv (erp-nil) acc bytes)
    (b* (((mv erp method-info-entry bytes)
          (parse-method-info-entry bytes constant-pool))
         ((when erp) (mv erp nil nil)))
      (parse-method-info-entries (+ -1 numentries) bytes (cons method-info-entry acc) constant-pool))))

(defthm raw-method-infosp-of-mv-nth-1-of-parse-method-info-entries
  (implies (raw-method-infosp acc)
           (raw-method-infosp (mv-nth 1 (parse-method-info-entries numentries bytes acc constant-pool))))
  :hints (("Goal" :in-theory (enable raw-method-infosp parse-method-info-entries))))

(defthm true-listp-of-mv-nth-2-of-parse-method-info-entries
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (parse-method-info-entries numentries bytes acc constant-pool))))
  :hints (("Goal" :in-theory (enable parse-method-info-entries))))

(defthm all-unsigned-byte-p-8-of-mv-nth-2-of-parse-method-info-entries
  (implies (all-unsigned-byte-p 8 bytes)
           (all-unsigned-byte-p 8 (mv-nth 2 (parse-method-info-entries numentries bytes acc constant-pool))))
  :hints (("Goal" :in-theory (enable parse-method-info-entries))))

;maybe every function should take the remaining bytes and the current info and return fewer bytes with some info added to info

;; Returns (mv erp name-or-none).
(defund parse-super_class (super_class constant-pool)
  (declare (xargs :guard (and (natp super_class)
                              )
                  :stobjs constant-pool))
  (if (equal 0 super_class) ;; only can happen for class Object
      (mv (erp-nil) :none)  ;"dummy-superclass-for-Object"
    (b* (((mv erp superclass-name) (get-class-name-from-src super_class constant-pool)) ;fixme can this be an array class?
         ((when erp) (mv erp nil)))
      (if (not (stringp superclass-name))
          (mv :bad-superclass nil)
        (mv (erp-nil)
            (turn-slashes-into-dots superclass-name))))))

(defthm class-namep-of-mv-nth-1-of-parse-super_class
  (implies (and (not (mv-nth 0 (parse-super_class super_class constant-pool)))
                (not (equal :none (mv-nth 1 (parse-super_class super_class constant-pool)))))
           (jvm::class-namep (mv-nth 1 (parse-super_class super_class constant-pool))))
  :hints (("Goal" :in-theory (enable parse-super_class))))

(defund superclass-and-interfaceness-okp (class-name superclass interfacep)
  (declare (xargs :guard t))
  (and ;; check the superclass:
   (if (equal class-name "java.lang.Object")
       (eq :none superclass)
     (if interfacep
         ;; the superclass of an interface is java.lang.Object (see jvms: the classfile structure)
         (equal "java.lang.Object" superclass)
       (jvm::class-namep superclass)))
   ;; and check that Object is not an interface:
   (not (and (equal class-name "java.lang.Object")
             interfacep))))

;;;
;;; raw-parsed-classp
;;;

(defund raw-parsed-classp (raw-parsed-class)
  (declare (xargs :guard t))
  (and (alistp raw-parsed-class)
       (raw-field-infosp (lookup-equal :fields raw-parsed-class))
       (raw-method-infosp (lookup-equal :methods raw-parsed-class))
       (keyword-listp (lookup-equal ':access_flags raw-parsed-class))
       (no-duplicatesp-equal (lookup-equal ':access_flags raw-parsed-class))
       (subsetp-equal (lookup-equal ':access_flags raw-parsed-class)
                      '(:acc_public :acc_final
                                    :acc_super :acc_interface
                                    :acc_abstract :acc_synthetic
                                    :acc_annotation :acc_enum))
       (true-listp (lookup-equal ':interfaces raw-parsed-class))
       (jvm::all-class-namesp (lookup-equal ':interfaces raw-parsed-class))
       ;; check the super class, etc:
       (let ((class-name (acl2::lookup-eq :this_class raw-parsed-class))
             (superclass (acl2::lookup-eq :super_class raw-parsed-class))
             (interfacep (member-eq :acc_interface (acl2::lookup-eq :access_flags raw-parsed-class))))
         (and (jvm::class-namep class-name)
              (superclass-and-interfaceness-okp class-name superclass interfacep)))))

(defthm raw-parsed-classp-forward-to-alistp
  (implies (raw-parsed-classp raw-parsed-class)
           (alistp raw-parsed-class))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable raw-parsed-classp))))

(defthmd stringp-of-lookup-equal-of-this-class-when-raw-parsed-classp
  (implies (raw-parsed-classp raw-parsed-class)
           (stringp (lookup-equal :this_class raw-parsed-class)))
  :hints (("Goal" :in-theory (enable raw-parsed-classp))))

(defthm class-namep-of-lookup-equal-of-this-class-when-raw-parsed-classp
  (implies (raw-parsed-classp raw-parsed-class)
           (jvm::class-namep (lookup-equal :this_class raw-parsed-class)))
  :hints (("Goal" :in-theory (enable raw-parsed-classp))))

(defthmd class-namep-of-lookup-equal-of-superclass-when-raw-parsed-classp
  (implies (raw-parsed-classp raw-parsed-class)
           (equal (jvm::class-namep (lookup-equal :super_class raw-parsed-class))
                  (not (equal (lookup-equal :this_class raw-parsed-class) "java.lang.Object"))))
  :hints (("Goal" :in-theory (enable raw-parsed-classp
                                      superclass-and-interfaceness-okp))))

(defthmd lookup-equal-of-superclass-when-raw-parsed-classp-and-interface
  (implies (and (raw-parsed-classp raw-parsed-class)
                (member-equal :acc_interface (lookup-equal :access_flags raw-parsed-class)))
           (equal (lookup-equal :super_class raw-parsed-class)
                  "java.lang.Object"))
  :hints (("Goal" :in-theory (enable raw-parsed-classp
                                     superclass-and-interfaceness-okp))))

(defthmd equal-of-none-of-lookup-equal-of-superclass-when-raw-parsed-classp
  (implies (raw-parsed-classp raw-parsed-class)
           (equal (EQUAL :NONE (LOOKUP-EQUAL :SUPER_CLASS RAW-PARSED-CLASS))
                  (equal (LOOKUP-EQUAL :this_CLASS RAW-PARSED-CLASS) "java.lang.Object")))
  :hints (("Goal" :in-theory (enable raw-parsed-classp
                                      superclass-and-interfaceness-okp))))

;;;
;;; parse-bytes-into-raw-parsed-class
;;;

;; STEP 1:
;; Parses the BYTES, as a Java class file.  Returns (mv erp raw-parsed-class constant-pool), where the raw-parsed-class is an alist.
(defund parse-bytes-into-raw-parsed-class (bytes constant-pool)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes))
                  :stobjs constant-pool))
  (b* ((info nil)
       ((mv erp magic bytes) (readu4 bytes))
       ((when erp) (mv erp nil constant-pool))
       ((when (not (equal magic #xCAFEBABE)))
        (er hard? 'parse-bytes-into-raw-parsed-class  "Incorrect magic number.  The file does not appear to be a valid class file.")
        (mv t nil constant-pool))
       ((mv erp & ;minor_version
            bytes)
        (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       ;;(info (acons :minor_version minor_version info))
       ((mv erp & ;major_version
            bytes)
        (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       ;;(info (acons :major_version major_version info))
       ((mv erp constant_pool_count bytes) (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       ;; constant_pool_count is one more than the actual count, so cannot be 0
       ((when (not (posp constant_pool_count)))
        (mv :bad-constant-pool-count nil constant-pool))
       (num-constant-pool-entries (+ -1 constant_pool_count)) ; constant_pool_count is one more than the number of entries
       (array-size-needed (+ 1 num-constant-pool-entries)) ; since entries are numbered from 1 to num-constant-pool-entries
       (constant-pool (if (< (entries-length constant-pool) array-size-needed)
                          (resize-entries array-size-needed constant-pool)
                        constant-pool))
       ((mv erp constant-pool bytes)
        (parse-constant-pool-entries
         1 ; first constant pool index
         num-constant-pool-entries ; max index
         bytes
         constant-pool))
       ((when erp) (mv erp nil constant-pool))
       ;;(info (acons :constant_pool constant-pool info))  ;omitted since we look up all references in it
       ((mv erp access_flags bytes) (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       (access-flags (parse-class-access-flags access_flags))
       (info (acons :access_flags
                    access-flags
                    info))
       ((mv erp this_class-cp-index bytes) (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       ((mv erp this-class-name) (get-class-name-from-src this_class-cp-index constant-pool))
       ((when erp) (mv erp nil constant-pool))
       ((when (not (jvm::class-namep this-class-name)))
        (er hard? 'parse-bytes-into-raw-parsed-class "Unexpected class name: ~x0." this-class-name)
        (mv `(:expected-class-name ,this-class-name) nil constant-pool))
       (info (acons :this_class this-class-name info))
       ((mv erp super_class bytes) (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       ((mv erp superclass-name) (parse-super_class super_class constant-pool))
       ((when erp) (mv erp nil constant-pool))
       (info (acons :super_class superclass-name info))
       ((mv erp interfaces_count bytes) (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       ((mv erp interfaces bytes) (readu2s interfaces_count bytes))
       ((when erp) (mv erp nil constant-pool))
       ((mv erp interface-names) (get-class-names-from-srcs interfaces constant-pool))
       ((when erp) (mv erp nil constant-pool))
       ((when (not (jvm::all-class-namesp interface-names))) ; exclude array classes?
        (mv :unexpected-interface-name nil constant-pool))
       (info (acons :interfaces interface-names info))
       ((mv erp fields_count bytes) (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       ((mv erp field-info-entries bytes)
        (parse-field-info-entries fields_count
                                  bytes
                                  nil ;initial accumulator
                                  constant-pool))
       ((when erp) (mv erp nil constant-pool))
       (info (acons :fields field-info-entries info))
       ((mv erp methods_count bytes) (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       ((mv erp method-info-entries bytes)
        (parse-method-info-entries methods_count
                                   bytes
                                   nil ;initial accumulator
                                   constant-pool))
       ((when erp) (mv erp nil constant-pool))
       (info (acons :methods method-info-entries info))
       ((mv erp attributes_count bytes) (readu2 bytes))
       ((when erp) (mv erp nil constant-pool))
       ((mv erp attributes & ;bytes  ;fixme check that no bytes remain?
            )
        (parse-attribute-info-entries attributes_count
                                      bytes
                                      nil ;initial accumulator
                                      constant-pool))
       ((when erp) (mv erp nil constant-pool))
       (info (acons :attributes attributes info))
       (interfacep (member-eq :acc_interface access-flags))
       ((when (not (superclass-and-interfaceness-okp this-class-name
                                                      superclass-name
                                                      interfacep)))
        (mv :bad-class nil constant-pool)))
    (mv (erp-nil) info constant-pool)))

(defthm raw-parsed-classp-of-mv-nth-1-of-parse-bytes-into-raw-parsed-class
  (implies (not (mv-nth 0 (parse-bytes-into-raw-parsed-class bytes constant-pool)))
           (raw-parsed-classp (mv-nth 1 (parse-bytes-into-raw-parsed-class bytes constant-pool))))
  :hints (("Goal" :in-theory (enable parse-bytes-into-raw-parsed-class raw-parsed-classp))))

(defthm alistp-of-mv-nth-1-of-parse-bytes-into-raw-parsed-class
  (alistp (mv-nth 1 (parse-bytes-into-raw-parsed-class bytes constant-pool)))
  :hints (("Goal" :in-theory (enable parse-bytes-into-raw-parsed-class))))

;fixme what if there is more than 1 attribute with that name?
;todo: do we need this error checking?
(defund get-attribute (name attribs signal-errorp)
  (declare (xargs :guard (and (stringp name)
                              (alistp attribs))))
  (let ((res (assoc-equal name attribs)))
    (if (not res)
        (if signal-errorp
            (er hard? 'get-attribute "Found no attribute named ~x0.~%" name)
          nil)
      (cdr res))))

(defthm get-attribute-becomes-lookup-equal
  (equal (get-attribute name attribs signal-errorp)
         (lookup-equal name attribs))
  :hints (("Goal" :in-theory (enable get-attribute))))

;where should this go?
(defun full-method-name (class-name method-name method-signature-string)
  (declare (xargs :guard (and (jvm::class-namep class-name)
                              (jvm::method-namep method-name)
                              (stringp method-signature-string) ;fixme call something better
                              )))
  (concatenate 'string class-name "." method-name "-" method-signature-string))

(defund full-field-name (class-name field-name)
  (declare (xargs :guard (and (jvm::class-namep class-name)
                              (jvm::field-namep field-name))))
  (concatenate 'string class-name "." field-name))

;; TODO: distinguish between fully-qualified and non-fully-qualified field names
;; (defthm jvm::field-namep-of-full-field-name
;;   (jvm::field-namep (full-field-name class-name field-name)))

;; ;throws a hard-error if there is not exactly one object in the file
;; (defun read-single-object (filename ctx state)
;;   (declare (xargs :stobjs state
;;                   :mode :program))
;;   (mv-let (erp lst state)
;;           (read-list filename ctx state)
;;           (if (equal 1 (len lst))
;;               (mv erp (car lst) state)
;;             (mv t
;;                 (er hard? 'read-single-object
;;                             "We expected exactly one object in the file ~x0 but we found ~x1."
;;                             filename (len lst))
;;                 state))))

;; ;returns (mv parsed-class state)
;; ;read in the class file for class-name
;; (defun read-in-class (class-name state)
;;   (declare (xargs :stobjs state :mode :program))
;;   (mv-let (erp parsed-class state)
;;           (read-single-object (string-append class-name ".acl2parsedclassfile")
;;                               'read-in-class
;;                               state)
;;           (declare (ignore erp)) ;fixme check the erp flag?
;;           (mv parsed-class state)))

;; ;; static-flg is t or nil depending on whether we are getting static fields or non-static-fields
;; (defun get-field-names-and-descriptors (fields static-flg)
;; ;  (declare (xargs :mode :program))
;;   (if (endp fields)
;;       nil
;;     (let* ((current-field-info (car fields))
;;            (field-name (lookup-eq :name current-field-info))
;;            (descriptor (lookup-eq :descriptor current-field-info))
;;            (access_flags (lookup-eq :access_flags current-field-info)))
;;       (if (equal static-flg (member-eq :acc_static access_flags))
;;           (s field-name
;;              descriptor
;;              (get-field-names-and-descriptors (cdr fields) static-flg))
;;         (get-field-names-and-descriptors (cdr fields) static-flg)))))

(defun field-constant-name (full-field-name)
    (declare (xargs :guard (jvm::field-namep full-field-name)))
    (intern (concatenate 'string "*" full-field-name "-FIELD*") "ACL2"))

;for ConstantValue fields only!
(defun field-value-name (full-field-name)
    (declare (xargs :guard (jvm::field-namep full-field-name)))
    (intern (concatenate 'string "*" full-field-name "*") "ACL2"))

;; Returns (mv defconsts non-static-field-info-alist static-field-info-alist)
(defund add-field-info (raw-field-info
                        class-name
                        defconsts                   ; an accumulator
                        non-static-field-info-alist ; an accumulator
                        static-field-info-alist     ; an accumulator
                        )
  (declare (xargs :guard (and (raw-field-infop raw-field-info)
                              (jvm::class-namep class-name)
                              (true-listp defconsts)
                              (alistp non-static-field-info-alist)
                              (alistp static-field-info-alist))
                  :guard-hints (("Goal" :in-theory (enable raw-field-infop)))))
  (let* ((field-name (lookup-eq :name raw-field-info))
         ;; Both the name and type are needed to uniquely identify a field:
         (type (lookup-eq :descriptor raw-field-info))
         (field-id (cons field-name type)) ;todo: call make-field-id
         (access-flags (lookup-eq :access_flags raw-field-info))
         (attributes (lookup-eq :attributes raw-field-info))
         (static-flag (memberp :acc_static access-flags))
         ;; We could check here that only one of public/private/protected is selected.
         ;;ffixme handle attributes here
         (full-field-name (full-field-name class-name field-name))
         ;; (field-constant-name (field-constant-name full-field-name))
         (field-info nil)
         (field-info (maybe-acons :access-flags access-flags field-info))
         (field-info (maybe-acons :attributes attributes field-info)) ;some attribs may not be handled and so give raw bytes
         ;;(field-defconst `(defconst ,field-constant-name ',(check-field-infop field-info)))  ;could use mydefconst here, but I worry about clashes..
         (constant-value-attribute (get-attribute "ConstantValue" attributes nil)))
    ;; TODO: Save space by not generating the field-info constants, or by referring to them in the class constant (like we used to do)?
    (mv
     ;; maybe add a defconst:
     (if constant-value-attribute ;todo: also check that the field is final?
         (cons `(defconst ,(field-value-name full-field-name) ;could use mydefconst here, but I worry about clashes..
                  ,constant-value-attribute)
               defconsts)
       defconsts)
     ;; maybe update the non-static-field-info-alist:
     (if static-flag
         non-static-field-info-alist ;this field is static, so update the other alist
       (acons field-id
              field-info
              non-static-field-info-alist))
     ;; update the static-field-info-alist:
     (if static-flag
         (acons field-id
                field-info
                static-field-info-alist)
       static-field-info-alist ;this field is not static, so update the other alist
       ))))

(defthm true-listp-of-mv-nth-0-of-add-field-info
  (implies (true-listp defconsts)
           (true-listp (mv-nth 0 (add-field-info raw-field-info class-name defconsts non-static-field-info-alist static-field-info-alist))))
  :hints (("Goal" :in-theory (enable add-field-info))))

(defthm alistp-of-mv-nth-1-of-add-field-info
  (implies (alistp non-static-field-info-alist)
           (alistp (mv-nth 1 (add-field-info raw-field-info class-name defconsts non-static-field-info-alist static-field-info-alist))))
  :hints (("Goal" :in-theory (enable add-field-info))))

(defthm field-info-alistp-of-mv-nth-1-of-add-field-info
  (implies (and (jvm::field-info-alistp non-static-field-info-alist)
                (raw-field-infop raw-field-info))
           (jvm::field-info-alistp (mv-nth 1 (add-field-info raw-field-info class-name defconsts non-static-field-info-alist static-field-info-alist))))
  :hints (("Goal" :in-theory (enable add-field-info JVM::FIELD-INFO-ALISTP
                                     maybe-acons
                                     JVM::FIELD-INFOP ;todo
                                     JVM::FIELD-IDP ;todo
                                     raw-field-infop
                                     ))))

(defthm alistp-of-mv-nth-2-of-add-field-info
  (implies (alistp static-field-info-alist)
           (alistp (mv-nth 2 (add-field-info raw-field-info class-name defconsts non-static-field-info-alist static-field-info-alist))))
  :hints (("Goal" :in-theory (enable add-field-info))))

(defthm field-info-alistp-of-mv-nth-2-of-add-field-info
  (implies (and (jvm::field-info-alistp static-field-info-alist)
                (raw-field-infop raw-field-info))
           (jvm::field-info-alistp (mv-nth 2 (add-field-info raw-field-info class-name defconsts non-static-field-info-alist static-field-info-alist))))
  :hints (("Goal" :in-theory (enable add-field-info JVM::FIELD-INFO-ALISTP
                                     maybe-acons
                                     JVM::FIELD-INFOP ;todo
                                     JVM::FIELD-IDP ;todo
                                     raw-field-infop
                                     ))))

;; Returns (mv field-defconsts non-static-field-info-list static-field-info-list)
(defun field-defconsts-and-infos (raw-field-infos
                                  class-name
                                  defconsts                   ; an accumulator
                                  non-static-field-info-alist ; an accumulator
                                  static-field-info-alist     ; an accumulator
                                  )
  (declare (xargs :guard (and (raw-field-infosp raw-field-infos)
                              (jvm::class-namep class-name)
                              (true-listp defconsts)
                              (alistp non-static-field-info-alist)
                              (alistp static-field-info-alist))
                  :guard-hints (("Goal" :in-theory (enable raw-field-infosp)))))
  (if (endp raw-field-infos)
      (mv defconsts non-static-field-info-alist static-field-info-alist) ;could reverse these
    (mv-let (defconsts non-static-field-info-alist static-field-info-alist)
      (add-field-info (first raw-field-infos) class-name defconsts non-static-field-info-alist static-field-info-alist)
      (field-defconsts-and-infos (rest raw-field-infos) class-name defconsts non-static-field-info-alist static-field-info-alist))))

(defthm true-listp-of-mv-nth-0-of-field-defconsts-and-infos
  (implies (true-listp defconsts)
           (true-listp (mv-nth 0 (field-defconsts-and-infos raw-field-infos class-name defconsts non-static-field-info-alist static-field-info-alist))))
  :hints (("Goal" :in-theory (enable field-defconsts-and-infos))))

(defthm field-info-alistp-of-mv-nth-1-of-field-defconsts-and-infos
  (implies (and (jvm::field-info-alistp non-static-field-info-alist)
                (raw-field-infosp raw-field-infos))
           (jvm::field-info-alistp (mv-nth 1 (field-defconsts-and-infos raw-field-infos class-name defconsts non-static-field-info-alist static-field-info-alist))))
  :hints (("Goal" :in-theory (enable field-defconsts-and-infos raw-field-infosp))))

(defthm field-info-alistp-of-mv-nth-2-of-field-defconsts-and-infos
  (implies (and (jvm::field-info-alistp static-field-info-alist)
                (raw-field-infosp raw-field-infos))
           (jvm::field-info-alistp (mv-nth 2 (field-defconsts-and-infos raw-field-infos class-name defconsts non-static-field-info-alist static-field-info-alist))))
  :hints (("Goal" :in-theory (enable field-defconsts-and-infos raw-field-infosp))))

;; (defun method-constant-name (full-method-name)
;;   (declare (xargs :mode :program))
;;   (packn (list '* full-method-name '-method*)))

;; ;FFIXME think about what to do if the method is abstract - should it go in the class file? it has no code...
;; (defun process-methods (class-name methods)
;;   (declare (xargs :mode :program))
;;   (if (endp methods)
;;       '(empty-alist)
;;     (let* ((entry (car methods))
;;            (name-descriptor-pair (car entry))
;;            (method-name (car name-descriptor-pair))
;;            (descriptor (cdr name-descriptor-pair))
;;            (full-method-name (full-method-name class-name method-name descriptor))
;;            (method-constant-name (method-constant-name full-method-name)))
;;       `(acons ',name-descriptor-pair ,method-constant-name
;;               ,(process-methods class-name (cdr methods))))))

;; ;; static-flg is t or nil depending on whether we are getting static fields or non-static-fields
;; ;builds a form that evaluates to an alist from field-name-descriptor-pairs to field-infos
;; (defun process-fields (fields class-name static-flg)
;;   (declare (xargs :mode :program))
;;   (if (endp fields)
;;       '(empty-alist)
;;     (let* ((current-field-info (first fields))
;;            (access_flags (lookup-eq :access_flags current-field-info)))
;;       (if (not (equal static-flg (member-eq :acc_static access_flags)))
;;           ;;it's a static field and we are looking for non-static fields, or vice versa:
;;           (process-fields (cdr fields) class-name static-flg)
;;         (let* ((field-name (lookup-eq :name current-field-info))
;;                ;; Both the name and descriptor are needed to uniquely identify a field:
;;                (descriptor (lookup-eq :descriptor current-field-info))
;;                (full-field-name (full-field-name class-name field-name))
;;                (field-constant-name (field-constant-name full-field-name)))
;;           `(acons ',(cons field-name descriptor)
;;                   ,field-constant-name
;;                   ,(process-fields (rest fields) class-name static-flg)))))))

;; Returns an extension of ACC with info about this method.
; (previously, this made a separate defconst for the method code and a separate mydefconst for the method info)
;FFIXME think about what to do if the method is abstract - should it go in the class file? it has no code... yes! right?
(defund extend-method-info-alist (raw-method-info acc)
  (declare (xargs :guard (and (raw-method-infop raw-method-info)
                              (jvm::method-info-alistp acc))
                  :guard-hints (("Goal" :in-theory (enable raw-method-infop
                                                           CODE-ATTRIBUTEP)))))
  (let* ((method-name (lookup-eq :name raw-method-info))
         (descriptor (lookup-eq :descriptor raw-method-info))
         (method-id (jvm::make-method-id method-name descriptor))
         (access-flags (lookup-eq :access_flags raw-method-info))
         (parameter-types (lookup-eq :parameter-types raw-method-info))
         (return-type (lookup-eq :return-type raw-method-info))
         (attributes (lookup-eq :attributes raw-method-info))
         ;; (- (cw "Method attribs: ~x0~%" attributes)) ;TODO: Add these to the method-info structure instead of the specific ones like local-variable-table?
         (native-flag (memberp :acc_native access-flags))
         (abstract-flag (memberp :acc_abstract access-flags))
         (no-codep (or abstract-flag native-flag)) ;; if it's abstract or native it has no code
         (code-attribute (and (not no-codep) (get-attribute "Code" attributes t)))
         (code (lookup-eq :code code-attribute))             ;might be nil
         (max-locals (lookup-eq :max_locals code-attribute)) ;might be nil
         (exception-table (lookup-eq :exception_table code-attribute)) ;(and (not no-codep) (lookup-eq :exception_table code-attribute))
         (code-attribute-attributes (lookup-eq :attributes code-attribute))
;can there be more than one of these?:
         (local-variable-table (and (not no-codep) (get-attribute "LocalVariableTable" code-attribute-attributes nil)))
;can there be more than one of these?:
         (line-number-table (and (not no-codep) (get-attribute "LineNumberTable" code-attribute-attributes nil)))
;         (full-method-name (full-method-name class-name method-name descriptor))
;         (method-code-constant-name (packn (list '* full-method-name '-code*)))
;         (method-constant-name (method-constant-name full-method-name))
         (program (if no-codep :no-program code))
         ;; (code-defconst-or-nothing
         ;;  (if no-codep
         ;;      nil
         ;;    `((mydefconst ,method-code-constant-name
         ;;                  ',code))))
         (method-info nil)
         ;; TODO: Just store the access flags as a list?
         ;; We put less interesting / larger items deeper in the structure:
         (method-info (maybe-acons :line-number-table line-number-table method-info))
         (method-info (maybe-acons :local-variable-table local-variable-table method-info))
         (method-info (maybe-acons :exception-table exception-table method-info))
         (method-info (maybe-acons :program program method-info))
         (method-info (maybe-acons :access-flags access-flags method-info))
         (method-info (maybe-acons :max-locals max-locals method-info))
         (method-info (maybe-acons :return-type return-type method-info))
         (method-info (maybe-acons :parameter-types parameter-types method-info))
         ;todo: use max-stack?
;         (method-defconst `(mydefconst ,method-constant-name ',(check-method-infop method-info)))  ;prove this check will always succeed and drop it
         )
    (acons method-id method-info acc)))

(defthm method-info-alistp-of-extend-method-info-alist
  (implies (and (raw-method-infop raw-method-info)
                (jvm::method-info-alistp acc))
           (jvm::method-info-alistp (extend-method-info-alist raw-method-info acc)))
  :hints (("Goal" :in-theory (e/d (extend-method-info-alist raw-method-infop
                                                            jvm::method-infop
                                                            CODE-ATTRIBUTEP)
                                  (acons
                                   jvm::method-idp
                                   natp)))))

;; raw-method-infos is a list of alists of the form created by parse-method-info-entry
;; Returns the method-info-alist
(defun make-method-info-alist (raw-method-infos acc)
  (declare (xargs :guard (and (raw-method-infosp raw-method-infos)
                              (jvm::method-info-alistp acc))
                  :guard-hints (("Goal" :in-theory (enable RAW-METHOD-INFOSP)))))
  (if (endp raw-method-infos)
      acc
    (make-method-info-alist (rest raw-method-infos)
                            (extend-method-info-alist (first raw-method-infos)
                                                      acc))))

(defthm method-info-alistp-of-make-method-info-alist
  (implies (and (raw-method-infosp raw-method-infos)
                (jvm::method-info-alistp acc))
           (jvm::method-info-alistp (make-method-info-alist raw-method-infos acc)))
  :hints (("Goal" :in-theory (e/d (make-method-info-alist RAW-METHOD-INFOSP)
                                  ()))))

;;;
;;; make-class-info-from-raw-parsed-class
;;;

;; STEP 2:
;; Makes a class-info structure from a raw-parsed-class.
;; Returns (mv class-info field-defconsts).
;; TODO: add an option to skip making the field-defconsts
(defund make-class-info-from-raw-parsed-class (raw-parsed-class)
  (declare (xargs :guard (raw-parsed-classp raw-parsed-class)
                  :guard-hints (("Goal" :in-theory (enable raw-parsed-classp)))))
  (b* ((raw-field-infos (lookup-eq :fields raw-parsed-class))
       (superclass (lookup-eq :super_class raw-parsed-class))
       (interfaces (lookup-eq :interfaces raw-parsed-class))
       (raw-method-infos (lookup-eq :methods raw-parsed-class))
       (access-flags (lookup-eq :access_flags raw-parsed-class))
       (this-class (lookup-eq :this_class raw-parsed-class))
       ;; (attributes (lookup-eq :attributes raw-parsed-class))
       ;; (- (cw "Attribs: ~x0~%" attributes)) ;TODO: Add these to the class-info structure!
;(nest-host-attribute (lookup-equal "NestHost" attributes))
       ;; TODO: Think about how to do this better?  Just use the name from the class file?  But it may be too slow to dig it out to check for redundancy (i.e., if the output file name is calculated by reading the input file, that could be slow).
       ;; TODO: Perhaps make this an error, but I am seeing problems with unicode characters:
       ;; (- (and (not (equal this-class class-name))
       ;;         ;;(er hard? 'make-class-info-from-raw-parsed-class "Class name mismatch.  Class name from .class file: ~x0.  Class name passed to build-book-for-class: ~x1.~%" this-class class-name)
       ;;         (cw "WARNING: Class name mismatch.  Class name from .class file: ~x0.  Class name passed to build-book-for-class: ~x1.~%" this-class class-name)))
       ;;FIXME think about slashes vs. dots (I think we turn slashes into dots pretty early on)
       ((mv field-defconsts non-static-field-info-alist static-field-info-alist)
        (field-defconsts-and-infos raw-field-infos this-class nil nil nil))
       (method-info-alist (make-method-info-alist raw-method-infos ;class-name
                                                  ;;nil
                                                  nil)))
    (mv (jvm::make-class-info superclass
                              interfaces
                              non-static-field-info-alist
                              static-field-info-alist
                              method-info-alist
                              access-flags)
        field-defconsts)))

(defthm class-infop0-of-mv-nth-0-of-make-class-info-from-raw-parsed-class
  (implies (raw-parsed-classp raw-parsed-class)
           (jvm::class-infop0 (mv-nth 0 (make-class-info-from-raw-parsed-class raw-parsed-class))))
  :hints (("Goal" :cases ((member-equal ':acc_interface (lookup-equal ':access_flags raw-parsed-class)))
           :in-theory (e/d (make-class-info-from-raw-parsed-class
                            JVM::CLASS-INFOP0 ;todo
                            raw-parsed-classp
                            superclass-and-interfaceness-okp
                            ) ( ;jvm::make-class-info ;todo
                            )))))

(defthm class-infop-of-mv-nth-0-of-make-class-info-from-raw-parsed-class
  (implies (raw-parsed-classp raw-parsed-class)
           (jvm::class-infop (mv-nth 0 (make-class-info-from-raw-parsed-class raw-parsed-class))
                             (lookup-equal :this_class raw-parsed-class)))
  :hints (("Goal" :use class-infop0-of-mv-nth-0-of-make-class-info-from-raw-parsed-class
           :in-theory (e/d (jvm::class-infop
                            JVM::CLASS-INFOP0
                            make-class-info-from-raw-parsed-class
                            lookup-equal-of-superclass-when-raw-parsed-classp-and-interface
                            class-namep-of-lookup-equal-of-superclass-when-raw-parsed-classp
                            equal-of-none-of-lookup-equal-of-superclass-when-raw-parsed-classp)
                           (class-infop0-of-mv-nth-0-of-make-class-info-from-raw-parsed-class)))))

(defthm true-listp-of-mv-nth-1-of-make-class-info-from-raw-parsed-class
  (implies (raw-parsed-classp raw-parsed-class)
           (true-listp (mv-nth 1 (make-class-info-from-raw-parsed-class raw-parsed-class))))
  :hints (("Goal" :in-theory (enable make-class-info-from-raw-parsed-class))))

(defthm true-listp-of-mv-nth-3-of-make-class-info-from-raw-parsed-class
  (implies (raw-parsed-classp raw-parsed-class)
           (true-listp (mv-nth 3 (make-class-info-from-raw-parsed-class raw-parsed-class))))
  :hints (("Goal" :in-theory (enable make-class-info-from-raw-parsed-class))))

;;;
;;; parse-class-file-bytes
;;;

;; Combines step 1 and step 2
;; Returns (mv erp class-name class-info field-defconsts constant-pool).
(defun parse-class-file-bytes (bytes constant-pool)
  (declare (xargs :guard (and (all-unsigned-byte-p 8 bytes)
                              (true-listp bytes))
                  :stobjs constant-pool
                  :guard-hints (("Goal" :in-theory (enable stringp-of-lookup-equal-of-this-class-when-raw-parsed-classp)))))
  (b* (((mv erp raw-parsed-class constant-pool)
        (parse-bytes-into-raw-parsed-class bytes constant-pool))
       ((when erp) (mv erp nil nil nil constant-pool))
       (class-name (acl2::lookup-eq :this_class raw-parsed-class))
       ((mv class-info
            field-defconsts ; todo: don't even compute these if not used
            )
        (make-class-info-from-raw-parsed-class raw-parsed-class)))
    (mv (erp-nil) class-name class-info field-defconsts constant-pool)))

(defthm class-namep-of-mv-nth-1-of-parse-class-file-bytes
  (implies (not (mv-nth 0 (parse-class-file-bytes bytes constant-pool)))
           (jvm::class-namep (mv-nth 1 (parse-class-file-bytes bytes constant-pool)))))

(defthm class-infop0-of-mv-nth-1-of-parse-class-file-bytes
  (implies (not (mv-nth 0 (parse-class-file-bytes bytes constant-pool)))
           (jvm::class-infop0 (mv-nth 2 (parse-class-file-bytes bytes constant-pool)))))

(defthm class-infop-of-mv-nth-1-of-parse-class-file-bytes
  (implies (not (mv-nth 0 (parse-class-file-bytes bytes constant-pool)))
           (jvm::class-infop (mv-nth 2 (parse-class-file-bytes bytes constant-pool))
                             (mv-nth 1 (parse-class-file-bytes bytes constant-pool)))))

(defthm true-listp-mv-nth-3-of-parse-class-file-bytes
  (true-listp (mv-nth 3 (parse-class-file-bytes bytes constant-pool)))
  :rule-classes :type-prescription)
