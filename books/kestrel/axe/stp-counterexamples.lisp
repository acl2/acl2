; Parsing counterexamples from STP
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/utilities/read-chars" :dir :system)
(include-book "kestrel/utilities/erp" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/alists-light/lookup-safe" :dir :system)
(include-book "kestrel/lists-light/reverse-list" :dir :system)
(include-book "kestrel/strings-light/parse-binary-digits" :dir :system)
(include-book "kestrel/strings-light/parse-decimal-digits" :dir :system)
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "kestrel/typed-lists-light/all-less" :dir :system)
(include-book "nodenum-type-alists")
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "kestrel/bv-lists/logext-list" :dir :system)
(include-book "dag-arrays")
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))
(local (include-book "kestrel/lists-light/append" :dir :system))

(defthm all-integerp-of-strip-cars-when-nodenum-type-alistp
  (implies (nodenum-type-alistp alist)
           (all-integerp (strip-cars alist)))
  :hints (("Goal" :in-theory (enable nodenum-type-alistp))))

(defthm alistp-of-reverse-list
  (equal (alistp (reverse-list x))
         (alistp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable alistp reverse-list))))

(local (in-theory (disable natp mv-nth)))

(local
 (defthm strip-cars-of-reverse-list
   (equal (strip-cars (reverse-list acc))
          (reverse-list (strip-cars acc)))
   :hints (("Goal" :in-theory (enable strip-cars reverse-list)))))

;;
;; counterexample parsing
;;

;; It seems that we have to tell STP to print the counterexample in binary,
;; since it does so anyway for single bit vars (maybe for any var whose size is
;; not a multiple of 4 bits so hex digits would be a bit deceptive?)

;; A raw-counterexample pairs nodenums or arraynodeum/index pairs to values (that
;; is, arrays are split into assignments of their individual elements).
(defun raw-counterexamplep (cex)
  (declare (xargs :guard t))
  (if (atom cex)
      (null cex)
    (let ((entry (first cex)))
      (and (consp entry)
           (let* ((key (car entry))
                  (val (cdr entry)))
             (and (or (natp key)       ;a nodenum
                      (and (consp key) ;(arraynodenum . index)
                           (natp (car key))
                           (natp (cdr key))))
                  (or (natp val)
                      (booleanp val))
                  (raw-counterexamplep (rest cex))))))))

(defthmd alistp-when-raw-counterexamplep
  (implies (raw-counterexamplep raw-counterexample)
           (alistp raw-counterexample))
  :hints (("Goal" :in-theory (enable raw-counterexamplep alistp))))

(defthm raw-counterexamplep-of-append
  (implies (and (raw-counterexamplep x)
                (raw-counterexamplep y))
           (raw-counterexamplep (append x y))))

(defthm raw-counterexamplep-of-reverse-list
  (implies (raw-counterexamplep x)
           (raw-counterexamplep (reverse-list x))))

;; Is the value if not a boolean it must be a natural.
(defthmd natp-of-lookup-equal-when-raw-counterexamplep
  (implies (and (raw-counterexamplep raw-counterexample)
                (not (booleanp (lookup-equal key raw-counterexample))))
           (natp (lookup-equal key raw-counterexample)))
  :hints (("Goal" :in-theory (enable raw-counterexamplep lookup-equal))))

(defconst *assert-chars* (coerce "ASSERT( " 'list))

(defconst *constant-array-node-chars* (coerce "ARRAY" 'list))

(defconst *normal-node-chars* (coerce "NODE" 'list))

;;move
;;returns (mv matchp rest-chars)
(defund match-chars (fixed-chars chars)
  (declare (xargs :guard (and (character-listp chars)
                              (character-listp fixed-chars))))
  (if (endp fixed-chars)
      (mv t chars)
    (if (endp chars)
        (mv nil chars)
      (if (eql (first fixed-chars)
               (first chars))
          (match-chars (rest fixed-chars) (rest chars))
        (mv nil chars)))))

(defthm match-chars-len-bound
  (<= (len (mv-nth 1 (match-chars fixed-chars chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable match-chars))))

(defthm len-of-mv-nth-1-of-match-chars
  (implies (mv-nth 0 (match-chars fixed-chars chars))
           (equal (len (mv-nth 1 (match-chars fixed-chars chars)))
                  (- (len chars)
                     (len fixed-chars))))
  :hints (("Goal" :in-theory (enable match-chars))))

(defthm character-listp-of-mv-nth-1-of-match-chars
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (match-chars fixed-chars chars))))
  :hints (("Goal" :in-theory (enable match-chars))))

(defthm true-listp-of-mv-nth-1-of-match-chars
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (match-chars fixed-chars chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable match-chars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; ; returns (mv number remainingchars)
;; (defund parse-binary-number (chars)
;;   (declare (xargs :guard (character-listp chars)))
;;   (b* (((mv num len chars)
;;         (str::parse-bits-from-charlist chars 0 0))
;;        ((when (zp len)) ; no digits for the nodenum
;;         (prog2$ (er hard? 'parse-binary-number "Failed to parse a number from chars: ~x0" chars)
;;                 (mv 0 chars))))
;;     (mv num chars)))

;; (defthm skip-leading-hex-digits-len-bound
;;   (<= (len (str::skip-leading-hex-digits chars))
;;       (len chars))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :in-theory (enable str::skip-leading-hex-digits))))

;; (defthm true-listp-of-skip-leading-hex-digits
;;   (implies (true-listp chars)
;;            (true-listp (str::skip-leading-hex-digits chars)))
;;   :rule-classes (:rewrite :type-prescription)
;;   :hints (("Goal" :in-theory (enable str::skip-leading-hex-digits))))

;; (defthm skip-leading-bit-digits-len-bound
;;   (<= (len (str::skip-leading-bit-digits chars))
;;       (len chars))
;;   :rule-classes (:rewrite :linear)
;;   :hints (("Goal" :in-theory (enable str::skip-leading-bit-digits))))

;; (defthm true-listp-of-skip-leading-bit-digits
;;   (implies (true-listp chars)
;;            (true-listp (str::skip-leading-bit-digits chars)))
;;   :rule-classes (:rewrite :type-prescription)
;;   :hints (("Goal" :in-theory (enable str::skip-leading-bit-digits))))

;; returns (mv bool remaining-chars)
(defund parse-boolean (chars)
  (declare (xargs :guard (character-listp chars)))
  (b* (((mv match-true true-chars)
        (match-chars '(#\T #\R #\U #\E) chars)))
    (if match-true
        (mv t true-chars)
      (b* (((mv match-false false-chars)
            (match-chars '(#\F #\A #\L #\S #\E) chars)))
        (if match-false
            (mv nil false-chars)
          (prog2$ (er hard? 'parse-boolean "Failed to parse a boolean from chars: ~x0" chars)
                  (mv nil chars)))))))

(defthm parse-boolean-len-bound
  (<= (len (mv-nth 1 (parse-boolean chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-boolean))))

(defthm true-listp-of-mv-nth-1-of-parse-boolean
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-boolean chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-boolean))))

(defthm character-listp-of-mv-nth-1-of-parse-boolean
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-boolean chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-boolean))))

(defthm booleanp-of-mv-nth-0-of-parse-boolean
  (booleanp (mv-nth 0 (parse-boolean chars)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-boolean))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; returns (mv value chars)
;; parse something like " = 0b00 );" or "<=>TRUE );"
(defund parse-equality-etc (chars all-chars)
  (declare (xargs :guard (character-listp chars)))
  (b* (((mv match chars1)
        (match-chars '(#\Space #\= #\Space #\0 #\b) chars)))
    (if match
        ;; non-boolean
        (b* ((chars chars1)
             ((mv value chars) (parse-binary-number-from-chars chars))
             ((when (not value))
              (prog2$ (er hard? 'parse-equality-etc "Ill-formed counterexample chars: ~X01" all-chars nil)
                      (mv nil chars)))
             ((mv match chars)
              (match-chars '(#\Space #\) #\; #\Newline) chars))
             ((when (not match))
              (prog2$ (er hard? 'parse-equality-etc "Ill-formed counterexample chars: ~X01" all-chars nil)
                      (mv nil chars))))
          (mv value chars))
      ;; must be a boolean:
      (b* (((mv match chars2)
            (match-chars '(#\< #\= #\>) chars)))
        (if match
            (b* ((chars chars2)
                 ((mv value chars) (parse-boolean chars))
                 ((mv match chars)
                  (match-chars '(#\Space #\) #\; #\Newline) chars))
                 ((when (not match))
                  (prog2$ (er hard? 'parse-equality-etc "Ill-formed counterexample chars: ~X01" all-chars nil)
                          (mv nil chars))))
              (mv value chars))
          (prog2$ (er hard? 'parse-equality-etc "Ill-formed counterexample chars: ~X01" all-chars nil)
                  (mv nil chars)))))))

(defthm parse-equality-etc-len-bound
  (<= (len (mv-nth 1 (parse-equality-etc chars all-chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-equality-etc))))

(defthm true-listp-of-mv-nth-1-of-parse-equality-etc
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-equality-etc chars all-chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-equality-etc))))

(defthm character-listp-of-mv-nth-1-of-parse-equality-etc
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-equality-etc chars all-chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-equality-etc))))

(defthm type-of-mv-nth-0-of-parse-equality-etc
  (or (natp (mv-nth 0 (parse-equality-etc chars all-chars)))
      (booleanp (mv-nth 0 (parse-equality-etc chars all-chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-equality-etc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;returns (mv array-index-or-nil chars)
;;example "[0b4]"
(defund maybe-parse-array-index (chars all-chars)
  (declare (xargs :guard (character-listp chars)))
  (if (not (eql #\[ (first chars)))
      (mv nil chars)
    ;; there is an index t parse:
    (b* ((chars (rest chars)) ;skip the [
         ((mv matchp chars)
          (match-chars '(#\0 #\b) chars))
         ((when (not matchp))
          (prog2$ (er hard? 'maybe-parse-array-index "Ill-formed counterexample chars: ~X01" all-chars nil)
                  (mv nil chars)))
         ((mv index chars) (parse-binary-number-from-chars chars))
         ((when (not index))
          (er hard? 'maybe-parse-array-index "Ill-formed counterexample chars: ~X01" all-chars nil)
          (mv nil chars))
         ((mv matchp chars)
          (match-chars '(#\]) chars))
         ((when (not matchp))
          (prog2$ (er hard? 'maybe-parse-array-index "Ill-formed counterexample chars: ~X01" all-chars nil)
                  (mv nil chars))))
      (mv index chars))))

(defthm maybe-parse-array-index-len-bound
  (<= (len (mv-nth 1 (maybe-parse-array-index chars all-chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable maybe-parse-array-index))))

(defthm true-listp-of-mv-nth-1-of-maybe-parse-array-index
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (maybe-parse-array-index chars all-chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable maybe-parse-array-index))))

(defthm character-listp-of-mv-nth-1-of-maybe-parse-array-index
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (maybe-parse-array-index chars all-chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable maybe-parse-array-index))))

(defthm type-of-mv-nth-0-of-maybe-parse-array-index
  (or (null (mv-nth 0 (maybe-parse-array-index chars all-chars)))
      (natp (mv-nth 0 (maybe-parse-array-index chars all-chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable maybe-parse-array-index))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; returns a raw-counterexamplep or :error
;;examples:
;; "ASSERT( NODE2<=>TRUE );"
;; "ASSERT( NODE0 = 0b00000000 );"
;; "ASSERT( NODE0[0b4] = 0b00 );"
(defund parse-counterexample (chars acc)
  (declare (xargs :guard (and (character-listp chars)
                              (alistp acc))
                  :measure (len chars)
                  :verify-guards nil ;done below
                  ))
  (if (endp chars)
      (reverse-list acc)
    (if (eql #\newline (first chars)) ;skip all newlines
        (parse-counterexample (rest chars) acc)
      (let ((old-chars chars))
        (mv-let (matchp chars) ;line must always start with "ASSERT( "
          (match-chars *assert-chars* chars)
          (if (not matchp)
              (prog2$ (er hard? 'parse-counterexample "Ill-formed counterexample: ~x0" old-chars)
                      :error)
            (mv-let (matchp chars) ;test for array... (only constant arrays are named that way)
              (match-chars *constant-array-node-chars* chars)
              (if matchp ;;this is a constant array node, but we already know their values, so skip it
                  (b* (((mv & chars)
                        (read-chars-to-terminator chars #\newline)) ;skip the rest of the line
                       (chars (cdr chars))) ;skip the newline
                    (parse-counterexample chars acc))
                (mv-let (matchp chars)
                  (match-chars *normal-node-chars* chars)
                  (if (not matchp)
                      (prog2$ (er hard? 'parse-counterexample "Ill-formed counterexample: ~x0" old-chars)
                              :error)
                    (b* (((mv nodenum chars) (parse-decimal-number-from-chars chars))
                         ((when (not nodenum))
                          (er hard? 'parse-counterexample "Ill-formed counterexample: ~x0" old-chars)
                          :error)
                         ((mv array-index-or-nil chars) (maybe-parse-array-index chars old-chars))
                         ((mv value chars) (parse-equality-etc chars old-chars))
                         (key (if array-index-or-nil
                                  (cons nodenum array-index-or-nil)
                                nodenum)))
                      (parse-counterexample chars (acons key value acc)))))))))))))

(defthm alistp-of-parse-counterexample
  (implies (and (alistp acc)
                (not (equal :error (parse-counterexample chars acc))))
           (alistp (parse-counterexample chars acc)))
  :hints (("Goal" :in-theory (enable parse-counterexample))))

(defthm raw-counterexamplep-of-parse-counterexample
  (implies (and (raw-counterexamplep acc)
                (not (equal :error (parse-counterexample chars acc))))
           (raw-counterexamplep (parse-counterexample chars acc)))
  :hints (("Goal" :in-theory (enable acons parse-counterexample))))

(verify-guards parse-counterexample)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A counterexample pairs nodenums to values.
(defun counterexamplep (cex)
  (declare (xargs :guard t))
  (if (atom cex)
      (null cex)
    (let ((entry (first cex)))
      (and (consp entry)
           (let* ((key (car entry))
                  (val (cdr entry)))
             (and (natp key)
                  (or (natp val)
                      (booleanp val)
                      (true-listp val))
                  (counterexamplep (rest cex))))))))

(defthmd alistp-when-counterexamplep
  (implies (counterexamplep cex)
           (alistp cex))
  :hints (("Goal" :in-theory (enable counterexamplep alistp))))

;; Since we use an accumulator below.
(defthm counterexamplep-of-reverse-list
  (implies (counterexamplep acc)
           (counterexamplep (reverse-list acc)))
  :hints (("Goal" :in-theory (enable counterexamplep))))

(defthm natp-of-maxelem-of-strip-cars-when-counterexamplep
  (implies (and (counterexamplep cex)
                (consp cex))
           (natp (maxelem (strip-cars cex))))
  :rule-classes (:rewrite :type-prescription))

(defthm rational-listp-of-strip-cars-when-counterexamplep
  (implies (counterexamplep cex)
           (rational-listp (strip-cars cex)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;drop?
(defthm <=-of-0-and-maxelem-of-strip-cars-when-counterexamplep
  (implies (and (counterexamplep cex)
                (consp cex))
           (<= 0 (maxelem (strip-cars cex))))
  :rule-classes (:linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund set-array-vals-from-counterexample (raw-counterexample nodenum array-val)
  (declare (xargs :guard (and (raw-counterexamplep raw-counterexample)
;                              (natp nodenum)
                              (true-listp array-val))))
  (if (endp raw-counterexample)
      array-val
    (let* ((entry (first raw-counterexample))
           (key (car entry))
           ;;(value (cdr entry))
           )
      (if (and (consp key)
               (eql (car key) nodenum)) ;;(nodenum . index)
          (set-array-vals-from-counterexample (rest raw-counterexample) nodenum (update-nth
                                                                                 (cdr key) ;the array index
                                                                                 (cdr entry)
                                                                                 array-val))
        (set-array-vals-from-counterexample (rest raw-counterexample) nodenum array-val)))))

(defthm true-listp-of-set-array-vals-from-counterexample
  (implies (true-listp array-val)
           (true-listp (set-array-vals-from-counterexample raw-counterexample nodenum array-val)))
  :hints (("Goal" :in-theory (enable set-array-vals-from-counterexample))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp counterexample).  Builds an alist that assigns a value to
;; each nodenum in cut-nodenum-type-alist.  For arrays, harvests values of
;; their individual elements from the raw counterexample.  Puts in a default
;; value for anything not assigned a value.
(defund fixup-counterexample (cut-nodenum-type-alist raw-counterexample acc)
  (declare (xargs :guard (and (raw-counterexamplep raw-counterexample)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (alistp acc))
                  :guard-hints (("Goal" :in-theory (enable alistp-when-raw-counterexamplep
                                                           nodenum-type-alistp)))))
  (if (endp cut-nodenum-type-alist)
      (mv (erp-nil) (reverse-list acc))
    (let* ((entry (first cut-nodenum-type-alist))
           (nodenum (car entry))
           (type (cdr entry)))
      (if (boolean-typep type)
          (let ((res (assoc-equal nodenum raw-counterexample)))
            (if (not res)
                (prog2$ (cw "(NOTE: No value in counterexample for node ~x0.)~%" nodenum)
                        ;; go ahead and pick a value (nil) so the counterexample is complete:
                        (fixup-counterexample (rest cut-nodenum-type-alist) raw-counterexample (acons nodenum nil acc)))
              (let ((val (cdr res)))
                (if (not (booleanp val))
                    (prog2$ (er hard? 'fixup-counterexample "Bad value, ~x0, in countexample.  Expected a boolean." val)
                            (mv :bad-val-in-counterexample nil))
                  (fixup-counterexample (rest cut-nodenum-type-alist) raw-counterexample (acons nodenum val acc))))))
        (if (bv-typep type)
            (let ((res (assoc-equal nodenum raw-counterexample)))
              (if (not res)
                  (prog2$ (cw "(NOTE: No value in counterexample for node ~x0.)~%" nodenum)
                          ;; go ahead and pick a value (0) so the counterexample is complete:
                          (fixup-counterexample (rest cut-nodenum-type-alist) raw-counterexample (acons nodenum 0 acc)))
                (let ((val (cdr res))
                      (width (bv-type-width type)))
                  (if (not (unsigned-byte-p width val))
                      (prog2$ (er hard? 'fixup-counterexample "Bad value, ~x0, in countexample.  Expected a BV of size ~x1." val width)
                              (mv :bad-val-in-counterexample nil))
                    (fixup-counterexample (rest cut-nodenum-type-alist) raw-counterexample (acons nodenum val acc))))))
          (if (and (bv-array-typep type)
                   ;;(quoted-posp (bv-array-type-len type))
                   )
              (fixup-counterexample (rest cut-nodenum-type-alist)
                                    raw-counterexample
                                    (acons nodenum
                                           (set-array-vals-from-counterexample raw-counterexample nodenum (repeat (bv-array-type-len type) 0))
                                           acc))
            (prog2$ (er hard? 'fixup-counterexample "Unexpected type: ~x0." type)
                    (mv :unexpected-type nil))))))))

(defthm alistp-of-mv-nth-1-of-fixup-counterexample
  (implies (alistp acc)
           (alistp (mv-nth 1 (fixup-counterexample cut-nodenum-type-alist raw-counterexample acc))))
  :hints (("Goal" :in-theory (enable fixup-counterexample))))

(defthm strip-cars-of-mv-nth-1-of-fixup-counterexample
  (implies (not (mv-nth 0 (fixup-counterexample cut-nodenum-type-alist raw-counterexample acc)))
           (equal (strip-cars (mv-nth 1 (fixup-counterexample cut-nodenum-type-alist raw-counterexample acc)))
                  (append (reverse (strip-cars acc))
                          (strip-cars cut-nodenum-type-alist))))
  :hints (("Goal" :in-theory (enable fixup-counterexample))))

(defthm consp-of-mv-nth-1-of-fixup-counterexample
  (implies (not (mv-nth 0 (fixup-counterexample cut-nodenum-type-alist raw-counterexample acc)))
           (equal (consp (mv-nth 1 (fixup-counterexample cut-nodenum-type-alist raw-counterexample acc)))
                  (or (consp cut-nodenum-type-alist)
                      (consp acc))))
  :hints (("Goal" :in-theory (enable fixup-counterexample))))

(defthm counterexamplep-of-mv-nth-1-of-fixup-counterexample
  (implies (and ;(not (mv-nth 0 (fixup-counterexample cut-nodenum-type-alist raw-counterexample acc)))
            (nodenum-type-alistp cut-nodenum-type-alist)
            (counterexamplep acc)
            (raw-counterexamplep raw-counterexample))
           (counterexamplep (mv-nth 1 (fixup-counterexample cut-nodenum-type-alist raw-counterexample acc))))
  :hints (("Goal" :in-theory (e/d (fixup-counterexample
                                   counterexamplep acons
                                   nodenum-type-alistp
                                   natp-of-lookup-equal-when-raw-counterexamplep)
                                  (boolean-typep bv-typep ;bv-array-typep bv-array-type-len
                                                 )))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizes a counterexample all of whose nodes are less than BOUND.
(defund bounded-counterexamplep (cex bound)
  (declare (xargs :guard (integerp bound)))
  (and (counterexamplep cex)
       (all-< (strip-cars cex) bound)))

(defthm bounded-counterexamplep-of-mv-nth-1-of-fixup-counterexample
  (implies (and (all-< (strip-cars cut-nodenum-type-alist) bound)
                (nodenum-type-alistp cut-nodenum-type-alist)
                (bounded-counterexamplep acc bound))
           (bounded-counterexamplep (mv-nth 1 (fixup-counterexample cut-nodenum-type-alist raw-counterexample acc)) bound))
  :hints (("Goal" :in-theory (enable fixup-counterexample bounded-counterexamplep nodenum-type-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Also chop arrays whose lengths are not powers of 2?
(defund print-counterexample (cex cut-nodenum-type-alist print-signedp dag-array-name dag-array)
  (declare (xargs :guard (and (counterexamplep cex)
                              (nodenum-type-alistp cut-nodenum-type-alist)
                              (booleanp print-signedp) ; whether to print BVs as signed integers
                              (if (consp cex)
                                  (pseudo-dag-arrayp dag-array-name dag-array (+ 1 (maxelem (strip-cars cex))))
                                t))))
  (if (endp cex)
      nil
    (b* ((entry (first cex))
         (nodenum (car entry))
         (value (cdr entry))
         (type (lookup-safe nodenum cut-nodenum-type-alist))
         ;;(expr (aref1 dag-array-name dag-array nodenum))
         (expr (dag-to-term-aux-array dag-array-name dag-array nodenum))
         (value (if (and print-signedp (symbolp expr)) ; for now, only do it for vars
                    (if (bv-typep type)
                        (let ((width (bv-type-width type)))
                          (if (not (unsigned-byte-p width value))
                              (er hard? 'print-counterexample "Wrong type value, ~x0, for node ~x1 (should be a BV of size ~x2)." value nodenum width)
                            (if (posp width)
                                (logext width value)
                              (er hard? 'print-counterexample "Can't treat a BV as signed when it has width 0."))))
                      (if (bv-array-typep type)
                          (let ((array-len (bv-array-type-len type))
                                (element-width (bv-array-type-element-width type)))
                            (if (posp element-width)
                                 ; todo: drop the bvchop-list and the true-list-fix?
                                (logext-list element-width (bvchop-list element-width
                                                                        (take array-len (true-list-fix value)) ; todo: ensure there are at least enough (there may be extra elements if we rounded the array size up to a power of 2
                                                                        ))
                              (er hard? 'print-counterexample "Can't treat an array as signed when its elements are of width 0.")))
                        value))
                  value))
         (- (cw "  Node ~x0: ~x1 is ~x2." nodenum expr value))
         ;; Print newline unless this is the last line:
         (- (and (consp (rest cex)) (cw "~%"))))
      (print-counterexample (rest cex) cut-nodenum-type-alist print-signedp dag-array-name dag-array))))
