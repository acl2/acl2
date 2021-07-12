; Parsing counterexamples from STP
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/binary" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "kestrel/utilities/read-chars" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/typed-lists-light/maxelem" :dir :system)
(include-book "nodenum-type-alists")
(include-book "kestrel/typed-lists-light/all-integerp" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/character-listp" :dir :system))

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

(defconst *assert-chars* (coerce "ASSERT( " 'list))

(defconst *constant-array-node-chars* (coerce "ARRAY" 'list))

(defconst *normal-node-chars* (coerce "NODE" 'list))

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
  (implies (and (mv-nth 0 (match-chars fixed-chars chars))
;                (<= (len fixed-chars) (len chars))
                )
           (equal (len (mv-nth 1 (match-chars fixed-chars chars)))
                  (- (len chars)
                     (len fixed-chars))))
  :hints (("Goal" :in-theory (enable match-chars))))

(defthm character-listp-of-mv-nth-1-of-match-chars
  (implies (character-listp chars)
           (character-listp (MV-NTH 1 (match-chars fixed-chars chars))))
  :hints (("Goal" :in-theory (enable match-chars))))

(defthm true-listp-of-mv-nth-1-of-match-chars
  (implies (true-listp chars)
           (true-listp (MV-NTH 1 (match-chars fixed-chars chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable match-chars))))

; returns (mv number remainingchars)
(defund parse-decimal-number (chars)
  (declare (xargs :guard (character-listp chars)))
  (b* (((mv num len chars)
        (str::parse-nat-from-charlist chars 0 0))
       ((when (zp len)) ; no digits for the nodenum
        (prog2$ (er hard? 'parse-decimal-number "Failed to parse a number from chars: ~x0" chars)
                (mv 0 chars))))
    (mv num chars)))

(defthm skip-leading-digits-len-bound
  (<= (len (str::skip-leading-digits chars))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable str::skip-leading-digits))))

(defthm true-listp-of-skip-leading-digits
  (implies (true-listp chars)
           (true-listp (str::skip-leading-digits chars)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable str::skip-leading-digits))))

(defthm parse-decimal-number-len-bound
  (<= (len (mv-nth 1 (parse-decimal-number chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-decimal-number))))

(defthm true-listp-of-mv-nth-1-of-parse-decimal-number
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-decimal-number chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-decimal-number))))

(defthm character-listp-of-mv-nth-1-of-parse-decimal-number
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-decimal-number chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-decimal-number))))

(defthm natp-of-mv-nth-0-of-parse-decimal-number
  (natp (mv-nth 0 (parse-decimal-number chars)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-decimal-number))))

; returns (mv number remainingchars)
(defund parse-binary-number (chars)
  (declare (xargs :guard (character-listp chars)))
  (b* (((mv num len chars)
        (str::parse-bits-from-charlist chars 0 0))
       ((when (zp len)) ; no digits for the nodenum
        (prog2$ (er hard? 'parse-binary-number "Failed to parse a number from chars: ~x0" chars)
                (mv 0 chars))))
    (mv num chars)))

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

(defthm skip-leading-bit-digits-len-bound
  (<= (len (str::skip-leading-bit-digits chars))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable str::skip-leading-bit-digits))))

(defthm true-listp-of-skip-leading-bit-digits
  (implies (true-listp chars)
           (true-listp (str::skip-leading-bit-digits chars)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable str::skip-leading-bit-digits))))

(defthm parse-binary-number-len-bound
  (<= (len (mv-nth 1 (parse-binary-number chars)))
      (len chars))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable parse-binary-number))))

(defthm true-listp-of-mv-nth-1-of-parse-binary-number
  (implies (true-listp chars)
           (true-listp (mv-nth 1 (parse-binary-number chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-binary-number))))

(defthm character-listp-of-mv-nth-1-of-parse-binary-number
  (implies (character-listp chars)
           (character-listp (mv-nth 1 (parse-binary-number chars))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-binary-number))))

(defthm natp-of-mv-nth-0-of-parse-binary-number
  (natp (mv-nth 0 (parse-binary-number chars)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable parse-binary-number))))

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

;; returns (mv value chars)
;; parse something like " = 0b00 );" or "<=>TRUE );"
(defund parse-equality-etc (chars all-chars)
  (declare (xargs :guard (character-listp chars)))
  (b* (((mv match chars1)
        (match-chars '(#\Space #\= #\Space #\0 #\b) chars)))
    (if match
        ;; non-boolean
        (b* ((chars chars1)
             ((mv value chars) (parse-binary-number chars))
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
         ((mv index chars) (parse-binary-number chars))
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
      (rev acc)
    (if (eql #\newline (first chars)) ;skip all newlines
        (parse-counterexample (rest chars) acc)
      (let ((old-chars chars))
        (mv-let (matchp chars) ;line must always start with "ASSERT( "
          (match-chars *assert-chars* chars)
          (if (not matchp)
              (prog2$ (er hard? 'parse-counterexample "Ill-formed counterexample: ~x0" old-chars)
                      nil)
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
                              nil)
                    (b* (((mv nodenum chars) (parse-decimal-number chars))
                         ((mv array-index-or-nil chars) (maybe-parse-array-index chars old-chars))
                         ((mv value chars) (parse-equality-etc chars old-chars))
                         (key (if array-index-or-nil
                                  (cons nodenum array-index-or-nil)
                                nodenum)))
                      (parse-counterexample chars (acons key value acc)))))))))))))

(defthm alistp-of-rev
  (equal (alistp (rev x))
         (alistp (true-list-fix x)))
  :hints (("Goal" :in-theory (enable alistp rev))))

(defthm alistp-of-parse-counterexample
  (implies (alistp acc)
           (alistp (parse-counterexample chars acc)))
  :hints (("Goal" :in-theory (enable parse-counterexample))))

(defthm raw-counterexamplep-of-append
  (implies (and (raw-counterexamplep x)
                (raw-counterexamplep y))
           (raw-counterexamplep (append x y))))

(defthm raw-counterexamplep-of-rev
  (implies (raw-counterexamplep x)
           (raw-counterexamplep (rev x))))

(defthm raw-counterexamplep-of-parse-counterexample
  (implies (raw-counterexamplep acc)
           (raw-counterexamplep (parse-counterexample chars acc)))
  :hints (("Goal" :in-theory (enable acons parse-counterexample))))

(verify-guards parse-counterexample)

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

(defthm <=-of-0-and-maxelem-of-strip-cars-when-nodenum-type-alistp
  (implies (and (nodenum-type-alistp alist)
                (consp alist))
           (<= 0 (maxelem (strip-cars alist))))
  :rule-classes (:linear)
  :hints (("Goal" :in-theory (enable nodenum-type-alistp))))

(defthm integerp-of-maxelem-of-strip-cars-when-nodenum-type-alistp
  (implies (and (nodenum-type-alistp alist)
                (consp alist))
           (integerp (maxelem (strip-cars alist))))
  :hints (("Goal" :in-theory (enable nodenum-type-alistp))))

(defthm all-integerp-of-strip-cars-when-nodenum-type-alistp
  (implies (nodenum-type-alistp alist)
           (all-integerp (strip-cars alist)))
  :hints (("Goal" :in-theory (enable nodenum-type-alistp))))

(defun set-array-vals-from-counterexample (raw-counterexample nodenum array-val)
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
                                                                                 (cdr key) ;the array indx
                                                                                 (cdr entry)
                                                                                 array-val))
        (set-array-vals-from-counterexample (rest raw-counterexample) nodenum array-val)))))

(defthmd alistp-when-raw-counterexamplep
  (implies (raw-counterexamplep raw-counterexample)
           (alistp raw-counterexample))
  :hints (("Goal" :in-theory (enable raw-counterexamplep alistp))))

;(local (in-theory (disable LIST-TYPEP BV-ARRAY-TYPEP)))

;(local (in-theory (disable bv-array-typep bv-typep boolean-typep BV-ARRAY-TYPE-LEN MOST-GENERAL-TYPEP)))

;; Build an alist that assigns a value to each nodenum in
;; cut-nodenum-type-alist.  For arrays, harvest values of their individual
;; elements from the raw counterexample. Put in a default value for anything
;; not assigned a value.
(defund fixup-counterexample (cut-nodenum-type-alist raw-counterexample)
  (declare (xargs :guard (and (raw-counterexamplep raw-counterexample)
                              (nodenum-type-alistp cut-nodenum-type-alist))
                  :guard-hints (("Goal" :in-theory (enable alistp-when-raw-counterexamplep)))
                  :verify-guards nil ;done below
                  ))
  (if (endp cut-nodenum-type-alist)
      nil
    (let* ((entry (first cut-nodenum-type-alist))
           (nodenum (car entry))
           (type (cdr entry)))
      (if (or (boolean-typep type)
              (bv-typep type))
          (acons nodenum
                 (or (lookup-equal nodenum raw-counterexample)
                     (prog2$ (cw "(NOTE: No value in counterexample for node ~x0.)~%" nodenum)
                             ;; go ahead and pick a value so the counterexample is complete:
                             (if (boolean-typep type)
                                 nil
                               0)))
                 (fixup-counterexample (rest cut-nodenum-type-alist) raw-counterexample))
        (if (and (bv-array-typep type)
                 ;;(quoted-posp (bv-array-type-len type))
                 )
            (acons nodenum
                   (set-array-vals-from-counterexample raw-counterexample nodenum (repeat (bv-array-type-len type) 0))
                   (fixup-counterexample (rest cut-nodenum-type-alist) raw-counterexample))
          (acons nodenum
                 (er hard? 'fixup-counterexample "Unexpected type: ~x0." type)
                 (fixup-counterexample (rest cut-nodenum-type-alist) raw-counterexample)))))))

(defthm alistp-of-fixup-counterexample
  (alistp (fixup-counterexample cut-nodenum-type-alist raw-counterexample))
  :hints (("Goal" :in-theory (enable fixup-counterexample))))

(verify-guards fixup-counterexample :hints (("Goal" :in-theory (enable nodenum-type-alistp))))

(defthm strip-cars-of-fixup-counterexample
  (equal (strip-cars (fixup-counterexample cut-nodenum-type-alist raw-counterexample))
         (strip-cars cut-nodenum-type-alist))
  :hints (("Goal" :in-theory (enable fixup-counterexample))))

(defthm consp-of-fixup-counterexample
  (equal (consp (fixup-counterexample cut-nodenum-type-alist raw-counterexample))
         (consp cut-nodenum-type-alist))
  :hints (("Goal" :in-theory (enable fixup-counterexample))))

(defthm true-listp-of-set-array-vals-from-counterexample
  (implies (true-listp array-val)
           (true-listp (set-array-vals-from-counterexample raw-counterexample nodenum array-val)))
  :hints (("Goal" :in-theory (enable set-array-vals-from-counterexample))))

(defthmd integerp-of-lookup-equal-when-raw-counterexamplep
  (implies (and (raw-counterexamplep raw-counterexample)
                (not (booleanp (lookup-equal nodenum raw-counterexample))))
           (integerp (lookup-equal nodenum raw-counterexample)))
  :hints (("Goal" :in-theory (enable raw-counterexamplep lookup-equal))))

(defthmd not-negative-of-lookup-equal-when-raw-counterexamplep
  (implies (raw-counterexamplep raw-counterexample)
           (not (< (lookup-equal nodenum raw-counterexample) 0)))
  :hints (("Goal" :in-theory (enable raw-counterexamplep lookup-equal))))

(defthm counterexamplep-of-fixup-counterexample
  (implies (and (nodenum-type-alistp cut-nodenum-type-alist)
                (raw-counterexamplep raw-counterexample))
           (counterexamplep (fixup-counterexample cut-nodenum-type-alist raw-counterexample)))
  :hints (("Goal" :in-theory (e/d (fixup-counterexample
                                   counterexamplep acons
                                   integerp-of-lookup-equal-when-raw-counterexamplep
                                   not-negative-of-lookup-equal-when-raw-counterexamplep
                                   nodenum-type-alistp)
                                  (BOOLEAN-TYPEP bv-typep BV-ARRAY-TYPEP BV-ARRAY-TYPE-LEN)))))
