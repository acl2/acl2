; Encodings of ARM32 instructions
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; TODO: Consider using lists instead of alists for the args and
;; auto-generating the boilerplate to extract list elems (also think about how
;; to do this without consing).

;; Section references are to the document "ARM Architecture Reference Manual
;; ARMv7-A and ARMv7-R edition" (see README.md).

(include-book "portcullis")
(include-book "kestrel/bv/bvor-def" :dir :system)
(include-book "kestrel/bv/bvand-def" :dir :system)
(include-book "kestrel/bv/getbit-def" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-def" :dir :system)
(local (include-book "kestrel/alists-light/alistp" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/bv/bvor" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognizer for an encoding-pattern, which is a list of items, each of which is 0 or 1 or of the form (<var> <numbits>).
;; These are already desugared.
(defun encoding-patternp (pat)
  (declare (xargs :guard t))
  (if (not (consp pat))
      (null pat)
    (let ((item (first pat)))
      (and (or (eql 0 item)
               (eql 1 item)
               (and (true-listp item)
                    (= 2 (len item))
                    (let ((var (first item))
                          (bits (second item)))
                      (and (symbolp var)
                           (posp bits)))))
           (encoding-patternp (rest pat))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An instruction mnemonic, such as :adc-immediate.
(defun mnemonicp (m)
  (declare (xargs :guard t))
  (keywordp m))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This does the following:
;; - drops underscores (just used as separators)
;; - replaces VAR with (VAR 1)
;; - replaces (0) with 0 -- for now
;; - replaces (1) with 1 -- for now
(defund desugar-pattern (pat)
  (declare (xargs :guard (true-listp pat)))
  (if (endp pat)
      nil
    (let ((item (first pat)))
      (if (atom item)
          (if (or (eql item 0)
                  (eql item 1))
              (cons item (desugar-pattern (rest pat)))
            ;; We ignore all underscores.  We can use _ to separate fields
            ;; (using | might be nicer, but it delimits symbols in Lisp).
            (if (eq item '_)
                (desugar-pattern (rest pat))
              (if (symbolp item)
                  ;; any other symbol is considered a single-bit item, so we
                  ;; can write s instead of (s 1):
                  (cons `(,item 1) (desugar-pattern (rest pat)))
                (er hard? 'desugar-pattern "Bad item in pattern: ~x0." item))))
        ;; it's a cons:
        (if (not (true-listp item))
            (er hard? 'desugar-pattern "Bad item in pattern: ~x0." item)
          (if (symbolp (first item)) ; (<var> <size>)
              (if (and (= 2 (len item))
                       (posp (second item)) ; item size can't be 0
                       )
                  (cons item (desugar-pattern (rest pat)))
                (er hard? 'desugar-pattern "Bad item in pattern: ~x0." item))
            (if (or (eql 0 (first item))
                    (eql 1 (first item)))
                (if (= 1 (len item))
                    ;; parenthesized (0) or (1) is a "should be" value.  for
                    ;; now, we treat these just like other (mandatory) bits,
                    ;; but we could relax that in the future.
                    (cons (first item) (desugar-pattern (rest pat)))
                  (er hard? 'desugar-pattern "Bad item in pattern: ~x0." item))
              (er hard? 'desugar-pattern "Bad item in pattern: ~x0." item))))))))

(defthm encoding-patternp-of-desugar-pattern
  (implies (true-listp pat)
           (encoding-patternp (desugar-pattern pat)))
  :hints (("Goal" :in-theory (enable desugar-pattern))))

;; todo: better name for this thing (not just a list of patterns)
(defun desugar-patterns (patterns)
  (declare (xargs :guard (true-listp patterns)))
  (if (endp patterns)
      nil
    (let ((entry (first patterns)))
      (if (not (and (consp entry)
                    (mnemonicp (car entry))
                    (true-listp (cdr entry))))
          (er hard? 'desugar-patterns "Bad pattern entry: ~x0." entry)
        (cons (cons (car entry) (desugar-pattern (cdr entry)))
              (desugar-patterns (rest patterns)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The number of bits in a pattern
(defund encoding-pattern-size (pat)
  (declare (xargs :guard (encoding-patternp pat)))
  (if (endp pat)
      0
    (+ (let ((item (first pat)))
         (if (consp item)
             ;; must be of the form (<var> <size>):
             (second item)
           ;; must be either 0 or 1:
           1))
       (encoding-pattern-size (rest pat)))))

(defthm natp-of-encoding-pattern-size
  (implies (encoding-patternp pat)
           (natp (encoding-pattern-size pat)))
  :hints (("Goal" :in-theory (enable encoding-pattern-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The variables listed in a pattern, representing its non-constant fields.
(defund encoding-pattern-vars (pat)
  (declare (xargs :guard (encoding-patternp pat)))
  (if (endp pat)
      nil
    (let ((item (first pat)))
      (if (consp item)
          ;; must be of the form (<var> <size>):
          (cons (first item)
                (encoding-pattern-vars (rest pat)))
        ;; must be either 0 or 1 (so not a var):
        (encoding-pattern-vars (rest pat))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A pattern is good if it has length 32 and has no duplicate vars
(defun is-good-encoding-patternp (pat)
  (declare (xargs :guard (encoding-patternp pat)))
  (and (if (= 32 (encoding-pattern-size pat))
           t
         (prog2$ (cw "WARNING: Size of pattern ~x0 is not 32." pat) ; todo: print the mnemonic
                 nil))
       (no-duplicatesp-equal (encoding-pattern-vars pat))))

;; Recognize a pattern that is good.
(defun good-encoding-patternp (pat)
  (declare (xargs :guard t))
  (and (encoding-patternp pat)
       (is-good-encoding-patternp pat)))

;; (is-good-encoding-patternp '((cond 4) 0 0 1 0 1 0 0 (s 1) (rn 4) (rd 4) (imm12 12)))


;; (defun good-encoding-pattern-listp (pats)
;;   (declare (xargs :guard t))
;;   (if (not (consp pats))
;;       (null pats)
;;     (and (good-encoding-patternp (first pats))
;;          (good-encoding-pattern-listp (rest pats)))))

;; An alist from mnemonics to encoding-patterns (alternatively, a list of
;; entries each of whose car is a mnemonic and whose cdr is an
;; encoding-pattern).
(defun encoding-pattern-alistp (alist)
  (declare (xargs :guard t))
  (if (not (consp alist))
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (mnemonicp (car entry))
           (if (good-encoding-patternp (cdr entry))
               t
             (prog2$ (cw "ERROR: Bad encoding pattern: ~x0.~%" (cdr entry))
                     nil))
           (encoding-pattern-alistp (rest alist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Given a pattern, produce a bitmask that has 1s where the pattern has constant bits (0 or 1).
;; Returns a bv32.
(defund mandatory-bit-mask (pat highbit mask)
  (declare (xargs :guard (and (encoding-patternp pat)
                              ;; including highbit as a param is just an optimization
                              (eql highbit (+ -1 (encoding-pattern-size pat)))
                              (unsigned-byte-p 32 mask))
                  :guard-hints (("Goal" :in-theory (enable encoding-pattern-size)))))
  (if (endp pat)
      mask
    (let ((item (first pat)))
      (if (consp item) ; not a 0 or a 1, so skip:
          (mandatory-bit-mask (rest pat) (- highbit (second item)) mask)
        ;; this bit is mandatory:
        (mandatory-bit-mask (rest pat)
                            (- highbit 1)
                            (bvor 32
                                  (expt 2 highbit)
                                  mask))))))

(defthm unsigned-byte-p-32-of-mandatory-bit-mask
  (implies (and (encoding-patternp pat)
                (< highbit 32)
                (equal highbit (+ -1 (encoding-pattern-size pat)))
                (unsigned-byte-p 32 mask))
           (unsigned-byte-p 32 (mandatory-bit-mask pat highbit mask)))
  :hints (("Goal" :induct t
           :in-theory (enable mandatory-bit-mask encoding-pattern-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Given a pattern, produce a bitmask that contains the mandatory values for
;; the constant bits (and zeros for the non-constant bits).
(defun mandatory-bits (pat highbit mask)
  (declare (xargs :guard (and (encoding-patternp pat)
                              ;; including highbit as a param is just an optimization
                              (equal highbit (+ -1 (encoding-pattern-size pat)))
                              (unsigned-byte-p 32 mask))
                  :guard-hints (("Goal" :in-theory (enable encoding-pattern-size)))))
  (if (endp pat)
      mask
    (let ((item (first pat)))
      (if (consp item) ; not a 0 or a 1, so skip
          (mandatory-bits (rest pat) (- highbit (second item)) mask)
        ;; this bit is mandatory:
        (mandatory-bits (rest pat)
                        (- highbit 1)
                        (if (equal 1 item)
                            (bvor 32
                                  (expt 2 highbit)
                                  mask)
                          ;; already 0:
                          mask))))))

(defthm unsigned-byte-p-32-of-mandatory-bits
  (implies (and (encoding-patternp pat)
                (< highbit 32)
                (equal highbit (+ -1 (encoding-pattern-size pat)))
                (unsigned-byte-p 32 mask))
           (unsigned-byte-p 32 (mandatory-bits pat highbit mask)))
  :hints (("Goal" :induct t
           :in-theory (enable mandatory-bits encoding-pattern-size))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund some-mandatory-bit-differsp (index
                                     pat1-mandatory-bits pat1-mandatory-bit-mask
                                     pat2-mandatory-bits pat2-mandatory-bit-mask)
  (declare (xargs :guard (and (integerp index)
                              (<= -1 index)
                              ;; i want the 32's here for efficiency (todo: add type decls):
                              (unsigned-byte-p 32 pat1-mandatory-bits)
                              (unsigned-byte-p 32 pat1-mandatory-bit-mask)
                              (unsigned-byte-p 32 pat2-mandatory-bits)
                              (unsigned-byte-p 32 pat2-mandatory-bit-mask))
                  :measure (nfix (+ 1 index))
                  ))
  (if (not (natp index))
      nil
    (if (and (= 1 (getbit index pat1-mandatory-bit-mask))
             (= 1 (getbit index pat2-mandatory-bit-mask))
             (not (equal (getbit index pat1-mandatory-bits)
                         (getbit index pat2-mandatory-bits))))
        t
      (some-mandatory-bit-differsp (+ -1 index)
                                   pat1-mandatory-bits pat1-mandatory-bit-mask
                                   pat2-mandatory-bits pat2-mandatory-bit-mask))))

(defund incompatible-patternsp (pat1 mnemonic1 pat2 mnemonic2)
  (declare (xargs :guard (and (encoding-patternp pat1)
                              (keywordp mnemonic1)
                              (encoding-patternp pat2)
                              (keywordp mnemonic2)
                              (equal (encoding-pattern-size pat1) 32)
                              (equal (encoding-pattern-size pat2) 32))))
  (let* ((pat1-mandatory-bit-mask (mandatory-bit-mask pat1 31 0))
         (pat1-mandatory-bits (mandatory-bits pat1 31 0))
         (pat2-mandatory-bit-mask (mandatory-bit-mask pat2 31 0))
         (pat2-mandatory-bits (mandatory-bits pat2 31 0))
         (pats-differp (some-mandatory-bit-differsp 31
                                                    pat1-mandatory-bits pat1-mandatory-bit-mask
                                                    pat2-mandatory-bits pat2-mandatory-bit-mask)))
    (if pats-differp
        t
      (prog2$ (cw "WARNING: Overlap in patterns for ~x0 and ~x1." mnemonic1 mnemonic2)
              nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun keyword-doubletp (d)
  (declare (xargs :guard t))
  (and (keyword-listp d)
       (= 2 (len d))))

(defun keyword-doublet-listp (lst)
  (declare (xargs :guard t))
  (if (not (consp lst))
      (null lst)
    (let ((doublet (first lst)))
      (and (keyword-doubletp doublet)
           (keyword-doublet-listp (rest lst))))))

;; Checks whether some allowed-overlap contains both mnemonic1 and mnemonic2.
(defund overlap-allowedp (mnemonic1 mnemonic2 allowed-overlaps)
  (declare (xargs :guard (and (keywordp mnemonic1)
                              (keywordp mnemonic2)
                              ;; (not (equal mnemonic1 mnemonic2)) ; uncomment?
                              (keyword-doublet-listp allowed-overlaps)
                              )))
  (if (endp allowed-overlaps)
      nil
    (let ((allowed-overlap (first allowed-overlaps)))
      (or (and (member-eq mnemonic1 allowed-overlap)
               (member-eq mnemonic2 allowed-overlap))
          (overlap-allowedp mnemonic1 mnemonic2 (rest allowed-overlaps))))))

(defun pattern-incompatible-with-allp (pat mnemonic alist allowed-overlaps)
  (declare (xargs :guard (and (good-encoding-patternp pat) ; maybe a bit overkill but we need the size to be 32
                              (keywordp mnemonic)
                              (encoding-pattern-alistp alist)
                              (keyword-doublet-listp allowed-overlaps))))
  (if (endp alist)
      t
    (let* ((entry2 (first alist))
           (mnemonic2 (car entry2))
           (pat2 (cdr entry2)))
      (and (if (overlap-allowedp mnemonic mnemonic2 allowed-overlaps)
               t
             (incompatible-patternsp pat mnemonic pat2 mnemonic2))
           (pattern-incompatible-with-allp pat mnemonic (rest alist) allowed-overlaps)))))

(defun all-patterns-incompatiblep (alist allowed-overlaps)
  (declare (xargs :guard (and (encoding-pattern-alistp alist)
                              (keyword-doublet-listp allowed-overlaps))))
  (if (endp alist)
      t
    (let* ((entry (first alist))
           (mnemonic (car entry))
           (pat (cdr entry)))
      (and (pattern-incompatible-with-allp pat mnemonic (rest alist) allowed-overlaps)
           (all-patterns-incompatiblep (rest alist) allowed-overlaps)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-instruction-arg-conjuncts (pattern)
  (declare (xargs :guard (encoding-patternp pattern)))
  (if (endp pattern)
      nil
    (let ((item (first pattern)))
      (if (not (consp item)) ; 0 or 1
          (make-instruction-arg-conjuncts (rest pattern))
        (let ((var (first item))
              (bits (second item)))
          (cons `(unsigned-byte-p ,bits (lookup-eq ',var args)) ;; implies that the var is bound in the args
                (make-instruction-arg-conjuncts (rest pattern))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun is-good-encoding-pattern-alistp (alist allowed-overlaps)
  (declare (xargs :guard (and (encoding-pattern-alistp alist)
                              (keyword-doublet-listp allowed-overlaps))))
  (and (no-duplicatesp-equal (strip-cars alist))
       (all-patterns-incompatiblep alist allowed-overlaps)
       ; the patterns must be pairwise disjoint (we compute the masks and check) ; todo: first divide the set as indicated by a tree of splitters (bits or slices).  for a splitter, all (remaining) patterns must have fully concrete values
       ))

;; todo: pass in the overlaps
(defun good-encoding-pattern-alistp (alist allowed-overlaps)
  (declare (xargs :guard (keyword-doublet-listp allowed-overlaps)))
  (and (encoding-pattern-alistp alist)
       (is-good-encoding-pattern-alistp alist allowed-overlaps)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun make-instruction-arg-predicates (alist allowed-overlaps)
  (declare (xargs :guard (and (keyword-doublet-listp allowed-overlaps)
                              (good-encoding-pattern-alistp alist allowed-overlaps))))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (mnemonic (car entry))
           (pattern (cdr entry)))
      (cons `(defund ,(pack-in-package "ARM" mnemonic '-argsp) (args)
               (declare (xargs :guard (symbol-alistp args)))
               (and ,@(make-instruction-arg-conjuncts pattern)))
            (make-instruction-arg-predicates (rest alist) allowed-overlaps)))))
