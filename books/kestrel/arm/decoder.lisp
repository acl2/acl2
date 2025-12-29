; A decoder for ARM32 instructions
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

;; STATUS: In-progress / incomplete

;; TODO: Consider using lists instead of alists for the args and
;; auto-generating the boilerplate to extract list elems (also think about how
;; to do this without consing).

;; Section references are to the document "ARM Architecture Reference Manual
;; ARMv7-A and ARMv7-R edition" (see README.md).

(include-book "portcullis")
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvand-def" :dir :system) ; todo: include just the def
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
(local (include-book "kestrel/alists-light/alistp" :dir :system))
;(include-book "std/util/bstar" :dir :system)
;(include-book "std/testing/must-be-redundant" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; These encodings come from "A8.8 Alphabetical list of instructions".
;; Here we include only the ARM encodings (Encoding A1, etc.), not the Thumb encodings (Encoding T1, etc.).
;; todo: do I want to use keywords for the field names?
;; TODO: Add more
(defconst *patterns*
  '((:adc-immediate                  (cond 4) 0 0 _ 1 _ 0 1 0 1 s (rn 4) (rd 4) (imm12 12))
    (:adc-register                   (cond 4) 0 0 _ 0 _ 0 1 0 1 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:adc-register-shifted-register  (cond 4) 0 0 _ 0 _ 0 1 0 1 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    (:add-immediate                  (cond 4) 0 0 _ 1 _ 0 1 0 0 s (rn 4) (rd 4) (imm12 12))
    (:add-register                   (cond 4) 0 0 _ 0 _ 0 1 0 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:add-register-shifted-register  (cond 4) 0 0 _ 0 _ 0 1 0 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))
    ;; These seem to be merely special cases of :add-immediate and :add-register
    ;; (:add-sp-plus-immediate          (cond 4) 0 0 _ 1 _ 0 1 0 0 s 1 1 0 1 (rd 4) (imm12 12))
    ;; (:add-sp-plus-register           (cond 4) 0 0 _ 0 _ 0 1 0 0 s 1 1 0 1 (rd 4) (imm5 5) (type 2) 0 (rm 4))

    (:adr-encoding-a1 (cond 4) 0 0 _ 1 _ 0 1 0 0 _ 0 _ 1 1 1 1 (rd 4) (imm12 12))
    (:adr-encoding-a2 (cond 4) 0 0 _ 1 _ 0 0 1 0 _ 0 _ 1 1 1 1 (rd 4) (imm12 12))

    (:and-immediate  (cond 4) 0 0 1 0 0 0 0 s (rn 4) (rd 4) (imm12 12))
    (:and-register   (cond 4) 0 0 0 0 0 0 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:and-register-shifted-register   (cond 4) 0 0 0 0 0 0 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    (:b  (cond 4) 1 0 1 0 (imm24 24))
    (:bl-immediate  (cond 4) 1 0 1 1 (imm24 24)) ;; Encoding A1 of BL/BLX (immediate)
    (:blx-immediate  1 1 1 1 1 0 1 h (imm24 24)) ;; Encoding A2 of BL/BLX (immediate)
    (:blx-register  (cond 4) 0 0 0 1 0 0 1 0 _ (1) (1) (1) (1) _ (1) (1) (1) (1) _ (1) (1) (1) (1) _ 0 0 1 1 (rm 4))

    (:cmp-immediate  (cond 4) 0 0 1 1 0 1 0 1 (rn 4) 0 0 0 0 (imm12 12)) ; todo: some zeros here are in parens
    (:cmp-register  (cond 4) 0 0 0 1 0 1 0 1 (rn 4) 0 0 0 0 (imm5 5) (type 2) 0 (rm 4)) ; todo: some zeros here are in parens

    (:eor-immediate  (cond 4) 0 0 1 0 0 0 1 s (rn 4) (rd 4) (imm12 12))
    (:eor-register   (cond 4) 0 0 0 0 0 0 1 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:eor-shifted-register   (cond 4) 0 0 0 0 0 0 1 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    (:ldr-immediate  (cond 4) 0 1 0 p u 0 w 1 (rn 4) (rt 4) (imm12 12))
    (:ldr-literal    (cond 4) 0 1 0 p u 0 w 1 1 1 1 1 (rt 4) (imm12 12))
    (:ldr-register    (cond 4) 0 1 1 p u 0 w 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:ldrb-immediate  (cond 4) 0 1 0 p u 1 w 1 (rn 4) (rt 4) (imm12 12))
    (:ldrb-literal  (cond 4) 0 1 0 p u 1 w 1 1 1 1 1 (rt 4) (imm12 12))
    (:ldrb-register  (cond 4) 0 1 1 p u 1 w 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:ldrbt-encoding-a1  (cond 4) 0 1 0 0 u 1 1 1 (rn 4) (rt 4) (imm12 12))
    (:ldrbt-encoding-a2  (cond 4) 0 1 1 0 u 1 1 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:ldrd-immediate  (cond 4) 0 0 0 p u 1 w 0 (rn 4) (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrd-literal    (cond 4) 0 0 0 1 u 1 0 0 1 1 1 1 (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4)) ; todo: parens around constants
    (:ldrd-register   (cond 4) 0 0 0 p u 0 w 0 (rn 4) (rt 4) 0 0 0 0 1 1 0 1 (rm 4)) ; todo: parens

    (:ldrex    (cond 4) 0 0 0 1 1 0 0 1 (rn 4) (rt 4) 1 1 1 1 1 0 0 1 1 1 1 1) ; todo: parens
    (:ldrexb   (cond 4) 0 0 0 1 1 1 0 1 (rn 4) (rt 4) 1 1 1 1 1 0 0 1 1 1 1 1) ; todo: parens
    (:ldrexd   (cond 4) 0 0 0 1 1 0 1 1 (rn 4) (rt 4) 1 1 1 1 1 0 0 1 1 1 1 1) ; todo: parens
    (:ldrexh   (cond 4) 0 0 0 1 1 1 1 1 (rn 4) (rt 4) 1 1 1 1 1 0 0 1 1 1 1 1) ; todo: parens

    (:ldrh-immediate  (cond 4) 0 0 0 p u 1 w 1 (rn 4) (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:ldrh-literal    (cond 4) 0 0 0 p u 1 w 1 1 1 1 1 (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:ldrh-register   (cond 4) 0 0 0 p u 0 w 1 (rn 4) (rt 4) 0 0 0 0 1 0 1 1 (rm 4)) ; parens

    (:ldrht-encoding-a1  (cond 4) 0 0 0 0 u 1 1 1 (rn 4) (rt 4) (imm4h 4) 1 0 1 1 (imm4l 4))
    (:ldrht-encoding-a2  (cond 4) 0 0 0 0 u 0 1 1 (rn 4) (rt 4) 0 0 0 0 1 0 1 1 (rm 4)) ; parens

    (:ldrsb-immediate  (cond 4) 0 0 0 p u 1 w 1 (rn 4) (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrsb-literal    (cond 4) 0 0 0 p u 1 w 1 1 1 1 1 (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrsb-register   (cond 4) 0 0 0 p u 0 w 1 (rn 4) (rt 4) 0 0 0 0 1 1 0 1 (rm 4)) ;parens

    (:ldrsbt-encoding-a1  (cond 4) 0 0 0 0 u 1 1 1 (rn 4) (rt 4) (imm4h 4) 1 1 0 1 (imm4l 4))
    (:ldrsbt-encoding-a2  (cond 4) 0 0 0 0 u 0 1 1 (rn 4) (rt 4) 0 0 0 0 1 1 0 1 (rm 4)) ; parens

    (:ldrsh-immediate  (cond 4) 0 0 0 p u 1 w 1 (rn 4) (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:ldrsh-literal    (cond 4) 0 0 0 p u 1 w 1 1 1 1 1 (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:ldrsh-register   (cond 4) 0 0 0 p u 0 w 1 (rn 4) (rt 4) 0 0 0 0 1 1 1 1 (rm 4)) ; todo: parens

    (:ldrsht-encoding-a1  (cond 4) 0 0 0 0 u 1 1 1 (rn 4) (rt 4) (imm4h 4) 1 1 1 1 (imm4l 4))
    (:ldrsht-encoding-a2  (cond 4) 0 0 0 0 u 0 1 1 (rn 4) (rt 4) 0 0 0 0 1 1 1 1 (rm 4)) ; parens

    (:ldrt-encoding-a1  (cond 4) 0 1 0 0 u 0 1 1 (rn 4) (rt 4) (imm12 12))
    (:ldrt-encoding-a2  (cond 4) 0 1 1 0 u 0 1 1 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:lsl-immediate  (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (imm5 5) 0 0 0 (rm 4))
    (:lsl-register  (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (rm 4) 0 0 0 1 (rn 4))

    (:lsr-immediate  (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (imm5 5) 0 1 0 (rm 4))
    (:lsr-register  (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) (rm 4) 0 0 1 1 (rn 4))

    (:mov-immediate-encoding-a1  (cond 4) 0 0 1 1 1 0 1 s 0 0 0 0 (rd 4) (imm12 12)) ; parens
    (:mov-immediate-encoding-a2  (cond 4) 0 0 1 1 0 0 0 0 (imm4 4) (rd 4) (imm12 12))
    (:mov-register  (cond 4) 0 0 0 1 1 0 1 s 0 0 0 0 (rd 4) 0 0 0 0 0 0 0 0 (rm 4)) ;parens
    (:movt  (cond 4) 0 0 1 1 0 1 0 0 (imm4 4) (rd 4) (imm12 12))

    (:nop  (cond 4) 0 0 1 1 0 0 1 0 0 0 0 0 1 1 1 1 0 0 0 0 0 0 0 0 0 0 0 0) ; parens

    (:orr-immediate  (cond 4) 0 0 1 1 1 0 0 s (rn 4) (rd 4) (imm12 12))
    (:orr-register   (cond 4) 0 0 0 1 1 0 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:orr-shifted-register   (cond 4) 0 0 0 1 1 0 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))

    (:push-encoding-a1  (cond 4) 1 0 0 1 0 0 1 0 1 1 0 1 (register_list 16))
    (:push-encoding-a2  (cond 4) 0 1 0 1 0 0 1 0 1 1 0 1 (rt 4) 0 0 0 0 0 0 0 0 0 1 0 0)

    (:str-immediate   (cond 4) 0 1 0 p u 0 w 0 (rn 4) (rt 4) (imm12 12))
    (:str-register    (cond 4) 0 1 1 p u 0 w 0 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))
    (:strb-immediate  (cond 4) 0 1 0 p u 1 w 0 (rn 4) (rt 4) (imm12 12))
    (:strb-register   (cond 4) 0 1 1 p u 1 w 0 (rn 4) (rt 4) (imm5 5) (type 2) 0 (rm 4))

    (:sub-immediate                   (cond 4) 0 0 1 0 0 1 0 s (rn 4) (rd 4) (imm12 12))
    (:sub-register                    (cond 4) 0 0 0 0 0 1 0 s (rn 4) (rd 4) (imm5 5) (type 2) 0 (rm 4))
    (:sub-register-shifted-register   (cond 4) 0 0 0 0 0 1 0 s (rn 4) (rd 4) (rs 4) 0 (type 2) 1 (rm 4))
    ))

;; Some bit patterns match multiple patterns.
;; For most of these, the one listed first has a special case that refers to the second.
(defconst *allowed-encoding-overlaps*
  '((:add-immediate :adr-encoding-a1)
    (:sub-immediate :adr-encoding-a2)
    (:str-immediate :push-encoding-a2)
    (:ldr-immediate :ldr-literal)
    (:ldrb-immediate :ldrb-literal)
    (:ldrb-immediate :ldrbt-encoding-a1)
    (:ldrb-literal :ldrbt-encoding-a1)
    (:ldrb-register :ldrbt-encoding-a2)
    (:ldrd-immediate :ldrd-literal)
    (:ldrh-immediate :ldrh-literal)
    (:ldrh-immediate :ldrht-encoding-a1)
    (:ldrh-literal :ldrht-encoding-a1)
    (:ldrh-register :ldrht-encoding-a2)
    (:ldrsb-immediate :ldrsb-literal)
    (:ldrsb-immediate :ldrsbt-encoding-a1)
    (:ldrsb-literal :ldrsbt-encoding-a1)
    (:ldrsb-register :ldrsbt-encoding-a2)
    (:ldrsh-immediate :ldrsh-literal)
    (:ldrsh-immediate :ldrsht-encoding-a1)
    (:ldrsh-literal :ldrsht-encoding-a1)
    (:ldrsh-register :ldrsht-encoding-a2)
    (:ldr-immediate :ldrt-encoding-a1)
    (:ldr-literal :ldrt-encoding-a1)
    (:ldr-register :ldrt-encoding-a2)
    (:b :blx-immediate) ; for the case of cond=1111 in B
    (:bl-immediate :blx-immediate) ; for the case of cond=1111 in BL
    (:mov-register :lsl-immediate) ; for the shift=0 case in LSL
    ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; An encoding-pattern is a list of items, each of which is 0 or 1 or of the form (<var> <numbits>).
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
;; - drops underscores (just used as seperators)
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
                (er hard? "Bad item in pattern: ~x0." item))))
        ;; it's a cons:
        (if (not (true-listp item))
            (er hard? "Bad item in pattern: ~x0." item)
          (if (symbolp (first item)) ; (<var> <size>)
              (if (and (= 2 (len item))
                       (posp (second item)) ; item size can't be 0
                       )
                  (cons item (desugar-pattern (rest pat)))
                (er hard? "Bad item in pattern: ~x0." item))
            (if (or (eql 0 (first item))
                    (eql 1 (first item)))
                (if (= 1 (len item))
                    ;; parenthesized (0) or (1) is a "should be" value.  for
                    ;; now, we treat these just like other (mandatory) bits,
                    ;; but we could relax that in the future.
                    (cons (first item) (desugar-pattern (rest pat)))
                  (er hard? "Bad item in pattern: ~x0." item))
              (er hard? "Bad item in pattern: ~x0." item))))))))

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
  (and (acl2::keyword-listp d) ; todo: import
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

(defun is-good-encoding-pattern-alistp (alist)
  (declare (xargs :guard (encoding-pattern-alistp alist)))
  (and (no-duplicatesp-equal (strip-cars alist))
       (all-patterns-incompatiblep alist *allowed-encoding-overlaps*)
       ; the patterns must be pairwise disjoint (we compute the masks and check) ; todo: first divide the set as indicated by a tree of splitters (bits or slices).  for a splitter, all (remaining) patterns must have fully concrete values
       ))

(defun good-encoding-pattern-alistp (alist)
  (declare (xargs :guard t))
  (and (encoding-pattern-alistp alist)
       (is-good-encoding-pattern-alistp alist)))

;move
(assert-event (good-encoding-pattern-alistp (desugar-patterns *patterns*)))


(defun make-alist-for-fields (highbit pat)
  (declare (xargs :guard (and (encoding-patternp pat)
                              (equal highbit (+ -1 (encoding-pattern-size pat))))
                  :guard-hints (("Goal" :in-theory (enable encoding-pattern-size)))))
  (if (endp pat)
      nil
    (let ((item (first pat)))
      (if (not (consp item)) ; it's a 0 or 1, so skip
          (make-alist-for-fields (- highbit 1) (rest pat))
        (let ((name (first item))
              (size (second item)))
          `(acons ',name
                  ,(if (= 1 size) ; todo: use bvchop if we can
                       `(getbit ,highbit inst)
                     `(slice ,highbit ,(+ 1 (- highbit size)) inst))
                  ,(make-alist-for-fields (- highbit size) (rest pat))))))))

;; for now this is linear, but see about for the idea of using a tree of splitters
(defun make-decoding-cases (alist)
  (declare (xargs :guard (good-encoding-pattern-alistp alist)))
  (if (endp alist)
      nil
    (cons (let* ((entry (first alist))
                 (opcode (car entry))
                 (pattern (cdr entry))
                 (mandatory-bit-mask (mandatory-bit-mask pattern 31 0)) ; has a 1 everywhere the pattern has a concrete value
                 (mandatory-bits (mandatory-bits pattern 31 0)) ; has all the mandatory bits the same as in the pattern and zeros for the don't cares
                 )
            ;; this is a cond clause:
            `((equal (bvand 32 inst ,mandatory-bit-mask) ,mandatory-bits)
              (mv nil ; no error
                  ,opcode
                  ,(make-alist-for-fields 31 pattern)
                  )))
          (make-decoding-cases (rest alist)))))

(defun make-instruction-arg-conjuncts (pattern)
  (declare (xargs :guard (encoding-patternp pattern)))
  (if (endp pattern)
      nil
    (let ((item (first pattern)))
      (if (not (consp item)) ; 0 or 1
          (make-instruction-arg-conjuncts (rest pattern))
        (let ((var (first item))
              (bits (second item)))
          (cons `(unsigned-byte-p ,bits (lookup-eq ',var args))
                (make-instruction-arg-conjuncts (rest pattern))))))))

(defun make-instruction-arg-predicates (alist)
  (declare (xargs :guard (good-encoding-pattern-alistp alist)))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (opcode (car entry))
           (pattern (cdr entry)))
      (cons `(defun ,(acl2::pack-in-package "ARM" opcode '-argsp) (args)
               (declare (xargs :guard (symbol-alistp args)))
               (and ,@(make-instruction-arg-conjuncts pattern)))
            (make-instruction-arg-predicates (rest alist))))))

(defun make-decoder (name alist)
  (declare (xargs :guard (and (symbolp name)
                              (good-encoding-pattern-alistp alist))))
  `(progn
     ;; Returns (mv erp opcode args).
     ,@(make-instruction-arg-predicates alist)

     ;; The decoder:
     (defun ,name (inst)
       (declare (xargs :guard (unsigned-byte-p 32 inst)))
       (cond
        ,@(make-decoding-cases alist)
        (t (mv :unsupported nil nil))))))

;; This makes a decoder called arm32-decode that decodes a USB32 into an
;; instruction (any of the instructions in the *patterns*):
(make-event (make-decoder 'arm32-decode (desugar-patterns *patterns*)))
