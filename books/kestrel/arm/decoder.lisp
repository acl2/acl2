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

(include-book "portcullis")
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/alists-light/lookup-eq" :dir :system)
(include-book "kestrel/alists-light/lookup-eq-safe" :dir :system)
;(include-book "std/util/bstar" :dir :system)
;(include-book "std/testing/must-be-redundant" :dir :system)
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/bv/unsigned-byte-p" :dir :system))

;; todo: do I want to use keywords here?
(defconst *patterns*
  '((:add-immediate .                 ((cond 4) 0 0 1 0 1 0 0 (s 1) (rn 4)  (rd 4) (imm12 12)))
    (:add-register .                  ((cond 4) 0 0 0 0 1 0 0 (s 1) (rn 4)  (rd 4) (imm5 5) (type 2) 0 (rm 4)))
    (:add-register-shifted-register . ((cond 4) 0 0 0 0 1 0 0 (s 1) (rn 4)  (rd 4) (rs 4) 0 (type 2) 1 (rm 4)))
    ;; (:add-sp-plus-immediate .         ((cond 4) 0 0 1 0 1 0 0 (s 1) 1 1 0 1 (rd 4) (imm12 12)))
    ;; (:add-sp-plus-register .          ((cond 4) 0 0 0 0 1 0 0 (s 1) 1 1 0 1 (rd 4) (imm5 5) (type 2) 0 (rm 4)))
    (:push-encoding-a1 . ((cond 4) 1 0 0 1 0 0 1 0 1 1 0 1 (register_list 16)))
    (:push-encoding-a2 . ((cond 4) 0 1 0 1 0 0 1 0 1 1 0 1 (rt 4) 0 0 0 0 0 0 0 0 0 1 0 0))
    ;; TODO: Add more
    ))

;; An encoding entry is a list of items each of which is 0 or 1 or of the form (<var> <bits>)
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

(defun is-good-encoding-patternp (pat)
  (declare (xargs :guard (encoding-patternp pat)))
  (and (= 32 (encoding-pattern-size pat))
       (no-duplicatesp-equal (encoding-pattern-vars pat))))

(defun good-encoding-patternp (pat)
  (declare (xargs :guard t))
  (and (encoding-patternp pat)
       (is-good-encoding-patternp pat)))

;; (is-good-encoding-patternp '((cond 4) 0 0 1 0 1 0 0 (s 1) (rn 4) (rd 4) (imm12 12)))


(defun encoding-pattern-alistp (alist)
  (declare (xargs :guard t))
  (if (not (consp alist))
      (null alist)
    (let ((entry (first alist)))
      (and (consp entry)
           (keywordp (car entry))
           (good-encoding-patternp (cdr entry))
           (encoding-pattern-alistp (rest alist))))))

;; Given a pattern, produce a m bitmask that has 1s where the pattern has constant bits (0 or 1).
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

;; Given a pattern, produce a m bitmask that zeros out the non-constant bits.
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

(defund incompatible-patternsp (pat1 pat2)
  (declare (xargs :guard (and (encoding-patternp pat1)
                              (encoding-patternp pat2)
                              (equal (encoding-pattern-size pat1) 32)
                              (equal (encoding-pattern-size pat2) 32))))
  (let ((pat1-mandatory-bit-mask (mandatory-bit-mask pat1 31 0))
        (pat1-mandatory-bits (mandatory-bits pat1 31 0))
        (pat2-mandatory-bit-mask (mandatory-bit-mask pat2 31 0))
        (pat2-mandatory-bits (mandatory-bits pat2 31 0)))
    (some-mandatory-bit-differsp 31
                                 pat1-mandatory-bits pat1-mandatory-bit-mask
                                 pat2-mandatory-bits pat2-mandatory-bit-mask)))

(defun good-encoding-pattern-listp (pats)
  (declare (xargs :guard t))
  (if (not (consp pats))
      (null pats)
    (and (good-encoding-patternp (first pats))
         (good-encoding-pattern-listp (rest pats)))))

(defun pattern-incompatible-with-allp (pat pats)
  (declare (xargs :guard (and (good-encoding-patternp pat) ; maybe a bit overkill but we need the size 32
                              (good-encoding-pattern-listp pats))))
  (if (endp pats)
      t
    (and (incompatible-patternsp pat (first pats))
         (pattern-incompatible-with-allp pat (rest pats)))))

(defun all-patterns-incompatiblep (pats)
  (declare (xargs :guard (good-encoding-pattern-listp pats)))
  (if (endp pats)
      t
    (and (pattern-incompatible-with-allp (first pats) (rest pats))
         (all-patterns-incompatiblep (rest pats)))))

(defun is-good-encoding-pattern-alistp (alist)
  (declare (xargs :guard (encoding-pattern-alistp alist)))
  (and (no-duplicatesp-equal (strip-cars alist))
       (all-patterns-incompatiblep (strip-cdrs alist))
       ; the patterns must be pairwise disjoint (we compute the masks and check) ; todo: first divide the set as indicated by a tree of splitters (bits or slices).  for a splitter, all (remaining) patterns must have fully concrete values
       ))

(defun good-encoding-pattern-alistp (alist)
  (declare (xargs :guard t))
  (and (encoding-pattern-alistp alist)
       (is-good-encoding-pattern-alistp alist)))

;move
(assert-event (good-encoding-pattern-alistp *patterns*))


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

(make-event (make-decoder 'arm32-decode *patterns*))
