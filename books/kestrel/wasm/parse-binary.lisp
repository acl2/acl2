; A parser for the Web Assembly binary format
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "WASM")

;; STATUS: IN-PROGRESS (need to keep adding more instructions)

;; TODO: Continue adding parsing of more instructions

(include-book "portcullis") ; for the package
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/lists-light/len-at-least" :dir :system)
(include-book "kestrel/alists-light/lookup" :dir :system)
(include-book "kestrel/bv-lists/byte-listp" :dir :system)
(include-book "kestrel/file-io-light/read-file-into-byte-list" :dir :system)
(include-book "kestrel/typed-lists-light/bytes-to-printable-string" :dir :system)
(include-book "kestrel/typed-lists-light/append-all" :dir :system)
(include-book "kestrel/lists-light/repeat" :dir :system)
(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/lists-light/take" :dir :system))
(local (include-book "kestrel/arithmetic-light/types" :dir :system))

(local (in-theory (enable acl2::acl2-numberp-when-natp)))

(local (in-theory (disable natp len acl2::bytep)))

(local
  (defthm bytep-forward-to-natp
    (implies (bytep x)
             (natp x))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (enable bytep)))))

(local
  (defthm acl2-numberp-when-bytep
    (implies (bytep x)
             (acl2-numberp x))
    :hints (("Goal" :in-theory (enable bytep)))))

(in-theory (disable mv-nth))

;; Returns (mv erp byte bytes).
(defund take-1 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (if (not (len-at-least 1 bytes))
      (mv :not-enough-bytes 0 nil)
    (mv nil (first bytes) (rest bytes))))

(defthm natp-of-mv-nth-1-of-take-1
  (implies (byte-listp bytes)
           (natp (mv-nth 1 (take-1 bytes))))
  :hints (("Goal" :in-theory (enable take-1 byte-listp bytep))))

(defthm bytep-of-mv-nth-1-of-take-1
  (implies (byte-listp bytes)
           (bytep (mv-nth 1 (take-1 bytes))))
  :hints (("Goal" :in-theory (enable take-1))))

(defthm natp-of-mv-nth-1-of-take-1-type
  (implies (byte-listp bytes)
           (natp (mv-nth 1 (take-1 bytes))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable take-1))))

(defthm byte-listp-of-mv-nth-2-of-take-1
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (take-1 bytes))))
  :hints (("Goal" :in-theory (enable take-1))))

(defthm true-listp-of-mv-nth-2-of-take-1
  (implies (true-listp bytes)
           (true-listp (mv-nth 2 (take-1 bytes))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable take-1))))

(defthm <-of-len-of-mv-nth-2-of-take-1-linear
  (implies (not (mv-nth 0 (take-1 bytes)))
           (< (len (mv-nth 2 (take-1 bytes)))
              (len bytes)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable take-1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp bytes bytes).
(defund take-n (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (len-at-least n bytes)
      (mv nil (take n bytes) (nthcdr n bytes))
    (mv :not-enough-bytes nil nil)))

(defthm byte-listp-of-mv-nth-1-of-take-n
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 1 (take-n n bytes))))
  :hints (("Goal" :in-theory (enable take-n))))

(defthm byte-listp-of-mv-nth-2-of-take-n
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (take-n n bytes))))
  :hints (("Goal" :in-theory (enable take-n))))

(defthm <=-of-len-of-mv-nth-2-of-take-n-linear
  (<= (len (mv-nth 2 (take-n n bytes)))
      (len bytes))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable take-n))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parse an unsigned integer in LEB128 encoding.
;; Returns (mv erp val bytes).
(defund parse-unsigned-leb128 (size bytes) ; size is called N in the spec
  (declare (xargs :guard (and (posp size)
                              (byte-listp bytes))
                  :verify-guards nil ; done below
                  :measure (len bytes)))
  (b* (((mv erp n bytes)
        (take-1 bytes))
       ((when erp) (mv erp 0 nil)))
    (if (< n (expt 2 7))
        (if (< n (expt 2 size)) ; n < 2^N
            (mv nil n bytes)
          (mv :unsigned-leb128-error 0 nil))
      (if (> size 7) ; N > 7
          (b* (((mv erp m bytes)
                (parse-unsigned-leb128 (+ -7 size) bytes))
               ((when erp) (mv erp 0 nil)))
            (mv nil (+ (* (expt 2 7) m) (- n (expt 2 7))) bytes))
        (mv :unsigned-leb128-error 0 nil)))))

;; (parse-unsigned-leb128 8 '(#x03))
;; (parse-unsigned-leb128 8 '(#x83 #x00))

(defthm natp-of-mv-nth-1-of-parse-unsigned-leb128
  (implies (byte-listp bytes)
           (natp (mv-nth 1 (parse-unsigned-leb128 size bytes))))
  :hints (("Goal" :in-theory (enable parse-unsigned-leb128 byte-listp natp))))

(verify-guards parse-unsigned-leb128)

(defthm byte-listp-of-mv-nth-2-of-parse-unsigned-leb128
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-unsigned-leb128 size bytes))))
  :hints (("Goal" :in-theory (enable parse-unsigned-leb128))))

(defthm <-of-len-of-mv-nth-2-of-parse-unsigned-leb128-linear
  (implies (not (mv-nth 0 (parse-unsigned-leb128 size bytes)))
           (< (len (mv-nth 2 (parse-unsigned-leb128 size bytes)))
              (len bytes)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-unsigned-leb128))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Parse a signed integer in LEB128 encoding.
;; Returns (mv erp val bytes).
(defund parse-signed-leb128 (size bytes) ; size is called N in the spec
  (declare (xargs :guard (and (posp size)
                              (byte-listp bytes))
                  :verify-guards nil ; done below
                  :measure (len bytes)))
  (b* (((mv erp n bytes)
        (take-1 bytes))
       ((when erp) (mv erp 0 nil)))
    (if (< n (expt 2 6)) ; n < 2^6
        (if (< n (expt 2 (+ -1 size))) ; n < 2^(N-1)
            (mv nil n bytes)
          (mv :signed-leb128-error 0 nil))
      (if (< n (expt 2 7)) ; 2^6 <= n < 2^7
          (if (>= n (- (expt 2 7) (expt 2 (+ -1 size)))) ; n >= 2^7 - 2^(N-1)
              (mv nil (- n (expt 2 7)) bytes)
            (mv :signed-leb128-error 0 nil))
        (if (> size 7) ; N > 7
            (b* (((mv erp m bytes)
                  (parse-signed-leb128 (+ -7 size) bytes))
                 ((when erp) (mv erp 0 nil)))
              (mv nil (+ (* (expt 2 7) m) (- n (expt 2 7))) bytes))
          (mv :signed-leb128-error 0 nil))))))

(defthm integerp-of-mv-nth-1-of-parse-signed-leb128
  (implies (byte-listp bytes)
           (integerp (mv-nth 1 (parse-signed-leb128 size bytes))))
  :hints (("Goal" :in-theory (enable parse-signed-leb128 byte-listp natp))))

(verify-guards parse-signed-leb128)

(defthm byte-listp-of-mv-nth-2-of-parse-signed-leb128
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-signed-leb128 size bytes))))
  :hints (("Goal" :in-theory (enable parse-signed-leb128))))

(defthm <-of-len-of-mv-nth-2-of-parse-signed-leb128-linear
  (implies (not (mv-nth 0 (parse-signed-leb128 size bytes)))
           (< (len (mv-nth 2 (parse-signed-leb128 size bytes)))
              (len bytes)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-signed-leb128))))

;; (parse-signed-leb128 8 '(#x7e))
;; (parse-signed-leb128 8 '(#xFE #x7F))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp u32 bytes).
(defund parse-u32 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-unsigned-leb128 32 bytes))

(defthm natp-of-mv-nth-1-of-parse-u32
  (implies (byte-listp bytes)
           (natp (mv-nth 1 (parse-u32 bytes))))
  :hints (("Goal" :in-theory (enable parse-u32))))

(defthm byte-listp-of-mv-nth-2-of-parse-u32
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-u32 bytes))))
  :hints (("Goal" :in-theory (enable parse-u32))))

(defthm <-of-len-of-mv-nth-2-of-parse-u32-linear
  (implies (not (mv-nth 0 (parse-u32 bytes)))
           (< (len (mv-nth 2 (parse-u32 bytes)))
              (len bytes)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-u32))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp i32 bytes).
(defun parse-i32 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-signed-leb128 32 bytes))

;; Returns (mv erp i64 bytes).
(defun parse-i64 (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-signed-leb128 64 bytes))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *section-ids*
  '((0 . :custom)
    (1 . :type)
    (2 . :import)
    (3 . :function)
    (4 . :table)
    (5 . :memory)
    (6 . :global)
    (7 . :export)
    (8 . :start)
    (9 . :element)
    (10 . :code)
    (11 . :data)
    (12 . :data-count)))

(defund section-idp (id)
  (declare (xargs :guard t))
  (member-eq id (strip-cdrs *section-ids*)))

;; Returns (mv erp vector-length bytes).
(defun parse-vector-length (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u32 bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp type bytes).
(defund parse-reftype (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp byte bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil bytes)))
    (case byte
      (#x70 (mv nil :funcref bytes))
      (#x6F (mv nil :externref bytes))
      (otherwise (mv `(:bad-reftype ,byte) nil nil)))))

(defthm byte-listp-of-mv-nth-2-of-parse-reftype
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-reftype bytes))))
  :hints (("Goal" :in-theory (enable parse-reftype))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp numtype bytes).
(defund parse-numtype (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp byte bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil bytes)))
    (case byte
      (#x7F (mv nil :i32 bytes))
      (#x7E (mv nil :i64 bytes))
      (#x7D (mv nil :f32 bytes))
      (#x7C (mv nil :f64 bytes))
      (otherwise (mv `(:bad-numtype ,byte) nil nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp vectype bytes).
(defund parse-vectype (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp byte bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil bytes)))
    (case byte
      (#x7B (mv nil :vectype bytes))
      (otherwise (mv `(:bad-vectype ,byte) nil nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp valtype bytes).
(defund parse-valtype (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp byte bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil bytes)))
    (case byte
      ;; numtypes:
      (#x7F (mv nil :i32 bytes))
      (#x7E (mv nil :i64 bytes))
      (#x7D (mv nil :f32 bytes))
      (#x7C (mv nil :f64 bytes))
      ;; vectype:
      (#x7B (mv nil :vectype bytes))
      ;; reftypes
      (#x70 (mv nil :funcref bytes))
      (#x6F (mv nil :externref bytes))
      (otherwise (mv `(:bad-valtype ,byte) nil nil)))))

(defthm byte-listp-of-mv-nth-2-of-parse-valtype
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-valtype bytes))))
  :hints (("Goal" :in-theory (enable parse-valtype))))

(defthm len-of-mv-nth-2-of-parse-valtype
  (implies (not (mv-nth 0 (parse-valtype bytes))) ; no error
           (< (len (mv-nth 2 (parse-valtype bytes)))
              (len bytes)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-valtype))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; Returns (mv erp limits bytes).
(defun parse-limits (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp byte bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil bytes)))
    (case byte
      (#x00 (b* (((mv erp n bytes)
                  (take-1 bytes))
                 ((when erp) (mv erp nil bytes)))
              (mv nil (acons :min n (acons :max :none nil)) bytes)))
      (#x01 (b* (((mv erp n bytes)
                  (take-1 bytes))
                 ((when erp) (mv erp nil bytes))
                 ((mv erp m bytes)
                  (take-1 bytes))
                 ((when erp) (mv erp nil bytes)))
              (mv nil (acons :min n (acons :max m nil)) bytes)))
      (otherwise (mv `(:bad-limits ,byte) nil nil)))))

;; Returns (mv erp table bytes).
(defun parse-table (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp et bytes)
        (parse-reftype bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp lim bytes)
        (parse-limits bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :reftype et
               (acons :limits lim nil))
        bytes)))

;; Returns (mv erp tables bytes).
(defun parse-n-tables (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp table bytes)
          (parse-table bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp tables bytes)
          (parse-n-tables (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil (cons table tables) bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp memtype bytes).
(defun parse-memtype (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp lim bytes)
        (parse-limits bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :limits lim nil)
        bytes)))

;; Returns (mv erp memory bytes).
(defun parse-memory (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp memtype bytes)
        (parse-memtype bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :memtype memtype nil)
        bytes)))

;; Returns (mv erp memories bytes).
(defun parse-n-memories (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp memory bytes)
          (parse-memory bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp memories bytes)
          (parse-n-memories (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil (cons memory memories) bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp mut bytes).
(defun parse-mut (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp byte bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil nil)))
    (case byte
      (#x00 (mv nil :const bytes))
      (#x01 (mv nil :var bytes))
      (otherwise (mv `(:bad-mut ,byte) nil nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp globaltype bytes).
(defun parse-globaltype (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp ty bytes) ;can't use the name "t" in lisp
        (parse-valtype bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp m bytes)
        (parse-mut bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :valtype ty (acons :mut m nil))
        bytes)))

(defthm byte-listp-of-mv-nth-2-of-parse-globaltype
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-globaltype bytes))))
  :hints (("Goal" :in-theory (enable parse-globaltype))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp blocktype bytes)
(defund parse-blocktype (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp byte bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil nil)))
    (if (= #x40 byte)
        (mv nil :empty bytes) ; epsilon in the spec
      (if (member byte '(;; numtypes:
                         #x7F
                         #x7E
                         #x7D
                         #x7C
                         ;; vectype:
                         #x7B
                         ;; reftypes
                         #x70
                         #x6F))
          (parse-valtype bytes)
        ;; must be an s33:
        (parse-signed-leb128 33 bytes)))))

(defthm <=-of-len-of-mv-nth-2-of-parse-blocktype
  (implies (not (mv-nth 0 (parse-blocktype bytes))) ; no error
           (<= (len (mv-nth 2 (parse-blocktype bytes)))
               (len bytes)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-blocktype))))

(defthm byte-listp-of-mv-nth-2-of-parse-blocktype
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-blocktype bytes))))
  :hints (("Goal" :in-theory (enable parse-blocktype))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp localidx bytes).
(defun parse-localidx (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u32 bytes))

;; Returns (mv erp globalidx bytes).
(defun parse-globalidx (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u32 bytes))

;; Returns (mv erp labelidx bytes).
(defun parse-labelidx (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u32 bytes))

;; Returns (mv erp funcidx bytes).
(defun parse-funcidx (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u32 bytes))

;; Returns (mv erp typeidx bytes).
(defun parse-typeidx (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u32 bytes))

;; Returns (mv erp tableidx bytes).
(defun parse-tableidx (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (parse-u32 bytes))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp labelidxs bytes).
(defun parse-n-labelidxs (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp labelidx bytes)
          (parse-labelidx bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp labelidxs bytes)
          (parse-n-labelidxs (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil (cons labelidx labelidxs) bytes))))

(defthm byte-listp-of-mv-nth-2-of-parse-n-labelidxs
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-n-labelidxs n bytes))))
  :hints (("Goal" :in-theory (enable parse-n-labelidxs))))

(defthm len-of-mv-nth-2-of-parse-n-labelidxs-linear
  (<= (len (mv-nth 2 (parse-n-labelidxs n bytes)))
      (len bytes))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-n-labelidxs))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp memarg bytes).
(defun parse-memarg (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp a bytes)
        (parse-u32 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp o bytes)
        (parse-u32 bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :align a
               (acons :offset o nil))
        bytes)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
  ;; Returns (mv erp instr bytes).
  (defund parse-instr (opcode bytes)
    (declare (xargs :guard (and (bytep opcode)
                                ; (not (= #x0B opcode)) ; not the end mark
                                ; (not (= #x05 opcode)) ; not the end mark
                                (byte-listp bytes))
                    :verify-guards nil ; done below
                    :measure (make-ord 1 (+ 1 (len bytes)) 1)))
    (case opcode
      (#x00 (mv nil '(:unreachable) bytes))
      (#x01 (mv nil '(:nop) bytes))
      (#x02 (b* (((mv erp bt bytes)
                  (parse-blocktype bytes))
                 ((when erp) (mv erp nil nil))
                 ((mv erp instrs & ; terminator
                      bytes)
                  (parse-instrs bytes '(#x0B) nil))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:block ,bt ,instrs) bytes)))
      (#x03 (b* (((mv erp bt bytes)
                  (parse-blocktype bytes))
                 ((when erp) (mv erp nil nil))
                 ((mv erp instrs & ; terminator
                      bytes)
                  (parse-instrs bytes '(#x0B) nil))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:loop ,bt ,instrs) bytes)))
      (#x04 (b* (((mv erp bt bytes)
                  (parse-blocktype bytes))
                 ((when erp) (mv erp nil nil))
                 (bytes-before-parse-instrs bytes) ; for the MBT below
                 ((mv erp instrs terminator bytes)
                  (parse-instrs bytes '(#x0B #x05) nil))
                 ((when erp) (mv erp nil nil))
                 ((when (not (mbt (<= (len bytes) (len bytes-before-parse-instrs)))))
                  (mv :termination-error nil nil)))
              (if (= terminator #x0B)
                  ;; empty else:
                  (mv nil `(:if ,bt ,instrs :empty) bytes)
                ;; non-empty else:
                (b* (((mv erp instrs2 & ;terminator
                          bytes)
                      (parse-instrs bytes '(#x0B) nil))
                     ((when erp) (mv erp nil nil)))
                  (mv nil `(:if ,bt ,instrs ,instrs2) bytes)))))
      (#x0C (b* (((mv erp l bytes)
                  (parse-labelidx bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:br ,l) bytes)))
      (#x0D (b* (((mv erp l bytes)
                  (parse-labelidx bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:br_if ,l) bytes)))
      (#x0E (b* (((mv erp vector-length bytes)
                  (parse-vector-length bytes))
                 ((when erp) (mv erp nil nil))
                 ((mv erp l* bytes)
                  (parse-n-labelidxs vector-length bytes))
                 ((when erp) (mv erp nil nil))
                 ((mv erp l_n bytes)
                  (parse-labelidx bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:br_table ,l* ,l_n) bytes)))
      (#x0F (mv nil :return bytes))
      (#x10 (b* (((mv erp x bytes)
                  (parse-funcidx bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:call ,x) bytes)))
      (#x11 (b* (((mv erp y bytes)
                  (parse-typeidx bytes))
                ((when erp) (mv erp nil nil))
                ((mv erp x bytes)
                  (parse-tableidx bytes))
                ((when erp) (mv erp nil nil)))
             (mv nil `(:call_indirect ,x ,y) bytes)))

      ;; Variable Instructions:
      (#x20 (b* (((mv erp x bytes)
                  (parse-localidx bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:local.get ,x) bytes)))
      (#x21 (b* (((mv erp x bytes)
                  (parse-localidx bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:local.set ,x) bytes)))
      (#x22 (b* (((mv erp x bytes)
                  (parse-localidx bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:local.tee ,x) bytes)))
      (#x23 (b* (((mv erp x bytes)
                  (parse-globalidx bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:global.get ,x) bytes)))
      (#x24 (b* (((mv erp x bytes)
                  (parse-globalidx bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:global.set ,x) bytes)))

      ;; Memory Instructions:
      (#x28 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i32.load ,m) bytes)))
      (#x29 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.load ,m) bytes)))
      (#x2A (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:f32.load ,m) bytes)))
      (#x2B (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:f64.load ,m) bytes)))
      (#x2C (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i32.load8_s ,m) bytes)))
      (#x2D (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i32.load8_u ,m) bytes)))
      (#x2E (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i32.load16_s ,m) bytes)))
      (#x2F (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i32.load16_u ,m) bytes)))
      (#x30 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.load8_s ,m) bytes)))
      (#x31 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.load8_u ,m) bytes)))
      (#x32 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.load16_s ,m) bytes)))
      (#x33 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.load16_u ,m) bytes)))
      (#x34 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.load32_s ,m) bytes)))
      (#x35 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.load32_u ,m) bytes)))
      (#x36 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i32.store ,m) bytes)))
      (#x37 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.store ,m) bytes)))
      (#x38 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:f32.store ,m) bytes)))
      (#x39 (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:f64.store ,m) bytes)))
      (#x3A (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i32.store8 ,m) bytes)))
      (#x3B (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i32.store16 ,m) bytes)))
      (#x3C (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.store8 ,m) bytes)))
      (#x3D (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.store16 ,m) bytes)))
      (#x3E (b* (((mv erp m bytes)
                  (parse-memarg bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.store32 ,m) bytes)))
      (#x3F (b* (((mv erp zero bytes)
                  (take-1 bytes))
                 ((when erp) (mv erp nil nil))
                 ((when (not (= #x00 zero)))
                  (mv erp :bad-memory.size-instruction nil)))
              (mv nil `(:memory.size) bytes)))
      (#x40 (b* (((mv erp zero bytes)
                  (take-1 bytes))
                 ((when erp) (mv erp nil nil))
                 ((when (not (= #x00 zero)))
                  (mv erp :bad-memory.size-instruction nil)))
              (mv nil `(:memory.grow) bytes)))


      ;; Numeric Instructions:
      (#x41 (b* (((mv erp n bytes)
                  (parse-i32 bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i32.const ,n) bytes)))
      (#x42 (b* (((mv erp n bytes)
                  (parse-i64 bytes))
                 ((when erp) (mv erp nil nil)))
              (mv nil `(:i64.const ,n) bytes)))
      ;...
      (#x45 (mv nil '(:i32.eqz) bytes))
      (#x46 (mv nil '(:i32.eq) bytes))
      (#x47 (mv nil '(:i32.ne) bytes))
      (#x48 (mv nil '(:i32.lt_s) bytes))
      (#x49 (mv nil '(:i32.lt_u) bytes))
      (#x4A (mv nil '(:i32.gt_s) bytes))
      (#x4B (mv nil '(:i32.gt_u) bytes))
      (#x4C (mv nil '(:i32.le_s) bytes))
      (#x4D (mv nil '(:i32.le_u) bytes))
      (#x4E (mv nil '(:i32.ge_s) bytes))
      (#x4F (mv nil '(:i32.ge_u) bytes))
      (#x50 (mv nil '(:i64.eqz) bytes))
      (#x51 (mv nil '(:i64.eq) bytes))
      (#x52 (mv nil '(:i64.ne) bytes))
      (#x53 (mv nil '(:i64.lt_s) bytes))
      (#x54 (mv nil '(:i64.lt_u) bytes))
      (#x55 (mv nil '(:i64.gt_s) bytes))
      (#x56 (mv nil '(:i64.gt_u) bytes))
      (#x57 (mv nil '(:i64.le_s) bytes))
      (#x58 (mv nil '(:i64.le_u) bytes))
      (#x59 (mv nil '(:i64.ge_s) bytes))
      (#x5A (mv nil '(:i64.ge_u) bytes))

      (#x5B (mv nil '(:f32.eq) bytes))
      (#x5C (mv nil '(:f32.ne) bytes))
      (#x5D (mv nil '(:f32.lt) bytes))
      (#x5E (mv nil '(:f32.gt) bytes))
      (#x5F (mv nil '(:f32.le) bytes))
      (#x60 (mv nil '(:f32.ge) bytes))

      (#x61 (mv nil '(:f64.eq) bytes))
      (#x62 (mv nil '(:f64.ne) bytes))
      (#x63 (mv nil '(:f64.lt) bytes))
      (#x64 (mv nil '(:f64.gt) bytes))
      (#x65 (mv nil '(:f64.le) bytes))
      (#x66 (mv nil '(:f64.ge) bytes))

      (#x67 (mv nil '(:i32.clz) bytes))
      (#x68 (mv nil '(:i32.ctz) bytes))
      (#x69 (mv nil '(:i32.popcnt) bytes))
      (#x6A (mv nil '(:i32.add) bytes))
      (#x6B (mv nil '(:i32.sub) bytes))
      (#x6C (mv nil '(:i32.mul) bytes))
      (#x6D (mv nil '(:i32.div_s) bytes))
      (#x6E (mv nil '(:i32.div_u) bytes))
      (#x6F (mv nil '(:i32.rem_s) bytes))
      (#x70 (mv nil '(:i32.rem_u) bytes))
      (#x71 (mv nil '(:i32.and) bytes))
      (#x72 (mv nil '(:i32.or) bytes))
      (#x73 (mv nil '(:i32.xor) bytes))
      (#x74 (mv nil '(:i32.shl) bytes))
      (#x75 (mv nil '(:i32.shr_s) bytes))
      (#x76 (mv nil '(:i32.shr_u) bytes))
      (#x77 (mv nil '(:i32.rotl) bytes))
      (#x78 (mv nil '(:i32.rotr) bytes))

      (#x79 (mv nil '(:i64.clz) bytes))
      (#x7A (mv nil '(:i64.ctz) bytes))
      (#x7B (mv nil '(:i64.popcnt) bytes))
      (#x7C (mv nil '(:i64.add) bytes))
      (#x7D (mv nil '(:i64.sub) bytes))
      (#x7E (mv nil '(:i64.mul) bytes))
      (#x7F (mv nil '(:i64.div_s) bytes))
      (#x80 (mv nil '(:i64.div_u) bytes))
      (#x81 (mv nil '(:i64.rem_s) bytes))
      (#x82 (mv nil '(:i64.rem_u) bytes))
      (#x83 (mv nil '(:i64.and) bytes))
      (#x84 (mv nil '(:i64.or) bytes))
      (#x85 (mv nil '(:i64.xor) bytes))
      (#x86 (mv nil '(:i64.shl) bytes))
      (#x87 (mv nil '(:i64.shr_s) bytes))
      (#x88 (mv nil '(:i64.shr_u) bytes))
      (#x89 (mv nil '(:i64.rotl) bytes))
      (#x8A (mv nil '(:i64.rotr) bytes))

      (#x8B (mv nil '(:f32.abs) bytes))
      (#x8C (mv nil '(:f32.neg) bytes))
      (#x8D (mv nil '(:f32.ceil) bytes))
      (#x8E (mv nil '(:f32.floor) bytes))
      (#x8F (mv nil '(:f32.trunc) bytes))
      (#x90 (mv nil '(:f32.nearest) bytes))
      (#x91 (mv nil '(:f32.sqrt) bytes))
      (#x92 (mv nil '(:f32.add) bytes))
      (#x93 (mv nil '(:f32.sub) bytes))
      (#x94 (mv nil '(:f32.mul) bytes))
      (#x95 (mv nil '(:f32.div) bytes))
      (#x96 (mv nil '(:f32.min) bytes))
      (#x97 (mv nil '(:f32.max) bytes))
      (#x98 (mv nil '(:f32.copysign) bytes))

      (#x99 (mv nil '(:f64.abs) bytes))
      (#x9A (mv nil '(:f64.neg) bytes))
      (#x9B (mv nil '(:f64.ceil) bytes))
      (#x9C (mv nil '(:f64.floor) bytes))
      (#x9D (mv nil '(:f64.trunc) bytes))
      (#x9E (mv nil '(:f64.nearest) bytes))
      (#x9F (mv nil '(:f64.sqrt) bytes))
      (#xA0 (mv nil '(:f64.add) bytes))
      (#xA1 (mv nil '(:f64.sub) bytes))
      (#xA2 (mv nil '(:f64.mul) bytes))
      (#xA3 (mv nil '(:f64.div) bytes))
      (#xA4 (mv nil '(:f64.min) bytes))
      (#xA5 (mv nil '(:f64.max) bytes))
      (#xA6 (mv nil '(:f64.copysign) bytes))

      (otherwise (mv `(:unknown-instruction ,opcode)
                     nil
                     bytes))))

  ;; Returns (mv erp instrs terminator bytes).
  (defund parse-instrs (bytes terminators acc)
    (declare (xargs :guard (and (byte-listp bytes)
                                (byte-listp terminators)
                                (true-listp acc))
                    :measure (make-ord 1 (+ 1 (len bytes)) 0)))
    (b* (((mv erp opcode bytes)
          (take-1 bytes))
         ;; running out of bytes is an error because we expect a terminator:
         ((when erp) (mv erp nil nil nil))
         ((when (member opcode terminators))
          ;; We return the terminator so that the caller can check which one it was:
          (mv nil (reverse acc) opcode bytes))
         (bytes-before-parse-instr bytes) ; for the MBT below
         ((mv erp instr bytes)
          (parse-instr opcode bytes))
         ((when erp) (mv erp nil nil nil))
         ((when (not (mbt (<= (len bytes) (len bytes-before-parse-instr)))))
          (mv :termination-error nil nil nil)))
      (parse-instrs bytes terminators (cons instr acc)))))

(acl2::make-flag parse-instr)

(defthm-flag-parse-instr
  (defthm byte-listp-of-mv-nth-2-of-parse-instr
    (implies (byte-listp bytes)
             (byte-listp (mv-nth 2 (parse-instr opcode bytes))))
    :flag parse-instr)
  (defthm byte-listp-of-mv-nth-3-of-parse-instrs
    (implies (and (byte-listp bytes)
                  (true-listp acc))
             (byte-listp (mv-nth 3 (parse-instrs bytes terminators acc))))
    :flag parse-instrs)
  :hints (("Goal" :expand (:free (opcode) (parse-instr opcode bytes))
           :in-theory (enable parse-instr parse-instrs))))

(defthm-flag-parse-instr
  (defthm len-of-mv-nth-2-of-parse-instr
    (<= (len (mv-nth 2 (parse-instr opcode bytes)))
        (len bytes))
    :rule-classes :linear
    :flag parse-instr)
  (defthm len-of-mv-nth-2-of-parse-instrs
    (<= (len (mv-nth 3 (parse-instrs bytes terminators acc)))
        (+ (len bytes)
           (len acc)))
    :rule-classes :linear
    :flag parse-instrs)
  :hints (("Goal" :expand (:free (opcode) (parse-instr opcode bytes))
           :in-theory (enable parse-instr parse-instrs))))

(defthm-flag-parse-instr
  (defthm member-equal-of-mv-nth-2-of-parse-instrs-linear
    (implies (not (mv-nth 0 (parse-instrs bytes terminators acc))) ; no error
             (member-equal (mv-nth 2 (parse-instrs bytes terminators acc))
                           terminators))
    :flag parse-instrs)
  :skip-others t
  :hints (("Goal" :expand (:free (opcode) (parse-instr opcode bytes))
           :in-theory (enable parse-instr parse-instrs))))

(local
  (defthm bytep-when-member-equal
    (implies (and (member-equal x bytes)
                  (byte-listp bytes))
             (bytep x))))

(defthm bytep-of-mv-nth-2-of-parse-instrs-linear
  (implies (and (not (mv-nth 0 (parse-instrs bytes terminators acc))) ; no error
                (byte-listp terminators))
           (bytep (mv-nth 2 (parse-instrs bytes terminators acc))))
  :hints (("Goal" :use (member-equal-of-mv-nth-2-of-parse-instrs-linear)
           :in-theory (disable member-equal-of-mv-nth-2-of-parse-instrs-linear))))

(verify-guards parse-instr)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp expr bytes).
(defun parse-expr (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp instrs
            & ; terminator
            bytes)
        (parse-instrs bytes '(#x0B) nil))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :instrs instrs nil)
        bytes)))

;; Returns (mv erp global bytes).
(defun parse-global (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp gt bytes)
        (parse-globaltype bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp e bytes)
        (parse-expr bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :type gt (acons :expr e nil))
        bytes)))

;; Returns (mv erp globals bytes).
(defun parse-n-globals (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp global bytes)
          (parse-global bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp globals bytes)
          (parse-n-globals (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil (cons global globals) bytes))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp mut bytes).
(defun parse-exportdesc (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp byte bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp x bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil nil)))
    (case byte
      (#x00 (mv nil `(:func ,x) bytes))
      (#x01 (mv nil `(:table ,x) bytes))
      (#x02 (mv nil `(:mem ,x) bytes))
      (#x03 (mv nil `(:global ,x) bytes))
      (otherwise (mv `(:bad-exportdesc ,byte) nil nil)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp name bytes).
(defund parse-name (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp vector-length bytes)
        (parse-vector-length bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp name-bytes bytes)
        (take-n vector-length bytes))
       ((when erp) (mv erp nil nil)))
    ;; fixme: handle utf-8:
    (mv nil (acl2::bytes-to-printable-string name-bytes) bytes)))

(defthm byte-listp-of-mv-nth-2-of-parse-name
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-name bytes))))
  :hints (("Goal" :in-theory (enable parse-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp export bytes).
(defun parse-export (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp nm bytes)
        (parse-name bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp d bytes)
        (parse-exportdesc bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :name nm (acons :desc d nil))
        bytes)))

;; Returns (mv erp exports bytes).
(defun parse-n-exports (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp export bytes)
          (parse-export bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp exports bytes)
          (parse-n-exports (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil (cons export exports) bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp valtypes bytes).
(defun parse-n-valtypes (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp valtype bytes)
          (parse-valtype bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp valtypes bytes)
          (parse-n-valtypes (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil (cons valtype valtypes) bytes))))

(defthm byte-listp-of-mv-nth-2-of-parse-n-valtypes
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-n-valtypes n bytes))))
  :hints (("Goal" :in-theory (enable parse-n-valtypes))))


;; Returns (mv erp resulttype bytes).
(defun parse-resulttype (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp vector-length bytes)
        (parse-vector-length bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp valtypes bytes)
        (parse-n-valtypes vector-length bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil valtypes bytes)))

;; Returns (mv erp functype bytes).
(defun parse-functype (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp byte bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil nil))
       ((when (not (= byte #x60)))
        (mv :bad-functype nil bytes))
       ((mv erp rt1 bytes)
        (parse-resulttype bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp rt2 bytes)
        (parse-resulttype bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :parameter-type rt1 (acons :result-type rt2 nil))
        bytes)))

;; Returns (mv erp functypes bytes).
(defun parse-n-functypes (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp functype bytes)
          (parse-functype bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp functypes bytes)
          (parse-n-functypes (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil (cons functype functypes) bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp typeidxs bytes).
(defun parse-n-typeidxs (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp typeidx bytes)
          (parse-typeidx bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp typeidxs bytes)
          (parse-n-typeidxs (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil (cons typeidx typeidxs) bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp locals bytes).
(defun parse-locals (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp n bytes)
        (parse-u32 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp ty bytes) ; can't use t in Lisp
        (parse-valtype bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil (repeat n ty) bytes)))

;; Returns (mv erp localss bytes).
(defun parse-n-localss (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp locals bytes)
          (parse-locals bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp localss bytes)
          (parse-n-localss (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil
          (cons locals localss) ; todo: just do the append here?
          bytes))))

(defthm true-list-listp-of-mv-nth-1-of-parse-n-localss
  (true-list-listp (mv-nth 1 (parse-n-localss n bytes)))
  :hints (("Goal" :in-theory (enable parse-n-localss))))

(defthm byte-listp-of-mv-nth-2-of-parse-n-localss
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-n-localss n bytes))))
  :hints (("Goal" :in-theory (enable parse-n-localss))))

;; Returns (mv erp func bytes).
(defun parse-func (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp vector-length bytes)
        (parse-vector-length bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp localss bytes)
        (parse-n-localss vector-length bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp expr bytes)
        (parse-expr bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :locals (append-all localss) ; todo: check side condition
               (acons :body expr nil))
        bytes)))

;; Returns (mv erp code bytes).
(defun parse-code (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((mv erp
            & ; size
            bytes)
        (parse-u32 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp code bytes)
        (parse-func bytes))
       ((when erp) (mv erp nil nil)))
    ;; todo; check the size?
    (mv nil code bytes)))

;; Returns (mv erp codes bytes).
(defun parse-n-codes (n bytes)
  (declare (xargs :guard (and (natp n)
                              (byte-listp bytes))))
  (if (zp n)
      (mv nil nil bytes)
    (b* (((mv erp code bytes)
          (parse-code bytes))
         ((when erp) (mv erp nil nil))
         ((mv erp codes bytes)
          (parse-n-codes (+ -1 n) bytes))
         ((when erp) (mv erp nil nil)))
      (mv nil (cons code codes) bytes))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp section) where the section is the contents
(defun parse-section-aux (id bytes) ; bytes are just for this section
  (declare (xargs :guard (and (section-idp id)
                              (byte-listp bytes))))
  (case id
    (:table (b* (((mv erp vector-length bytes)
                  (parse-vector-length bytes))
                 ((when erp) (mv erp nil))
                 ((mv erp tables bytes)
                  (parse-n-tables vector-length bytes))
                 ((when erp) (mv erp nil))
                 ((when (consp bytes))
                  (mv `(:extra-bytes-in-section ,id) nil)))
              (mv nil tables)))
    (:memory (b* (((mv erp vector-length bytes)
                   (parse-vector-length bytes))
                  ((when erp) (mv erp nil))
                  ((mv erp memories bytes)
                   (parse-n-memories vector-length bytes))
                  ((when erp) (mv erp nil))
                  ((when (consp bytes))
                   (mv `(:extra-bytes-in-section ,id) nil)))
               (mv nil memories)))
    (:global (b* (((mv erp vector-length bytes)
                   (parse-vector-length bytes))
                  ((when erp) (mv erp nil))
                  ((mv erp globals bytes)
                   (parse-n-globals vector-length bytes))
                  ((when erp) (mv erp nil))
                  ((when (consp bytes))
                   (mv `(:extra-bytes-in-section ,id) nil)))
               (mv nil globals)))
    (:export (b* (((mv erp vector-length bytes)
                   (parse-vector-length bytes))
                  ((when erp) (mv erp nil))
                  ((mv erp exports bytes)
                   (parse-n-exports vector-length bytes))
                  ((when erp) (mv erp nil))
                  ((when (consp bytes))
                   (mv `(:extra-bytes-in-section ,id) nil)))
               (mv nil exports)))
    (:code (b* (((mv erp vector-length bytes)
                 (parse-vector-length bytes))
                ((when erp) (mv erp nil))
                ((mv erp codes bytes)
                 (parse-n-codes vector-length bytes))
                ((when erp) (mv erp nil))
                ((when (consp bytes))
                 (mv `(:extra-bytes-in-section ,id) nil)))
             (mv nil codes)))
    (:type (b* (((mv erp vector-length bytes)
                 (parse-vector-length bytes))
                ((when erp) (mv erp nil))
                ((mv erp functypes bytes)
                 (parse-n-functypes vector-length bytes))
                ((when erp) (mv erp nil))
                ((when (consp bytes))
                 (mv `(:extra-bytes-in-section ,id) nil)))
             (mv nil functypes)))
    (:function (b* (((mv erp vector-length bytes)
                     (parse-vector-length bytes))
                    ((when erp) (mv erp nil))
                    ((mv erp typeidxs bytes)
                     (parse-n-typeidxs vector-length bytes))
                    ((when erp) (mv erp nil))
                    ((when (consp bytes))
                     (mv `(:extra-bytes-in-section ,id) nil)))
                 (mv nil typeidxs)))
    (:custom (b* (((mv erp name bytes)
                   (parse-name bytes))
                  ((when erp) (mv erp nil)))
               (mv nil (acons :name name (acons :bytes bytes nil)))))
    (otherwise (mv :unknown-section nil))))



;; Returns (mv erp section bytes).
(defund parse-section (bytes)
  (declare (xargs :guard (byte-listp bytes)
                  :guard-hints (("Goal" :in-theory (enable acl2::lookup-equal)))))
  (b* (((mv erp n bytes)
        (take-1 bytes))
       ((when erp) (mv erp nil nil))
       (id (lookup n *section-ids*))
       ((when (not id))
        (mv (list :bad-id n) nil nil))
       ((mv erp size bytes)
        (parse-u32 bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp section-bytes bytes) ; todo: optimize?
        (take-n size bytes))
       ((when erp) (mv erp nil nil))
       ((mv erp cont)
        (parse-section-aux id section-bytes))
       ((when erp) (mv erp nil nil)))
    (mv nil
        (acons :id id (acons :contents cont nil))
        bytes)))

(defthm <-of-len-of-mv-nth-2-of-parse-section-linear
  (implies (not (mv-nth 0 (parse-section bytes))) ; no error
           (< (len (mv-nth 2 (parse-section bytes)))
              (len bytes)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable parse-section))))

(defthm byte-listp-of-mv-nth-2-of-parse-section
  (implies (byte-listp bytes)
           (byte-listp (mv-nth 2 (parse-section bytes))))
  :hints (("Goal" :in-theory (enable parse-section))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp sections bytes).
(defun parse-sections (bytes)
  (declare (xargs :guard (byte-listp bytes)
                  :measure (len bytes)))
  (if (endp bytes)
      (mv nil nil bytes)
    (b* (((mv erp section bytes)
          (parse-section bytes))
         ((when erp) (mv erp nil bytes))
         ((mv erp sections bytes)
          (parse-sections bytes))
         ((when erp) (mv erp nil bytes)))
      (mv nil (cons section sections) bytes))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp module) where MODULE is just the parsed sections.
(defun parse-module-bytes (bytes)
  (declare (xargs :guard (byte-listp bytes)))
  (b* (((when (not (len-at-least 4 bytes)))
        (mv :not-enough-bytes-for-magic nil))
       (magic (take 4 bytes))
       (bytes (nthcdr 4 bytes))
       ((when (not (equal magic (list #x00 #x61 #x73 #x6D))))
        (mv :bad-magic-number nil))
       ((when (not (len-at-least 4 bytes)))
        (mv :not-enough-bytes-for-version nil))
       (version (take 4 bytes))
       (bytes (nthcdr 4 bytes))
       ((when (not (equal version (list #x01 #x00 #x00 #x00)))) ; only version 1 is currently defined
        (mv :bad-magic-version nil))
       ((mv erp sections bytes)
        (parse-sections bytes))
       ((when erp) (mv erp nil))
       ((when (consp bytes))
        (mv :extra-bytes nil))
       ;; todo: check the side constraints
       )
    (mv nil sections)))

;; Returns (mv erp module state).
(defun parse-module (path-to-file acl2::state)
  (declare (xargs :guard (stringp path-to-file)
                  :stobjs acl2::state))
  (b* (((mv erp bytes acl2::state)
        (acl2::read-file-into-byte-list path-to-file acl2::state))
       ((when erp) (mv erp nil acl2::state))
       ((mv erp module)
        (parse-module-bytes bytes))
       ((when erp) (mv erp nil acl2::state)))
    (mv nil module acl2::state)))

;;(trace$ parse-instrs)
;;(parse-module "add.wasm" acl2::state)
;;(parse-module "if.wasm" acl2::state)
