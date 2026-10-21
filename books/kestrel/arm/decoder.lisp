; A decoder for ARM32 instructions
;
; Copyright (C) 2025-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "encodings")
(local (include-book "kestrel/bv/slice" :dir :system))
(local (include-book "kestrel/alists-light/acons" :dir :system))
(local (include-book "kestrel/alists-light/symbol-alistp" :dir :system))

 ; for speed:
(local (in-theory (disable acl2::equal-constant-when-bvchop-equal-constant-false
                           acl2::bvand-type
                           symbol-alistp)))

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
                 (mnemonic (car entry))
                 (pattern (cdr entry))
                 (mandatory-bit-mask (mandatory-bit-mask pattern 31 0)) ; has a 1 everywhere the pattern has a concrete value
                 (mandatory-bits (mandatory-bits pattern 31 0)) ; has all the mandatory bits the same as in the pattern and zeros for the don't cares
                 )
            ;; this is a cond clause:
            `((equal (bvand 32 inst ,mandatory-bit-mask) ,mandatory-bits)
              (mv nil ; no error
                  ,mnemonic
                  ,(make-alist-for-fields 31 pattern)
                  )))
          (make-decoding-cases (rest alist)))))

(defun make-good-inst-cases (alist)
  (declare (xargs :guard (good-encoding-pattern-alistp alist)))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (mnemonic (car entry))
           ;; (pattern (cdr entry))
           )
      (cons `(,mnemonic (,(pack-in-package "ARM" mnemonic '-argsp) args))
            (make-good-inst-cases (rest alist))))))

(defun make-good-inst-names (alist)
  (declare (xargs :guard (good-encoding-pattern-alistp alist)))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
           (mnemonic (car entry))
           ;; (pattern (cdr entry))
           )
      (cons (pack-in-package "ARM" mnemonic '-argsp)
            (make-good-inst-names (rest alist))))))

;; Helps make the guard conjecture trivial
(local
 (defthm acl2::alistp-of-acons-type
   (implies (alistp acl2::alist)
            (alistp (acons acl2::key acl2::datum acl2::alist)))
   :rule-classes :type-prescription))

;; For speed
(local
 (defthm unsigned-byte-p-1-of-getbit
   (unsigned-byte-p 1 (getbit n x))))

(defun make-decoder (name alist)
  (declare (xargs :guard (and (symbolp name)
                              (good-encoding-pattern-alistp alist))))
  `(progn
     ;; ,@(make-instruction-arg-predicates alist)

     ;; Recognize a "good" instruction
     ;; todo: it's really the args that we are checking here
     ;; todo:  show decoder always produces a good-inst?
     (defund good-instp (mnemonic args)
       (declare (xargs :guard t))
       (and (mnemonicp mnemonic)
            (symbol-alistp args)
            (case mnemonic
              ,@(make-good-inst-cases alist)
              (otherwise nil))))

     ;; The decoder.  Given an instruction, attempt to decode it into mnemonic and args.
     ;; Returns (mv erp mnemonic args) where ARGS is an alist from field names
     ;; to their values from in the instruction (e.g., rd=14).
     (defund ,name (inst)
       (declare (xargs :guard (unsigned-byte-p 32 inst)))
       (cond
        ,@(make-decoding-cases alist)
        (t (mv :unsupported nil nil))))

     ;; Speed helper for the return-type proof:
     (local
      (defund good-decoder-resultp (res)
        (or (mv-nth 0 res)
            (good-instp (mv-nth 1 res) (mv-nth 2 res)))))

     ;; Speed helper for the return-type proof:
     (local
      (defthm good-decoder-resultp-of-if
        (equal (good-decoder-resultp (if test res1 res2))
               (if test (good-decoder-resultp res1) (good-decoder-resultp res2)))))

     ;; Speed helper for the return-type proof:
     (local
      (defthm good-decoder-resultp-of-decoder
        (good-decoder-resultp (,name inst))
        :hints (("Goal" :in-theory (enable ,name good-instp good-decoder-resultp ,@(make-good-inst-names alist))))))

     (defthm ,(pack-in-package "ARM" name '-return-type)
       (implies (not (mv-nth 0 (,name inst)))
                (good-instp (mv-nth 1 (,name inst))
                            (mv-nth 2 (,name inst))))
       ;; :hints (("Goal" :in-theory (enable ,name good-instp ,@(make-good-inst-names alist))))
       :hints (("Goal" :use good-decoder-resultp-of-decoder
                       :in-theory (e/d (good-decoder-resultp)
                                       (good-decoder-resultp-of-decoder)))))))

;; This makes a decoder called arm32-decode that decodes a USB32 into an
;; instruction (any of the instructions in the *patterns*):
(make-event (make-decoder 'arm32-decode *desugared-patterns*))

(defthm alistp-of-mv-nth-2-of-arm32-decode
  (alistp (mv-nth 2 (arm32-decode instr)))
  :hints (("Goal" :in-theory '(arm32-decode acl2::alistp-of-acons (:e alistp)))))
