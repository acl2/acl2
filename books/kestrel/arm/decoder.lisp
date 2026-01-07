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

     (defthm ,(pack-in-package "ARM" name '-return-type)
       (implies (not (mv-nth 0 (arm32-decode inst)))
                (good-instp (mv-nth 1 (arm32-decode inst))
                            (mv-nth 2 (arm32-decode inst))))
       :hints (("Goal" :in-theory (enable ,name good-instp ,@(make-good-inst-names alist)))))))

;; This makes a decoder called arm32-decode that decodes a USB32 into an
;; instruction (any of the instructions in the *patterns*):
(make-event (make-decoder 'arm32-decode *desugared-patterns*))
