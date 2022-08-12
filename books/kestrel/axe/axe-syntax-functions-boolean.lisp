; Boolean-related syntactic tests
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "dag-arrays")

;; This machinery should only be used heuristically, so soundness should not
;; depend on it.  Thus, we can list functions as syntactically boolean without
;; bringing their definitions into this book.

(defconst *syntactically-boolean-fns*
  '(not
    equal
    bvlt
    boolif          ;new
    booland boolor boolxor
    bool-fix$inline ;new
    memberp
    unsigned-byte-p natp integerp rationalp acl2-numberp consp booleanp
    true-listp ;new
    iff        ;newer
    <
    sbvlt bvle sbvle ; these may often be rewritten to bvlt
    unsigned-byte-p-forced
    all-unsigned-byte-p items-have-len all-true-listp all-all-unsigned-byte-p
    prefixp         ;new
    set::in ; maybe drop?
    ))

;TODO: Would like to make this sensitive to the :known-booleans table, but that would require passing in wrld here, which axe-syntaxp doesn't yet support
(defund syntactic-booleanp (nodenum-or-quotep dag-array)
  (declare (xargs :guard (or (myquotep nodenum-or-quotep)
                             (and (natp nodenum-or-quotep)
                                  (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum-or-quotep))))))
  (if (quotep nodenum-or-quotep)
      (booleanp (unquote nodenum-or-quotep))
    (let ((expr (aref1 'dag-array dag-array nodenum-or-quotep)))
      (and (consp expr)
           (member-eq (ffn-symb expr) *syntactically-boolean-fns*)))))
