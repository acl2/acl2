; Some utilities related to read-string
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/io/read-string" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

;; Returns (mv erp item state).
(defund read-string-as-single-item (string state)
  (declare (xargs :guard (stringp string)
                  :stobjs state))
  (mv-let (erp objects state)
    (read-string string)
    (if erp
        (mv erp nil state)
      (if (not (consp objects))
          (mv :string-parsed-to-no-objects nil state)
        (if (not (null (cdr objects)))
            (mv :string-parsed-to-more-than-one-object nil state)
          (mv nil (first objects) state))))))

;; Returns (mv erp sym state).
(defund read-string-as-single-symbol (string state)
  (declare (xargs :guard (stringp string)
                  :stobjs state))
  (mv-let (erp item state)
    (read-string-as-single-item string state)
    (if erp
        (mv erp nil state)
      (if (not (symbolp item))
          (mv :string-parsed-to-a-non-symbol nil state)
        (mv nil item state)))))

(defthm symbolp-of-mv-nth-1-of-read-string-as-single-symbol
  (symbolp (mv-nth 1 (read-string-as-single-symbol string state)))
  :hints (("Goal" :in-theory (enable read-string-as-single-symbol))))

;; Returns (mv erp symbols state).
;; Each string must parse to a single symbol.
(defund read-strings-as-single-symbols (strings acc state)
  (declare (xargs :guard (and (string-listp strings)
                              (true-listp acc))
                  :stobjs state))
  (if (endp strings)
      (mv nil (reverse acc) state)
    (mv-let (erp symbol state)
      (read-string-as-single-symbol (first strings) state)
      (if erp
          (mv erp nil state)
        (read-strings-as-single-symbols (rest strings)
                                        (cons symbol acc)
                                        state)))))

(defthm true-listp-of-mv-nth-1-of-read-strings-as-single-symbols
  (implies (true-listp acc)
           (true-listp (mv-nth 1 (read-strings-as-single-symbols strings acc state))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable read-strings-as-single-symbols))))

(defthm symbol-listp-of-mv-nth-1-of-read-strings-as-single-symbols
  (implies (symbol-listp acc)
           (symbol-listp (mv-nth 1 (read-strings-as-single-symbols strings acc state))))
  :hints (("Goal" :in-theory (enable read-strings-as-single-symbols))))
