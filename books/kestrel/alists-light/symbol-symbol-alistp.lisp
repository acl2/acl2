; A lightweight book about alists whose keys and values are all symbols
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; From including std/typed-alists/symbol-symbol-alistp.lisp
(defund symbol-symbol-alistp (x)
  (declare (xargs :guard t
                  :normalize nil))
  (if (consp x)
      (and (consp (car x))
           (symbolp (caar x))
           (symbolp (cdar x))
           (symbol-symbol-alistp (cdr x)))
    (null x)))

(defthm symbol-symbol-alistp-forward-to-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-alistp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-symbol-alistp))))

;; Could disable if we forward-chain from symbol-alistp to alistp.
(defthm symbol-symbol-alistp-forward-to-alistp
  (implies (symbol-symbol-alistp x)
           (alistp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable symbol-symbol-alistp))))

;; Disabled because it introduces reasoning about symbol-symbol-alistp out of nowhere.
(defthmd symbol-alistp-when-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbol-alistp x))
  :hints (("Goal" :in-theory (enable symbol-symbol-alistp))))
