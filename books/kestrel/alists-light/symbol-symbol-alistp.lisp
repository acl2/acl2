; A lightweight book about alists whose keys and values are all symbols
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "symbol-symbol-alistp-def")

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

(defthm symbol-symbol-alistp-of-cons-of-cons
  (equal (symbol-symbol-alistp (cons (cons key val) x))
         (and (symbolp key)
              (symbolp val)
              (symbol-symbol-alistp x)))
  :hints (("Goal" :in-theory (enable symbol-symbol-alistp))))

(defthm symbolp-of-cdr-of-assoc-equal-when-symbol-symbol-alistp
  (implies (symbol-symbol-alistp x)
           (symbolp (cdr (assoc-equal key x))))
  :hints (("Goal" :in-theory (enable symbol-symbol-alistp))))
