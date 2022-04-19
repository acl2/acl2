; A lightweight book about the built-in function keyword-value-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;todo: strengthen (if the length of x is even)
(defthm keyword-value-listp-of-append
  (implies (and (keyword-value-listp x)
                (keyword-value-listp y))
           (keyword-value-listp (append x y)))
  :hints (("Goal" :in-theory (enable keyword-value-listp append))))

;todo: strengthen
(defthm keyword-value-listp-of-cons-of-cons
  (implies (keyword-value-listp keyword-value-list)
           (equal (keyword-value-listp (cons k (cons v keyword-value-list)))
                  (keywordp k)))
  :hints (("Goal" :in-theory (enable keyword-value-listp))))

(defthm keyword-value-listp-of-assoc-keyword
  (implies (keyword-value-listp keyword-value-list)
           (keyword-value-listp (assoc-keyword key keyword-value-list))))
