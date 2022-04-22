; A lightweight book about the built-in-function assoc-keyword
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable assoc-keyword))

(defthm consp-of-cdr-of-assoc-keyword
  (implies (keyword-value-listp keyword-value-list)
           (iff (consp (cdr (assoc-keyword key keyword-value-list)))
                (assoc-keyword key keyword-value-list)))
  :hints (("Goal" :in-theory (enable keyword-value-listp
                                     assoc-keyword))))

(defthm cdr-of-assoc-keyword-iff
  (implies (keyword-value-listp keyword-value-list)
           (iff (cdr (assoc-keyword key keyword-value-list))
                (assoc-keyword key keyword-value-list)))
  :hints (("Goal" :in-theory (enable keyword-value-listp
                                     assoc-keyword))))

(defthm keywordp-of-car-of-assoc-keyword
  (implies (keyword-value-listp keyword-value-list)
           (iff (keywordp (car (assoc-keyword key keyword-value-list)))
                (assoc-keyword key keyword-value-list)))
  :hints (("Goal" :in-theory (enable keyword-value-listp
                                     assoc-keyword))))

(defthm keywordp-when-assoc-keyword
  (implies (and (assoc-keyword key keyword-value-list)
                (keyword-value-listp keyword-value-list))
           (keywordp key))
  :hints (("Goal" :in-theory (enable keyword-value-listp assoc-keyword))))

;; Hung on symbolp, so disabled by default
(defthmd symbolp-when-assoc-keyword
  (implies (and (assoc-keyword key keyword-value-list)
                (keyword-value-listp keyword-value-list))
           (symbolp key))
  :hints (("Goal" :in-theory (enable keyword-value-listp assoc-keyword))))

(defthm <=-of-len-of-assoc-keyword-forward-linear
  (implies (and (assoc-keyword key keyword-value-list)
                (keyword-value-listp keyword-value-list))
           (<= 2 (len (assoc-keyword key keyword-value-list))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable keyword-value-listp assoc-keyword))))
