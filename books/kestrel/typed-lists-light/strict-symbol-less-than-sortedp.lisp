; A lightweight book about the built-in function strict-symbol<-sortedp
;
; Copyright (C) 2023-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/reverse-list" :dir :system))
;(local (include-book "symbol-listp"))

(in-theory (disable strict-symbol<-sortedp))

(defthm strict-symbol<-sortedp-of-append
  (implies (and (true-listp l1)
                (true-listp l2))
           (equal (strict-symbol<-sortedp (append l1 l2))
                  (and (strict-symbol<-sortedp l1)
                       (strict-symbol<-sortedp l2)
                       (implies (and (consp l1) (consp l2))
                                (symbol< (car (last l1))
                                         (car l2))))))
  :hints (("Goal" :in-theory (enable strict-symbol<-sortedp append))))

(defthm strict-symbol<-sortedp-of-revappend
  (implies (and (symbol-listp l1)
                (symbol-listp l2))
           (equal (strict-symbol<-sortedp (revappend l1 l2))
                  (and (strict-symbol<-sortedp (reverse l1))
                       (strict-symbol<-sortedp l2)
                       (implies (and (consp l1) (consp l2))
                                (symbol< (car l1)
                                         (car l2))))))
  :hints (("Goal" :in-theory (enable strict-symbol<-sortedp reverse-list))))

(defthm strict-symbol<-sortedp-when-not-consp
  (implies (not (consp l))
           (strict-symbol<-sortedp l))
  :hints (("Goal" :in-theory (enable strict-symbol<-sortedp))))

(defthm strict-symbol<-sortedp-when-not-consp-of-cdr
  (implies (and (not (consp (cdr l)))
                (true-listp l) ; because strict-symbol<-sortedp tests for null
                )
           (strict-symbol<-sortedp l))
  :hints (("Goal" :in-theory (enable strict-symbol<-sortedp))))
