; A lightweight book about the built-in function string-listp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;dup
(defthm string-listp-of-append
  ;; [Jared] changed from having a true-listp hyp to list-fixing a in the
  ;; conclusion, for compatibility with std.
  (equal (string-listp (append a b))
         (and (string-listp (true-list-fix a))
              (string-listp b)))
  :hints (("Goal" :in-theory (enable STRING-LISTP append))))

;; (defthm string-listp-of-append
;;   (implies (and (string-listp x)
;;                 (string-listp y))
;;            (string-listp (append x y))))
