; Some rules about split-list-fast
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "split-list-fast")

(defthm symbol-listp-of-mv-nth-0-of-split-list-fast-aux
  (implies (and (symbol-listp acc)
                (symbol-listp lst)
                (symbol-listp tail))
           (symbol-listp (mv-nth 0 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm symbol-listp-of-mv-nth-1-of-split-list-fast-aux
  (implies (and (symbol-listp acc)
                (symbol-listp lst)
                (symbol-listp tail))
           (symbol-listp (mv-nth 1 (split-list-fast-aux lst tail acc))))
  :hints (("Goal" :in-theory (enable split-list-fast-aux))))

(defthm symbol-listp-of-mv-nth-0-of-split-list-fast
  (implies (symbol-listp lst)
           (symbol-listp (mv-nth 0 (split-list-fast lst))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable split-list-fast))))

(defthm symbol-listp-of-mv-nth-1-of-split-list-fast
  (implies (symbol-listp lst)
           (symbol-listp (mv-nth 1 (split-list-fast lst))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable split-list-fast))))
