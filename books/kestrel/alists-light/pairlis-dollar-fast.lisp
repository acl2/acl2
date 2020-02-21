; A faster version of pairlis$ when reversing the order is ok.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "kestrel/lists-light/append" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))

;; Calls to pairlis$ can be replaced with this, when the order of the pairs in
;; the alist doesn't matter (which it shouldn't if the alist is only used as an
;; alist and there are no duplicate keys).

;; Make an alist that binds the KEYS to the corresponding VALS.  This version
;; of the function is tail recursive and should be faster than pairlis$ since
;; pairlis$ reverses the alist at the end.
(defund pairlis$-fast-aux (keys vals acc)
  (declare (xargs :guard (and (true-listp keys)
                              (true-listp vals))))
  (if (endp keys)
      acc
    (pairlis$-fast-aux (rest keys)
                       (rest vals)
                       (cons (cons (first keys) (first vals))
                             acc))))

(defmacro pairlis$-fast (keys vals)
  `(pairlis$-fast-aux ,keys ,vals nil))

(defthm strip-cars-of-pairlis$-fast-aux
  (equal (strip-cars (pairlis$-fast-aux keys vals acc))
         (append (reverse keys) (strip-cars acc)))
  :hints (("Goal" :in-theory (enable append
                                     pairlis$-fast-aux))))

(defthm strip-cdrs-of-pairlis$-fast-aux
  (equal (strip-cdrs (pairlis$-fast-aux keys vals acc))
         (append (reverse (take (len keys) vals))
                 (strip-cdrs acc)))
  :hints (("Goal" :in-theory (enable append
                                     pairlis$-fast-aux))))

(defthm symbol-alistp-of-pairlis$-fast-aux
  (equal (symbol-alistp (pairlis$-fast-aux keys vals acc))
         (and (symbol-listp (true-list-fix keys))
              (symbol-alistp acc)))
  :hints (("Goal" :in-theory (enable pairlis$-fast-aux))))
