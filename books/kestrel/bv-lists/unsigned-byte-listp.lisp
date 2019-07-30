; A lightweight book connecting unsigned-byte-listp to all-unsigned-byte-p.
;
; Copyright (C) 2019 Kestrel Institute
; For unsigned-byte-listp, see the copyright for books/std.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The BV library doesn't use this function very much.  Instead, it uses
;; all-unsigned-byte-p.  In this book, we provide some rules to connect the two
;; functions.

(include-book "all-unsigned-byte-p")

;unlike all-unsigned-byte-p, this one implies true-listp.
;also in std/typed-lists/unsigned-byte-listp.lisp
(defund unsigned-byte-listp (n x)
;  (declare (type t n x))
  (if (atom x)
      (null x)
      (and (unsigned-byte-p n (car x))
           (unsigned-byte-listp n (cdr x)))))

(verify-guards unsigned-byte-listp)

(defthmd unsigned-byte-listp-rewrite
  (equal (unsigned-byte-listp n x)
         (and (all-unsigned-byte-p n x)
              (true-listp x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))

(defthmd unsigned-byte-listp-forward
  (implies (unsigned-byte-listp n x)
           (and (all-unsigned-byte-p n x)
                (true-listp x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable unsigned-byte-listp))))
