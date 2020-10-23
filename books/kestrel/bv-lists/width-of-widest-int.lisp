; A function to return the integer, from a list, that uses the most bits
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../typed-lists-light/all-integerp")
(include-book "kestrel/typed-lists-light/all-natp" :dir :system)
(include-book "all-unsigned-byte-p")
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))

(local (in-theory (disable unsigned-byte-p)))

;;
;; width-of-widest-int
;;

;; TODO: Strengthen guard to requite that ints have at least one element?
;; TODO: Consider renaming this to match the (perhaps unfortunate) terminology
;; implicit in the name integer-length (that the number of bits in an integer
;; is its "length" rather than its "width").
(defund width-of-widest-int (ints)
  (declare (xargs :guard (all-integerp ints)))
  (if (atom ints)
      0 ;error?
    (max (integer-length (car ints))
         (width-of-widest-int (cdr ints)))))

(defthm width-of-widest-int-of-cons
  (equal (width-of-widest-int (cons a b))
         (max (integer-length a)
              (width-of-widest-int b)))
  :hints (("Goal" :in-theory (enable width-of-widest-int))))

(defthm all-unsigned-byte-p-of-width-of-widest-int
  (implies (all-natp vals)
           (all-unsigned-byte-p (width-of-widest-int vals)
                                 vals))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable all-natp all-unsigned-byte-p width-of-widest-int unsigned-byte-p-of-integer-length-gen))))
