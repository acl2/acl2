; A lightweight book about the built-in function evenp
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also even-and-oddp.lisp.  TODO: move some of that material here.

(local (include-book "expt"))
(local (include-book "times"))
(local (include-book "mod"))
(local (include-book "mod-and-expt"))

(in-theory (disable evenp))

(defthm evenp-of-expt2
  (implies (natp m)
           (equal (evenp (expt 2 m))
                  (not (equal m 0))))
  :hints (("Goal" :in-theory (enable evenp expt))))

(defthmd evenp-becomes-equal-of-0-and-mod
  (implies (integerp x)
           (equal (evenp x)
                  (equal 0 (mod x 2))))
  :hints (("Goal" :in-theory (enable evenp
                                     integerp-of-*-of-/-becomes-equal-of-0-and-mod))))

(defthm evenp-of-mod-of-expt-of-2
  (implies (and (posp n) ;gen?
                (integerp x))
           (equal (evenp (mod x (expt 2 n)))
                  (evenp x)))
  :hints (("Goal" :in-theory (enable evenp-becomes-equal-of-0-and-mod))))
