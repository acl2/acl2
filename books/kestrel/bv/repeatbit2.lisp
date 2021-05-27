; More theorems about repeatbit
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "repeatbit")
(include-book "bvchop")
(include-book "logtail")
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))

(defthm bvchop-of-repeatbit
  (implies (and (<= n size)
                (integerp n)
                (integerp size))
           (equal (bvchop n (repeatbit size bit))
                  (repeatbit n bit)))
  :hints (("Goal" :in-theory (enable repeatbit))))

(defthm logtail-of-repeatbit
  (implies (and (<= n size)
                (natp n)
                (integerp size))
           (equal (logtail n (repeatbit size bit))
                  (repeatbit (- size n) bit)))
  :hints (("Goal" :in-theory (enable repeatbit logtail
                                     expt-of-+))))
