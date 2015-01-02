; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "ACL2")

(include-book "ihs/ihs-lemmas" :dir :system)
(local (include-book "arithmetic")) ;bzo this breaks stuff when loghead is enabled in this book.

;(include-book "loghead")
;(include-book "logtail")

(in-theory (disable logapp))

(in-theory (disable (:TYPE-PRESCRIPTION LOGAPP))) ;we have logapp-type

(defthm logapp-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logapp size i j)
                  (ash j (nfix size))))
  :hints (("Goal" :in-theory (e/d (ash logapp) ()))))

(defthm logapp-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logapp size i j)
                  (loghead size i)))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm logapp-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (logapp size i j)
                  (ifix j)))
  :hints (("Goal" :in-theory (enable logext
                                     LOGAPP))))

(defthm logapp-when-size-is-negative
  (implies (< size 0)
           (equal (logapp size i j)
                  (ifix j)))
  :hints (("Goal" :in-theory (enable logext
                                     LOGAPP))))


(defthm my-logapp-<-0
  (equal (< (logapp size i j) 0)
         (< (ifix j) 0))
  :hints (("Goal" :use (:instance logapp-<-0 (i (ifix i)))
           :in-theory (disable logapp-<-0))))

(in-theory (disable LOGAPP-<-0))

(defthm logapp-non-negative-type-prescription
  (implies (<= 0 j)
           (<= 0 (logapp size i j)))
  :rule-classes :type-prescription)

(defthm logapp-negative-type-prescription
  (implies (and (< j 0)
                (integerp j))
           (< (logapp size i j) 0))
  :rule-classes :type-prescription)

(defthm logapp-non-negative-linear
  (implies (<= 0 j)
           (<= 0 (logapp size i j)))
  :rule-classes :linear)

(defthm logapp-negative-linear
  (implies (and (< j 0)
                (integerp j))
           (< (logapp size i j) 0))
  :rule-classes :linear)



;generalize?
(defthm logapp-of-logapp-with-same-size
  (equal (logapp size (logapp size i j1) j2)
         (logapp size i j2))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logapp))))

(defthm logapp-0-part-2-better
  (equal (logapp size 0 j)
         (ash j (nfix size)) ;(* (ifix i) (expt 2 (nfix size)))
         )
  :hints (("Goal" :in-theory (enable logapp ash))))

(defthm logapp-0-part-1-better
  (equal (logapp size i 0)
         (loghead size i))
  :hints (("Goal" :in-theory (enable logapp))))


(defthm logapp-0-part-3-better
  (equal (logapp 0 i j)
         (ifix j)
         )
  :hints (("Goal" :in-theory (enable logapp)))
  )

(in-theory (disable logapp-0))

(defthm evenp-of-logapp
  (equal (evenp (logapp size a b))
         (if (not (zp size))
             (evenp (ifix a))
           (evenp (ifix b))))
  :hints (("Goal" :in-theory (enable logapp))))

;; (defthm logcdr-logapp
;;   (implies (and (integerp x)
;;                 (integerp y)
;;                 (integerp n)
;;                 (< 0 n)
;;                 )
;;            (equal (LOGCDR (LOGAPP n x y))
;;                   (LOGAPP (+ -1 n) (logcdr x) y)))
;;   :hints (("Goal" :in-theory (enable logapp))))


(defthmd ash-as-logapp
  (implies (<= 0 n)
           (equal (ash x n)
                  (logapp n 0 x)))
  :hints (("goal" :in-theory (enable logapp ash))))

(theory-invariant (incompatible (:rewrite ash-as-logapp)
                                (:rewrite logapp-0-part-2-better)))