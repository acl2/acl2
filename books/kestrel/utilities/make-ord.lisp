; A lightweight book about the built-in function make-ord.
;
; Copyright (C) 2019-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable make-ord))

(defthm o<-of-make-ord-and-make-ord
  (implies (and (natp x1)
                (natp y1)
                (natp x2)
                (natp y2))
           (equal (o< (make-ord 1 x1 y1) (make-ord 1 x2 y2))
                  (or (< x1 x2)
                      (and (equal x1 x2)
                           (< y1 y2)))))
  :hints (("Goal" :in-theory (enable make-ord))))

(defthm o-p-of-make-ord
  (equal (o-p (make-ord 1 x y))
         (and (posp x)
              (natp y)))
  :hints (("Goal" :in-theory (enable make-ord))))
