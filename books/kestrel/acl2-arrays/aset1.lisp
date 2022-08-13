; A lightweight book about the built-in function aset1
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2022 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable aset1))

(local (include-book "compress1"))
(local (include-book "dimensions"))
(local (include-book "default"))

(defthm dimensions-of-aset1
  (equal (dimensions array-name (aset1 array-name array n val))
         (if (eq :header n)
             (cadr (assoc-keyword :dimensions val))
           (dimensions array-name array)))
  :hints (("Goal" :in-theory (enable aset1))))

(defthm default-of-aset1
  (implies (integerp n)
           (equal (default array-name (aset1 array-name array n val))
                  (default array-name array)))
  :hints (("Goal" :in-theory (enable aset1))))
