; Rules about IF and IF-lifting
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defthm natp-of-if
  (implies (and (natp y)
                (natp z))
           (natp (if x y z))))

(defthm natp-of-if-strong
  (equal (natp (if x y z))
         (if x (natp y) (natp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integerp-of-if
  (implies (and (integerp y)
                (integerp z))
           (integerp (if x y z))))

(defthm integerp-of-if-strong
  (equal (integerp (if x y z))
         (if x (integerp y) (integerp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm booleanp-of-if
  (implies (and (booleanp y)
                (booleanp z))
           (booleanp (if x y z))))

(defthm booleanp-of-if-strong
  (equal (booleanp (if x y z))
         (if x (booleanp y) (booleanp z))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm rationalp-of-if
  (implies (and (rationalp y)
                (rationalp z))
           (rationalp (if x y z))))

(defthm rationalp-of-if-strong
  (equal (rationalp (if x y z))
         (if x (rationalp y) (rationalp z))))
