; A book about the built-in function arities-okp
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(in-theory (disable arities-okp))

(defthm arities-okp-when-arities-okp-and-subsetp-equal
  (implies (and (arities-okp arities+ w)
                (subsetp-equal arities arities+))
           (arities-okp arities w))
  :hints (("Goal" :in-theory (enable arities-okp
                                     subsetp-equal))))

(defthm arities-okp-of-append
  (equal (arities-okp (append x y) w)
         (and (arities-okp x w)
              (arities-okp y w)))
  :hints (("Goal" :in-theory (enable arities-okp))))

(defthm arities-okp-of-cons
  (equal (arities-okp (cons pair alist) w)
         (and (equal (arity (car pair) w) (cdr pair))
              (logicp (car pair) w)
              (arities-okp alist w)))
  :hints (("Goal" :in-theory (enable arities-okp))))

(defthm arity-when-arities-okp
  (implies (and (arities-okp alist w)
                (assoc-eq fn alist))
           (equal (arity fn w)
                  (cdr (assoc-eq fn alist))))
  :hints (("Goal" :in-theory (enable arities-okp))))
