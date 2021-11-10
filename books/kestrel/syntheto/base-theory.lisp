; Syntheto base level theory
;
; Copyright (C) 2021 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-package "SYNTHETO")

(include-book "process-toplevel")
(include-book "kestrel/arithmetic-light/top" :dir :system)

(define syndef::|max| ((syndef::|x| integerp) (syndef::|y| integerp))
  :guard (and (integerp syndef::|x|)
              (integerp syndef::|y|))
  :normalize nil
  :prepwork ((set-ignore-ok t))
  :no-function t
  :returns (syndef::|m| integerp :hyp :guard)
  (if (or (not (mbt (and (integerp syndef::|x|)
                         (integerp syndef::|y|))))
          (> syndef::|y| syndef::|x|))
      syndef::|y| syndef::|x|)
  ///
  (defret syndef::|max-ENSURES| :hyp
    :guard (and (integerp syndef::|m|))))

;; Todo: Define in syntheto 
(defthm max-less-equal
  (implies (and (integerp x)
                (integerp y)
                (or (<= n x)
                    (<= n y)))
           (<= n (syndef::|max| x y)))
  :hints (("Goal" :in-theory (enable syndef::|max|))))

(define syndef::|min| ((syndef::|x| integerp) (syndef::|y| integerp))
  :guard (and (integerp syndef::|x|)
              (integerp syndef::|y|))
  :normalize nil
  :prepwork ((set-ignore-ok t))
  :no-function t
  :returns (syndef::|m| integerp :hyp :guard)
  (if (or (not (mbt (and (integerp syndef::|x|)
                         (integerp syndef::|y|))))
          (< syndef::|y| syndef::|x|))
      syndef::|y| syndef::|x|)
  ///
  (defret syndef::|min-ENSURES| :hyp
    :guard (and (integerp syndef::|m|))))

(define syndef::|even| (syndef::|i|)
  :normalize nil
  :enabled t
  :no-function t
  :returns (syndef::|b| booleanp :hyp :guard)
  (and (integerp syndef::|i|)
       (equal (rem syndef::|i| 2) 0))
  ///
  (defret syndef::|even-ENSURES| :hyp
    :guard (and (booleanp syndef::|b|))
    :hints (("Goal" :in-theory (enable))))
  (defthm syndef::|even-IMPLIES|
    (implies (syndef::|even| syndef::|i|)
             (and (integerp syndef::|i|)))))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm even-is-evenp
  (implies (integerp x)
           (equal (syndef::|even| x)
                  (evenp x)))
  :hints (("Goal" :in-theory (enable evenp))))

(define syndef::|odd| (syndef::|i|)
  :normalize nil
  :enabled t
  :no-function t
  :returns (syndef::|b| booleanp :hyp :guard)
  (and (integerp syndef::|i|)
       (not (syndef::|even| syndef::|i|)))
  ///
  (defret syndef::|odd-ENSURES| :hyp
    :guard (and (booleanp syndef::|b|))
    :hints (("Goal" :in-theory (enable))))
  (defthm syndef::|odd-IMPLIES|
    (implies (syndef::|odd| syndef::|i|)
             (and (integerp syndef::|i|)))))

(in-theory (enable oddp))

(defthm odd-is-oddp
  (implies (integerp x)
           (equal (syndef::|odd| x)
                  (oddp x))))

(in-theory (disable syndef::|even| syndef::|odd|))

(defthm even_of_+_of_if
  (equal (syndef::|even| (+ x (if p y z)))
         (if p (syndef::|even| (+ x y))
           (syndef::|even| (+ x (if p y z))))))

(defthm odd_of_+_of_if
  (equal (syndef::|odd| (+ x (if p y z)))
         (if p (syndef::|odd| (+ x y))
           (syndef::|odd| (+ x (if p y z))))))
