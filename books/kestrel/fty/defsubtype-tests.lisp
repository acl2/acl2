; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2-USER")

(include-book "defsubtype")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Tests of defsubtype

(fty::defsubtype positive-even
  :supertype acl2::pos  ;; I'm surprised POS isn't in the ACL2-USER package
  :restriction (lambda (x) (and (integerp x) (evenp x)))
  :fix-value 2)

(assert-event (and (positive-even-p 4)
                   (not (positive-even-p 3))
                   (not (positive-even-p 0))
                   (not (positive-even-p -4))
                   (not (positive-even-p :a))
                   (not (positive-even-p nil))
                   (not (positive-even-p '(2 . 4)))))

(defthm check-positive-even-fix
  (or (positive-even-p x)
      (equal (positive-even-fix x) 2))
  :hints (("Goal" :in-theory (enable positive-even-fix))))

;; Define a list of positive-even values
(fty::deflist pos-even-list :elt-type positive-even :true-listp t)

(assert-event (and (pos-even-list-p '(8 12 4 2))
                   (not (pos-even-list-p '(8 11 4 2)))
                   (not (pos-even-list-p '(8 12 4 . 2)))))
