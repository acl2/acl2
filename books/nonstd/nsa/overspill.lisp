; Copyright (C) 2015, Regents of the University of Texas
; Written by Matt Kaufmann in consultation with Cuong Chau, April, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See overspill-test.lisp for a trivial application.

; cert_param: (uses-acl2r)

(in-package "ACL2")

; Formalization of the overspill property in ACL2(r)

; In order to apply overspill-p-overspill (at the end, below) to one's own
; predicate, (p0 i x), I expect the following approach to suffice.  First,
; define p0* and p0-witness in analogy to overspill-p* and overspill-p-witness
; below, respectively.  Second, functionally instantiate overspill-p-overspill.
; Now, suppose that you prove a theorem of the form:

;   (implies (and (hyps x) (natp i) (standardp i))
;            (p0 i x))

; Then you can easily conclude the following from your functional instance of
; overspill-p-overspill, saying that p0 "overspills" to some nonstandard n:

;   (implies (hyps x)
;            (let ((n (overspill-p-witness x)))
;              (and (natp n)
;                   (overspill-p n x)
;                   (i-large n)))

(local (include-book "overspill-proof"))

(set-enforce-redundancy t)

(defstub overspill-p (n x) t)

(defun overspill-p* (n x)
  (if (zp n)
      (overspill-p 0 x)
    (and (overspill-p n x)
         (overspill-p* (1- n) x))))

(defchoose overspill-p-witness (n) (x)
  (or (and (natp n)
           (standardp n)
           (not (overspill-p n x)))
      (and (natp n)
           (i-large n)
           (overspill-p* n x))))

(defthm overspill-p-overspill
  (let ((n (overspill-p-witness x)))
    (or (and (natp n)
             (standardp n)
             (not (overspill-p n x)))
        (and (natp n)
             (i-large n)
             (implies (and (natp m)
                           (<= m n))
                      (overspill-p m x)))))
  :rule-classes nil)

(set-enforce-redundancy nil)

; Now we introduce a macro that automates the application of the overspill
; principle.  I suspect that with more work we could make the witness
; classical, but it's not at all clear to me that there is value in doing so.
; I actually think that it's best for the generic witness function,
; overspill-p-witness, not to be classical, to avoid needlessly restricting the
; set of legal functional substitutions.

(defmacro overspill (pred &key pred* witness pred-overspill)
  (let ((pred*
         (or pred*
             (intern-in-package-of-symbol
              (concatenate 'string (symbol-name pred) "*")
              pred)))
        (witness
         (or witness
             (intern-in-package-of-symbol
              (concatenate 'string (symbol-name pred) "-WITNESS")
              pred)))
        (pred-overspill
         (or pred-overspill
             (intern-in-package-of-symbol
              (concatenate 'string (symbol-name pred) "-OVERSPILL")
              pred))))
    `(encapsulate
      ()

      (local (include-book ; linebreak defeats bogus cert.pl dependency
              "nonstd/nsa/overspill" :dir :system))

      (defun ,pred* (n x)
        (if (zp n)
            (,pred 0 x)
          (and (,pred n x)
               (,pred* (1- n) x))))

      (defchoose ,witness (n) (x)
        (or (and (natp n)
                 (standardp n)
                 (not (,pred n x)))
            (and (natp n)
                 (i-large n)
                 (,pred* n x))))

      (defthm ,pred-overspill
        (let ((n (,witness x)))
          (or (and (natp n)
                   (standardp n)
                   (not (,pred n x)))
              (and (natp n)
                   (i-large n)
                   (implies (and (natp m)
                                 (<= m n))
                            (,pred m x)))))
        :hints (("Goal"
                 :by (:functional-instance
                      overspill-p-overspill
                      (overspill-p ,pred)
                      (overspill-p* ,pred*)
                      (overspill-p-witness ,witness))
                 :in-theory (theory 'minimal-theory)
                 :expand ((,pred* n x)))
                '(:use ,witness))
        :rule-classes nil)
      )))
