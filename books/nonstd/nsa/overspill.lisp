; Copyright (C) 2015, Regents of the University of Texas
; Written by Cuong Chau and Matt Kaufmann, April/May, 2015
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See overspill-test.lisp for trivial applications.

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

; We can avoid an include-book with :dir :system, since overspill-proof is in
; this same directory.
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

(defun make-nth-calls (i var acc)

; Return the user-level term list ((nth 0 var) (nth 1 var) ... (nth i-1 var)).

  (declare (xargs :guard (and (natp i)
                              (symbolp var))))
  (cond ((zp i) acc)
        (t (let ((k (1- i)))
             (make-nth-calls k
                             var
                             (cons `(nth ,k ,var) acc))))))

(defun create-bindings (x y)
  (declare (xargs :guard (and (true-listp x)
                              (true-listp y))))
  (pairlis$ x (pairlis$ y nil)))

(defmacro overspill (pred params &key pred* witness pred-overspill)

; Params is a list of distinct variable names in one-to-one correspondence with
; the cdr of the formals of pred -- so, (pred n . params) is a well-formed call
; -- or else is a single variable.

  (let* ((atom-p
          (atom params))
         (nth-x ; list of expressions representing the parameters
          (if atom-p
              '(x)
            (make-nth-calls (len params) 'x nil)))
         (params
          (if (atom params) (list params) params))
         (pred*
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

      (defun ,pred* (n ,@params)
        (if (zp n)
            (,pred 0 ,@params)
          (and (,pred n ,@params)
               (,pred* (1- n) ,@params))))

      (defchoose ,witness (n) (,@params)
        (or (and (natp n)
                 (standardp n)
                 (not (,pred n ,@params)))
            (and (natp n)
                 (i-large n)
                 (,pred* n ,@params))))

      (defthm ,pred-overspill
        (let ((n (,witness ,@nth-x)))
          (or (and (natp n)
                   (standardp n)
                   (not (,pred n ,@nth-x)))
              (and (natp n)
                   (i-large n)
                   (implies (and (natp m)
                                 (<= m n))
                            (,pred m ,@nth-x)))))
        :hints (("Goal"
                 :by (:functional-instance
                      overspill-p-overspill
                      (overspill-p
                       (lambda (n x)
                         (,pred n ,@nth-x)))
                      (overspill-p*
                       (lambda (n x)
                         (,pred* n ,@nth-x)))
                      (overspill-p-witness
                       (lambda (x)
                         (,witness ,@nth-x))))
                 :in-theory (theory 'minimal-theory)
                 :expand ((,pred* n ,@nth-x)))
                '(:use (:instance ,witness
                                  ,@(create-bindings params nth-x))))
        :rule-classes nil)
      )))
