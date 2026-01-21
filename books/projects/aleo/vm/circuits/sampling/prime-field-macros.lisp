; AleoVM Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ALEOVM")

(include-book "projects/bls12-377-curves/primes/bls12-377-prime" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "std/util/defmacro-plus" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

;; Some more books not needed for the macros but useful for books that need
;; the macros:
(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/fty/nati" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This book should be moved.

(defxdoc+ prime-field-macros
  :parents (circuits)
  :short "Macros that hide the prime field modulus for brevity."
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ eprime ()
  :short "The prime of the Edwards-BLS12 prime field."
  '(primes::bls12-377-scalar-field-prime))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ efep (x)
  :short "Checks if @('x') is an Edwards-BLS12 field element."
  ;; The bls12-377 scalar field prime is the same as the
  ;; Edwards-BLS12 base field prime.
  `(pfield::fep ,x (primes::bls12-377-scalar-field-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ efe-listp (xs)
  :short "Checks if all the elements of the list @('xs')
          are Edwards-BLS12 field elements."
  `(pfield::fe-listp ,xs (primes::bls12-377-scalar-field-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ eadd (x y)
  :short "Binary addition in the Edwards-BLS12 prime field."
  `(pfield::add ,x ,y (primes::bls12-377-scalar-field-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ eaddall (&rest rst)
  :short "@($n$)-ary addition in the Edwards-BLS12 prime field."
  (if rst
      (if (cdr rst)
          (xxxjoin 'eadd rst)
        (cons 'eadd
              (cons 0 (cons (car rst) nil))))
    0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ eneg (x)
  :short "Negation in the Edwards-BLS12 prime field."
  `(pfield::neg ,x (primes::bls12-377-scalar-field-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ esub (x y)
  :short "Subtraction in the Edwards-BLS12 prime field."
  `(pfield::sub ,x ,y (primes::bls12-377-scalar-field-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ emul (x y)
  :short "Binary multiplication in the Edwards-BLS12 prime field."
  `(pfield::mul ,x ,y (primes::bls12-377-scalar-field-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ emulall (&rest rst)
  :short
  "@($n$)-ary multiplication in the Edwards-BLS12 prime field."
  (if rst
      (if (cdr rst)
          (xxxjoin 'emul rst)
        (cons 'emul
              (cons 1 (cons (car rst) nil))))
    1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ einv (x)
  :short "Inverse in the Edwards-BLS12 prime field."
  `(pfield::inv ,x (primes::bls12-377-scalar-field-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ ediv (x y)
  :short "Division in the Edwards-BLS12 prime field."
  `(pfield::div ,x ,y (primes::bls12-377-scalar-field-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ eminus1 ()
  :short "-1 in the Edwards-BLS12 prime field."
  '(pfield::minus1 (primes::bls12-377-scalar-field-prime)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ wvar (i)
  :short "R1CS private variable symbol."
  `(packn-pos (list "w" ,i) (pkg-witness "R1CS")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ xvar (i)
  :short "R1CS public variable symbol."
  `(packn-pos (list "x" ,i) (pkg-witness "R1CS")))
