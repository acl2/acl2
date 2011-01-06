;;;***************************************************************
;;;An ACL2 Library of Floating Point Arithmetic

;;;David M. Russinoff
;;;Advanced Micro Devices, Inc.
;;;June, 2001
;;;***************************************************************

;This book is a modified version of support/top.  BOZO clean this up.

(in-package "ACL2")

(include-book "bits")
(include-book "bitn")
(include-book "cat")
(include-book "bvecp")
;(include-book "ash")
;(include-book "decode")
;(include-book "encode")
(include-book "mulcat")
;(include-book "shft")
;(include-book "all-ones")
;(include-book "merge")  ;a mix of lemmas.  eric is sorting these out into appropriate books
                        ;but some lemmas really do mix several functions
(include-book "logior1")
(include-book "setbits")
(include-book "setbitn")

;(include-book "float") ;theorems about floating point numbers (factorization into sgn, sig, and expo;
;exactness)
;Eric might want to sort these out into books call sig.lisp, exactp,list, etc.

;floating-point representations:
(include-book "bias")
(include-book "ereps")
;(include-book "ireps")

;built-in logical operators:
;(include-book "logeqv")
;(include-book "logorc1")
;(include-book "lognot")
;(include-book "logand")
;(include-book "logior")
;(include-book "logxor")

;(include-book "log") ;theorems mixing logical operators with bits and bitn, etc.  some junk in here to sort
  ;out?
  ;figure out the difference between this and merge?

;new logical operators:
(include-book "lnot")
(include-book "land")
(include-book "lior")
(include-book "lxor")
(include-book "lextra")

;(include-book "logs") ;other "logical" operators

;floating-point rounding:
(include-book "trunc")
(include-book "away")
(include-book "near")
;(include-book "near+")
;(include-book "oddr")
;(include-book "sticky")
;(include-book "rnd")
;(include-book "drnd")

(include-book "bits-trunc") ;theorems about how we implement trunc rounding...

;theorems about circuits for addition
;(include-book "add3") ;theorems about how we implement addition of (2 or) 3 bit vectors
;(include-book "lop1") ;leading-one prediction
;(include-book "lop2") ;leading-one prediction
;(include-book "lop3") ;leading-one prediction
(include-book "stick") ;sticky-bit computation?

(include-book "sumbits") ;help for reducing equality of bit vectors to equality
                         ;of respective bits

;helpers
;(include-book "bvecp-helpers")
;(include-book "model-helpers") ; do we use this?
;(include-book "rom-helpers")
;(include-book "simple-loop-helpers")
;BOZO consider moving lib/simplify-model-helpers to support/ of (better yet), move all the helpers books to lib/
