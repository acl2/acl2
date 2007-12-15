(value :q)
(setq si::*multiply-stacks* 2)

(in-package "ACL2")

; In each case, we include the necessary books (presumably because at
; least something needs to be included in order to provide the
; necessary packages), then we certify a book, then we undo back to
; the start, avoiding all queries by using :u.

; First, we define the POWERLISTS package.  All the books need it.

(ld "defpkg.lisp")

; We start out with the basic axioms and theorems about powerlists

(certify-book "algebra" 4)
:u

; This proves some basic properties about powerlists (mostly examples from
; Misra's TOPLAS paper)

(certify-book "simple" 4)
:u

; This proves the correctness of a gray-code sequence generator

(certify-book "gray-code" 4)
:u

; This gives the specification for a sorting routine

(certify-book "sort" 4)
:u

; This proves the correctness of merge sorting

(certify-book "merge-sort" 4)
:u

; This proves the correctness of batcher sorting

(certify-book "batcher-sort" 4)
:u

; This proves the correctness of bitonic sorting

(certify-book "bitonic-sort" 4)
:u

; This proves the correctness of two fast prefix sums computations, including
; the one dut to Ladner and Fischer.

(certify-book "prefix-sum" 4)
:u

; This proves the correctness of a fast (ladner-fischer based) carry-lookahead
; adder

(certify-book "cla-adder" 4)
:u

; Finally, we retract even the definition of the POWERLISTS package

:u :u :u :u
