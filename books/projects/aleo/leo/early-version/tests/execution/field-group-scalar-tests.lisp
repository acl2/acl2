; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "../../definition/execution")
(include-book "../../testing/test-json2ast")

(include-book "std/testing/assert-equal" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains some tests of executing field, group, and scalar operations

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Field addition wraparound

; (/ (+ (ecurve::edwards-bls12-q) 1) 2)
; 4222230874714185212124412469390773265687949667577031913967616727958704619521


(defconst *file-field-wraparound*
  (abs-file (parse-from-string "program a.b {
                                function main() -> field {
 let x: field = 4222230874714185212124412469390773265687949667577031913967616727958704619521field; return x + x; }}")))

(assert-equal (exec-file-main *file-field-wraparound*
                              nil
                              :edwards-bls12
                              1000)
              (value-result-ok (value-field 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar addition wraparound

; (/ (+ (ecurve::edwards-bls12-r) 1) 2)
; 1055557718678546303031103117347693316419435463204204097596842623197360680192

(defconst *file-scalar-wraparound*
  (abs-file (parse-from-string "program a.b {
                                function main() -> scalar {
 let x: scalar = 1055557718678546303031103117347693316419435463204204097596842623197360680192scalar; return x + x; }}")))

(assert-equal (exec-file-main *file-scalar-wraparound*
                              nil
                              :edwards-bls12
                              1000)
              (value-result-ok (value-scalar 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Scalar multiplied by group wraparound


(defconst *group-mul-wraparound*
  (abs-file (parse-from-string "program a.b {
                                function main() -> group {
  let x: scalar = 1055557718678546303031103117347693316419435463204204097596842623197360680192scalar;
  return (x + 1scalar)*2group - 2group - 1group; }}")))

; x is (r+1)/2
; x+1 is (r+3)/2
; (x+1)*2 is r+3
; return value is r+3 - 2 - 1 = r = 0group = (0,1)group

(assert-equal (exec-file-main *group-mul-wraparound*
                              nil
                              :edwards-bls12
                              1000)
              (value-result-ok (value-group (cons 0 1))))
