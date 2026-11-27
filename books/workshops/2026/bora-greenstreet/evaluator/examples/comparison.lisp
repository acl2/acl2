; Erlang in ACL2
;
; Copyright (C) Kuter Bora.
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Kuter Bora
; Contributing Author: Mark Greenstreet

(in-package "ACL2")
(include-book "util")

; This file contains some test for Erlang comparison operations
;
; TODO: add tests for fun and pid

(assert-equal (erl-compare '(:integer 9) '(:integer 3)) 1)

(assert-equal (erl-compare '(:integer 3) '(:integer 3)) 0)
(assert-equal (erl-compare '(:integer 1) '(:integer 3)) -1)


(assert-equal (erl-compare '(:atom z) '(:atom foo)) 1)
(assert-equal (erl-compare '(:atom foo) '(:atom foo)) 0)
(assert-equal (erl-compare '(:atom bar) '(:atom foo)) -1)

(assert-equal (erl-compare '(:integer 100) '(:atom foo)) -1)
(assert-equal (erl-compare '(:integer 100) '(:tuple nil)) -1)
(assert-equal (erl-compare '(:tuple nil) '(:cons nil)) -1)

(assert-equal (erl-compare '(:tuple ((:integer 1))) '(:tuple ((:integer 0)))) 1)
(assert-equal (erl-compare '(:tuple ((:integer 1))) '(:tuple ((:integer 1)))) 0)
(assert-equal (erl-compare '(:tuple ((:integer 1))) '(:tuple ((:integer 2)))) -1)
(assert-equal (erl-compare '(:tuple ((:integer 1) (:integer 2))) 
                           '(:tuple ((:integer 1) (:integer 1)))) 
              1)
(assert-equal (erl-compare '(:tuple ((:integer 2))) 
                           '(:tuple ((:integer 1) (:integer 1)))) 
              -1)

(assert-equal (erl-compare '(:cons ((:integer 1))) '(:cons ((:integer 0)))) 1)
(assert-equal (erl-compare '(:cons ((:integer 1))) '(:cons ((:integer 1)))) 0)
(assert-equal (erl-compare '(:cons ((:integer 1))) '(:cons ((:integer 2)))) -1)
(assert-equal (erl-compare '(:cons ((:integer 1) (:integer 2))) 
                           '(:cons ((:integer 1) (:integer 1)))) 
              1)
(assert-equal (erl-compare '(:cons ((:integer 2))) 
                           '(:cons ((:integer 1) (:integer 1)))) 
              1)