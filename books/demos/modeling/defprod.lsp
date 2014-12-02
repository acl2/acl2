; FTY::defprod Example
; Copyright (C) 2014, Oracle and/or its affiliates. All rights reserved.
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: David L. Rager <david.rager@oracle.com>

(in-package "ACL2")

; WARNING: This file is a work in progress.  Hopefully at some point it will
; suffice as a nice working example for defprod's dependent types feature, but
; as of December 2015, it's broken.  It is currently intended to be "ld"'d into
; a system, not certified or included as a book.

(include-book "tools/bstar" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/top" :dir :system)

(defmacro maybe-skip-expensive-proof (event)
  `(make-event
    (if (table-alist 'maybe-skip-expensive-proofs (w state))
        '(skip-proofs ,event)
      ',event)))

(local (table maybe-skip-expensive-proofs 1 t))

(defxdoc shifting-fifo-model
  :short "The start of a FIFO model that looks like a shifting-fifo in its
          implementation")

(local (set-default-parents shifting-fifo-model))

(define unsigned4b-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 4 x))

(defun unsigned4b-p-fix (x)
  (if (unsigned4b-p x)
      x
    0))

(fty::deffixtype unsigned4b-p
  :pred unsigned4b-p
  :fix unsigned4b-p-fix
  :equiv equal)

(define unsigned8b-p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 8 x))

(defun unsigned8b-p-fix (x)
  (if (unsigned8b-p x)
      x
    0))

(fty::deffixtype unsigned8b-p
  :pred unsigned8b-p
  :fix unsigned8b-p-fix
  :equiv equal)

(fty::deffixtype bitp
  :pred bitp
  :fix bfix
  :equiv equal)

(define boolean-fix (x)
  (if (booleanp x) x nil))

(fty::deffixtype boolean
                 :fix boolean-fix
                 :pred booleanp
                 :equiv equal)
(in-theory (enable boolean-fix))

(fty::defprod data-address-valid
  ((data unsigned8b-p)
   (address unsigned4b-p)
   (valid booleanp :reqfix (if (booleanp valid) valid nil))))

(defval *default-invalid-data-address*
  :short "Default values for invalid address and associated data"
  (data-address-valid 0 0 nil))

(define match-address
  ((buffer data-address-valid-p)
   (in data-address-valid-p))
  :returns (retval booleanp :rule-classes :type-prescription)
  (b* (((data-address-valid buffer))
       ((data-address-valid in)))
    (and buffer.valid in.valid
         (equal buffer.address in.address))))

(defrule match-of-default-is-always-nil
; For subgoal 23.9 in one of the following thms, but it's not a horrible lemma
; to have in general.
  (equal (MATCH-ADDRESS *default-invalid-data-address* xxx)
         nil)
  :enable match-address)

(defrule match-of-default-is-always-nil-2
  (equal (MATCH-ADDRESS xxx *default-invalid-data-address* )
         nil)
  :enable match-address)

(defrule match-iff-match
  (equal (match-address x y)
         (match-address y x))
  :enable match-address)

(define buffers-req
  ((b1 data-address-valid-p)
   (b2 data-address-valid-p)
   (b3 data-address-valid-p)
   (b4 data-address-valid-p))
  (and (not (match-address b1 b2))
       (not (match-address b1 b3))
       (not (match-address b1 b4))
       (not (match-address b2 b3))
       (not (match-address b2 b4))
       (not (match-address b3 b4))))

(define data-address-valid-fix-for-buffers
  ((x data-address-valid-p)
   (b2 data-address-valid-p)
   (b3 data-address-valid-p)
   (b4 data-address-valid-p))
  :returns (retval data-address-valid-p :hyp :fguard)
  (if (or (match-address x b2)
          (match-address x b3)
          (match-address x b4))
        *default-invalid-data-address*
      x))

;; (defrulel buffers-identity
;;   (IMPLIES
;;     (AND (ALISTP X)
;;          (CDDDDR X)
;;          (NOT (CDR (CDDDDR X)))
;;          (EQUAL (CAR (CAR (CDDDDR X))) 'OUT)
;;          (EQUAL (CAR (CADDDR X)) 'B4)
;;          (EQUAL (CAR (CADDR X)) 'B3)
;;          (EQUAL (CAR (CADR X)) 'B2)
;;          (EQUAL (CAR (CAR X)) 'B1)
;;          (DATA-ADDRESS-VALID-P (CDR (CAR X)))
;;          (DATA-ADDRESS-VALID-P (CDR (CADR X)))
;;          (DATA-ADDRESS-VALID-P (CDR (CADDR X)))
;;          (DATA-ADDRESS-VALID-P (CDR (CADDDR X)))
;;          (DATA-ADDRESS-VALID-P (CDR (CAR (CDDDDR X))))
;;          (BUFFERS-REQ (CDR (CAR X))
;;                       (CDR (CADR X))
;;                       (CDR (CADDR X))
;;                       (CDR (CADDDR X))))
;;     (EQUAL (LIST (CONS 'B1
;;                        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CAR X))
;;                                                            (CDR (CADR X))
;;                                                            (CDR (CADDR X))
;;                                                            (CDR (CADDDR X))))
;;                  (CONS 'B2
;;                        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADR X))
;;                                                            (CDR (CAR X))
;;                                                            (CDR (CADDR X))
;;                                                            (CDR (CADDDR X))))
;;                  (CONS 'B3
;;                        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADDR X))
;;                                                            (CDR (CAR X))
;;                                                            (CDR (CADR X))
;;                                                            (CDR (CADDDR X))))
;;                  (CONS 'B4
;;                        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADDDR X))
;;                                                            (CDR (CAR X))
;;                                                            (CDR (CADR X))
;;                                                            (CDR (CADDR X))))
;;                  (CONS 'OUT (CDR (CAR (CDDDDR X)))))
;;            X))
;;      :hints (("goal" :in-theory (enable buffers-req data-address-valid-fix-for-buffers))))

;; (defrule buffers-identity2 ; bozo: kind of weird
;;   (IMPLIES
;;    (AND (ALISTP X)
;;         (CDDDDR X)
;;         (NOT (CDR (CDDDDR X)))
;;         (EQUAL (CAR (CAR (CDDDDR X))) 'OUT)
;;         (EQUAL (CAR (CADDDR X)) 'B4)
;;         (EQUAL (CAR (CADDR X)) 'B3)
;;         (EQUAL (CAR (CADR X)) 'B2)
;;         (EQUAL (CAR (CAR X)) 'B1)
;;         (DATA-ADDRESS-VALID-P (CDR (CAR X)))
;;         (DATA-ADDRESS-VALID-P (CDR (CADR X)))
;;         (DATA-ADDRESS-VALID-P (CDR (CADDR X)))
;;         (DATA-ADDRESS-VALID-P (CDR (CADDDR X)))
;;         (DATA-ADDRESS-VALID-P (CDR (CAR (CDDDDR X))))
;;         (BUFFERS-REQ (CDR (CAR X))
;;                      (CDR (CADR X))
;;                      (CDR (CADDR X))
;;                      (CDR (CADDDR X))))
;;    (EQUAL (LIST (CONS 'B1 (CDR (CAR X)))
;;                 (CONS 'B2
;;                       (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADR X))
;;                                                           (CDR (CAR X))
;;                                                           (CDR (CADDR X))
;;                                                           (CDR (CADDDR X))))
;;                 (CONS 'B3
;;                       (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADDR X))
;;                                                           (CDR (CAR X))
;;                                                           (CDR (CADR X))
;;                                                           (CDR (CADDDR X))))
;;                 (CONS 'B4
;;                       (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADDDR X))
;;                                                           (CDR (CAR X))
;;                                                           (CDR (CADR X))
;;                                                           (CDR (CADDR X))))
;;                 (CONS 'OUT (CDR (CAR (CDDDDR X)))))
;;           X))
;;   :enable (buffers-req data-address-valid-fix-for-buffers))

;; (defrulel buffers-identity3 ; bozo: kind of weird
;;   (IMPLIES
;;     (AND (ALISTP X)
;;          (CDDDDR X)
;;          (NOT (CDR (CDDDDR X)))
;;          (EQUAL (CAR (CAR (CDDDDR X))) 'OUT)
;;          (EQUAL (CAR (CADDDR X)) 'B4)
;;          (EQUAL (CAR (CADDR X)) 'B3)
;;          (EQUAL (CAR (CADR X)) 'B2)
;;          (EQUAL (CAR (CAR X)) 'B1)
;;          (DATA-ADDRESS-VALID-P (CDR (CAR X)))
;;          (DATA-ADDRESS-VALID-P (CDR (CADR X)))
;;          (DATA-ADDRESS-VALID-P (CDR (CADDR X)))
;;          (DATA-ADDRESS-VALID-P (CDR (CADDDR X)))
;;          (DATA-ADDRESS-VALID-P (CDR (CAR (CDDDDR X))))
;;          (BUFFERS-REQ (CDR (CAR X))
;;                       (CDR (CADR X))
;;                       (CDR (CADDR X))
;;                       (CDR (CADDDR X))))
;;     (EQUAL (LIST (CONS 'B1 (CDR (CAR X)))
;;                  (CONS 'B2 (CDR (CADR X)))
;;                  (CONS 'B3
;;                        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADDR X))
;;                                                            (CDR (CAR X))
;;                                                            (CDR (CADR X))
;;                                                            (CDR (CADDDR X))))
;;                  (CONS 'B4
;;                        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADDDR X))
;;                                                            (CDR (CAR X))
;;                                                            (CDR (CADR X))
;;                                                            (CDR (CADDR X))))
;;                  (CONS 'OUT (CDR (CAR (CDDDDR X)))))
;;            X))
;;      :hints (("goal" :in-theory (enable buffers-req data-address-valid-fix-for-buffers))))

(defrulel buffers-req-of-fix
  (BUFFERS-REQ (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
                (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
               (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
                (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
               (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
                (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
               (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
                (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
                (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))))
  :hints (("Goal" :in-theory (enable data-address-valid-fix-for-buffers buffers-req))))

;; (defrulel buffers-not-match-addresses
;;   (and (implies (buffers-req x a b c)
;;                 (not (match-address x a)))
;;        (implies (buffers-req x a b c)
;;                 (not (match-address x b)))
;;        (implies (buffers-req x a b c)
;;                 (not (match-address x c))))
;;   :enable buffers-req)

;; (defrule data-address-valid-fix-identity-1
;;   (IMPLIES (AND (ALISTP X)
;;                 (CDDDDR X)
;;                 (NOT (CDR (CDDDDR X)))
;;                 (EQUAL (CAR (CAR (CDDDDR X))) 'OUT)
;;                 (EQUAL (CAR (CADDDR X)) 'B4)
;;                 (EQUAL (CAR (CADDR X)) 'B3)
;;                 (EQUAL (CAR (CADR X)) 'B2)
;;                 (EQUAL (CAR (CAR X)) 'B1)
;;                 (DATA-ADDRESS-VALID-P (CDR (CAR X)))
;;                 (DATA-ADDRESS-VALID-P (CDR (CADR X)))
;;                 (DATA-ADDRESS-VALID-P (CDR (CADDR X)))
;;                 (DATA-ADDRESS-VALID-P (CDR (CADDDR X)))
;;                 (DATA-ADDRESS-VALID-P (CDR (CAR (CDDDDR X))))
;;                 (BUFFERS-REQ (CDR (CAR X))
;;                              (CDR (CADR X))
;;                              (CDR (CADDR X))
;;                              (CDR (CADDDR X))))
;;            (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CAR X))
;;                                                       (CDR (CADR X))
;;                                                       (CDR (CADDR X))
;;                                                       (CDR (CADDDR X)))
;;                   (CDR (CAR X))))
;;   :enable (data-address-valid-fix-for-buffers buffers-not-match-addresses))

;; (maybe-skip-expensive-proof
;; (defrulel DATA-ADDRESS-VALID-FIX-FOR-BUFFERS-4-no-ops-b1
;; ; proves in 866.58 seconds.
;;   (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X))) ; b1
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X))) ; b2
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X))) ; b3
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))) ; b4
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))))
;;        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;             (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))))
;;   :enable (data-address-valid-fix data-address-valid-fix-for-buffers))
;; )

;; (maybe-skip-expensive-proof
;; (defrulel DATA-ADDRESS-VALID-FIX-FOR-BUFFERS-4-no-ops-b2
;;   (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X))) ; b2
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X))) ; b1
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X))) ; b3
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))) ; b4
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))))
;;        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))))
;;   :enable (data-address-valid-fix data-address-valid-fix-for-buffers))
;; )

;; (maybe-skip-expensive-proof
;; (defrulel DATA-ADDRESS-VALID-FIX-FOR-BUFFERS-4-no-ops-b3
;;   (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X))) ; b3
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X))) ; b1
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X))) ; b2
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))) ; b4
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))))
;;        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))))
;;   :enable (data-address-valid-fix data-address-valid-fix-for-buffers))
;; )

;; (maybe-skip-expensive-proof
;; (defrulel DATA-ADDRESS-VALID-FIX-FOR-BUFFERS-4-no-ops-b4
;;   (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))) ; b4
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X))) ; b1
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X))) ; b2
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))) ; b3
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X))))
;;             (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;                  (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))))
;;        (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADDDR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CAR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADR X)))
;;             (DATA-ADDRESS-VALID-FIX (CDR (CADDR X)))))
;;   :enable (data-address-valid-fix data-address-valid-fix-for-buffers))
;; )

;; (defrule DATA-ADDRESS-VALID-FIX-FOR-BUFFERS-no-op-b2
;;   (IMPLIES (AND (ALISTP X)
;;               (CDDDDR X)
;;               (NOT (CDR (CDDDDR X)))
;;               (EQUAL (CAR (CAR (CDDDDR X))) 'OUT)
;;               (EQUAL (CAR (CADDDR X)) 'B4)
;;               (EQUAL (CAR (CADDR X)) 'B3)
;;               (EQUAL (CAR (CADR X)) 'B2)
;;               (EQUAL (CAR (CAR X)) 'B1)
;;               (DATA-ADDRESS-VALID-P (CDR (CAR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CADR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CADDR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CADDDR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CAR (CDDDDR X))))
;;               (BUFFERS-REQ (CDR (CAR X))
;;                            (CDR (CADR X))
;;                            (CDR (CADDR X))
;;                            (CDR (CADDDR X))))
;;          (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADR X)) ; b2
;;                                                     (CDR (CAR X)) ; b1
;;                                                     (CDR (CADDR X)) ; b3
;;                                                     (CDR (CADDDR X))) ; b4
;;                 (CDR (CADR X)))) ; b2
;;   :enable (buffers-req data-address-valid-fix-for-buffers))

;; (defrule DATA-ADDRESS-VALID-FIX-FOR-BUFFERS-no-op-b3
;;   (IMPLIES (AND (ALISTP X)
;;               (CDDDDR X)
;;               (NOT (CDR (CDDDDR X)))
;;               (EQUAL (CAR (CAR (CDDDDR X))) 'OUT)
;;               (EQUAL (CAR (CADDDR X)) 'B4)
;;               (EQUAL (CAR (CADDR X)) 'B3)
;;               (EQUAL (CAR (CADR X)) 'B2)
;;               (EQUAL (CAR (CAR X)) 'B1)
;;               (DATA-ADDRESS-VALID-P (CDR (CAR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CADR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CADDR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CADDDR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CAR (CDDDDR X))))
;;               (BUFFERS-REQ (CDR (CAR X))
;;                            (CDR (CADR X))
;;                            (CDR (CADDR X))
;;                            (CDR (CADDDR X))))
;;          (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADDR X))
;;                                                     (CDR (CAR X))
;;                                                     (CDR (CADR X))
;;                                                     (CDR (CADDDR X)))
;;                 (CDR (CADDR X)))) ; b3
;;     :enable (buffers-req data-address-valid-fix-for-buffers))

;; (defrule data-address-valid-fix-for-buffers-no-op-b4
;;   (IMPLIES (AND (ALISTP X)
;;               (CDDDDR X)
;;               (NOT (CDR (CDDDDR X)))
;;               (EQUAL (CAR (CAR (CDDDDR X))) 'OUT)
;;               (EQUAL (CAR (CADDDR X)) 'B4)
;;               (EQUAL (CAR (CADDR X)) 'B3)
;;               (EQUAL (CAR (CADR X)) 'B2)
;;               (EQUAL (CAR (CAR X)) 'B1)
;;               (DATA-ADDRESS-VALID-P (CDR (CAR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CADR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CADDR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CADDDR X)))
;;               (DATA-ADDRESS-VALID-P (CDR (CAR (CDDDDR X))))
;;               (BUFFERS-REQ (CDR (CAR X))
;;                            (CDR (CADR X))
;;                            (CDR (CADDR X))
;;                            (CDR (CADDDR X))))
;;          (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADDDR X))
;;                                                     (CDR (CAR X))
;;                                                     (CDR (CADR X))
;;                                                     (CDR (CADDR X)))
;;                 (CDR (CADDDR X)))) ; b4
;;     :enable (buffers-req data-address-valid-fix-for-buffers))

;; (defrule exploded-call-of-data-address-valid-fix-for-buffers
;;   (IMPLIES
;;      (AND (ALISTP X)
;;           (CDDDDR X) ; implies (consp (cdr x)) ^ (consp (cdr (cdr x))) ^ ...
;;           (NOT (CDR (CDDDDR X)))
;;           (EQUAL (CAR (CAR (CDDDDR X))) 'OUT)
;;           (EQUAL (CAR (CADDDR X)) 'B4)
;;           (EQUAL (CAR (CADDR X)) 'B3)
;;           (EQUAL (CAR (CADR X)) 'B2)
;;           (EQUAL (CAR (CAR X)) 'B1)
;;           (DATA-ADDRESS-VALID-P (CDR (CAR X)))
;;           (DATA-ADDRESS-VALID-P (CDR (CADR X)))
;;           (DATA-ADDRESS-VALID-P (CDR (CADDR X)))
;;           (DATA-ADDRESS-VALID-P (CDR (CADDDR X)))
;;           (DATA-ADDRESS-VALID-P (CDR (CAR (CDDDDR X))))
;;           (BUFFERS-REQ (CDR (CAR X))
;;                        (CDR (CADR X))
;;                        (CDR (CADDR X))
;;                        (CDR (CADDDR X))))
;;      (EQUAL (LIST (CONS 'B1 (CDR (CAR X)))
;;                   (CONS 'B2 (CDR (CADR X)))
;;                   (CONS 'B3 (CDR (CADDR X)))
;;                   (CONS 'B4
;;                         (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (CDR (CADDDR X)) ; b4
;;                                                             (CDR (CAR X))
;;                                                             (CDR (CADR X))
;;                                                             (CDR (CADDR X))))
;;                   (CONS 'OUT (CDR (CAR (CDDDDR X)))))
;;             X))
;;     :enable (buffers-req data-address-valid-fix-for-buffers))

(defrule all-four ; this is an implementation of Sol's second rule
  (and (IMPLIES (AND (BUFFERS-REQ B1 B2 B3 B4)
                     (DATA-ADDRESS-VALID-P B4)
                     (DATA-ADDRESS-VALID-P B3)
                     (DATA-ADDRESS-VALID-P B2)
                     (DATA-ADDRESS-VALID-P B1))
                (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS B2 B1 B3 B4)
                       B2))
       (IMPLIES (AND (BUFFERS-REQ B1 B2 B3 B4)
                     (DATA-ADDRESS-VALID-P B4)
                     (DATA-ADDRESS-VALID-P B3)
                     (DATA-ADDRESS-VALID-P B2)
                     (DATA-ADDRESS-VALID-P B1))
                (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS B4 B1 B2 B3)
                       B4))
       (IMPLIES (AND (BUFFERS-REQ B1 B2 B3 B4)
                     (DATA-ADDRESS-VALID-P B4)
                     (DATA-ADDRESS-VALID-P B3)
                     (DATA-ADDRESS-VALID-P B2)
                     (DATA-ADDRESS-VALID-P B1))
                (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS B1 B2 B3 B4)
                       B1))
       (IMPLIES (AND (BUFFERS-REQ B1 B2 B3 B4)
                     (DATA-ADDRESS-VALID-P B4)
                     (DATA-ADDRESS-VALID-P B3)
                     (DATA-ADDRESS-VALID-P B2)
                     (DATA-ADDRESS-VALID-P B1))
                (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS B3 B1 B2 B4)
                       B3)))
  :enable (buffers-req data-address-valid-fix-for-buffers))


(defrule buffers-req-of-fixes
  (BUFFERS-REQ
     (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (DATA-ADDRESS-VALID-FIX B1)
                                         (DATA-ADDRESS-VALID-FIX B2)
                                         (DATA-ADDRESS-VALID-FIX B3)
                                         (DATA-ADDRESS-VALID-FIX B4))
     (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (DATA-ADDRESS-VALID-FIX B2)
                                         (DATA-ADDRESS-VALID-FIX B1)
                                         (DATA-ADDRESS-VALID-FIX B3)
                                         (DATA-ADDRESS-VALID-FIX B4))
     (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (DATA-ADDRESS-VALID-FIX B3)
                                         (DATA-ADDRESS-VALID-FIX B1)
                                         (DATA-ADDRESS-VALID-FIX B2)
                                         (DATA-ADDRESS-VALID-FIX B4))
     (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (DATA-ADDRESS-VALID-FIX B4)
                                         (DATA-ADDRESS-VALID-FIX B1)
                                         (DATA-ADDRESS-VALID-FIX B2)
                                         (DATA-ADDRESS-VALID-FIX B3)))
    :enable (buffers-req DATA-ADDRESS-VALID-FIX-FOR-BUFFERS))

(defrule sol1
; implements:
;;; the reqfixes always produce something that satisfies the requirement:
;;; (implies  (a,b,c are of the right types)
;;;               (requirement (reqfix-a a b c) (reqfix-b a b c) (reqfix-c a b c)))
  (implies (and (data-address-valid-p b1)
                (data-address-valid-p b2)
                (data-address-valid-p b3)
                (data-address-valid-p b4))
           (buffers-req (data-address-valid-fix-for-buffers b1 b2 b3 b4)
                        (data-address-valid-fix-for-buffers b2 b1 b3 b4)
                        (data-address-valid-fix-for-buffers b3 b1 b2 b4)
                        (data-address-valid-fix-for-buffers b4 b1 b1 b2)))
  :enable (data-address-valid-fix-for-buffers  buffers-req))

; The following is already implemented by all-four
;; the reqfixes don't change things if they already satisfy the requirement:
;;; (implies (and (a,b,c are of the right types)
;;;                      (requirement a b c))
;;;              (and (equal (reqfix-a a b c) a)
;;;                      (equal (reqfix-b a b c) b)
;;;                      (equal (reqfix-c a b c) c)))



(i-am-here)

(fty::defprod buffers
  ((b1 data-address-valid :reqfix (data-address-valid-fix-for-buffers b1 b2 b3 b4))
   (b2 data-address-valid :reqfix (data-address-valid-fix-for-buffers b2 b1 b3 b4))
   (b3 data-address-valid :reqfix (data-address-valid-fix-for-buffers b3 b1 b2 b4))
   (b4 data-address-valid :reqfix (data-address-valid-fix-for-buffers b4 b1 b2 b3))
   (out data-address-valid))
  :require (buffers-req b1 b2 b3 b4))
