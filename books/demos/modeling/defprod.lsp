; FTY::defprod Example
; Copyright (C) 2014, Oracle and/or its affiliates. All rights reserved.
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: David L. Rager <david.rager@oracle.com>

(in-package "ACL2")

; WARNING: This file is a work in progress.  Hopefully at some point it will
; suffice as a nice working example for defprod's dependent types feature, but
; as of December 2015, it's broken.  It is currently intended to be "ld"'d into
; a system, not certified or included as a book.

(include-book "std/util/bstar" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/top" :dir :system)

(defxdoc shifting-fifo-model
  :short "The start of a FIFO model that looks like a shifting-fifo in its
          implementation")

(local (set-default-parents shifting-fifo-model))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Here begins the "defprod" part of this modeling example
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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

(defrule match-commute
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

(defrule data-address-valid-fix-for-buffers-identities
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

(defrulel match-of-default-is-always-nil
; For subgoal 23.9 in buffers-fix-works and buffers-req-of-fixes, but it's not
; a horrible lemma to have in general.  Still, we make it local.
  (equal (MATCH-ADDRESS *default-invalid-data-address* xxx)
         nil)
  :enable match-address)

;; (defrule match-of-default-is-always-nil-2
;;    (equal (MATCH-ADDRESS xxx *default-invalid-data-address* )
;;           nil)
;;    :enable match-address)

(defrule buffers-fix-works
  (implies (and (data-address-valid-p b1)
                (data-address-valid-p b2)
                (data-address-valid-p b3)
                (data-address-valid-p b4))
           (buffers-req (data-address-valid-fix-for-buffers b1 b2 b3 b4)
                        (data-address-valid-fix-for-buffers b2 b1 b3 b4)
                        (data-address-valid-fix-for-buffers b3 b1 b2 b4)
                        (data-address-valid-fix-for-buffers b4 b1 b1 b2)))
  :enable (data-address-valid-fix-for-buffers  buffers-req))

(defrule buffers-req-of-fixes
; I don't quite understand why this is necessary, but it is.  At least it's
; clear how to duplicate this to one's own work.
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

(defrulel obscure-fact
; The rewrite rule has to be structured to rewrite an equality to t, because if
; it's used to rewrite the lhs of the inner equality to the rhs of the inner
; equality, it generates bad checkpoints for other proof obligations (during
; the buffers defprod).

; That being said, why this rule is necessary (and corresponding rules for b2,
; b3, and b4 aren't necessary) is still a mystery.
  (equal (EQUAL (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (DATA-ADDRESS-VALID-FIX B1)
                                                    (DATA-ADDRESS-VALID-FIX B2)
                                                    (DATA-ADDRESS-VALID-FIX B3)
                                                    (DATA-ADDRESS-VALID-FIX B4))
                (DATA-ADDRESS-VALID-FIX-FOR-BUFFERS (DATA-ADDRESS-VALID-FIX B1)
                                                    B2 B3 B4))
         t)
  :enable (data-address-valid-fix-for-buffers match-address))

(fty::defprod buffers
  ((b1 data-address-valid :reqfix (data-address-valid-fix-for-buffers b1 b2 b3 b4))
   (b2 data-address-valid :reqfix (data-address-valid-fix-for-buffers b2 b1 b3 b4))
   (b3 data-address-valid :reqfix (data-address-valid-fix-for-buffers b3 b1 b2 b4))
   (b4 data-address-valid :reqfix (data-address-valid-fix-for-buffers b4 b1 b2 b3))
   (out data-address-valid))
  :require (buffers-req b1 b2 b3 b4))
