;; SPDX-FileCopyrightText: Copyright 2025 Arm Limited and/or its affiliates <open-source-office@arm.com>
;; SPDX-License-Identifier: BSD-3-Clause
;; 
;; Redistribution and use in source and binary forms, with or without
;; modification, are permitted provided that the following conditions are
;; met:

;; o Redistributions of source code must retain the above copyright
;;   notice, this list of conditions and the following disclaimer.

;; o Redistributions in binary form must reproduce the above copyright
;;   notice, this list of conditions and the following disclaimer in the
;;   documentation and/or other materials provided with the distribution.

;; o Neither the name of the copyright holder nor the names of
;;   its contributors may be used to endorse or promote products derived
;;   from this software without specific prior written permission.

;; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
;; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
;; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
;; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
;; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
;; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
;; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
;; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
;; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
;; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
;; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

;; Author: Sol Swords <sol.swords@arm.com>

(in-package "FTY")
(include-book "../multicase")
(include-book "../deftypes")
(include-book "../basetypes")
(include-book "std/util/defenum" :dir :System)


(deftagsum val
  (:int ((val integerp)))
  (:rat ((val rationalp)))
  (:str ((val stringp)))
  (:bool ((val booleanp)))
  (:err ((msg stringp))))

(std::defenum op-p (:plus :times :div :eq :noteq :concat :and :or :unimpl))

(def-enumcase op-case op-p)

(define apply-op ((op op-p)
                  (v1 val-p)
                  (v2 val-p))
  :returns (res val-p)
  (multicase
    ((op-case op)
     (val-case v1)
     (val-case v2))

    ((:plus :int :int)     (val-int (+ v1.val v2.val)))
    ((:plus :rat :rat)     (val-rat (+ v1.val v2.val)))

    ((:times :int :int)    (val-int (* v1.val v2.val)))
    ((:times -    :int)    (val-err "Times of non-int and int"))
    ((:times :rat :rat)    (val-rat (* v1.val v2.val)))
    ((:times :int :rat)    (val-rat (* v1.val v2.val)))
    ((:times :int -) :when (eql v1.val 0)
                           (val-int 0))

    ((:div :int :int) :when (not (eql 0 v2.val))
                           (val-rat (/ v1.val v2.val)))
    ((:div :rat :rat) :when (not (eql 0 v2.val))
                           (val-rat (/ v1.val v2.val)))

    ((-    :err -)         (val-fix v1))
    ((-    -    :err)      (val-err v2.msg))
    
    ((:eq :int :int)       (val-bool (eql v1.val v2.val)))
    ((:eq :rat :rat)       (val-bool (eql v1.val v2.val)))
    ((:eq :str :str)       (val-bool (equal v1.val v2.val)))
    ((:eq :bool :bool)     (val-bool (iff v1.val v2.val)))

    ((:noteq :int :int)    (val-bool (not (eql v1.val v2.val))))
    ((:noteq :rat :rat)    (val-bool (not (eql v1.val v2.val))))
    ((:noteq :str :str)    (val-bool (not (equal v1.val v2.val))))
    ((:noteq :bool :bool)  (val-bool (not (iff v1.val v2.val))))

    ((:concat :str :str)   (val-str (concatenate 'string v1.val v2.val)))

    ((:and :bool :bool)    (val-bool (and v1.val v2.val)))
    ((:or :bool :bool)     (val-bool (or v1.val v2.val)))

    (-                     (val-err "Bad operator application"))))

(assert-event (equal (apply-op :plus (val-int 1) (val-int 2))
                     (val-int 3)))

(assert-event (equal (apply-op :concat (val-str "hello") (val-str " world"))
                     (val-str "hello world")))

(assert-event (equal (apply-op :times (val-int 4) (val-rat 2/3))
                     (val-rat 8/3)))

(assert-event (equal (apply-op :times (val-rat 2/3) (val-int 4))
                     (val-err "Times of non-int and int")))

(assert-event (equal (apply-op :div (val-rat 2/3) (val-rat 4))
                     (val-rat 1/6)))

(assert-event (equal (apply-op :div (val-int 1) (val-int 0))
                     (val-err "Bad operator application")))

(assert-event (equal (apply-op :plus (val-int 1) (val-rat 0))
                     (val-err "Bad operator application")))

(assert-event (equal (apply-op :eq (val-int 1) (val-rat 0))
                     (val-err "Bad operator application")))

(assert-event (equal (apply-op :eq (val-int 1) (val-rat 0))
                     (val-err "Bad operator application")))

(assert-event (equal (apply-op :unimpl (val-int 1) (val-int 1))
                     (val-err "Bad operator application")))

(assert-event (equal (apply-op :plus (val-err "bad") (val-int 0))
                     (val-err "bad")))

(assert-event (equal (apply-op :times (val-err "bad") (val-int 0))
                     (val-err "Times of non-int and int")))

(assert-event (equal (apply-op :times (val-int 0) (val-err "bad"))
                     (val-int 0)))


(fty::deflist vallist :elt-type val-p :true-listp t)

(define apply-prim ((op stringp) (vals vallist-p))
  :returns (res val-p)
  (multicase
    ((case*-equal op)
     ((list val-case v0 v1 v2) vals))

    (("Log2" (:int)) (val-int (1- (integer-length (abs v0.val)))))
    (("Ite" (:bool & &)) (if v0.val (val-fix v1) (val-fix v2)))
    (("RoundDown" (:rat)) (val-int (floor v0.val 1)))
    (-                     (val-err "Bad"))))


(assert-event (equal (apply-prim "Ite" (list (val-bool t) (val-int 4) (val-int 3)))
                     (val-int 4)))

(assert-event (equal (apply-prim "Log2" (list (val-int 7)))
                     (val-int 2)))

(assert-event (equal (apply-prim "RoundDown" (list (val-rat 7/3)))
                     (val-int 2)))

(assert-event (equal (apply-prim "Log2" (list (val-int 7) (val-int 3)))
                     (val-err "Bad")))

(assert-event (equal (apply-prim "Log2" (list (val-rat 7)))
                     (val-err "Bad")))

(assert-event (equal (apply-prim "Log2" nil)
                     (val-err "Bad")))

