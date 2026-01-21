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

(in-package "STOBJS")

(include-book "../def-hash")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(def-hash basehash)

(def-hash basehashfix :alist-fix acl2::alist-fix)

(fty::defmap symbol-key-alist :key-type symbolp)

(def-hash symkeyhash :alistp symbol-key-alist-p :key-p symbolp :hash-test eq)
(def-hash symkeyhashfix :alistp symbol-key-alist-p :alist-fix symbol-key-alist-fix :key-p symbolp :hash-test eq)
(def-hash symkeyhashkeyfix :alistp symbol-key-alist-p :key-p symbolp :key-fix acl2::symbol-fix :hash-test eq)
(def-hash symkeyhashfixkeyfix :alistp symbol-key-alist-p :alist-fix symbol-key-alist-fix :key-p symbolp :key-fix acl2::symbol-fix :hash-test eq)


(fty::defmap symbol-key-alisttr :key-type symbolp :true-listp t)

(def-hash symkeytrhash :alistp symbol-key-alisttr-p :key-p symbolp :hash-test eq)
(def-hash symkeytrhashfix :alistp symbol-key-alisttr-p :alist-fix symbol-key-alisttr-fix :key-p symbolp :hash-test eq)
(def-hash symkeytrhashkeyfix :alistp symbol-key-alisttr-p :key-p symbolp :key-fix acl2::symbol-fix :hash-test eq)
(def-hash symkeytrhashfixkeyfix :alistp symbol-key-alisttr-p :alist-fix symbol-key-alisttr-fix :key-p symbolp :key-fix acl2::symbol-fix :hash-test eq)

(fty::defmap integer-val-alist :val-type integerp)

(def-hash intvalhash :alistp integer-val-alist-p :val-p integerp :default-val (+ 1 2) :type-decl integer)
(def-hash intvalhashfix :alistp integer-val-alist-p :alist-fix integer-val-alist-fix :val-p integerp :default-val (+ 1 2):type-decl integer)
(def-hash intvalhashkeyfix :alistp integer-val-alist-p :val-p integerp :val-fix ifix :default-val (+ 1 2) :type-decl integer)
(def-hash intvalhashfixkeyfix :alistp integer-val-alist-p :alist-fix integer-val-alist-fix :val-p integerp :val-fix ifix :default-val (+ 1 2) :type-decl integer)


(fty::defalist int-nat-alist :key-type integerp :val-type natp :true-listp t)

(def-hash intnathash :alistp int-nat-alist-p :key-p integerp :val-p natp :hash-test eql :default-val (+ 1 2) :type-decl (integer 0 *))
(def-hash intnathashfix :alistp int-nat-alist-p :alist-fix int-nat-alist-fix :key-p integerp :val-p natp :hash-test eql :default-val (+ 1 2) :type-decl (integer 0 *))
(def-hash intnathashkeyfix :alistp int-nat-alist-p :key-p integerp :key-fix ifix :val-p natp :hash-test eql :default-val (+ 1 2) :type-decl (integer 0 *))
(def-hash intnathashvalfix :alistp int-nat-alist-p :alist-fix int-nat-alist-fix :key-p integerp :val-p natp :val-fix nfix :hash-test eql :default-val (+ 1 2) :type-decl (integer 0 *))
(def-hash intnathashallfix :alistp int-nat-alist-p :alist-fix int-nat-alist-fix :key-p integerp :key-fix ifix :val-p natp :val-fix nfix :hash-test eql :default-val (+ 1 2) :type-decl (integer 0 *))
