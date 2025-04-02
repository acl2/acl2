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

(include-book "std/alists/alist-defuns" :dir :system)
(include-book "std/alists/alist-fix" :dir :system)
(local (include-book "std/alists/hons-remove-assoc" :dir :system))
(local (include-book "std/alists/hons-put-assoc" :dir :system))
(local (include-book "std/alists/alist-equiv" :dir :system))
(defthm defhash-member-of-append
  (iff (member-equal k (append x y))
       (or (member-equal k x) (member-equal k y)))
  :hints(("Goal" :in-theory (enable member-equal append))))
(defthm defhash-no-duplicatesp-of-append
  (iff (no-duplicatesp-equal (append x y))
       (and (no-duplicatesp-equal x)
            (no-duplicatesp-equal y)
            (not (intersectp-equal x y))))
  :hints(("Goal" :in-theory (enable no-duplicatesp-equal
                                    intersectp-equal
                                    append))))

(defcong acl2::alist-equiv acl2::alist-equiv (acl2::hons-remove-assoc k x) 2
  :hints(("Goal" :in-theory (enable acl2::alist-equiv-when-agree-on-bad-guy))))



(defthm defhash-intersectp-of-singleton
  (iff (intersectp-equal x (list k))
       (member-equal k x))
  :hints(("Goal" :in-theory (enable intersectp-equal
                                    member-equal))))

(defthm defhash-member-alist-keys
  (iff (member-equal k (acl2::alist-keys x))
       (hons-assoc-equal k x))
  :hints(("Goal" :in-theory (enable acl2::alist-keys
                                    hons-assoc-equal))))

(defthm defhash-alist-keys-of-hons-remove-assoc
  (equal (acl2::alist-keys (acl2::hons-remove-assoc k x))
         (remove-equal k (acl2::alist-keys x)))
  :hints(("Goal" :in-theory (enable acl2::alist-keys
                                    acl2::hons-remove-assoc
                                    remove-equal))))

(defthm defhash-member-of-remove
  (implies (not (member-equal j x))
           (not (member-equal j (remove-equal k x)))))

(defthm defhash-no-duplicates-of-remove
  (implies (no-duplicatesp-equal x)
           (no-duplicatesp-equal (remove-equal k x)))
  :hints(("Goal" :in-theory (enable no-duplicatesp-equal remove-equal))))

(defthm defhash-alist-keys-of-alist-fix
  (equal (acl2::alist-keys (acl2::alist-fix x))
         (acl2::alist-keys x))
  :hints(("Goal" :in-theory (enable acl2::alist-fix
                                    acl2::alist-keys))))

(defthm defhash-alist-fix-under-alist-equiv
  (acl2::alist-equiv (acl2::alist-fix x) x)
  :hints(("Goal" :in-theory (enable acl2::alist-equiv-iff-agree-on-bad-guy))))

(defthm defhash-alist-equiv-of-hons-put-assoc
  (acl2::alist-equiv (cons (cons k v) x)
                     (acl2::hons-put-assoc k v x))
  :hints(("Goal" :in-theory (enable acl2::alist-equiv-iff-agree-on-bad-guy))))

(defcong acl2::alist-equiv acl2::alist-equiv (acl2::hons-put-assoc k v x) 3
  :hints(("Goal" :in-theory (enable acl2::alist-equiv-when-agree-on-bad-guy))))

(defthm defhash-duplicate-keys-of-hons-put-assoc
  (implies (no-duplicatesp-equal (acl2::alist-keys x))
           (no-duplicatesp-equal (acl2::alist-keys (acl2::hons-put-assoc k v x)))))

(defthm defhash-alistp-of-hons-put-assoc
  (implies (alistp x)
           (alistp (acl2::hons-put-assoc k v x))))

(defcong acl2::Alist-equiv equal (hons-assoc-equal k x) 2)
