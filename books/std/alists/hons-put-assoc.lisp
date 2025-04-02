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

(in-package "ACL2")

(include-book "alist-defuns")

(defthm hons-put-assoc-identity
  (implies (and (hons-assoc-equal k x)
                (equal v (cdr (hons-assoc-equal k x))))
           (equal (hons-put-assoc k v x)
                  x))
  :hints(("Goal" :in-theory (enable assoc-equal hons-put-assoc))))


(defthm hons-assoc-equal-of-hons-put-assoc
  (equal (hons-assoc-equal k (hons-put-assoc k1 v x))
         (if (equal k k1)
             (cons k v)
           (hons-assoc-equal k x)))
  :hints(("Goal" :in-theory (enable hons-assoc-equal hons-put-assoc))))

(local (defthm fal-extract-of-acons-non-mem
         (implies (not (member-equal k keys))
                  (equal (acl2::fal-extract keys (cons (cons k v) x))
                         (acl2::fal-extract keys x)))
         :hints(("Goal" :in-theory (enable acl2::fal-extract)))))

(local (defthm car-hons-assoc-equal
         (equal (car (hons-assoc-equal k x))
                (and (hons-assoc-equal k x) k))))

(defthm fal-extract-of-hons-put-assoc
    (implies (and (no-duplicatesp-equal keys)
                  (hons-assoc-equal k x))
             (equal (acl2::fal-extract keys (hons-put-assoc k v x))
                    (if (member-equal k keys)
                        (hons-put-assoc k v (acl2::fal-extract keys x))
                      (acl2::fal-extract keys x))))
    :hints(("Goal" :in-theory (enable acl2::fal-extract hons-put-assoc))))

(local (defthm member-alist-keys
           (iff (member-equal k (acl2::alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable acl2::alist-keys)))))

(defthm no-duplicate-keys-of-hons-put-assoc
  (implies (no-duplicatesp-equal (acl2::alist-keys x))
           (no-duplicatesp-equal (acl2::alist-keys (hons-put-assoc k v x))))
  :hints(("Goal" :in-theory (enable acl2::alist-keys no-duplicatesp-equal hons-put-assoc))))


(defthm hons-put-assoc-alternate
  (implies (hons-assoc-equal k1 x)
           (equal (hons-put-assoc k1 v1 (hons-put-assoc k2 v2 (hons-put-assoc k1 v3 x)))
                  (hons-put-assoc k1 v1 (hons-put-assoc k2 v2 x))))
  :hints(("Goal" :in-theory (enable hons-put-assoc))))

(defthm hons-put-assoc-redundant
  (equal (hons-put-assoc k1 v1 (hons-put-assoc k1 v2 x))
         (hons-put-assoc k1 v1 x))
  :hints(("Goal" :in-theory (enable hons-put-assoc))))


(defthm alist-keys-of-hons-put-assoc
  (implies (or (alistp x) k)
           (equal (acl2::alist-keys (hons-put-assoc k v x))
                  (if (hons-assoc-equal k x)
                      (acl2::alist-keys x)
                    (append (acl2::alist-keys x) (list k)))))
  :hints(("Goal" :in-theory (enable acl2::alist-keys hons-put-assoc))))


(defthm remove-assoc-equal-of-hons-put-assoc
  (equal (remove-assoc-equal name (hons-put-assoc name val x))
         (remove-assoc-equal name x))
  :hints(("Goal" :in-theory (enable remove-assoc-equal hons-put-assoc))))

(defthm alistp-of-hons-put-assoc
  (implies (alistp x)
           (alistp (hons-put-assoc k v x)))
  :hints(("Goal" :in-theory (enable hons-put-assoc))))


