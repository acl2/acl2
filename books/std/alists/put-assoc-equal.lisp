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

(defthm put-assoc-equal-identity
  (implies (and (assoc-equal k x)
                (alistp x)
                (equal v (cdr (assoc-equal k x))))
           (equal (put-assoc-equal k v x) x))
  :hints(("Goal" :in-theory (enable assoc-equal put-assoc-equal))))


(defthm hons-assoc-equal-of-put-assoc-equal
  (equal (hons-assoc-equal k (put-assoc-equal k1 v x))
         (if (equal k k1)
             (cons k v)
           (hons-assoc-equal k x)))
  :hints(("Goal" :in-theory (enable hons-assoc-equal put-assoc-equal))))

(local (defthm fal-extract-of-acons-non-mem
         (implies (not (member-equal k keys))
                  (equal (acl2::fal-extract keys (cons (cons k v) x))
                         (acl2::fal-extract keys x)))
         :hints(("Goal" :in-theory (enable acl2::fal-extract)))))

(local (defthm car-hons-assoc-equal
         (equal (car (hons-assoc-equal k x))
                (and (hons-assoc-equal k x) k))))

(defthm fal-extract-of-put-assoc-equal
    (implies (and (no-duplicatesp-equal keys)
                  (hons-assoc-equal k x))
             (equal (acl2::fal-extract keys (put-assoc-equal k v x))
                    (if (member-equal k keys)
                        (put-assoc-equal k v (acl2::fal-extract keys x))
                      (acl2::fal-extract keys x))))
    :hints(("Goal" :in-theory (enable acl2::fal-extract put-assoc-equal))))

(local (defthm member-alist-keys
           (iff (member-equal k (acl2::alist-keys x))
                (hons-assoc-equal k x))
           :hints(("Goal" :in-theory (enable acl2::alist-keys)))))

(defthm no-duplicate-keys-of-put-assoc-equal
  (implies (and (no-duplicatesp-equal (acl2::alist-keys x))
                (alistp x))
           (no-duplicatesp-equal (acl2::alist-keys (put-assoc-equal k v x))))
  :hints(("Goal" :in-theory (enable acl2::alist-keys no-duplicatesp-equal put-assoc-equal))))


(defthm put-assoc-equal-alternate
  (implies (hons-assoc-equal k1 x)
           (equal (put-assoc-equal k1 v1 (put-assoc-equal k2 v2 (put-assoc-equal k1 v3 x)))
                  (put-assoc-equal k1 v1 (put-assoc-equal k2 v2 x))))
  :hints(("Goal" :in-theory (enable put-assoc-equal))))

(defthm put-assoc-equal-redundant
  (implies (hons-assoc-equal k1 x)
           (equal (put-assoc-equal k1 v1 (put-assoc-equal k1 v3 x))
                  (put-assoc-equal k1 v1 x)))
  :hints(("Goal" :in-theory (enable put-assoc-equal))))


(defthm alist-keys-of-put-assoc-equal
  (implies (or (alistp x) k)
           (equal (acl2::alist-keys (put-assoc-equal k v x))
                  (if (hons-assoc-equal k x)
                      (acl2::alist-keys x)
                    (append (acl2::alist-keys x) (list k)))))
  :hints(("Goal" :in-theory (enable acl2::alist-keys put-assoc-equal))))


(defthm remove-assoc-equal-of-put-assoc-equal
  (equal (remove-assoc-equal name (put-assoc-equal name val x))
         (remove-assoc-equal name x))
  :hints(("Goal" :in-theory (enable remove-assoc-equal put-assoc-equal))))

(defthm alistp-of-put-assoc-equal
  (implies (alistp x)
           (alistp (put-assoc-equal k v x))))

