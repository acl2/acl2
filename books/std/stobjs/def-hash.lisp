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
(include-book "absstobjs")
; (include-book "xdoc/str" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(include-book "std/alists/alist-fix" :dir :system)


(defxdoc def-hash
  :parents (std/stobjs)
  :short "Defines a @(see abstract-stobj) that logically just appears to be an
alist but is implemented as a stobj hash table.")


(defconst *def-hash-template*
  '(defsection <name>
     (local (include-book "std/stobjs/def-hash-theory" :dir :system))
     
     (make-event
      `(defstobj <name>$c
         (<name>-ht$c :type (hash-table <hash-test> <init-size> <type-decl>) :initially ,<default-val>)))

     (define <name>$ap (x)
       :enabled t
       (and (<alistp> x)
            (no-duplicatesp-equal (acl2::alist-keys x))))

     (define create-<name>$a () nil)

     (define <name>-put$a ((key (:@ :key-p <key-p>)) (val (:@ :val-p <val-p>)) (x <name>$ap))
       :enabled t
       (acl2::hons-put-assoc (:@ :key-fix (<key-fix> key)) (:@ (not :key-fix) key)
                       (:@ :val-fix (<val-fix> val)) (:@ (not :val-fix) val)
                       (:@ :alist-fix (<alist-fix> x)) (:@ (not :alist-fix) x)))

     (define <name>-boundp$a ((key (:@ :key-p <key-p>)) (x <name>$ap))
       :enabled t
       (consp (hons-assoc-equal (:@ :key-fix (<key-fix> key)) (:@ (not :key-fix) key)
                                (:@ :alist-fix (<alist-fix> x)) (:@ (not :alist-fix) x))))

     (define <name>-get$a ((key (:@ :key-p <key-p>)) (x <name>$ap))
       :enabled t
       (let ((look (hons-assoc-equal (:@ :key-fix (<key-fix> key)) (:@ (not :key-fix) key)
                                     (:@ :alist-fix (<alist-fix> x)) (:@ (not :alist-fix) x))))
         (if look (cdr look) <default-val>)))

     (define <name>-get?$a ((key (:@ :key-p <key-p>)) (x <name>$ap))
       :enabled t
       :guard-debug t
       (mv (<name>-get$a key x)
           (<name>-boundp$a key x)))

     (define <name>-rem$a ((key (:@ :key-p <key-p>)) (x <name>$ap))
       :enabled t
       (acl2::hons-remove-assoc (:@ :key-fix (<key-fix> key)) (:@ (not :key-fix) key)
                                (:@ :alist-fix (<alist-fix> x)) (:@ (not :alist-fix) x)))

     (define <name>-clear$a ((x <name>$ap))
       :enabled t
       (declare (ignorable x))
       nil)


     (define <name>-init$a ((size acl2::maybe-natp)
                            (rehash-size )
                            (rehash-threshold)
                            (x <name>$ap))
       :guard (and (or (not rehash-size) (and (rationalp rehash-size)
                                              (<= 1 rehash-size)))
                   (or (not rehash-threshold) (and (rationalp rehash-threshold)
                                                   (<= 0 rehash-threshold)
                                                   (<= rehash-threshold 1))))
       :enabled t
       (declare (ignorable size rehash-size rehash-threshold x))
       nil)



     (local (define <name>-corr (<name>$c x)
              :non-executable t
              :enabled t
              (and (acl2::alist-equiv (nth 0 <name>$c) x)
                   (no-duplicatesp-equal (acl2::alist-keys x)))))

  
     (local (defthm <alistp>-of-hons-remove-assoc-for-def-hash
              (implies (<alistp> x)
                       (<alistp> (acl2::hons-remove-assoc k x)))
              :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc)))))

     (:@ (or :key-p :val-p)
      (local (defthm defhash-<alistp>-of-hons-put-assoc
               (implies (and (:@ :key-p (<key-p> key))
                             (:@ :val-p (<val-p> val))
                             (<alistp> x))
                        (<alistp> (acl2::hons-put-assoc key val x)))
               :hints(("Goal" :in-theory (enable acl2::hons-put-assoc))))))
     
  
     (acl2::defabsstobj-events <name>
       :foundation <name>$c
       :corr-fn <name>-corr
       :recognizer (<name>p :logic <name>$ap :exec <name>$cp)
       :creator (create-<name> :logic create-<name>$a)
       :exports ((<name>-put :exec <name>-ht$c-put)
                 (<name>-get :exec <name>-ht$c-get)
                 (<name>-boundp :exec <name>-ht$c-boundp)
                 (<name>-get? :exec <name>-ht$c-get?)
                 (<name>-rem :exec <name>-ht$c-rem)
                 (<name>-clear :exec <name>-ht$c-clear)
                 (<name>-init :exec <name>-ht$c-init)))

     

     (defxdoc <name>
       :parents <parents>
       :short (or <short>
                  "Abstract stobj: logically a duplicate-free @('<ALISTP>') alist, implemented as a hash table.")
       :long (or <long>
                 "<p>This is a simple abstract stobj hash table, introduced by @(see stobjs::def-hash).</p>"))))


(defun def-hash-fn (name alistp alist-fix
                         key-p key-fix
                         val-p val-fix
                         default-val
                         type-decl hash-test init-size
                         rename pkg-sym
                         parents short long)
  (declare (xargs :mode :program))
  (b* (((unless (and (symbolp name)
                     (not (keywordp name))))
        (er hard? 'def-hash "Invalid stobj name: ~x0" name))
       ((unless (implies key-fix key-p))
        (er hard? 'def-hash "If :key-fix is supplied, :key-p must also be"))
       ((unless (implies val-fix val-p))
        (er hard? 'def-hash "If :val-fix is supplied, :val-p must also be"))
       (type-decl (or type-decl (if val-p
                                    `(satisfies ,val-p)
                                  t)))
       (pkg-sym (or pkg-sym name))
       (features (append (and key-p '(:key-p))
                         (and key-fix '(:key-fix))
                         (and val-p '(:val-p))
                         (and val-fix '(:val-fix))
                         (and alist-fix '(:alist-fix))))
       (symsubst `((<name> . ,name)
                   (<alistp> . ,alistp)
                   (<alist-fix> . ,alist-fix)
                   (<key-p> . ,key-p)
                   (<key-fix> . ,key-fix)
                   (<val-p> . ,val-p)
                   (<val-fix> . ,val-fix)
                   (<default-val> . ,default-val)
                   (<type-decl> . ,type-decl)
                   (<hash-test> . ,hash-test)
                   (<init-size> . ,init-size)
                   (<parents> . ,parents)
                   (<short> . ,short)
                   (<long> . ,long)))
       (strsubst (acl2::tmpl-symbol-alist-to-str-alist symsubst))
       (tmpl (template-subst *def-hash-template*
                             :features features
                             :atom-alist symsubst
                             :str-alist strsubst
                             :string-str-alist strsubst
                             :pkg-sym pkg-sym)))
    (if rename
        (sublis rename tmpl)
      tmpl)))
                 

(defmacro def-hash (name &key
                         (alistp 'alistp)
                         alist-fix
                         key-p key-fix
                         val-p val-fix
                         default-val
                         type-decl
                         (hash-test 'equal)
                         init-size
                         rename pkg-sym
                         parents short long)
  (def-hash-fn name alistp alist-fix
    key-p key-fix
    val-p val-fix
    default-val
    type-decl hash-test init-size
    rename pkg-sym
    parents short long))



