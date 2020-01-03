; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "basics" :ttags (:include-raw :undef-flg :syscall-exec :other-non-det))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ===================================================================

(defsection x86-RoW-WoW-thms

  :parents (proof-utilities)

  :short "Miscellaneous RoW and WoW theorems"
  :long "<p>See @(see state-field-theorems) for a detailed description
  of RoW and WoW theorems.</p>"

  )

(local (xdoc::set-default-parents x86-RoW-WoW-thms))

;; ======================================================================

(defthm assoc-equal-put-assoc-equal-diff
  (equal (assoc-equal x (put-assoc-equal y z ss))
         (if (equal x y)
             (cons x z)
           (assoc-equal x ss))))

(defthm assoc-equal-consp
  (implies (consp (assoc-equal x ss))
           (consp (assoc-equal x (put-assoc-equal x z ss)))))

(local
 (defthm read-x86-file-des-write-x86-file-des-different-indices-helper
   (implies (or (env-alistp env) (not env))
            (env-alistp
             (list
              (cons :file-descriptors
                    (put-assoc-equal
                     fd2 fd2-field
                     (cdr (assoc-equal :file-descriptors env))))
              (cons :file-contents (cdr (assoc-equal :file-contents env)))
              (cons :oracle (cdr (assoc-equal :oracle env))))))
   :hints (("Goal" :in-theory (e/d (env-alistp) ())))))

(defthm read-x86-file-des-write-x86-file-des-different-indices
  (implies (not (equal fd1 fd2))
           (equal (read-x86-file-des fd1 (write-x86-file-des fd2 fd2-field x86))
                  (read-x86-file-des fd1 x86)))
  :hints (("Goal" 
           :cases ((x86p x86))
           :in-theory (e/d (read-x86-file-des
                            read-x86-file-des-logic
                            write-x86-file-des
                            write-x86-file-des-logic)
                           ()))))

(defthm read-x86-file-des-write-x86-file-des-same-indices
  (implies (x86p x86)
           (equal (read-x86-file-des fd (write-x86-file-des fd fd-field x86))
                  (cdr
                   (assoc-equal
                    fd
                    (put-assoc-equal fd fd-field
                                     (cdr (assoc-equal :file-descriptors (env-read x86))))))))
  :hints (("Goal" :in-theory (e/d (read-x86-file-des
                                   write-x86-file-des
                                   read-x86-file-des-logic
                                   write-x86-file-des-logic)
                                  ()))))

(local
 (defthm read-x86-file-des-write-x86-file-des-same-indices-helper
   (implies (or (env-alistp env) (not env))
            (env-alistp
             (list
              (cons :file-descriptors
                    (cdr (assoc-equal :file-descriptors env)))
              (cons
               :file-contents
               (put-assoc-equal name name-field
                                (cdr (assoc-equal :file-contents env))))
              (cons :oracle (cdr (assoc-equal :oracle env))))))
   :hints (("Goal"
            :use ((:instance env-alistp-env (i 0)))
            :in-theory (e/d (env-alistp rip-ret-alistp) ())))))

(defthm read-x86-file-contents-write-x86-file-contents-same-indices
  (equal
   (read-x86-file-contents name (write-x86-file-contents name name-field x86))
   (cdr
    (assoc-equal
     name
     (put-assoc-equal name name-field
                      (cdr (assoc-equal :file-contents (env-read x86)))))))
  :hints (("Goal" :cases ((x86p x86))
           :in-theory (e/d (read-x86-file-contents
                            write-x86-file-contents
                            read-x86-file-contents-logic
                            write-x86-file-contents-logic)
                           ()))))

(defthm read-x86-file-contents-write-x86-file-contents-different-indices  
  (implies (and (not (equal name1 name2))
                (x86p x86))
           (equal (read-x86-file-contents
                   name1 (write-x86-file-contents name2 name-field x86))
                  (read-x86-file-contents name1 x86)))
  :hints (("Goal" :in-theory (e/d (read-x86-file-contents
                                   write-x86-file-contents
                                   read-x86-file-contents-logic
                                   write-x86-file-contents-logic)
                                  ()))))

(defthm read-x86-file-des-write-x86-file-contents
  (equal (read-x86-file-des id (write-x86-file-contents i v x86))
         (read-x86-file-des id x86))
  :hints (("Goal" :in-theory (e/d (read-x86-file-des
                                   read-x86-file-des-logic
                                   write-x86-file-contents
                                   write-x86-file-contents-logic)
                                  ()))))

(defthm read-x86-file-contents-write-x86-file-des
  (equal (read-x86-file-contents name (write-x86-file-des i v x86))
         (read-x86-file-contents name x86))
  :hints (("Goal" :in-theory (e/d (read-x86-file-contents
                                   read-x86-file-contents-logic
                                   write-x86-file-des
                                   write-x86-file-des-logic)
                                  ()))))

(defthm read-x86-file-des-wb-1
  (implies (app-view x86)
           (equal (read-x86-file-des id (mv-nth 1 (wb-1 n addr w value x86)))
                  (read-x86-file-des id x86)))
  :hints (("Goal"
           :in-theory (e/d* (read-x86-file-des read-x86-file-des-logic)
                            ()))))

(defthm read-x86-file-des-wb
  (implies (app-view x86)
           (equal (read-x86-file-des id (mv-nth 1 (wb n addr w value x86)))
                  (read-x86-file-des id x86)))
  :hints (("Goal"
           :use ((:instance read-x86-file-des-wb-1))
           :in-theory (e/d* (read-x86-file-des read-x86-file-des-logic)
                            (wb wb-1 read-x86-file-des-wb-1)))))

(defthm write-x86-file-des-wb
  (implies (app-view x86)
           (equal (write-x86-file-des i v (mv-nth 1 (wb n addr w value x86)))
                  (mv-nth 1 (wb n addr w value (write-x86-file-des i v x86)))))
  :hints (("Goal"
           :in-theory (e/d* (write-x86-file-des write-x86-file-des-logic)
                            ()))))

(defthm read-x86-file-contents-wb-1
  (implies (app-view x86)
           (equal (read-x86-file-contents id (mv-nth 1 (wb-1 n addr w value x86)))
                  (read-x86-file-contents id x86)))
  :hints (("Goal"
           :in-theory (e/d* (read-x86-file-contents read-x86-file-contents-logic)
                            ()))))

(defthm read-x86-file-contents-wb
  (implies (app-view x86)
           (equal (read-x86-file-contents id (mv-nth 1 (wb n addr w value x86)))
                  (read-x86-file-contents id x86)))
  :hints (("Goal"
           :use ((:instance read-x86-file-contents-wb-1))
           :in-theory (e/d* (read-x86-file-contents read-x86-file-contents-logic)
                            (wb wb-1 read-x86-file-contents-wb-1)))))

;; ======================================================================

;; Some rules about alignment-checking-enabled-p:

(defthm alignment-checking-enabled-p-write-x86-file-des
  (equal (alignment-checking-enabled-p (write-x86-file-des i v x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (e/d* (write-x86-file-des write-x86-file-des-logic)
                                   ()))))

(defthm alignment-checking-enabled-p-write-x86-file-contents
  (equal (alignment-checking-enabled-p (write-x86-file-contents i v x86))
         (alignment-checking-enabled-p x86))
  :hints (("Goal" :in-theory (e/d* (write-x86-file-contents write-x86-file-contents-logic)
                                   ()))))

;; ======================================================================

;; Some rules about flags:

(defthm read-x86-file-des-write-user-rflags
  (equal (read-x86-file-des i (write-user-rflags flags mask x86))
         (read-x86-file-des i x86))
  :hints (("Goal" :in-theory (e/d* (write-user-rflags)
                                   (force (force))))))

(defthm read-x86-file-contents-write-user-rflags
  (equal (read-x86-file-contents i (write-user-rflags flags mask x86))
         (read-x86-file-contents i x86))
  :hints (("Goal" :in-theory (e/d* (write-user-rflags)
                                   (force (force))))))

(defthm logbitp-0-and-loghead-1
  (iff (logbitp 0 n) (equal (loghead 1 n) 1))
  :hints (("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                    bitops::ihsext-recursive-redefs)
                                   ()))))

(defthm write-user-rflags-and-xw
  (implies (and (not (equal fld :rflags))
                (not (equal fld :undef)))
           (equal (write-user-rflags flags mask (xw fld index value x86))
                  (xw fld index value (write-user-rflags flags mask x86))))
  :hints (("Goal" :in-theory (e/d* (write-user-rflags)
                                   ((tau-system) force (force))))))

(defthm write-user-rflags-write-user-rflags-when-no-mask
  (implies (x86p x86)
           (equal (write-user-rflags flags1 0 (write-user-rflags flags2 0 x86))
                  (write-user-rflags flags1 0 x86)))
  :hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables) ()))))

(defthm alignment-checking-enabled-p-and-write-user-rflags
  (implies (x86p x86)
           (equal (alignment-checking-enabled-p (write-user-rflags flgs mask x86))
                  (alignment-checking-enabled-p x86)))
  :hints (("Goal" :in-theory (e/d* (rflag-RoWs-enables
                                    write-user-rflags)
                                   ()))))

;; ======================================================================

;; Making some functions untouchable after proving RoW/WoW thms about
;; them:

(push-untouchable (
                   ;; Accessors
                   env$inline
                   env$a
                   env$c
                   env-read-logic
                   env-write-logic
                   read-x86-file-des-logic
                   read-x86-file-contents-logic
                   ;; Updaters
                   !env$inline
                   !env$a
                   !env$c
                   write-x86-file-des-logic
                   delete-x86-file-des-logic
                   write-x86-file-contents-logic
                   delete-x86-file-contents-logic
                   pop-x86-oracle-logic
                   !undef$inline
                   )
                  t)

;; ======================================================================
