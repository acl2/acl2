; Verification of a RISC-V program that adds 2 numbers
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "R")

;; TODO: Move to examples subdir

;; STATUS: COMPLETE, needs automation

(include-book "support")
(include-book "read-and-write")
(include-book "kestrel/x86/parsers/elf-tools" :dir :system)
(include-book "kestrel/x86/parsers/parse-executable" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/bv/bvchop" :dir :system)) ; for acl2::mod-becomes-bvchop-when-power-of-2p
(local (include-book "kestrel/bv/rules" :dir :system)) ; for ACL2::BVPLUS-OF-LOGEXT-ARG3, etc.
;(include-book "kestrel/x86/assumptions-new" :dir :system) ; reduce!  has ttags!

(local (in-theory (enable acl2::mod-becomes-bvchop-when-power-of-2p)))

(local (in-theory (disable logext)))

(acl2::defconst-x86 *executable* "add.elf32")

;(acl2::parse-executable "add-32im-ilp32" state)

;; (acl2::elf64-regions-to-load *executable*)

;(x::elf-info "add-32im-ilp32")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; after stepping, we extract the return value and prove that it is the correct sum
;; todo: also characterize the rest of the state components
(defthm add-correct
  (implies (and (equal (read32-pc stat) #x101b0) ; this is the offset of "f"
                (equal (read 4 #x101b0 stat) #xfe010113) ; these bytes are from looking at add-32im-ilp32.objdump for function <f>
                (equal (read 4 #x101b4 stat) #x00112e23)
                (equal (read 4 #x101b8 stat) #x00812c23)
                (equal (read 4 #x101bc stat) #x02010413)
                (equal (read 4 #x101c0 stat) #xfea42623)
                (equal (read 4 #x101c4 stat) #xfeb42423)
                (equal (read 4 #x101c8 stat) #xfec42703)
                (equal (read 4 #x101cc stat) #xfe842783)
                (equal (read 4 #x101d0 stat) #x00f707b3)
                (equal (read 4 #x101d4 stat) #x00078513)
                (equal (read 4 #x101d8 stat) #x01c12083)
                (equal (read 4 #x101dc stat) #x01812403)
                (equal (read 4 #x101e0 stat) #x02010113)
                (equal (read 4 #x101e4 stat) #x00008067)
                (not (error32p stat))
                ;; (state32p xx)
                ;; The code is disjoint from the area the stack will grow into:
                (x::disjoint-regions32p 56 #x101b0 56 (+ -32 (sp stat)))
                )
           (equal (a0 (step32n 14 stat))
                  (bvplus 32 (a0 stat) (a1 stat))))
  :hints (("Goal" :expand ((:free (n stat) (step32n n stat))))))
