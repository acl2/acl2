; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2018, Shilpi Goel
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
; Shilpi Goel         <shigoel@gmail.com>

(in-package "X86ISA")

;; ----------------------------------------------------------------------

(local (xdoc::set-default-parents cpuid))

(defconst *fp-simd-feature-flags*
  '(:mmx :sse :sse2 :sse3 :ssse3 :sse4.1 :sse4.2))

(defconst *avx512-feature-flags*
  '(:avx512f
    :avx512dq :avx512_ifma
    :avx512pf :avx512er ;; PF and ER only on Intel Xeon Phi
    :avx512cd :avx512bw :avx512vl :avx512_vbmi
    :avx512_4fmaps :avx512_4vnniw ;; only on Intel Xeon Phi
    ))

(defconst *mode-feature-flags*
  '(:vmx :smx :sgx))

(include-book "defsort/defsort" :dir :system)

(defconst *misc-feature-flags*
  '(:1g-pages
    :acpi :adx 
    ;; The following flag was listed as AESNI in the CPUID instruction
    ;; description, but on other instructions' pages, it is listed as AES.
    :aes
    :apic :avx512-state
    :avx-state :bmi1 :bmi2 :clflushopt :clfsh
    :clwb :cmov :cmpxchg16b :cnxt-id :cx8 :dca :de
    :dep-fpu-cs-ds :ds :ds-cpl :dtes64 :eist
    :execute-disable :f16c :fdp_excptn_only :fma
    :fpu :fsgsbase :fxsr :hle :htt :ia32_tsc_adjust
    :ia32_xss_0 :ia32_xss_1 :intel64 :invpcid
    :lahf-sahf :lzcnt :mawau :mca :mce :monitor
    :movbe :mpx :mpx-state :msr :mtrr :ospke :osxsave
    :pae :pat :pbe :pcid :pclmulqdq :pdcm :pge :pkru
    :pku :popcnt :prefetchwt1 :prfchw :proc-trace :pse
    :pse-36 :psn :rdpid :rdrand :rdseed :rdt-a :rdt-m
    :rdtscp :rep-movsb-stosb :rtm :sdbg :sep :sgx1
    :sgx2 :sgx_lc :pks :sha :smap :smep :ss :sse-state
    :syscall-sysret :tm :tm2 :tsc :tsc-deadline
    :umip :vme :x2pic :x87-state :xgetbv :xsave
    :xsavec :xsaveopt :xss :xtpr-up-ctrl
    :maxphyaddr :linearaddr
    :cet :la57))

(defconst *supported-feature-flags*
  (append *fp-simd-feature-flags*
	  (list :avx :avx2 :bmi1 :bmi2)
	  *avx512-feature-flags*
	  *mode-feature-flags*
	  *misc-feature-flags*))

;; ----------------------------------------------------------------------
