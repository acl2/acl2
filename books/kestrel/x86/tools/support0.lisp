; Supporting utilities for x86 reasoning
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

;; Maybe deprecate this book if something like this is added to the model

(include-book "projects/x86isa/tools/execution/init-state" :dir :system)
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/logbitp-bounds" :dir :system))

;; ;; Intialize the x86 state and set up 64-bit execution.  Returns (mv error-flag x86)
;; (defun init-x86-state-64 (status start-addr halt-addr gprs ctrs msrs flags mem x86)
;;   (declare (xargs :stobjs x86
;;                   :guard (and (canonical-address-p start-addr)
;;                               (canonical-address-p halt-addr)
;;                               (rgfi-alistp gprs)
;;                               (ctri-alistp ctrs)
;;                               (msri-alistp msrs)
;;                               (n64p flags)
;;                               (n64p-byte-alistp mem))))
;;   (b* (((mv flg x86)
;;         (init-x86-state STATUS START-ADDR HALT-ADDR GPRS CTRS MSRS FLAGS MEM X86))
;;        ((when flg) (mv t x86))
;;        ;; The following two updates to X86 make 64-BIT-MODEP true.
;;        ;; The resulting state does not necessarily satisfy
;;        ;; expected invariants of the processor state,
;;        ;; but it suffices for the proof to go through.
;;        ;; set IA32_EFER.LMA to 1:
;;        (ia32_efer (n12 (msri *ia32_efer-idx* x86)))
;;        (ia32_efer (n64 (!ia32_efer-slice :ia32_efer-lma 1 ia32_efer)))
;;        (x86 (!msri *ia32_efer-idx* ia32_efer x86))
;;        ;; set CS.L to 1 (TODO: Improve this?):
;;        (x86 (!seg-hiddeni *cs* (expt 2 105) x86))
;;        )
;;     (mv nil x86)))
