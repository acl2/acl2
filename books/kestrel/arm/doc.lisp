; A formal model of the ARM32 CPU
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "portcullis")
(include-book "xdoc/top" :dir :system)
(include-book "kestrel/utilities/xdoc-paras" :dir :system)

(acl2::defxdoc arm32
      :short "A formal model of the ARM32 CPU."
      :parents (software-verification hardware-verification)
      :long (xdoc::topparas
"The ARM32 model is an in-progress formal model of a 32-bit ARM CPU.  It
attempts to formalize (some of) the <b>ARM Architecture Reference Manual,
ARMv7-A and ARMv7-R edition</b>, which focuses on versions 4 through 7 of the
ARM Architecture.

The ARM32 model formalizes the state of the ARM32 CPU as well as the decoding and
execution of instructions (how each instruction affects the CPU state).

See the individual files in this directory for more documentation.

This model is intended for use with a forthcoming ARM32 variant of the @(see
acl2::axe) toolkit."

))
