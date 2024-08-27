; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) May - August 2023, Regents of the University of Texas
; Copyright (C) August 2023 - May 2024, Yahya Sohail
; Copyright (C) May 2024 - August 2024, Intel Corporation

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
; Yahya Sohail        <yahya.sohail@intel.com>

(in-package "X86ISA")

(include-book "centaur/bitops/ihsext-basics" :dir :system)

(defsection
  tty
  :parents (peripherals)
  :short "A TTY device for the @('x86isa')."
  :long "<p>In our effort to boot Linux on the @('x86isa') model, it was desirable
  to have a TTY device to allow us to interact with Linux running on the
  machine, like one would interact at a shell with any Linux machine. Instead
  of emulating an existing TTY device, we implement a custom TTY device and
  implement a Linux driver for it so we could use it under Linux. This device,
  like all other peripherals, is only available when the
  @('enable-peripherals') field of the @('x86') stobj is set to @('t').</p>

  <h3>Semantics</h3>
  <p>Logically this TTY device reads bytes from the list @('tty-in') field on
  the @('x86') stobj and writes bytes to the list in the @('tty-out') field.
  The output in @('tty-out') ends up being in reversed order because new bytes
  are consed onto the front rather than appended to the end.</p>

  <p>By default, this is also how the TTY device behaves in execution. Since
  such an implementation is difficult to interact with, we provide an
  additional @('tty-raw.lsp') Common Lisp file which may be included with
  @('include-raw') (which requires an active trust tag) that opens a TCP socket
  (on localhost port 6444) and smashes the definitions of @(tsee read-tty) and
  @(tsee write-tty) so that the TTY reads and writes to the opened TCP socket.
  This allows interaction with the model by connecting to the TCP socket with
  programs like netcat or socat. @('tty-raw.lisp') depends on CCL specific code
  to open the socket, so it only works on ACL2 running under CCL.</p>

  <h3>Interface</h3>
  <p>The TTY device presents a simple memory mapped interface to software. If a
  byte is available for reading the byte at memory address @('#x3FB') is set to
  1. The byte may be read from memory address @('#x3FA'). Once the byte has
  been read, the software should set @('#x3FB') to 0 to allow TTY to write a
  new byte. If another byte is present in the buffer, it will be available in
  memory before the next instruction is executed.</p>

  <p>Writing to the TTY is similar. To write a byte, write the byte to
  @('#x3F8') and then write a non-zero value to @('#x3F9'). Before the next
  instruction is executed, the TTY device will set @('#x3F9') to zero.</p>")

(define tty-bufferp (x)
  :parents (tty)
  :short "Recognizer for the TTY buffers."
  :long "<p>@('tty-bufferp') recognizes buffers which are valid as the
  @('tty-in') and @('tty-out') fields of the @('x86') stobj. These are
  @('true-listp')s which only contain 8-bit unsigned integers.</p>"
  :enabled t
  (or (null x)
      (and (consp x)
           (unsigned-byte-p 8 (car x))
           (tty-bufferp (cdr x)))))

(define tty-buffer-fix (x)
  :returns (fixed tty-bufferp)
  (if (tty-bufferp x)
    x
    nil)
  ///
  (defthm tty-buffer-fix-identity-on-tty-bufferp
          (implies (tty-bufferp x)
                   (equal (tty-buffer-fix x)
                          x))))
