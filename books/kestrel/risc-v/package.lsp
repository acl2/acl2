; RISC-V Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (acoglio on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defpkg "RISCV" (append (set-difference-eq *std-pkg-symbols*
                                           '(error
                                             pi
                                             step))
                        '(bool
                          defxdoc+
                          impossible
                          logext
                          loghead
                          sbyte32
                          sbyte32p
                          sbyte64
                          sbyte64p
                          ubyte1
                          ubyte1p
                          ubyte3
                          ubyte3p
                          ubyte3-fix
                          ubyte4
                          ubyte4p
                          ubyte4-fix
                          ubyte5
                          ubyte5p
                          ubyte5-fix
                          ubyte5-equiv
                          ubyte6
                          ubyte6p
                          ubyte6-fix
                          ubyte7p
                          ubyte8
                          ubyte8p
                          ubyte8-fix
                          ubyte12
                          ubyte12p
                          ubyte12-fix
                          ubyte16
                          ubyte16p
                          ubyte16-fix
                          ubyte20
                          ubyte20p
                          ubyte20-fix
                          ubyte32
                          ubyte32p
                          ubyte32-fix
                          ubyte64
                          ubyte64p
                          ubyte64-fix
                          ubyte128
                          ubyte128p
                          ubyte8-list
                          ubyte8-listp
                          ubyte64-list
                          ubyte64-listp
                          bitops::part-select)))
