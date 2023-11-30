; Top book for x86 binary parsing sub-library
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "parser-utils")
(include-book "parse-pe-file")
(include-book "parse-mach-o-file")
(include-book "parse-elf-file")
(include-book "parse-executable")

(include-book "elf-tools")
(include-book "mach-o-tools")
(include-book "pe-tools")
(include-book "parsed-executable-tools")
