; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

; Import test for the MIR importer on an extracted AES-128 crate: parse the
; serialized crate, expand its sharing, map it to a MIR program, and check that
; the result is exactly the committed fixture @('*aes-fixslice-program*').  So
; this book validates that the importer, run on the committed sample, reproduces
; the fixture that the interpreter tests (../mir/tests/aes-fixslice) run on.
;
; The committed input is the gzipped ULLBC dump
; ../samples/aes_ullbc_elaborated.json.gz (see ../samples/README.md); it is
; decompressed here at certification time with gunzip, which is why this book
; has a trust tag.  The decompressed .json is a git-ignored build product.
; Certification requires the sample and gzip: if the .gz is missing, or gzip
; is unavailable or fails, this book fails rather than skipping silently.

(include-book "ullbc-to-mir")
(include-book "../mir/tests/aes-fixslice-program")
(include-book "kestrel/json-parser/parse-json-file" :dir :system)

(defttag :rust-aes-import-test)

; (depends-on "../samples/aes_ullbc_elaborated.json.gz")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(make-event
 (b* ((gz "../samples/aes_ullbc_elaborated.json.gz")
      (json "../samples/aes_ullbc_elaborated.json")
      (ctx 'aes-import-test)
      ((mv gz? acl2::state) (acl2::file-existsp gz acl2::state))
      ((unless gz?)
       (acl2::er acl2::soft ctx
                 "Required sample file ~x0 is missing; it is committed to the repository (see ../samples/README.md)."
                 gz))
      ((mv gzerp & acl2::state)
       (acl2::sys-call+ "gzip" (list "-dkf" gz) acl2::state))
      ((when gzerp)
       (acl2::er acl2::soft ctx
                 "Decompressing ~x0 with `gzip -dkf` failed (exit status ~x1); is gzip installed and on PATH?"
                 gz gzerp))
      ((mv json? acl2::state) (acl2::file-existsp json acl2::state))
      ((unless json?)
       (acl2::er acl2::soft ctx
                 "`gzip -dkf ~x0` did not produce ~x1." gz json))
      ((mv perp parsed acl2::state) (acl2::parse-file-as-json json acl2::state))
      ((when perp)
       (acl2::er acl2::soft ctx "Parsing ~x0 as JSON failed: ~x1." json perp))
      ((mv verp jval) (json::parsed-to-value parsed))
      ((when verp)
       (acl2::er acl2::soft ctx
                 "Converting the parsed JSON to a value failed: ~x0." verp))
      ((mv ierp program) (ullbc-to-mir jval))
      ((when ierp)
       (acl2::er acl2::soft ctx "Importing the MIR failed: ~x0." ierp))
      ((unless (equal program *aes-fixslice-program*))
       (acl2::er acl2::soft ctx
                 "The imported MIR program does not match the committed fixture *aes-fixslice-program* (see ../mir/tests/aes-fixslice-program.lisp); regenerate the fixture if the importer or sample changed intentionally.")))
   (acl2::value '(acl2::value-triple :aes-import-matches-fixture))))
