; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Benchmarks for the hash functions.
;
; Usage: start ACL2 in this directory (the customization file loads the
; package), then:
;
;   (ld "benchmark.lsp")
;
; Loading runs a quick smoke suite. For the full suite, which writes CSV
; to results/, evaluate afterwards, in raw Lisp:
;
;   (hash-bench::run-full)
;
; For stable numbers, run on a quiet machine, ideally pinned to a core
; (taskset -c 2) with the performance governor.

(in-package "HASH")

(include-book "../jenkins-defs")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :benchmarking)
(set-raw-mode t)

(load "../../benchmark/harness.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(load "driver.lsp")

