; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Benchmarks for treemaps, comparing against std/omaps, fast alists, and
; raw Common Lisp hash tables on identical input streams.
;
; Usage: start ACL2 in this directory (the customization file loads the
; package), then:
;
;   (ld "benchmark.lsp")
;
; Loading runs a quick smoke suite. For the full suite, which writes CSV
; to results/, evaluate afterwards, in raw Lisp:
;
;   (treemap-bench::run-full)
;
; Treap shape statistics (also included in run-full) are available
; standalone as (treemap-bench::depth-report).
;
; For stable numbers, run on a quiet machine, ideally pinned to a core
; (taskset -c 2) with the performance governor.

(in-package "TREEMAP")

(include-book "../lookup-defs")
(include-book "../update-defs")
(include-book "../delete-defs")
(include-book "../update-star-defs")
(include-book "../to-omap-defs")

(include-book "std/omaps/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :benchmarking)
(set-raw-mode t)

(load "../../benchmark/harness.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(load "driver.lsp")
