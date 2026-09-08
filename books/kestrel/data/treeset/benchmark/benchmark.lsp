; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Benchmarks for treesets, comparing against std/osets, fast alists, and
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
;   (treeset-bench::run-full)
;
; Treap shape statistics (also included in run-full) are available
; standalone as (treeset-bench::depth-report).
;
; For stable numbers, run on a quiet machine, ideally pinned to a core
; (taskset -c 2) with the performance governor.

(in-package "TREESET")

(include-book "../set-defs")
(include-book "../in-defs")
(include-book "../insert-defs")
(include-book "../delete-defs")
(include-book "../union-defs")
(include-book "../intersect-defs")
(include-book "../diff-defs")
(include-book "../to-oset-defs")
(include-book "../hash-defs")

(include-book "std/osets/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :benchmarking)
(set-raw-mode t)

(load "../../benchmark/harness.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(load "driver.lsp")
