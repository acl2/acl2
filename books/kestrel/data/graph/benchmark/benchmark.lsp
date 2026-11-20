; Copyright (C) 2026 by Kestrel Institute
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Benchmarks for the graph operations whose execution visits every node of
; the graph or every element of a set: predecessors, predecessors-of-set,
; successors-of-set, and transpose. Alongside the timings, a stack report
; finds the graph size at which each of them exhausts the control stack.
;
; Usage: start ACL2 in this directory (the customization file loads the
; package), then:
;
;   (ld "benchmark.lsp")
;
; Loading runs a quick smoke suite. For the full suite, which writes CSV
; to results/ and ends with the stack report, evaluate afterwards, in raw
; Lisp:
;
;   (graph-bench::run-full)
;
; The stack report is also available standalone as
; (graph-bench::stack-report).
;
; For stable numbers, run on a quiet machine, ideally pinned to a core
; (taskset -c 2) with the performance governor.

(in-package "GRAPH")

(include-book "../defs")

(include-book "kestrel/data/tset/insert-defs" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defttag :benchmarking)
(set-raw-mode t)

(load "../../benchmark/harness.lsp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(load "driver.lsp")
