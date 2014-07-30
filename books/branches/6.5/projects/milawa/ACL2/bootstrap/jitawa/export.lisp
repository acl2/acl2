; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "compatible-write-file")
(include-book "memory-mgmt-raw")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(acl2::set-debugger-enable t)
(acl2::set-max-mem (* 56 (expt 2 30)))


(defun milawa-read-files (files)
  (declare (xargs :mode :program))
  (if (consp files)
      (cons (milawa-read-file (car files))
            (milawa-read-files (cdr files)))
    nil))

(defconst *events-files*
  '("../../../Proofs/utilities.events"
    "../../../Proofs/logic.events"
    "../../../Proofs/level2.events"
    "../../../Proofs/level3.events"
    "../../../Proofs/level4.events"
    "../../../Proofs/level5.events"
    "../../../Proofs/level6.events"
    "../../../Proofs/level7.events"
    "../../../Proofs/level8.events"
    "../../../Proofs/level9.events"
    "../../../Proofs/level10.events"
    "../../../Proofs/level11.events"
    "../../../Proofs/user.events"))

(defconst *events*
  (simple-flatten (milawa-read-files *events-files*)))




(defun convert-events (events acc)
  (declare (xargs :mode :program))
  (if (not (consp events))
      acc
    (let* ((entry (car events))
          (acc (cond
                ((equal (first entry) 'VERIFY)
                 (let* ((name      (second entry))
                        (formula   (third entry))
                        (filename  (str::cat "../../../" (fourth entry)))
                        (proof     (car (milawa-read-file filename)))
                        (new-event (acl2::hons-list 'VERIFY name formula proof)))
                   (acl2::hons new-event acc)))

                ((equal (first entry) 'DEFINE)
                 (let* ((name     (second entry))
                        (formals  (third entry))
                        (body     (fourth entry))
                        (measure   (fifth entry))
                        ;; (inlinep  (memberp name functions-to-inline))
                        (filename (str::cat "../../../" (ACL2::seventh entry)))
                        (proofs   (car (milawa-read-file filename)))
                        (new-event (acl2::hons-list 'DEFINE name formals body measure proofs)))
                   (acl2::hons new-event acc)))

                ((or (equal (first entry) 'SKOLEM)
                     (equal (first entry) 'SWITCH))
                 (acl2::hons entry acc))

                ((equal (first entry) 'FINISH) ;; drop any "finish" events
                 acc)

                (t
                 (acl2::er acl2::hard? 'convert-events
                           "Bad event: ~x0.~%" entry)))))
      (convert-events (cdr events) acc))))


;; looks like there are about 525 million unique conses
;; we can probably reduce this number.
;; there is some lousy memory management stuff happening in the default acl2h.
;; what are we fixing with memory-mgmt-raw in stp?
(ACL2::hons-resize :addr-ht 650000000)

(defconst *new-events*
  ;; This took about 4400 seconds on fv-1.
  ;; Allocated 28 GB.
  ;; aha, with the fixed memory management it only takes 2500 sec
  (acl2::reverse (acl2::time$ (convert-events *events* nil))))

;; Throw away massive address table
(acl2::time$ (acl2::hons-clear nil))
(acl2::time$ (acl2::hons-resize :addr-ht 1000))

;; with lousy mem mgmt, 24.6 gb allocated, 15 gb freed
;; with fixed mem mgmt, 53.6 gb allocated, 44 gb freed
(acl2::gc$)



(defun do-save ()
  (declare (xargs :mode :program))
  ;; compact-write-file took about 4800 seconds on fv-1.
  ;; (acl2::time$ (compact-write-file *new-events* "full.new-events")))
  (acl2::time$
   ;; this was taking about 4400 seconds, well, probably more like 3000
   ;; with the fixed memory mgmt, it's only 1170 seconds
   (acl2::compatible-write-file *new-events*
                                "full.events"
                                650000000)))

(do-save)


#||

;; other commands to generate short files of fewer events

(defun do-save2 ()
  (declare (xargs :mode :program))
  (acl2::time$
   (acl2::compatible-write-file (firstn 100 *new-events*)
                                "100.events"
                                650000000)))


(do-save2)

(defun do-save3 ()
  (declare (xargs :mode :program))
  (acl2::time$
   (acl2::compatible-write-file (firstn 1000 *new-events*)
                                "1000.events"
                                650000000)))

(do-save3)

||#
