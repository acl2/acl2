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


;; Performance Testing for our Utilities.
;;
;; The results mentioned in this file were obtained on a 2.8 GHz Pentium D
;; (dual core) running Linux.  This is not a certifiable book, nor can you
;; expect to just run acl2 < test-utilities.lisp because some of the tests
;; segfault and such.
;;
;; All of these tests have been run inside of ACL2.  Actual results in raw
;; lisps might be different.  Particularly, CMUCL results might improve a lot
;; with inlining.

(include-book "utilities")

(in-package "MILAWA")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(defund integers (n acc)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n)
      acc
    (integers (- n 1)
              (cons n acc))))

(defun fast-firstn$ (n x acc)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n)
      acc
    (fast-firstn$ (- n 1) (cdr x) (cons (car x) acc))))


(ACL2::comp t)

:q




;; Performance of LEN, FAST-LEN, and SAME-LEN for comparing equal-length lists.

(compile
 (defun test-len (n times)
   (let ((test (MILAWA::integers n nil)))
     (time
      (loop for i fixnum from 1 to times do
            (equal (MILAWA::len test)
                   (MILAWA::len test)))))))

(compile
 (defun test-fast-len (n times)
   (let ((test (MILAWA::integers n nil)))
     (time
      (loop for i fixnum from 1 to times do
            (equal (MILAWA::fast-len test 0)
                   (MILAWA::fast-len test 0)))))))

(compile
 (defun test-same-len (n times)
   (let ((test (MILAWA::integers n nil)))
     (time
      (loop for i fixnum from 1 to times do
            (MILAWA::same-len test test))))))



;; Performance Tests (on Ivan)    ACL2-CMUCL   ACL2-GCL

(test-len      5 20000000)  ; ==> 15.20        33.30
(test-fast-len 5 20000000)  ; ==> 11.93 (22%)  32.05 (4%)
(test-same-len 5 20000000)  ; ==>  0.57 (96%)  0.35  (99%)

(test-len      10 10000000) ; ==> 15.82        34.06
(test-fast-len 10 10000000) ; ==> 11.43 (27%)  31.86 (7%)
(test-same-len 10 10000000) ; ==>  0.59 (96%)  0.29  (99%)

(test-len      100 1000000) ; ==> 14.67        35.99
(test-fast-len 100 1000000) ; ==> 10.76 (27%)  30.45 (15%)
(test-same-len 100 1000000) ; ==>  0.29 (98%)  0.26  (99%)

(test-len      1000 100000) ; ==> 15.22        36.81
(test-fast-len 1000 100000) ; ==> 10.63 (30%)  30.42 (17%)
(test-same-len 1000 100000) ; ==>  0.24 (98%)   0.23 (99%)

;; [[ note: gcl starts gc'ing fixnums here for some reason ]]

(test-len      10000 10000) ; ==> 14.97        44.79
(test-fast-len 10000 10000) ; ==> 10.89 (27%)  38.54 (14%)
(test-same-len 10000 10000) ; ==>  0.46 (97%)   0.50 (99%)

(test-len      100000 1000) ; ==> 15.62        47.08
(test-fast-len 100000 1000) ; ==> 10.75 (31%)  38.52 (18%)
(test-same-len 100000 1000) ; ==>  0.48 (97%)   0.59 (99%)

(test-len      1000000 100) ; ==> 15.02        segfault
(test-fast-len 1000000 100) ; ==> 10.29 (31%)  42.87
(test-same-len 1000000 100) ; ==>  0.46 (97%)   0.54

(test-len      10000000 10) ; ==> overflow     segfault
(test-fast-len 10000000 10) ; ==> 10.34        45.19
(test-same-len 10000000 10) ; ==>  0.48         0.52




;; Performance of APP, FAST-APP, and REVAPPEND for joining a list to itself.

(compile
 (defun test-app (n times)
   (let ((test (MILAWA::integers n nil)))
     (time
      (loop for i fixnum from 1 to times do
            (MILAWA::app test test))))))

(compile
 (defun test-fast-app (n times)
   (let ((test (MILAWA::integers n nil)))
     (time
      (loop for i fixnum from 1 to times do
            (MILAWA::fast-app test test))))))

(compile
 (defun test-revappend (n times)
   (let ((test (MILAWA::integers n nil)))
     (time
      (loop for i fixnum from 1 to times do
            (MILAWA::revappend test test))))))




;; Performance Tests (on Ivan)     ACL2-CMUCL   ACL2-GCL

(test-app       10 10000000) ; ==> 20.88        8.47
(test-fast-app  10 10000000) ; ==> 19.87 (5%)   7.68 (9%)
(test-revappend 10 10000000) ; ==>   9.6 (54%)  3.58 (58%)

(test-app       100 1000000) ; ==> 21.74        10.57
(test-fast-app  100 1000000) ; ==> 19.14 (11%)  6.89 (35%)
(test-revappend 100 1000000) ; ==>  9.47 (56%)  3.33 (68%)

(test-app       1000 100000) ; ==> 20.87        10.59
(test-fast-app  1000 100000) ; ==> 18.79 (10%)  6.41 (39%)
(test-revappend 1000 100000) ; ==>  9.45 (55%)  3.08 (71%)

(test-app       10000 10000) ; ==> 21.72        11.02
(test-fast-app  10000 10000) ; ==> 19.45 (10%)  6.46 (41%)
(test-revappend 10000 10000) ; ==>  9.61 (55%)  3.08 (72%)

(test-app       100000 1000) ; ==> 30.34        11.87
(test-fast-app  100000 1000) ; ==> 23.07 (24%)  6.77 (43%)
(test-revappend 100000 1000) ; ==> 10.77 (65%)  3.26 (73%)

(test-app       1000000 100) ; ==> 80.53        segfault
(test-fast-app  1000000 100) ; ==> 42.18 (48%)  12.71
(test-revappend 1000000 100) ; ==> 14.26 (82%)  5.75





(compile
 (defun test-rev (n times)
   (let ((test (MILAWA::integers n nil)))
     (time
      (loop for i fixnum from 1 to times do
            (MILAWA::rev test))))))


;; We'll use the same data from revappend above, since it doesn't really matter
;; what we revappend onto.  Rrev is so slow we can't do the same number of
;; iterations.  We take this into account and multiply the times below by the
;; factors on the right.  The data is:
;;   [raw time for rev]s (revappend is faster by this %)


;;                           ACL2-CMUCL       ACL2-GCL
(test-rev 10 10000000) ; ==> 69.83 (86%)      27.3  (86%)       ; [1x]
(test-rev 100  100000) ; ==> 52.55 (98%)      20.17 (98%)       ; [10x]
(test-rev 1000   1000) ; ==> 59.88 (99.8%)    20.05 (99.8%)     ; [100x]
(test-rev 10000    10) ; ==> 92.88 (99.99%)   19.98 (99.98%)    ; [1000x]




(compile
 (defun test-remove-all (n times)
   (let ((test (MILAWA::integers n nil)))
     (time
      (loop for i from 1 to times do
            (MILAWA::remove-all 1 test))))))

(compile
 (defun test-fast-remove-all$ (n times)
   (let ((test (MILAWA::integers n nil)))
     (time
      (loop for i from 1 to times do
            (MILAWA::fast-remove-all$ 1 test nil))))))


;;                                        ACL2-CMUCL     ACL2-GCL
(test-remove-all       10 10000000) ; ==> 12.45          5.28
(test-fast-remove-all$ 10 10000000) ; ==> 10.42 (16%)    5.30 (.3% worse)

(test-remove-all       100 1000000) ; ==> 12.52          5.75
(test-fast-remove-all$ 100 1000000) ; ==> 10.89 (13%)    4.55 (20%)

(test-remove-all       1000 100000) ; ==> 12.93          5.54
(test-fast-remove-all$ 1000 100000) ; ==> 11.04 (15%)    4.77 (14%)

(test-remove-all       10000 10000) ; ==> 12.86          5.10
(test-fast-remove-all$ 10000 10000) ; ==> 10.88 (15%)    4.70 (8%)

(test-remove-all       100000 1000) ; ==> 14.42          7.18
(test-fast-remove-all$ 100000 1000) ; ==> 12.16 (16%)    5.04 (30%)

(test-remove-all       1000000 100) ; ==> 25.51          segfault
(test-fast-remove-all$ 1000000 100) ; ==> 16.04 (37%)    7.47

(test-remove-all       10000000 10) ; ==> overflow       segfault
(test-fast-remove-all$ 10000000 10) ; ==> 30.6           inf. loop (gcl bug?)



