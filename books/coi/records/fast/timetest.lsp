; Memories: Array-like Records for ACL2
; Copyright (C) 2005-2006 Kookamara LLC
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
;
; COI Version.  See books/data-structures/memories/ for the original version.

; timetest.lisp 
;
; This is a simple timing test program.  After running 'make' to compile the 
; memory library, you can feed this script to ACL2 using:
;
;    acl2 < timetest.lisp
;
; and you will see some very rough performance figures.  
;
; For rough comparison purposes, I get the following averages on Dimebox, a 
; Pentium 4 2.8 GHz machine running Linux.
;
; ACL2-2.9.2 on GCL 2.6.6 (memory size = 2^64)
;
;   295,000 loads per second
;   108,000 stores per second
;
; ACL2-2.9.2 on Allegro (memory size = 2^64)
;
;   438,000 loads per second 
;   102,000 stores per second
  
(include-book "memory")
(in-package "MEM")




; For write tests we will just zero out a block of memory.  It doesn't really
; matter what addresses we use, because they're all the same depth from the
; root.  For read tests, we'll just sequentially scan a block of memory. 

(defun zero-memory (i mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p i mem)))
           (type (signed-byte 29) i))                              
  (if (mbe :logic (zp i)
           :exec (= i 0))
      (store 0 0 mem)
    (zero-memory (the-fixnum (1- i))
                 (store i 0 mem))))

(defun scan-memory (i mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p i mem)))
           (type (signed-byte 29) i))
  (if (mbe :logic (zp i)
           :exec (= i 0))
      (load 0 mem)
    (let ((element (load i mem)))
      (declare (ignore element))
      (scan-memory (the-fixnum (1- i)) mem))))
                  
                  


:comp t
:q

; Turn off garbage collection messages in GCL

#+gcl
(setq SI::*notify-gbc* nil)

#+gcl
(setq SI::*gbc-notify* nil)

#+gcl
(setq SI::*gbc-messages* nil)


(defconst *memory-bits* 16)
(defconst *test-size* 65535)
(defconst *iters* 100)

(cw "Creating a memory with capacity of 2^~x0 elements." *memory-bits*)

(defconst *base-mem* (MEM::new (expt 2 *memory-bits*)))



(cw "Repeatedly timing ~x0 loads:" (* *test-size* *iters*))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::scan-memory *test-size* *base-mem*))
              nil))




(cw "Repeatedly timing ~x0 stores:" (* *test-size* *iters*))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))

(time (prog2$ (loop for i fixnum from 1 to *iters* do 
                    (MEM::zero-memory *test-size* *base-mem*))
              nil))
