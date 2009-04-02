;
; Memories: Array-like Records for ACL2
; Copyright (C) 2005-2006 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.
;
; This program is distributed in the hope that it will be useful, but WITHOUT
; ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
; FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
; details.
;
; You should have received a copy of the GNU General Public License along with
; this program; if not, write to the Free Software Foundation, Inc., 51
; Franklin Street, Fifth Floor, Boston, MA 02110-1301, USA.
;


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



(defun zero-memory-with-misc-records (i r)
  (declare (xargs :guard (natp i))
           (type (signed-byte 30) i))
  (if (mbe :logic (zp i)
           :exec (= i 0))
      (s 0 0 r)
    (zero-memory-with-misc-records
     (the-fixnum (1- i))
     (s i 0 r))))



; For write tests we will just zero out a block of memory.  It doesn't really
; matter what addresses we use, because they're all the same depth from the
; root.  For read tests, we'll just sequentially scan a block of memory. 

(defun zero-memory (i mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p i mem)))
           (type (signed-byte 30) i))                              
  (if (mbe :logic (zp i)
           :exec (= i 0))
      (store 0 0 mem)
    (zero-memory (the-fixnum (1- i))
                 (store i 0 mem))))

(defun scan-memory (i mem)
  (declare (xargs :guard (and (memory-p mem)
                              (address-p i mem)))
           (type (signed-byte 30) i))
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


#|

(time (zero-memory-with-misc-records 65535 nil))

|#


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
