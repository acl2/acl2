; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
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

(in-package "ACL2")

(local
 (encapsulate
     ()

(encapsulate
    (
     ((local-ifloor * *) => *)
     ((local-imod * *) => *)
     ((local-expt2 *) => *)
     ((local-logcar *) => *)
     ((local-loghead * *) => *)
     ((local-logtail * *) => *)
     ((local-logapp * * *) => *)
     )

  (local
   (encapsulate
       ()

     (defun local-ifloor (i j)
       (floor (ifix i) (ifix j)))

     (defun local-imod (i j)
       (mod (ifix i) (ifix j)))

     (defun local-expt2 (n)
       (expt 2 (nfix n)))

     (defun local-logcar (i)
       (local-imod i 2))

     (defun local-loghead (size i)
       (local-imod i (local-expt2 size)))

     (defun local-logtail (pos i)
       (local-ifloor i (local-expt2 pos)))

     (defun local-logapp (size i j)
       (let ((j (ifix j)))
	 (+ (local-loghead size i) (* j (local-expt2 size)))))

     ))

  (defthm local-ifloor-defn
    (equal (local-ifloor i j)
	   (floor (ifix i) (ifix j))))

  (defthm local-imod-defn
    (equal (local-imod i j)
	   (mod (ifix i) (ifix j))))

  (defthm local-expt2-defn
    (equal (local-expt2 n)
	   (expt 2 (nfix n))))

  (defthm local-logcar-defn
    (equal (local-logcar i)
	   (local-imod i 2)))

  (defthm local-loghead-defn
    (equal (local-loghead size i)
	   (local-imod i (local-expt2 size))))

  (defthm local-logtail-defn
    (equal (local-logtail size i)
	   (local-ifloor i (local-expt2 size))))

  (defthm local-logapp-defn
    (equal (local-logapp size i j)
	   (let ((j (ifix j)))
	     (+ (local-loghead size i) (* j (local-expt2 size))))))

  )

(encapsulate
    ()

    (local (include-book "arithmetic-3/bind-free/top" :dir :system))

    (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

; Matt K.: There was formerly a set-default-hints at the end of an embedded
; encapsulate, which had no effect since set-default-hints was local to that
; encapsulate.

  (defthm local-special-32-bit-overflow-reduction
    (implies
     (and
      (syntaxp (quotep c))
      (equal (local-loghead 16 c) 0)
      (integerp c)
      (integerp x))
     (equal (signed-byte-p 32 (+ c x))
	    (signed-byte-p 16 (+ (local-logtail 16 c) (local-logtail 16 x))))))

     )


))

(include-book "ihs/ihs-lemmas" :dir :system)

(defthm special-32-bit-overflow-reduction
  (implies
   (and
    (syntaxp (quotep c))
    (equal (loghead 16 c) 0)
    (integerp c)
    (integerp x))
   (equal (signed-byte-p 32 (+ c x))
	  (signed-byte-p 16 (+ (logtail 16 c) (logtail 16 x)))))
  :hints (("Goal" :in-theory `(logapp loghead logtail logcar expt2 imod ifloor)
	   :use (:functional-instance
		 local-special-32-bit-overflow-reduction
		 (local-ifloor  ifloor)
		 (local-imod    imod)
		 (local-expt2   expt2)
		 (local-logcar  logcar)
		 (local-loghead loghead)
		 (local-logtail logtail)
		 (local-logapp  logapp)))))

