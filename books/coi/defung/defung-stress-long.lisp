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

#||
;; Jared added this comment to avoid having Centaur's cluster kill this book
;; for using too much memory.  See cert.pl for details.

(set-max-mem (* 6 (expt 2 30)))

;; Then Sol split this out into a separate book.
||#

(include-book "defung")

#+joe
(defmacro hide-local (&rest args)
  `(encapsulate
       ()
     (local
      (encapsulate
	  ()
	,@args))))

(defmacro hide-local (&rest args)
  `(local
    (encapsulate
	()
      ,@args)))

; Added by Matt K. after v8-2 for (HIDE (COMMENT ...)) change:
(defattach-system ; generates (local (defattach ...))
  remove-guard-holders-blocked-by-hide-p
  constant-nil-function-arity-0)

(hide-local
 (def::ung one-4 (n)
   (if (zp n) 1
     (let ((n (if (< n 7) (1+ n) (1- n))))
       (let ((n (one-4 n)))
	 (let ((n (if (> n 10) (1- n) (1+ n))))
	   (let ((n (if (< (if (< (one-4 n) n) (one-4 (1+ n)) (1+ (one-4 n))) n) (one-4 (1+ n)) (one-4 (1- n)))))
	     (one-4 n)))))))
 )
