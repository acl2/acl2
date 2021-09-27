; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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


; solutions.lisp - Solutions to the tutorial exercises
;
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

; This is a certifiable book, or would be if it were named .lisp.  For some
; time we called it solutions.lisp.  However, it frequently causes resource
; problems for certain Lisps, so we've renamed it to solutions.lsp so that
; it won't get automatically certified.

(in-package "ACL2")
(include-book "gl")


;; Solutions to exercises in the GL Basic Tutorial
;;
;; We space these out excessively, so you can avoid looking at answers you
;; haven't gotten to yet.













(def-gl-thm 1a
  :hyp (and (unsigned-byte-p 4 x)
            (unsigned-byte-p 4 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings '((x (:g-number (1 2 3 4 5)))
                (y (:g-number (6 7 8 9 10)))))

















(def-gl-thm 1b-using-auto-bindings
  :hyp (and (unsigned-byte-p 4 x)
            (unsigned-byte-p 4 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:nat x 4)
                                 (:nat y 4)))


















(def-gl-thm 1b-using-g-int
  :hyp (and (unsigned-byte-p 4 x)
            (unsigned-byte-p 4 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings `((x ,(gl::g-int 0 1 5))
                (y ,(gl::g-int 6 1 5))))















;; We already did 1b manually (see 1a).


















(def-gl-thm 1c
  :hyp (and (unsigned-byte-p 20 x)
            (unsigned-byte-p 20 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:nat x 20)
                                 (:nat y 20)))

;; The above took 24 seconds.


(value-triple (hons-summary))  ;; It allocated 8 million honses.


















; 1d doesn't require a new proof.

#||

:u
(def-gl-thm 1c
  :hyp (and (unsigned-byte-p 20 x)
            (unsigned-byte-p 20 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:nat x 20)
                                 (:nat y 20)))

||#

















(value-triple (clear-memoize-tables))
(value-triple (hons-clear nil))

(def-gl-thm 1e
  :hyp (and (unsigned-byte-p 20 x)
            (unsigned-byte-p 20 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:mix (:nat x 20)
                                       (:nat y 20))))

(value-triple (clear-memoize-tables))
(value-triple (hons-clear nil))

(def-gl-thm 1e-alt
  :hyp (and (unsigned-byte-p 20 x)
            (unsigned-byte-p 20 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings `((x ,(gl::g-int 0 2 21))
                (y ,(gl::g-int 1 2 21))))











; To make this execute much faster, we'll want a higher memory ceiling.

; Added 8/24/13 by Matt K.: This book failed to certify because of a missing
; :ttags for the include-book form below.  However, the difference between
; using the two forms below, and not, was trivial when I used time$ to time the
; proof of 1f below:
;
;   ; including memory-mgmt:
;   36.39 seconds realtime, 36.29 seconds runtime
;   (3,472,888,144 bytes allocated).
;
;   ; NOT including memory-mgmt:
;   36.46 seconds realtime, 36.37 seconds runtime
;   (3,472,888,240 bytes allocated).
;
; (include-book "centaur/misc/memory-mgmt" :dir :system)
; (value-triple (set-max-mem (* 8 (expt 2 30))))

; Added by Matt K., 9/21/2013:

; With cmucl, one gets the following error for 1f (below) using a value here of
; 3000, even if -dynamic-space-size is set to 1632 on the command line, which
; is the maximum allowable in our CMUCL implementation, "CMU Common Lisp
; snapshot-2013-06 (20D Unicode)".
;   *A1 gc_alloc_large failed, nbytes=65244752.
;    CMUCL has run out of dynamic heap space (1632 MB).
;     You can control heap size with the -dynamic-space-size commandline option.
; So we use a smaller for limit CMUCL.  Note: Adding the two forms just above, to
; invoke set-max-mem, didn't solve the problem, whether I added them just above
; or added them at the beginning of this book.

; Added by Matt K., 11/3/2013: I killed an ACL2(h) certification run for this
; book using GCL 2.6.10pre that had already taken about 1 hour 36 minutes,
; which was using the first version of the next event.  So I tried
; certification using the second version of that event, but after 20 minutes
; working on that event, I killed that run, too.  So I'm avoiding the next form
; for GCL; but I will mention this to the GCL implementor.  Note that this book
; recently took less than 2 minutes to certify using ACL2(h) built on CCL, and
; for v6-3 took about 9 minutes using ACL2(h) built on CMUCL, which is normally
; a much slower lisp than GCL.

#+(not cmucl)
(def-gl-thm 1f
  :hyp (and (unsigned-byte-p 3000 x)
            (unsigned-byte-p 3000 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:mix (:nat x 3000)
                                       (:nat y 3000))))

#+cmucl
(def-gl-thm 1f
  :hyp (and (unsigned-byte-p 2000 x)
            (unsigned-byte-p 2000 y))
  :concl (equal (+ x y) (+ y x))
  :g-bindings (gl::auto-bindings (:mix (:nat x 2000)
                                       (:nat y 2000))))

