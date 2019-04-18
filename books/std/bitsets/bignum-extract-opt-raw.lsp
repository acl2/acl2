; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "BITSETS")


;; SBCL has a bug with (byte size pos) where it assumes that pos is a fixnum.
;; It also doesn't seem to have a fast definition of LDB anyway.
;;
;;   From sbcl:src/code/numbers.lisp:
;;
;;     (defun %ldb (size posn integer)
;;       (declare (type bit-index size posn))
;;       (logand (ash integer (- posn))
;;               (1- (ash 1 size))))
;;
;; So trying to work around this just slows SBCL down anyway and it's much
;; better to just use the original version.
;;
;; If this ever gets improved and SBCL's LDB is faster/better than ash, we
;; can revive the SBCL code below, but also edit bitsets-opt-raw.lsp and
;; undo the SBCL-specific things there!

;; #+sbcl
;; (defun test-for-sbcl-bug (x slice)
;;   (ldb (byte 32 (* 32 slice)) x))

;; #+sbcl
;; (eval-when
;;  (:compile-toplevel :load-toplevel :execute)
;;  (handler-case
;;    (test-for-sbcl-bug -1 (expt 2 57))
;;    (error (condition)
;;           (declare (ignore condition))
;;           (format t "~%WARNING (from std/bitsets/bignum-extract-opt-raw.lisp):~%~
;;                      Your copy of SBCL has a bug with BYTE.  Using a slower~%~
;;                      version of bignum-extract to work around this bug.~%~%")
;;           (pushnew :sbcl-has-byte-bug *features*))))

;; ;; An implementation of bignum-extract for SBCL versions with the BYTE bug.
;; #+sbcl-has-byte-bug
;; (if (and (typep slice 'fixnum)
;;          (< (the fixnum slice) #.(expt 2 57)))
;;     ;; Use the fast version for sensible slice numbers
;;     (the (unsigned-byte 32)
;;          (ldb (byte 32 (the (unsigned-byte 62) (* 32 (the fixnum slice)))) x))
;;   ;; Otherwise use the ordinary definition.
;;   (the (unsigned-byte 32)
;;        (logand (the (unsigned-byte 32) (1- (expt 2 32)))
;;                (ash x (* -32 slice)))))

; We just won't do anything at all for SBCL.

; Added by Matt K., 7/20/2015: LispWorks 7.0.0 also can cause an error for a
; non-fixnum second argument of byte, e.g., (byte 32 72057594037927936).  So
; essentially following Jared's suggestion (github Issue #460), I'm excluding
; LispWorks just as SBCL is excluded.

; Added by Matt K., 9/16/2015: CMU CL snapshot-2014-12 (20F Unicode) also
; causes an error for the call of byte shown just above; actually I found the
; CMU CL problem with the call (bitsets::test0 1 2251799813685248).  So I'm
; excluding CMU CL, too.

#-(or sbcl lispworks cmucl)
(declaim (inline bignum-extract))

#-(or sbcl lispworks cmucl)
(defun bignum-extract (x slice)

  ;; Simple Lisp version for most Lisps.  (Matt K. mode 4/2019: Added acl2::
  ;; package prefix since byte is excluded from the list of symbols imported
  ;; into "BITSETS" in books/std/package.lsp.)
  #-(and Clozure x86-64)
  (the (unsigned-byte 32)
       (ldb (acl2::byte 32 (* 32 slice)) x))

  #+(and Clozure x86-64)
  (cond ((not (typep slice 'fixnum))
         ;; If the slice is not even a fixnum, you have bigger problems.  We
         ;; just fall back to the logical definition.
         (bignum-extract-slow x slice))
        ((typep x 'fixnum)
         ;; Since fixnums are 60 bits, the only valid slices are 0 and 1.
         (cond ((= (the fixnum slice) 0)
                (the fixnum (logand (1- (expt 2 32))
                                    (the fixnum x))))
               ((= (the fixnum slice) 1)
                (the fixnum (logand (1- (expt 2 32))
                                    (the fixnum (ash (the fixnum x) -32)))))
               ;; For slices beyond these, we need to consider whether X is
               ;; negative since in 2's complement negative numbers have
               ;; "infinite leading 1's."
               ((< x 0)
                (1- (expt 2 32)))
               (t
                0)))
        ;; Else, a bignum.  CCL represents bignums as vectors of 32-bit numbers
        ;; with the least significant chunks coming first.
        ((< (the fixnum slice) (the fixnum (ccl::uvsize x)))
         ;; In bounds for the array -- just an array access.
         (ccl::uvref x slice))
        ;; Else, out of bounds -- like indexing beyond a fixnum, we need to
        ;; return all 0's or all 1's depending on whether X is negative.
        ((< x 0)
         (1- (expt 2 32)))
        (t
         0)))

