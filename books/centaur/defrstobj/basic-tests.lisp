; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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

(in-package "ACL2")
(include-book "defrstobj")
(include-book "typed-record-tests")  ;; for various typed-record types

#||

;; Fool dependency scanner into allowing more memory for this book on our cluster
(set-max-mem (* 4 (expt 2 30)))

||#


; basic-tests.lisp
;
; This is just some basic tests of the defrstobj command.  We do some messing
; with packages to see if the macro breaks, and also try defining a large
; machine to see how well proving the supporting theorems scales.


(defrstobj m1  ;; "machine 1"                 ; Executable interface:

  (regs  :type (array integer (32))           ; (get-regs i m1)
         :initially 0                         ; (set-regs i val m1)
         :typed-record int-tr-p)

  (pctr  :type integer                        ; (get-pctr m1)
         :initially 0                         ; (set-pctr x m1)
         :fix (ifix x))

  :inline t
  ;; [Shilpi] Added top-level accessor and updater functions.
  :accessor m1a
  :updater  m1u)


(defrstobj rstobj::m2 ;; weird package to see if we blow up

  ;; Test of a machine with multiple arrays and other fields

  (m2-regs :type (array integer (64))
           :initially 0
           :typed-record int-tr-p)

  ;; Large array to make sure we don't blow up
  (m2-mem  :type (array integer (8192))
           :initially 0
           :resizable t
           :typed-record int-tr-p)

  (m2-foo  :initially nil)
  (m2-bar  :initially bar)

  (m2-actr :type integer :initially 0 :fix (ifix x))
  (m2-bctr :type integer :initially 1 :fix (ifix x))

  :inline t
  :accessor m2a
  :updater  m2u)

(defrstobj m21-no-arrays


  (m21-foo  :initially nil)
  (m21-bar  :initially bar)

  (m21-actr :type integer :initially 0 :fix (ifix x))
  (m21-bctr :type integer :initially 1 :fix (ifix x))

  :inline t
  :accessor m21a
  :updater  m21u)


(make-event
 `(defrstobj m3

    ;; Test of some other typed-record types

    (m3-regs :type (array integer (64))
             :initially 0
             :typed-record int-tr-p)

    (rstobj::m3-mem  :type (array integer (8192))
                     :initially 0
                     :typed-record int-tr-p)

    (m3-chars :type (array character (256))
              :initially ,(code-char 0)
              :typed-record char-tr-p)

    (m3-bits  :type (array bit (12345))
              :initially 0
              :typed-record bit-tr-p)

    (m3-foo  :initially nil)
    (m3-bar  :initially bar)

    (m3-actr :type integer :initially 0 :fix (ifix x))
    (m3-bctr :type integer :initially 1 :fix (ifix x))

    :inline t
    :accessor m3a
    :updater  m3u))


(defrstobj m41-no-scalars

  (m41-regs :type (array (unsigned-byte 128) (64))
           :initially 0
           :typed-record ub128-tr-p)

  (m41-mem :type (array (unsigned-byte 8) (65536))
          :initially 0
          :typed-record ub8-tr-p)

  (m41-sregs :type (array (signed-byte 32) (11))
            :initially 0
            :typed-record sb32-tr-p)

  :inline t)

(defrstobj m42-no-scalars-resizable

  (m42-regs :type (array (unsigned-byte 128) (64))
            :initially 0
            :resizable t
            :typed-record ub128-tr-p)

  (m42-mem :type (array (unsigned-byte 8) (65536))
           :initially 0
           :resizable t
           :typed-record ub8-tr-p)

  (m42-sregs :type (array (signed-byte 32) (11))
             :initially 0
             :resizable t
             :typed-record sb32-tr-p)

  :inline t
  :accessor m42a
  :updater  m42u)

(defrstobj m4

  (m4-regs :type (array (unsigned-byte 128) (64))
           :initially 0
           :typed-record ub128-tr-p)

  (m4-mem :type (array (unsigned-byte 8) (65536))
          :initially 0
          :typed-record ub8-tr-p)

  (m4-sregs :type (array (signed-byte 32) (11))
            :initially 0
            :typed-record sb32-tr-p)

  (m4-flags :type (unsigned-byte 1234) :initially 0
            :fix (unsigned-byte-fix 1234 x))

  :inline t
  :accessor m4a
  :updater  m4u)




(defun nonneg-fix (x)
  (declare (xargs :guard t))
  (if (integerp x)
      (if (< x 0)
          (- x)
        x)
    0))

(def-typed-record nonneg
  :elem-p (natp x)
  :elem-list-p (nat-listp x)
  :elem-default 0
  :elem-fix (nonneg-fix x))


(defrstobj m4andahalf
  (m4.5-regs :type (array (unsigned-byte 128) (64))
           :initially 0
           :typed-record ub128-tr-p)

  (m4.5-mem :type (array (integer 0 *) (65536))
          :initially 0
          :typed-record nonneg-tr-p)

  (m4.5-sregs :type (array (signed-byte 32) (11))
            :initially 0
            :typed-record sb32-tr-p)

  (m4.5-flags :type (unsigned-byte 1234) :initially 127
              :fix (unsigned-byte-fix 1234 x))

  :inline t)


;; (defun char-fix (x)
;;   (declare (xargs :guard t))
;;   (if (characterp x) x #\a))

(defrstobj m5

  ;; Just a big test of a stobj with many array fields and many normal fields.
  ;; Performance is GREAT.

  (m5-arr0 :type (array (unsigned-byte 128) (64))
           :initially 0 :resizable t
           :typed-record ub128-tr-p)

  (m5-arr1 :type (array (unsigned-byte 128) (64))
           :initially 0 :resizable t
           :typed-record ub128-tr-p)

  (m5-arr2 :type (array (unsigned-byte 128) (64))
           :initially 0 :resizable t
           :typed-record ub128-tr-p)

  (m5-arr3 :type (array (unsigned-byte 128) (64))
           :initially 0 :resizable t
           :typed-record ub128-tr-p)

  (m5-arr4 :type (array (unsigned-byte 128) (64))
           :initially 0 :resizable t
           :typed-record ub128-tr-p)



  (m5-arr5 :type (array (unsigned-byte 8) (64))
           :initially 0 :resizable t
           :typed-record ub8-tr-p)

  (m5-arr6 :type (array (unsigned-byte 8) (64))
           :initially 0 :resizable t
           :typed-record ub8-tr-p)

  (m5-arr7 :type (array (unsigned-byte 8) (64))
           :initially 0 :resizable t
           :typed-record ub8-tr-p)

  (m5-arr8 :type (array (unsigned-byte 8) (64))
           :initially 0
           :typed-record ub8-tr-p)

  (m5-arr9 :type (array (unsigned-byte 8) (64))
           :initially 0
           :typed-record ub8-tr-p)


  (m5-arr10 :type (array integer (64))
            :initially 0
            :typed-record int-tr-p)

  (m5-arr11 :type (array integer (64))
            :initially 0
            :typed-record int-tr-p)

  (m5-arr12 :type (array integer (64))
            :initially 0
            :typed-record int-tr-p)

  (m5-arr13 :type (array integer (64))
            :initially 0
            :typed-record int-tr-p)

  (m5-arr14 :type (array integer (64))
            :initially 0
            :typed-record int-tr-p)


  (m5-fld1 :type integer :initially 0 :fix (ifix x))
  (m5-fld2 :type integer :initially 0 :fix (ifix x))
  (m5-fld3 :type integer :initially 0 :fix (ifix x))
  (m5-fld4 :type integer :initially 0 :fix (ifix x))
  (m5-fld5 :type integer :initially 0 :fix (ifix x))

  (m5-fld6 :type character :initially #\a :fix (char-fix x))
  (m5-fld7 :type character :initially #\a :fix (char-fix x))
  (m5-fld8 :type character :initially #\a :fix (char-fix x))
  (m5-fld9 :type character :initially #\a :fix (char-fix x))
  (m5-fld10 :type character :initially #\a :fix (char-fix x))

  (m5-fld11 :initially nil)
  (m5-fld12 :initially nil)
  (m5-fld13 :initially nil)
  (m5-fld14 :initially nil)
  (m5-fld15 :initially nil))





(defrstobj matt-example
  ;; Example stobj from Matt Kaufmann that previously did not work due to a
  ;; theory problem, which we have now fixed.
  (fld1 :type integer :initially 0 :fix (ifix x))  
  :accessor matta
  :updater  mattu)

