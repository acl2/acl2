; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>
; Warren A. Hunt, Jr. <hunt@cs.utexas.edu>
; Matt Kaufmann       <kaufmann@cs.utexas.edu>

(in-package "X86ISA")

(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "centaur/bitops/part-install" :dir :system)
(include-book "centaur/gl/def-gl-rule" :dir :system)
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/logbitp-bounds" :dir :system))

;; =============================================================================

(defsection utils
  :parents (x86isa)
  :short "The books in this directory provide some supporting events
  for the rest of the books in @('X86ISA')."

  :long "<p>Include Order:</p>
<table>

<tr>
<th> Book/Directory </th>
<th> Corresponding Documentation Topic </th>
</tr>

<tr>
<td> utilities.lisp </td>
<td> @(see utilities) </td>
</tr>

<tr>
<td> decoding-utilities.lisp </td>
<td> @(see decoding-utilities) </td>
</tr>

<tr>
<td> constants.lisp </td>
<td> @(see x86-constants) </td>
</tr>

<tr>
<td> records-0.lisp </td>
<td> Doc topic coming soon! </td>
</tr>

</table>"
  )

(defsection utilities
  :parents (utils)
  )

;; =============================================================================

(defsection mk-name

  :parents (utilities)
  :short "Macro that can be used to create event names by
  concatenating strings, symbols, and numbers."
  :long "@(def mk-name)

@(def string-concatenate)"

  (defun string-cat (lst)
    (declare (xargs :verify-guards nil))
    (cond ((atom lst)
           "")
          ((stringp (car lst))
           (string-append (str::upcase-string (car lst))
                          (string-cat (cdr lst))))
          ((symbolp (car lst))
           (string-append (symbol-name (car lst))
                          (string-cat (cdr lst))))
          ((natp (car lst))
           (string-append
            (coerce (explode-nonnegative-integer (car lst) 10 '())
                    'string)
            (string-cat (cdr lst))))
          (t
           (string-cat (cdr lst)))))

  (defmacro string-concatenate (&rest x)
    `(string-cat (list ,@x)))

  (defmacro mk-name (&rest x)
    ;; Note that the package is X86ISA here.
    `(intern$ (string-concatenate ,@x) "X86ISA"))

  (defmacro acl2-mk-name (&rest x)
    ;; Note that intern, unlike the regular Lisp reader, is sensitive to
    ;; case.
    `(intern (string-concatenate ,@x) "ACL2"))

  )

;; ======================================================================

(defsection proving-bounds
  :parents (utilities)

  :short "Some helpful macros that generate appropriate rewrite,
  type-prescription, and linear rules when needed"

  :long "<ul>
<li><p>Use the macro @('defthm-natp') to prove
a @('type-prescription') rule saying that some function returns a @('natp'),
and a @('linear') corollary saying that the function
returns a value greater than or equal to zero.</p>

<p>Usage:</p>

@({

  (defthm-natp <theorem-name>
    :hyp <hypotheses>
    :concl <conclusion>
    :hints <usual ACL2 hints>)
  })

<p>The above form produces a theorem of the form:</p>

@({
  (defthm <theorem-name>
    (implies <hypotheses>
             (natp <conclusion>))
    :hints <usual ACL2 hints>
    :rule-classes
    (:type-prescription
     (:linear
      :corollary
      (implies <hypotheses>
               (<= 0 <conclusion>))
      :hints <usual ACL2 hints>)))

  })

</li>

<li><p>Use the macro @('defthm-usb') to prove
a @('rewrite') rule saying that some function returns an @('unsigned-byte-p'),
a @('type-prescription') corollary saying that the function returns a @('natp'),
and a @('linear') corollary saying that the function
returns a value less than or equal to <tt>(expt 2 bound)</tt>.</p>

<p>Usage:</p>

@({

  (defthm-usb <theorem-name>
    :hyp <hypotheses>
    :bound <n>
    :concl <conclusion>
    :hints <usual ACL2 hints for the main theorem>
    :gen-type <t or nil>    ;; Generate :type-prescription corollary
    :gen-linear <t or nil>  ;; Generate :linear corollary
    :hyp-t <hypotheses for the :type-prescription corollary>
    :hyp-l <hypotheses for the :linear corollary>
    :hints-t <usual ACL2 hints for the :type-prescription corollary>
    :hints-l <usual ACL2 hints for the :linear corollary>
    :otf-flg <t or nil>)
  })

<p>The above form produces a theorem of the following form (if both
@(':gen-type') and @(':gen-linear') are @('t')):</p>

@({
  (defthm <theorem-name>
    (implies <hypotheses>
             (unsigned-byte-p <n> <conclusion>))
    :hints <usual ACL2 hints for the main theorem>
    :otf-flg <t or nil>
    :rule-classes
    (:rewrite
     (:type-prescription
      :corollary
      (implies <hypotheses for the :type-prescription corollary>
               (natp <conclusion>))
      :hints <usual ACL2 hints for the :type-prescription corollary>)
     (:linear
      :corollary
      (implies <hypotheses for the :linear corollary>
               (< <conclusion> (expt 2 <n>)))
      :hints <usual ACL2 hints for the :linear corollary>)))

  })

</li>

<li><p>Use the macro @('defthm-sb') to prove
a @('rewrite') rule saying that some function returns a @('signed-byte-p'),
a @('type-prescription') corollary saying that the function returns an
@('integerp'), and a @('linear') corollary saying that the function
returns a value greater than or equal to <tt>(- (expt 2 (1-
bound)))</tt> and less than <tt>(expt 2 (1- bound))</tt>.</p>

<p>Usage:</p>

@({

  (defthm-sb <theorem-name>
    :hyp <hypotheses>
    :bound <n>
    :concl <conclusion>
    :hints <usual ACL2 hints for the main theorem>
    :gen-type <t or nil>    ;; Generate :type-prescription corollary
    :gen-linear <t or nil>  ;; Generate :linear corollary
    :hyp-t <hypotheses for the :type-prescription corollary>
    :hyp-l <hypotheses for the :linear corollary>
    :hints-t <usual ACL2 hints for the :type-prescription corollary>
    :hints-l <usual ACL2 hints for the :linear corollary>
    :otf-flg <t or nil>)
  })

<p>The above form produces a theorem of the form: (if both
@(':gen-type') and @(':gen-linear') are @('t'))</p>

@({
  (defthm <theorem-name>
    (implies <hypotheses>
             (signed-byte-p <n> <conclusion>))
    :hints <usual ACL2 hints for the main theorem>
    :otf-flg <t or nil>
    :rule-classes
    (:rewrite
     (:type-prescription
      :corollary
      (implies <hypotheses for the :type-prescription corollary>
               (integerp <conclusion>))
      :hints <usual ACL2 hints for the :type-prescription corollary>)
     (:linear
      :corollary
      (implies <hypotheses for the :linear corollary>
               (and (<= (- (expt 2 (1- <n>)) <conclusion>))
               (< <conclusion> (expt 2 (1- <n>)))))
      :hints <usual ACL2 hints for the :linear corollary>)))

  })

</li>

</ul>"

  ;; since corollaries must just follow from their theorems,
  ;; it may be possible to generate simpler hints for the corollaries below

  (defmacro defthm-natp (name &key hyp concl hints)
    (if concl
        `(defthm ,name
           ,(if (atom hyp)
                `(natp ,concl)
              `(implies ,hyp (natp ,concl)))
           ,@(and hints `(:hints ,hints))
           :rule-classes
           (:type-prescription
            (:linear
             :corollary
             ,(if (atom hyp)
                  `(<= 0 ,concl)
                `(implies ,hyp (<= 0 ,concl)))
             ,@(and hints `(:hints ,hints)))))
      nil))

  (defmacro defthm-usb
      (name &key hyp bound concl
            gen-type gen-linear
            hyp-t hyp-l
            hints
            hints-t hints-l
            otf-flg)

    (if (and concl bound)
        (let ((hints-t (or hints-t hints))
              (hints-l (or hints-l hints))
              (2^bound (if (natp bound)
                           (expt 2 bound)
                         `(expt 2 ,bound))))
          `(defthm ,name
             ,(if (atom hyp)
                  `(unsigned-byte-p ,bound ,concl)
                `(implies ,hyp
                          (unsigned-byte-p ,bound ,concl)))
             ,@(and hints `(:hints ,hints))
             ,@(and otf-flg `(:otf-flg t))
             :rule-classes
             (:rewrite
              ,@(and gen-type
                     `((:type-prescription
                        :corollary
                        ,(if (or (and (atom hyp-t) (atom hyp))
                                 (equal hyp-t 't))
                             `(natp ,concl)
                           `(implies ,(or hyp-t hyp)
                                     (natp ,concl)))
                        ,@(and hints-t `(:hints ,hints-t)))))
              ,@(and gen-linear
                     `((:linear
                        :corollary
                        ,(if (or (and (atom hyp-l) (atom hyp))
                                 (equal hyp-l 't))
                             `(< ,concl ,2^bound)
                           `(implies ,(or hyp-l hyp)
                                     (< ,concl ,2^bound)))
                        ,@(and hints-l `(:hints ,hints-l))))))))
      nil))
  ;; no need to generate a (>= ... 0) linear rule so far

  (defmacro defthm-sb
      (name &key hyp bound concl
            gen-type gen-linear
            hyp-t hyp-l
            hints
            hints-t hints-l
            otf-flg)

    (if (and concl bound)
        (let* ((hints-t (or hints-t hints))
               (hints-l (or hints-l hints))
               (2^bound-1 (if (natp bound)
                              (expt 2 (1- bound))
                            `(expt 2 (1- ,bound))))
               (low-2^bound-1 (if (natp bound)
                                  (- 2^bound-1)
                                `(- (expt 2 (1- ,bound))))))
          `(defthm ,name
             ,(if (atom hyp)
                  `(signed-byte-p ,bound ,concl)
                `(implies ,hyp
                          (signed-byte-p ,bound ,concl)))
             ,@(and hints `(:hints ,hints))
             ,@(and otf-flg `(:otf-flg t))
             :rule-classes
             (:rewrite
              ,@(and gen-type
                     `((:type-prescription
                        :corollary
                        ,(if (or (and (atom hyp-t) (atom hyp))
                                 (equal hyp-t 't))
                             `(integerp ,concl)
                           `(implies ,(or hyp-t hyp)
                                     (integerp ,concl)))
                        ,@(and hints-t `(:hints ,hints-t)))))
              ,@(and gen-linear
                     `((:linear
                        :corollary
                        ,(if (or (and (atom hyp-l) (atom hyp))
                                 (equal hyp-l 't))
                             `(and
                               (<= ,low-2^bound-1 ,concl)
                               (< ,concl ,2^bound-1))
                           `(implies ,(or hyp-l hyp)
                                     (and
                                      (<= ,low-2^bound-1 ,concl)
                                      (< ,concl ,2^bound-1))))
                        ,@(and hints-l `(:hints ,hints-l))))))))
      nil)))

;; Misc.:

(defmacro defthml (&rest args)
  `(local (defthm ,@args)))

(defmacro defthmld (&rest args)
  `(local (defthmd ,@args)))

(defmacro def-gl-export
  (name &key hyp concl g-bindings rule-classes)

  (if (and hyp concl g-bindings)

      (let ((gl-name (mk-name name "-GL")))

        `(progn

           (gl::def-gl-ruledl
            ,gl-name
            :hyp ,hyp
            :concl ,concl
            :g-bindings ,g-bindings)

           (defthm ,name
             (implies ,hyp ,concl)
             :hints (("Goal" :in-theory (theory 'minimal-theory)
                      :use ((:instance ,gl-name))))
             :rule-classes ,(or rule-classes :rewrite))))
    nil))

;; ======================================================================

;; Convenient forcing idiom:

(defun formal-force-list (x)
  (declare (xargs :guard (true-listp x)))
  (cond ((endp x) nil)
        (t (cons `(force ,(car x))
                 (formal-force-list (cdr x))))))

(defmacro forced-and (&rest x)
  `(and ,@(formal-force-list x)))

;; ======================================================================

(defsection constants-conversions-and-bounds
  :parents (utilities)
  :short "Definitions of commonly used constants and some functions to
  convert between @('natp') and @('integerp'), etc."

  :long "<p>Definitions of constants (of the form @('2^W')) and
functions/macros grouped in @('ruleset')s of the following form are defined (where W is at
least a two-digit natural number; @('8') is represented as
@('08')):</p>

<ul>
<li> @('nWp') belongs to @('nwp-defs') ruleset.
@({
    (define nWp (x)
      (unsigned-byte-p W x))
})</li>

<li> @('nW') belongs to @('nw-defs') ruleset.
@({
    (define nW ((x integerp))
      (mbe :logic (loghead W x)
           :exec (logand 2^W-1 x)))
})</li>

<li> @('iWp') belongs to @('iwp-defs') ruleset.
@({
    (define iWp (x)
      (signed-byte-p W x))
})</li>

<li> @('iW') belongs to @('iw-defs') ruleset.
@({
    (define iW ((x integerp))
      (logext W x))
})</li>

<li> @('nW-to-iW') belongs to @('nw-to-iw-defs') ruleset.
@({
    (define nW-to-iW ((x nWp :type (unsigned-byte W)))
        (mbe :logic (logext W x)
             :exec (if (< x 2^(W-1)) x (- x 2^W))))
})</li>

<li> @('iW-to-nW') belongs to @('iw-to-nw-defs') ruleset.
@({
    (define iW-to-Nw ((x iWp :type (signed-byte W)))
        (mbe :logic (logext W x)
             :exec (if (>= x 0) x (+ x 2^W))))
})</li>

</ul>

<p> The function @('np-def-n') is used to automatically create these
constants and functions; it also proves some associated lemmas.</p>"


  )

;; Lemmas to help in the MBE proof obligation of ntoi rules:

(local
 (encapsulate
  ()

  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (defthm logext-is-the-same-as-ntoi-helper-1
    (implies (and (unsigned-byte-p (1+ n) x)
                  (<= 0 n)
                  (< x (expt 2 n)))
             (equal (loghead n x) x)))))

(local
 (encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defthm logext-is-the-same-as-ntoi-helper-2
    (implies (and (unsigned-byte-p (1+ n) x)
                  (not (zp (1+ n)))
                  (<= (expt 2 n) x))
             (equal (logapp n x -1)
                    (+ x (- (expt 2 (1+ n))))))
    :hints (("Goal" :in-theory (e/d (logapp loghead) ()))))

  (defthm logext-is-the-same-as-ntoi-helper-3
    (implies (and (unsigned-byte-p (1+ n) x)
                  (logbitp n x)
                  (natp n)
                  (< x (expt 2 n)))
             (equal (logapp n x -1)
                    x))
    :hints (("Goal" :in-theory (e/d (logapp logbitp) ()))))

  (defthm loghead-is-the-same-as-iton-helper
    (implies (signed-byte-p n x)
             (equal (loghead n x)
                    (if (>= x 0) x (+ x (expt 2 n)))))
    :hints (("Goal" :in-theory (enable loghead** logcons))))))

(def-ruleset nwp-defs       nil)
(def-ruleset nw-defs        nil)
(def-ruleset iwp-defs       nil)
(def-ruleset iw-defs        nil)
(def-ruleset nw-to-iw-defs  nil)
(def-ruleset iw-to-nw-defs  nil)

(define np-def-n (n)
  :mode :program ;; NP-DEF-N is a :program mode function
  :guard (posp n)
  :parents (constants-conversions-and-bounds)
  (let* ((str-n          (symbol-name (if (< n 10)
                                          (acl2::packn (list 0 n))
                                        (acl2::packn (list n)))))
         (digits         (symbol-name (acl2::packn (list n))))
         (2^XY           (mk-name "*2^" digits "*"))
         (nXYp           (mk-name "N" str-n "P"))
         (nXY            (mk-name "N" str-n))
         (iXYp           (mk-name "I" str-n "P"))
         (iXY            (mk-name "I" str-n))
         (ntoi           (mk-name "N" str-n "-TO-I" str-n))
         (iton           (mk-name "I" str-n "-TO-N" str-n)))
    (list

     `(defconst ,2^XY
        (expt 2 ,n))

     `(define ,nXYp (x)
        ;; XY-bit natural number recognizer
        :inline t
        :enabled t
        :parents (constants-conversions-and-bounds)
        (unsigned-byte-p ,n x))

     `(define ,nXY ((x integerp))
        ;; Truncate input to an XY-bit natural number
        ;; This function can be used to convert, say a 32-bit integer
        ;; to a 32-bit natural number.  We choose to keep this function
        ;; enabled.
        :inline t
        :enabled t
        :parents (constants-conversions-and-bounds)
        (mbe :logic (loghead ,n x)
             :exec (logand ,(1- (expt 2 n)) x)))

     `(define ,iXYp (x)
        :inline t
        :enabled t
        :parents (constants-conversions-and-bounds)
        ;; XY-bit integer recognizer
        (signed-byte-p ,n x))

     `(define ,iXY ((x integerp))
        ;; Truncate input to an XY-bit signed integer number
        ;; This function can be used to convert, say a 32-bit natural number
        ;; to a 32-bit integer.  We choose to keep this function
        ;; enabled.
        :inline t
        :enabled t
        :parents (constants-conversions-and-bounds)
        (logext ,n x))

     `(define ,ntoi
        :inline t
        :enabled t
        :parents (constants-conversions-and-bounds)
        ;; Convert natural number to integer
        :guard-hints (("Goal" :in-theory (enable logext)))
        ((x ,nXYp :type (unsigned-byte ,n)))

        (mbe :logic (logext ,n x)
             :exec (if (< x ,(expt 2 (1- n)))
                       x
                     (- x ,(expt 2 n)))))

     `(define ,iton
        :inline t
        :enabled t
        :parents (constants-conversions-and-bounds)
        ;; Convert integer to natural number
        ((x ,iXYp :type (signed-byte ,n)))

        (mbe :logic (loghead ,n x)
             :exec (if (>= x 0)
                       x
                     (+ x ,(expt 2 n)))))

     `(add-to-ruleset nwp-defs       '(,nXYp))
     `(add-to-ruleset nw-defs        '(,nXY))
     `(add-to-ruleset iwp-defs       '(,iXYp))
     `(add-to-ruleset iw-defs        '(,iXY))
     `(add-to-ruleset nw-to-iw-defs  '(,ntoi))
     `(add-to-ruleset iw-to-nw-defs  '(,iton))
     )))

(define np-defs (lst)
  :mode :program
  :guard (acl2::pos-listp lst)
  :parents (constants-conversions-and-bounds)
  (if (atom lst) nil
    (append (np-def-n (car lst))
            (np-defs (cdr lst)))))

(defmacro defuns-np (&rest lst)
  (cons 'progn (np-defs lst)))

(defuns-np 1 2 3 4 5 6 8 9 11 12 16 17 18 20 21 22 24 25 26 27 28
  30 32 33 35 43 44 45 47 48 49 51 52 59 60 64 65 80 112 120 128)


(defmacro n-size (n x)
  ;; I prefer using n-size in functions that generate functions. E.g.,
  ;; see gpr-add-spec-gen-fn in
  ;; machine/instructions-spec/add-adc-sub-sbb-or-and-xor-cmp-test.lisp.
  (let* ((fn-name (mk-name "N"
                           (symbol-name (if (< n 10)
                                            (acl2::packn (list 0 n))
                                          (acl2::packn (list n)))))))
    `(,fn-name ,x)))


(defmacro ntoi (n x)
  ;; I prefer using ntoi in functions that generate functions. E.g.,
  ;; see idiv-spec-gen in
  ;; machine/instructions-spec/div-idiv.lisp
  (let* ((val (symbol-name (if (< n 10)
                               (acl2::packn (list 0 n))
                             (acl2::packn (list n)))))
         (fn-name (mk-name "N" val "-TO-I" val)))
    `(,fn-name ,x)))

(define trunc
  ;; I prefer using trunc in function definitions.
  ((n :type (integer 0 *))
   (x :type integer))
  :inline t
  :enabled t
  (case n
    (1  (n08 x))
    (2  (n16 x))
    (4  (n32 x))
    (8  (n64 x))
    (16 (n128 x))
    (t (part-select x :low 0 :width n))))

;; =============================================================================

;; Handy utility for turning a positional list into an array

(defun list-to-alist (x i acc)
  (declare (xargs :guard (and (true-listp x)
                              (natp i)
                              (alistp acc))))
  (cond ((endp x) (reverse acc))
        (t (list-to-alist (cdr x)
                          (1+ i)
                          (acons i (car x) acc)))))

(defthm alistp-revappend
  (implies (true-listp x)
           (equal (alistp (revappend x y))
                  (and (alistp x)
                       (alistp y))))
  :hints (("Goal" :induct (revappend x y))))

(defthm alist-list-to-alist
  (implies (alistp acc)
           (alistp (list-to-alist x i acc))))

(defthm bounded-integer-alistp-monotone
  (implies (and (bounded-integer-alistp x i)
                (natp i)
                (natp j)
                (<= i j))
           (bounded-integer-alistp x j)))

(defthm bounded-integer-alistp-revappend
  (implies (true-listp x)
           (equal (bounded-integer-alistp (revappend x y) i)
                  (and (bounded-integer-alistp x i)
                       (bounded-integer-alistp y i))))
  :hints (("Goal" :induct (revappend x y))))

(defthm bounded-integer-alistp-list-to-alist
  (implies (and (natp i)
                (bounded-integer-alistp acc i)
                (equal k (+ i (len x))))
           (bounded-integer-alistp (list-to-alist x i acc)
                                   k)))

(defun list-to-array (name x)
  (declare (xargs :guard (and (symbolp name)
                              (true-listp x)
                              x
                              (< (length x)
                                 acl2::*maximum-positive-32-bit-integer*))))
  (let ((alist (list-to-alist x 0 nil))
        (len (length x)))
    (compress1 name
               `((:header :dimensions (,len)
                          :maximum-length ,(1+ len)
                          :default x
                          :name ,name)
                 ,@alist))))

(defun ints-to-booleans-acc (x acc)
  (declare (xargs :guard (and (integer-listp x)
                              (true-listp acc))))
  (cond ((endp x) (reverse acc))
        (t (ints-to-booleans-acc (cdr x)
                                 (cons (not (zerop (car x)))
                                       acc)))))

(defun ints-to-booleans (x)

  ;; Maps a list of integers to a corresponding list of Booleans,
  ;; treating 0 as false.  Example: (ints-to-booleans '(0 1 0 0 1)) ==>
  ;; (nil t nil nil t).

  (declare (xargs :guard (integer-listp x)))
  (ints-to-booleans-acc x nil))

;; =============================================================================

(defsection slicing-operations
  :parents (utilities)
  :short "Definitions of @('slice') and @('!slice')"

  :long "<p>Slicing functions @('slice') and @('!slice') open up to an
@('MBE').  The @(':logic') part is defined using @(see part-select) or
@(see part-install) and the @(':exec') is heavily type-declared for
the sake of efficiency.</p>"

  )

(encapsulate
 ()

 (local (include-book "arithmetic/top-with-meta" :dir :system))

 (define layout-constant-alistp (alst position max-size)
   :short "Recognizer for all the layout constants, i.e. contiguous bit fields"
   :guard (and (natp position)
               (natp max-size))
   :enabled t
   :parents (slicing-operations)
   (if (atom alst)
       (null alst)
     (let ((entry (car alst)))
       (and (consp entry)
            (consp (cdr entry))
            (consp (cddr entry))
            (null (cdddr entry))
            (let ((key (car entry))
                  (pos (cadr entry))
                  (width (caddr entry)))
              (and (or (keywordp key)
                       (and (natp key)
                            (or (= key 0)
                                (= key 1))))
                   (natp pos)
                   (natp width)
                   (= position pos)
                   (<= (+ pos width) max-size)
                   (layout-constant-alistp (cdr alst)
                                           (+ pos width)
                                           max-size)))))))

 (local
  (defthm sanity-check-of-layout-constant-alistp
    (layout-constant-alistp
     ;; Example of a layout constant
     '((0          0  3) ;; 0
       (:cr3-pwt   3  1) ;; Page-Level Writes Tranparent
       (:cr3-pcd   4  1) ;; Page-Level Cache Disable
       (0          5  7) ;; 0
       (:cr3-pdb  12 40) ;; Page Directory Base
       (0         52 12) ;; Reserved (must be zero)
       )
     0 64)
    :rule-classes nil))

 (define field-pos-width (flg layout-constant)
   :parents (slicing-operations)
   :enabled t
   :short "Returns the position and width of @('flg'), given
    @('layout-constant')"
   (declare (xargs :guard (symbolp flg)))
   (if (atom layout-constant)
       (mv 0 (or (cw "field-pos-width:  Unknown flag:   ~p0.~%" flg) 0))
     (let ((entry (car layout-constant)))
       (if (not (and (consp entry)
                     (consp (cdr entry))
                     (consp (cddr entry))
                     (null (cdddr entry))
                     (or (symbolp (car entry))
                         (natp    (car entry)))
                     (natp (cadr entry))
                     (natp (caddr entry))))
           (mv 0 (or (cw "field-pos-width:  Entry malformed:   ~p0.~%" entry) 0))
         (let ((name (car entry))
               (pos  (cadr entry))
               (width (caddr entry)))
           (if (eq name flg)
               (mv pos width)
             (field-pos-width flg (cdr layout-constant))))))))

 (define slice (flg reg reg-width layout-constant)
   :enabled t
   :parents (slicing-operations)
   :short "Used to define efficient bit-slice accessor forms for
    reasoning and execution"
   :guard (and (symbolp flg)
               (natp reg-width)
               (layout-constant-alistp layout-constant 0 reg-width))
   :guard-hints (("Goal" :do-not '(preprocess simplify)))
   (mv-let (pos size)
           (field-pos-width flg layout-constant)
           (let* ((pos (if (natp pos) pos 0))
                  (size (if (natp size) size 0))
                  (mask (1- (expt 2 size)))
                  (reg-width-pos (- reg-width pos)))
             `(mbe :logic (part-select ,reg :low ,pos :width ,size)
                   :exec
                   (the (unsigned-byte ,size)
                     (logand (the (unsigned-byte ,size) ,mask)
                             (the (unsigned-byte ,reg-width-pos)
                               (ash
                                (the (unsigned-byte ,reg-width) ,reg)
                                (- ,pos)))))))))

 (define !slice (flg val reg reg-size layout-constant)
   :guard (and (symbolp flg)
               (natp reg-size))
   :parents (slicing-operations)
   :short "Used to define efficient bit-slice updater forms for
    reasoning and execution"
   (mv-let (pos size)
           (field-pos-width flg layout-constant)
           (let* ((mask (lognot (ash (logmask size) pos)))
                  (size+pos (+ pos size))
                  (mask-size (+ 1 size+pos)))
             `(let ((reg-for-!slice-do-not-use
                     (the (unsigned-byte ,reg-size) ,reg)))
                (declare (type (unsigned-byte ,reg-size)
                               reg-for-!slice-do-not-use))
                (mbe :logic (part-install ,val reg-for-!slice-do-not-use
                                          :low ,pos :width ,size)
                     :exec (the (unsigned-byte ,reg-size)
                             (logior
                              (the (unsigned-byte ,reg-size)
                                (logand
                                 (the (unsigned-byte ,reg-size)
                                   reg-for-!slice-do-not-use)
                                 (the (signed-byte ,mask-size) ,mask)))
                              (the (unsigned-byte ,size+pos)
                                (ash (the (unsigned-byte ,size) ,val)
                                     ,pos)))))))))

 ) ;; End of encapsulate

;; ======================================================================

(defsection globally-disabled-events
  :parents (utilities)

  :short "A ruleset containing all the events supposed to be mostly
  globally disabled in our books"

  :long "<p>The macro @('globally-disable') adds its argument ---
  either a ruleset or an event --- to the ruleset called
  @('globally-disabled-events'), and then disables
  @('globally-disabled-events').</p>

<p>Use the following form to see the events in this ruleset:</p>

<code>
\(show-globally-disabled-events-ruleset\)
</code>

<p>The idea behind having a @('globally-disabled-events') ruleset is
to provide some indication to the user of these books which events are
supposed to be mostly disabled throughout the books. This ruleset does
NOT reflect the enabled status of these events at any point, i.e., we
do not guarantee that an event @('FOO') in this ruleset will be
disabled everywhere in these books.</p>

<p>If you need to enable some events in @('globally-disabled-events')
during book/proof development, it is recommended to do so locally.</p>

<p>Use the following form to see the current status (enabled or
disabled) of the events in the @('globally-disabled-events')
ruleset:</p>

<code>
\(show-globally-disabled-events-status\)
</code>

<p>@('show-globally-disabled-events-status') simply calls @(see
disabledp) recursively on the events in
@('globally-disabled-events').</p>"

  (def-ruleset globally-disabled-events nil)

  (define globally-disable-fn
    ((events "Can be a symbol (another ruleset) or a @('true-listp') (set of events)"))
    (b* ((events (if (true-listp events)
                     `(quote ,events)
                   events)))
        `(progn
           ;; add-to-ruleset will catch any invalid events, e.g.,
           ;; those that don't exist.
           (add-to-ruleset globally-disabled-events ,events)
           (in-theory (disable* globally-disabled-events)))))

  (defmacro globally-disable (events)
    `(make-event (globally-disable-fn ,events)))

  (define show-globally-disabled-events-fn
    ((state))
    :mode :program
    (let ((world (w state)))
      (ruleset-theory 'globally-disabled-events)))

  (defmacro show-globally-disabled-events-ruleset ()
    `(show-globally-disabled-events-fn state))

  (defun disabledp-lst (lst count state)
    (declare (xargs :stobjs (state)
                    :mode :program))
    (if (endp lst)
        (mv (cw "~%~%Number of events in GLOBALLY-DISABLED-EVENTS: ~x0~%~%" count)
            :invisible
            state)

      (b* ((- (cw "~%-- ~x0 ~%~t1 ~x2~%"
                  (car lst)
                  1
                  (or (disabledp (car lst))
                      :ENABLED))))
          (disabledp-lst (cdr lst) (1+ count) state))))

  (defmacro show-globally-disabled-events-status ()
    `(disabledp-lst (show-globally-disabled-events-ruleset) 0 state))

  (globally-disable '(logior logand logxor floor mod ash))

  )

;; ======================================================================
