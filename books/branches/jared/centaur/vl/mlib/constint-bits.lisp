; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "welltyped")
(local (include-book "../util/arithmetic"))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
(local (std::add-default-post-define-hook :fix))
(local (in-theory (disable acl2::functional-commutativity-of-minus-*-left
                           acl2::normalize-factors-gather-exponents)))

;; The code here is styled after vl-msb-bitslice-constint, but whereas that
;; code produces new expressions, here we just produce a bit list.

(local (defthm logand-1
         (implies (natp value)
                  (equal (logand value 1)
                         (mod value 2)))))

(define vl-constint-lsb-bits-aux
  :parents (vl-constint->msb-bits)
  ((len   natp)
   (value natp))
  :returns (lsb-bits vl-bitlist-p)
  :verbosep t
  :measure (nfix len)
  (b* (((when (zp len))
        nil)
       (floor2          (mbe :logic (floor (nfix value) 2)
                             :exec (ash value -1)))
       ((the bit mod2)  (mbe :logic (mod (nfix value) 2)
                             :exec (logand value 1)))
       (bit             (if (eql mod2 0)
                            :vl-0val
                          :vl-1val)))
    (cons bit
          (vl-constint-lsb-bits-aux (mbe :logic (- (nfix len) 1)
                                         :exec (- len 1))
                                    floor2)))
  ///
  (defthm true-listp-of-vl-constint-lsb-bits-aux
    (true-listp (vl-constint-lsb-bits-aux len value))
    :rule-classes :type-prescription)
  (defthm len-of-vl-constint-lsb-bits-aux
    (equal (len (vl-constint-lsb-bits-aux len value))
           (nfix len))))


(define vl-constint-msb-bits-aux
  :parents (vl-constint->msb-bits)
  :short "Accumulate lsb's into acc, which produces an MSB-ordered list."
  ((len natp)
   (value natp)
   acc)
  :measure (nfix len)
  :enabled t
  (mbe :logic
       (revappend (vl-constint-lsb-bits-aux len value) acc)
       :exec
       (b* (((when (zp len))
             acc)
            (floor2           (mbe :logic (floor value 2)
                                   :exec (ash value -1)))
            ((the bit mod2)   (mbe :logic (mod value 2)
                                   :exec (logand value 1)))
            (bit              (if (eql mod2 0)
                                  :vl-0val
                                :vl-1val)))
         (vl-constint-msb-bits-aux (mbe :logic (- (nfix len) 1)
                                        :exec (- len 1))
                                   floor2
                                   (cons bit acc))))
    :prepwork
    ((local (in-theory (enable vl-constint-lsb-bits-aux)))))


(define vl-constint->msb-bits
  :parents (vl-constint-p)
  :short "Explode a <see topic='@(url vl-expr-welltyped-p)'>well-typed</see>
@(see vl-constint-p) atom into MSB-ordered @(see vl-bitlist-p)."

  ((x vl-expr-p))
  :guard (and (vl-atom-p x)
              (vl-atom-welltyped-p x)
              (vl-fast-constint-p (vl-atom->guts x)))
  :returns (bits vl-bitlist-p)

  :long "<p>We require that @('X') is a well-typed constant integer expression,
i.e., our @(see expression-sizing) transform should have already been run.
Note that the \"propagation step\" of expression sizing should have already
handled any sign/zero extensions, so we assume here that the atom's
@('finalwidth') is already correct and that no extensions are necessary.</p>"

  :prepwork
  ((local (in-theory (enable vl-atom-welltyped-p))))

  (vl-constint-msb-bits-aux (vl-atom->finalwidth x)
                            (vl-constint->value (vl-atom->guts x))
                            nil)
  ///
  (defthm true-listp-of-vl-constint->msb-bits
    (true-listp (vl-constint->msb-bits x))
    :rule-classes :type-prescription)
  (defthm len-of-vl-constint->msb-bits
    (equal (len (vl-constint->msb-bits x))
           (nfix (vl-atom->finalwidth x)))))


(local
 (assert! (equal (vl-constint->msb-bits
                  (make-vl-atom :guts (make-vl-constint :origwidth 5
                                                        :origtype :vl-signed
                                                        :value 7)
                                :finalwidth 5
                                :finaltype :vl-signed))
                 (list :vl-0val
                       :vl-0val
                       :vl-1val
                       :vl-1val
                       :vl-1val))))

(local
 (assert! (equal (vl-constint->msb-bits
                  (make-vl-atom :guts (make-vl-constint :origwidth 5
                                                        :origtype :vl-unsigned
                                                        :value 15)
                                :finalwidth 5
                                :finaltype :vl-unsigned))
                 (list :vl-0val
                       :vl-1val
                       :vl-1val
                       :vl-1val
                       :vl-1val))))



