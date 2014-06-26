; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "toe-emodwire")
(include-book "../mlib/range-tools")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/intersectp-equal"))


(defsection empty-intersect-of-vl-emodwires-by-basename

  (local (defthm equal-of-cons-rewrite
           (equal (equal (cons a b) x)
                  (and (consp x)
                       (equal (car x) a)
                       (equal (cdr x) b)))))

  (local (defthm replicate-len-hack
           (implies (equal x (replicate n a))
                    (equal (len x) (nfix n)))
           :rule-classes nil))

  (local (defthm l0
           (implies (and (equal (vl-emodwirelist->basenames x)
                                (replicate (len x) basename))
                         (member-equal a x))
                    (equal (vl-emodwire->basename a) basename))
           :hints(("Goal" :induct (len x)))))

  (local (defthm l1
           (implies (and (equal (vl-emodwirelist->basenames x)
                                (replicate n basename))
                         (member-equal a x))
                    (equal (vl-emodwire->basename a) basename))
           :hints(("Goal" :use ((:instance replicate-len-hack
                                           (x (vl-emodwirelist->basenames x))
                                           (a basename)
                                           (n n)))))))

  (local (defthm l2
           (implies (and (equal (vl-emodwirelist->basenames x)
                                (replicate (len x) basename))
                         (vl-emodwire-p a)
                         (vl-emodwirelist-p x))
                    (iff (member-equal a x)
                         (and (equal (vl-emodwire->basename a) basename)
                              (member-equal (vl-emodwire->index a)
                                            (vl-emodwirelist->indices x)))))
           :hints(("Goal" :induct (len x)))))

  (local (defthm l3
           (implies (and (equal (vl-emodwirelist->basenames x)
                                (replicate n basename))
                         (vl-emodwire-p a)
                         (vl-emodwirelist-p x))
                    (iff (member-equal a x)
                         (and (equal (vl-emodwire->basename a) basename)
                              (member-equal (vl-emodwire->index a)
                                            (vl-emodwirelist->indices x)))))
           :hints(("Goal" :use ((:instance replicate-len-hack
                                           (x (vl-emodwirelist->basenames x))
                                           (a basename)
                                           (n n)))))))

  (defthm empty-intersect-of-vl-emodwires-by-basename
    (implies (and (equal (vl-emodwirelist->basenames x) (replicate (len x) xname))
                  (equal (vl-emodwirelist->basenames y) (replicate (len y) yname))
                  (not (equal xname yname))
                  (vl-emodwirelist-p x)
                  (vl-emodwirelist-p y))
             (not (intersectp-equal x y)))))



(local (defthm no-duplicatesp-equal-when-no-duplicatesp-equal-of-vl-emodwirelist->indices
         (implies (no-duplicatesp-equal (vl-emodwirelist->indices x))
                  (no-duplicatesp-equal x))
         :hints(("Goal" :induct (len x)))))

(local (defthm no-duplicatesp-equal-when-no-duplicatesp-equal-of-vl-emodwirelist->basenames
         (implies (no-duplicatesp-equal (vl-emodwirelist->basenames x))
                  (no-duplicatesp-equal x))
         :hints(("Goal" :induct (len x)))))




(define vl-wirealist-p (x)
  :parents (exploding-vectors)
  :short "Associates wire names (strings) to lists of @(see vl-emodwire-p)s
which represent the wire's bits in <b>msb-first order</b>."

  :long "<p>A wire alist provides a bit-level view of the wires in a module by
associating the names of each net and register declared in the Verilog
module (strings) with lists of @(see vl-emodwire-p)s that represent the
individual bits of the wire, in msb-first order.</p>

<p>In particular,</p>

<ul>

<li>Given a range-free Verilog wire named @('w'), we bind the string @('\"w\"')
to @('(ACL2::w)'), i.e., a singleton list with just one symbol; and</li>

<li>Given a Verilog wire, @('w'), with range @('[high:low]'), we bind
@('\"w\"') to @('(ACL2::w[high] ... ACL2::w[low])'), i.e., a list of symbols
from high to low, inclusive.</li>

<li>Given a Verilog wire, @('w'), with range @('[low:high]'), we bind
@('\"w\"') to @('(ACL2::w[low] ... ACL2::w[high])').</li>

</ul>

<p>Our @(see vl-emodwire-p) representation is robust and can reliably deal with
wires no matter what their names.  We can guarantee that the bits produced in a
wire alist are unique as long as the net and register declarations for the
module are uniquely named.</p>

<p>We take special care to avoid generating the names @('T'), @('NIL'), and
@('F'), since these have a special special meaning in Emod; see @(see
vl-plain-wire-name).</p>

<h3>Efficiency Considerations</h3>

<p>Profiling might \"unfairly\" suggest that wire-alist construction is very
expensive.</p>

<p>In particular, the first time we build a wire alist for a module, we are
generally doing \"first-time\" @('intern')s for the names of every bit.  It is
far more expensive to @('intern') a string for the first time than to
subsequently @('intern') it again.  For instance, when we run the following
code in a fresh CCL session, we find that it takes 2.2 seconds to intern
100,000 fresh strings the first time, but it only takes 0.15 seconds to intern
them all again.</p>

@({
 (defpackage \"FOO\" (:use))

 (ccl::egc nil)

 (defparameter *strings*
  (loop for i fixnum from 1 to 100000
        collect
        (concatenate 'string \"FOO-\"
                     (format nil \"~a\" i))))

 ;; 2.21 seconds, 15 MB allocated
 (time (loop for str in *strings* do (intern str \"FOO\")))

 ;; 0.15 seconds, no allocation
 (time (loop for str in *strings* do (intern str \"FOO\")))
})

<p>When we are interning millions of symbols, the package's size also has a
huge impact on interning performance.  Because of this, we typically build ACL2
with @('ACL2_SIZE=3000000') to avoid very slow interning.</p>

<p>Moreover, whether we intern these symbols \"eagerly\" by constructing a wire
alist or \"lazily\" as they are needed, we will end up doing the same number of
first-time interns.  There is not really any way to avoid this interning
without either fundamentally changing the design of the E language (e.g., to
support vectors), or abandoning named wires in E modules (e.g., using numbers
instead).</p>"

;; bozo switch to defalist?

  (if (atom x)
      t
    (and (consp (car x))
         (stringp (caar x))
         (true-listp (cdar x))             ;; bozo why do we care?
         (vl-emodwirelist-p (cdar x))
         (vl-wirealist-p (cdr x))))
  ///
  (defthm vl-wirealist-p-when-atom
    (implies (atom x)
             (equal (vl-wirealist-p x)
                    t)))

  (defthm vl-wirealist-p-of-cons
    (equal (vl-wirealist-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (true-listp (cdr a))
                (vl-emodwirelist-p (cdr a))
                (vl-wirealist-p x))))

  (defthm cons-listp-when-vl-wirealist-p
    (implies (vl-wirealist-p x)
             (cons-listp x)))

  (defthm vl-wirealist-p-of-hons-shrink-alist
    (implies (and (vl-wirealist-p x)
                  (vl-wirealist-p y))
             (vl-wirealist-p (hons-shrink-alist x y)))
    :hints(("Goal" :in-theory (enable (:i hons-shrink-alist)))))

  (defthm vl-emodwirelist-p-of-cdr-of-hons-assoc-equal-when-vl-wirealist-p
    (implies (vl-wirealist-p walist)
             (vl-emodwirelist-p (cdr (hons-assoc-equal name walist)))))

  (defthm true-listp-of-cdr-of-hons-assoc-equal-when-vl-wirealist-p
    (implies (vl-wirealist-p walist)
             (true-listp (cdr (hons-assoc-equal name walist))))))



(define vl-plain-wire-name ((name stringp))
  :returns (emodwire vl-emodwire-p)
  :parents (vl-wirealist-p)
  :short "@(call vl-plain-wire-name) is given @('name'), a string, and
typically returns the symbol @('ACL2::name')."

  :long "<p>Typically, for a wire named @('foo'), we generate the symbol
@('ACL2::|foo|').  But there are three special cases.</p>

<p>The symbols @('ACL2::T') and @('ACL2::F') were historically given a special
interpretation by the EMOD hardware simulator, and represented the constant
true and false functions.  These wires no longer have a special meaning in
ESIM, but throughout VL our notion of emodwires still assumes that T and F
stand for constant true and false, and, e.g., we still rely on this in @(see
e-conversion).  We might eventually get away from this by using a transform
analagous to @(see weirdint-elim) to introduce T/F wires and eliminate
constants.</p>

<p>The symbol @('ACL2::NIL') is also special, but for a different and more
fundamental reason: NIL has a special meaning in @(see acl2::patterns), so to
make sure that every @(see vl-emodwire-p) is a good atom in the sense of
patterns, we do not allow NIL to even be an emodwire.</p>

<p>At any rate, if we encounter a Verilog wire named @('T'), @('F'), or
@('NIL'), we must use some other name.  What other name should we use?  We want
to pick something that will not clash with other wire names, but which reflects
the original name of the wire.</p>

<p>We have chosen to use @('T[0]'), @('F[0]'), and @('NIL[0]') as the
replacements.  This should not be too confusing since, e.g., in Verilog
@('T[0]') is typically a valid way to reference a wire named @('T').</p>"

; Performance comparison:
;   Logic:  6.286, 6.285, 6.298
;   Exec:  5.291, 5.232, 5.232

  #||
 (prog2$ (gc$)
        (time$
         (loop for i fixnum from 1 to 10000000 do
               (vl::vl-plain-wire-name "looksLikeAVerilogWire"))))
  ||#

  :inline t

  (mbe :logic
       (cond ((equal name "T")
              (make-vl-emodwire :basename "T" :index 0))
             ((equal name "F")
              (make-vl-emodwire :basename "F" :index 0))
             ((equal name "NIL")
              (make-vl-emodwire :basename "NIL" :index 0))
             (t
              (make-vl-emodwire :basename (string-fix name) :index nil)))
       :exec
       (let ((len (length name)))
         (cond ((and (= len 1)
                     (eql (char name 0) #\T))
                (make-vl-emodwire :basename "T" :index 0))
               ((and (= len 1)
                     (eql (char name 0) #\F))
                (make-vl-emodwire :basename "F" :index 0))
               ((and (= len 3)
                     (eql (char name 0) #\N)
                     (eql (char name 1) #\I)
                     (eql (char name 2) #\L))
                (make-vl-emodwire :basename "NIL" :index 0))
               (t
                (make-vl-emodwire :basename name :index nil)))))

  :guard-hints(("Goal" :in-theory (disable str::explode-under-iff)))
  :prepwork
  ((local (defthm equal-string-constant
            (implies (and (syntaxp (quotep name))
                          (stringp name))
                     (equal (equal x name)
                            (and (stringp x)
                                 (equal (explode x) (explode name)))))
            :hints(("Goal"
                    :in-theory (disable str::implode-of-explode)
                    :use ((:instance str::implode-of-explode (str::x x))
                          (:instance str::implode-of-explode (str::x name)))))))

   (local (defthm open-equal-len
            (implies (syntaxp (quotep n))
                     (equal (equal (len x) n)
                            (if (zp n)
                                (and (= n 0)
                                     (atom x))
                              (and (consp x)
                                   (equal (len (cdr x)) (- n 1))))))
            :hints(("Goal" :in-theory (enable len)))))

   (local (defthm open-nth
            (implies (syntaxp (quotep n))
                     (equal (nth n x)
                            (if (zp n)
                                (car x)
                              (nth (- n 1) (cdr x)))))
            :hints(("Goal" :in-theory (enable nth)))))

   (local (in-theory (enable len)))))



(defsection vl-emodwires-from-high-to-low
  :parents (vl-wirealist-p)
  :short "@(call vl-emodwires-from-high-to-low) returns a list of @(see
vl-emodwire-p)s: @('(name[high] name[high-1] ... name[low])')"

  :long "<p>The range is inclusive on both sides, so if @('low') and @('high')
are the same you still get one wire.</p>"

  ;; Here's a stupid performance testing loop.  It's somewhat sensitive to
  ;; how full the ACL2 package is.  The times below were gathered in a fresh
  ;; session that had just loaded the book up until here.

  #||
  (progn (gc$)
  (time$
  (loop for i from 1 to 1000000 do
  (vl::vl-emodwires-from-high-to-low "aTypicalWireName" 7 0))))
  ||#

  ;; On fv-1, after adding fast-cat:
  ;;   - Original version: 5.223 seconds, 896 MB
  ;;   - Tail-recursive version: 5.094 seconds, 896 MB
  ;;   - Tail-recursive, pre-encode names: 4.601 seconds, 896 MB
  ;;
  ;; So we're only 1.13x faster than the simple implementation.
  ;;
  ;; Note that the above loop interns 8 million symbols, which seems to
  ;; take 3.33 seconds all by itself:

  #||
  (progn (gc$)
  (time$
  (loop for i from 1 to 8000000 do
  (intern "aTypicalWireName" "ACL2"))))
  ||#

  ;; I don't really see a good way to do any better.  I tried making it faster
  ;; using raw-lisp code that would reuse a character array, but this caused
  ;; problems in CCL.  Looking at the CLHS documentation for "intern", it looks
  ;; like changing the contents of the string you've interned is undefined, so I
  ;; guess it's just not a valid optimization.

  (defund vl-emodwires-from-high-to-low-aux (name high low acc)
    ;; Name must be pre-encoded.
    (declare (type string name)
             (xargs :guard (and (natp high)
                                (natp low)
                                (>= high low))
                    :measure (nfix (- (nfix high) (nfix low)))))
    (b* ((name[low] (vl-emodwire-encoded name low))
         (acc       (cons name[low] acc))
         ((when (mbe :logic (<= (nfix high) (nfix low))
                     :exec (= high low)))
          acc))
      (vl-emodwires-from-high-to-low-aux name
                                         (lnfix high)
                                         (+ 1 (lnfix low))
                                         acc)))

  (definlined vl-emodwires-from-high-to-low-aux-fixnum (name high low acc)
    ;; Fixnum and otherwise optimized version of the above.
    (declare (type string name)
             (type (unsigned-byte 32) high)
             (type (unsigned-byte 32) low)
             (xargs :guard (>= high low)
                    :guard-hints(("Goal" :in-theory (enable vl-emodwire-encoded)))
                    :measure (nfix (- (nfix high)
                                      (nfix low)))))
    (b* ((name[low] (mbe :logic (vl-emodwire-encoded name low)
                         :exec (if (< (the (unsigned-byte 32) low) 256)
                                   (intern (cat name
                                                (aref1 '*vl-indexed-wire-name-array*
                                                       *vl-indexed-wire-name-array*
                                                       low))
                                           "ACL2")
                                 (intern (cat name "[" (natstr low) "]")
                                         "ACL2"))))
         (acc       (cons name[low] acc))
         ((when (mbe :logic (<= (nfix high) (nfix low))
                     :exec (= (the (unsigned-byte 32) high)
                              (the (unsigned-byte 32) low))))
          acc))
      (vl-emodwires-from-high-to-low-aux-fixnum name
                                                (lnfix high)
                                                (mbe :logic (+ 1 (nfix low))
                                                     :exec (the (unsigned-byte 32)
                                                             (+ low 1)))
                                                acc)))

  (local (defthm vl-emodwires-from-high-to-low-aux-fixnum-removal
           (equal (vl-emodwires-from-high-to-low-aux-fixnum name high low acc)
                  (vl-emodwires-from-high-to-low-aux name high low acc))
           :hints(("Goal" :in-theory (enable vl-emodwires-from-high-to-low-aux-fixnum
                                             vl-emodwires-from-high-to-low-aux)))))

  (defund vl-emodwires-from-high-to-low (name high low)
    (declare (type string name)
             (xargs :guard (and (natp high)
                                (natp low)
                                (>= high low))
                    :measure (nfix (- (nfix high) (nfix low)))))
    (mbe :logic
         (vl-emodwires-from-high-to-low-aux (vl-emodwire-encode (string-fix name))
                                            (nfix high)
                                            (nfix low)
                                            nil)
         :exec
         (let ((name (vl-emodwire-encode name)))
           (if (< high (expt 2 30))
               (vl-emodwires-from-high-to-low-aux-fixnum name high low nil)
             (vl-emodwires-from-high-to-low-aux name high low nil)))))

  (local (assert!
          ;; Basic sanity check, handy when mucking with the definition
          (and (equal (vl-emodwires-from-high-to-low "foo" 5 0)
                      #!ACL2 '(|foo[5]| |foo[4]| |foo[3]| |foo[2]| |foo[1]| |foo[0]|))
               (equal (vl-emodwires-from-high-to-low "foo" 5 3)
                      #!ACL2 '(|foo[5]| |foo[4]| |foo[3]|))
               (equal (vl-emodwires-from-high-to-low "foo" 5 5)
                      #!ACL2 '(|foo[5]|)))))



  (local (defun simpler-aux-function (name high low acc)
           (declare (xargs :measure (nfix (- (nfix high) (nfix low)))))
           (b* ((name[low] (make-vl-emodwire :basename name :index low))
                (acc       (cons name[low] acc))
                ((when (<= (nfix high) (nfix low)))
                 acc))
             (simpler-aux-function name (nfix high) (+ 1 (nfix low)) acc))))

  (local (defthm vl-emodwires-from-high-to-low-aux-removal
           (equal (vl-emodwires-from-high-to-low-aux (vl-emodwire-encode name) high low acc)
                  (simpler-aux-function name high low acc))
           :hints(("Goal" :in-theory (enable vl-emodwires-from-high-to-low-aux
                                             vl-emodwire-is-vl-emodwire-exec
                                             vl-emodwire-exec)))))

  (local (defthm true-listp-of-simpler-aux-function
           (implies (true-listp acc)
                    (true-listp (simpler-aux-function name high low acc)))
           :rule-classes :type-prescription))

  (local (defthm vl-emodwirelist-p-of-simpler-aux-function
           (implies (and (force (vl-emodwirelist-p acc))
                         (force (stringp name))
                         (force (natp high))
                         (force (natp low)))
                    (vl-emodwirelist-p (simpler-aux-function name high low acc)))))

  (local (defthm len-of-simpler-aux-function
           (equal (len (simpler-aux-function name high low acc))
                  (+ 1
                     (nfix (- (nfix high) (nfix low)))
                     (len acc)))))

  (local (defthm cons-same-onto-replicate
           (equal (cons a (replicate n a))
                  (replicate (+ 1 (nfix n)) a))
           :hints(("Goal" :in-theory (enable replicate)))))

  (local (defthm vl-emodwirelist->basenames-of-simpler-aux-function
           (implies (and (stringp name)
                         (natp high)
                         (natp low))
                    (equal (vl-emodwirelist->basenames (simpler-aux-function name high low acc))
                           (append (replicate (+ 1 (nfix (- (nfix high) (nfix low)))) name)
                                   (vl-emodwirelist->basenames acc))))
           :hints(("Goal" :do-not '(generalize fertilize)))))

  (local (defthm member-equal-of-indicies-of-simpler-aux-function
           (implies (and (stringp name)
                         (natp high)
                         (natp low)
                         (>= high low))
                    (iff (member-equal idx (vl-emodwirelist->indices
                                            (simpler-aux-function name high low acc)))
                         (or (and (natp idx)
                                  (<= low idx)
                                  (<= idx high))
                             (member-equal idx (vl-emodwirelist->indices acc)))))
           :hints(("Goal" :in-theory (disable (force))))))

  (local (defun nats-from (low high)
           (declare (xargs :measure (nfix (- (nfix high) (nfix low)))))
           (if (zp (- (nfix high) (nfix low)))
               (list (nfix low))
             (cons (nfix low)
                   (nats-from (+ 1 (nfix low)) (nfix high))))))

  (local (defthm member-equal-of-nats-from
           (implies (and (natp low)
                         (natp high)
                         (<= low high))
                    (iff (member-equal idx (nats-from low high))
                         (and (natp idx)
                              (<= (nfix low) idx)
                              (<= idx (nfix high)))))
           :hints(("Goal" :induct (nats-from low high)))))

  (local (defthm unique-indicies-of-simpler-aux-function
           (implies (and (stringp name)
                         (natp high)
                         (natp low)
                         (no-duplicatesp-equal (vl-emodwirelist->indices acc))
                         (not (intersectp-equal (vl-emodwirelist->indices acc)
                                                (nats-from low high))))
                    (no-duplicatesp-equal
                     (vl-emodwirelist->indices
                      (simpler-aux-function name high low acc))))
           :hints(("Goal" :in-theory (disable (force))))))

  (local (in-theory (enable vl-emodwires-from-high-to-low)))

  (defthm true-listp-of-vl-emodwires-from-high-to-low
    (true-listp (vl-emodwires-from-high-to-low name high low))
    :rule-classes :type-prescription)

  (defthm vl-emodwirelist-p-of-vl-emodwires-from-high-to-low
    (vl-emodwirelist-p (vl-emodwires-from-high-to-low name high low)))

  (defthm basenames-of-vl-emodwires-from-high-to-low
    (equal (vl-emodwirelist->basenames (vl-emodwires-from-high-to-low name high low))
           (replicate (len (vl-emodwires-from-high-to-low name high low))
                   (string-fix name))))

  (defthm member-equal-of-indicies-of-vl-emodwires-from-high-to-low
    (implies (>= (nfix high) (nfix low))
             (iff (member-equal idx (vl-emodwirelist->indices
                                     (vl-emodwires-from-high-to-low name high low)))
                  (and (natp idx)
                       (<= (nfix low) idx)
                       (<= idx (nfix high))))))

  (defthm unique-indicies-of-vl-emodwires-from-high-to-low
    (no-duplicatesp-equal
     (vl-emodwirelist->indices
      (vl-emodwires-from-high-to-low name high low))))

  (local (defthm d0
           (implies (no-duplicatesp-equal (vl-emodwirelist->indices x))
                    (no-duplicatesp-equal x))
           :hints(("Goal" :in-theory (enable vl-emodwirelist->indices)))))

  (defthm no-duplicatesp-equal-of-vl-emodwires-from-high-to-low
    (no-duplicatesp-equal (vl-emodwires-from-high-to-low name high low)))

  (defthm len-of-vl-emodwires-from-high-to-low
    (equal (len (vl-emodwires-from-high-to-low name high low))
           (+ 1 (nfix (- (nfix high) (nfix low)))))))




(define vl-emodwires-from-msb-to-lsb
  :parents (vl-wirealist-p)
  :short "@(call vl-emodwires-from-msb-to-lsb) returns a list of @(see
vl-emodwire-p)s: @('(name[msb] name[msb +/- 1] ... name[lsb])')"
  ((name stringp)
   (msb  natp)
   (lsb  natp))
  :long "<p>The range is inclusive on both sides, so if @('msb') and @('lsb')
are the same you still get one wire.</p>"
  :enabled t
  ;; We think most ranges we'll encounter are [high:low], so we don't bother to
  ;; optimize the reverse case, but it would be easy enough to do if it's slow.
  (b* ((high          (max msb lsb))
       (low           (min msb lsb))
       (|w[high:low]| (vl-emodwires-from-high-to-low name high low))
       (|w[msb:lsb]|  (if (>= msb lsb)
                          |w[high:low]|
                        ;; Unusual case of a wire like w[0:3], so the
                        ;; w[high:low] is in the wrong order.
                        (reverse |w[high:low]|))))
    |w[msb:lsb]|))


(define vl-netdecl-msb-emodwires
  :parents (vl-wirealist-p)
  :short "Compute the @(see vl-emodwire-p)s for a net declaration, in MSB-first order."
  ((x        vl-netdecl-p)
   (warnings vl-warninglist-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (emodwires vl-emodwirelist-p))
  (b* (((vl-netdecl x) x)
       ((when x.arrdims)
        (mv nil
            (fatal :type :vl-bad-netdecl
                   :msg "~a0 has array dimensions, which are not supported."
                   :args (list x))
            nil))

       ((when (not (vl-maybe-range-resolved-p x.range)))
        (mv nil
            (fatal :type :vl-bad-netdecl
                   :msg "~a0 has unresolved range ~a1."
                   :args (list x x.range))
            nil))

       ((when (not x.range))
        (mv t (ok) (list (vl-plain-wire-name x.name))))

       (msb          (vl-resolved->val (vl-range->msb x.range)))
       (lsb          (vl-resolved->val (vl-range->lsb x.range)))
       (|w[msb:lsb]| (vl-emodwires-from-msb-to-lsb x.name msb lsb)))
    (mv t (ok) |w[msb:lsb]|))
  ///
  (local (in-theory (enable vl-netdecl-msb-emodwires)))

  (defthm true-listp-of-vl-netdecl-msb-emodwires
    (true-listp (mv-nth 2 (vl-netdecl-msb-emodwires x warnings)))
    :rule-classes :type-prescription)

  (defthm basenames-of-vl-netdecl-msb-emodwires
    (implies (vl-netdecl-p x)
             (let ((wires (mv-nth 2 (vl-netdecl-msb-emodwires x warnings))))
               (equal (vl-emodwirelist->basenames wires)
                      (replicate (len wires) (vl-netdecl->name x)))))
    :hints(("Goal" :in-theory (enable vl-plain-wire-name))))

  (defthm unique-indicies-of-vl-netdecl-msb-emodwires
    (no-duplicatesp-equal
     (vl-emodwirelist->indices
      (mv-nth 2 (vl-netdecl-msb-emodwires x warnings))))))


(define vl-netdecllist-to-wirealist
  :parents (vl-wirealist-p)
  :short "Generate a (fast) wirealist from a @(see vl-netdecllist-p)."
  ((x        vl-netdecllist-p)
   (warnings vl-warninglist-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription
                         "Whether <em>all</em> nets were successfully converted
                          into wire-alist entries.")
               (warnings vl-warninglist-p)
               (walist   vl-wirealist-p))
  :long "<p>Even if @('successp') is @('nil'), we will produce at least a
partial wire alist for this module which is as complete as possible.  Any
failure will result in at least one fatal warning.</p>"

  (b* (((when (atom x))
        (mv t (ok) nil))
       ((mv successp1 warnings wires1)
        (vl-netdecl-msb-emodwires (car x) warnings))
       ((mv successp2 warnings walist)
        (vl-netdecllist-to-wirealist (cdr x) warnings))
       (successp (and successp1 successp2))
       (walist   (if successp1
                     (hons-acons (vl-netdecl->name (car x)) wires1 walist)
                   walist)))
    (mv successp warnings walist))
  ///
  (defthm subsetp-equal-of-strip-cars-of-vl-netdecllist-to-wirealist
    (subsetp-equal (strip-cars (mv-nth 2 (vl-netdecllist-to-wirealist x warnings)))
                   (vl-netdecllist->names x))))

(define vl-vardecl-msb-emodwires
  :parents (vl-wirealist-p)
  :short "Same as @(see vl-netdecl-msb-emodwires), but for variables."
  ((x        vl-vardecl-p)
   (warnings vl-warninglist-p))
  :returns (mv (successp  booleanp :rule-classes :type-prescription)
               (warnings  vl-warninglist-p)
               (emodwires vl-emodwirelist-p))
  (b* (((vl-vardecl x) x)
       ((unless (vl-simplereg-p x))
        (mv nil
            (fatal :type :vl-bad-vardecl
                   :msg "~a0 is not yet supported: we only handle simple reg/logic ~
                         wires with at most a single range."
                   :args (list x))
            nil))
       (range (vl-simplereg->range x))
       ((unless (vl-maybe-range-resolved-p range))
        (mv nil
            (fatal :type :vl-bad-vardecl
                   :msg "~a0 has unresolved range ~a1."
                   :args (list x range))
            nil))
       ((unless range)
        (mv t (ok) (list (vl-plain-wire-name x.name))))
       (msb          (vl-resolved->val (vl-range->msb range)))
       (lsb          (vl-resolved->val (vl-range->lsb range)))
       (|w[msb:lsb]| (vl-emodwires-from-msb-to-lsb x.name msb lsb)))
    (mv t (ok) |w[msb:lsb]|))
  ///
  (defthm true-listp-of-vl-vardecl-msb-emodwires
    (true-listp (mv-nth 2 (vl-vardecl-msb-emodwires x warnings)))
    :rule-classes :type-prescription)

  (defthm basenames-of-vl-vardecl-msb-emodwires
    (implies (vl-vardecl-p x)
             (let ((wires (mv-nth 2 (vl-vardecl-msb-emodwires x warnings))))
               (equal (vl-emodwirelist->basenames wires)
                      (replicate (len wires) (vl-vardecl->name x)))))
    :hints(("Goal" :in-theory (enable vl-plain-wire-name))))

  (defthm unique-indicies-of-vl-vardecl-msb-emodwires
    (no-duplicatesp-equal
     (vl-emodwirelist->indices
      (mv-nth 2 (vl-vardecl-msb-emodwires x warnings))))))


(defsection vl-vardecllist-to-wirealist
  :parents (vl-wirealist-p)
  :short "Same as @(see vl-netdecllist-to-wirealist), but for variables."

  (defund vl-vardecllist-to-wirealist (x warnings)
    (declare (xargs :guard (and (vl-vardecllist-p x)
                                (vl-warninglist-p warnings))))
    (if (atom x)
        (mv t warnings nil)
      (b* (((mv successp1 warnings wires1)
            (vl-vardecl-msb-emodwires (car x) warnings))
           ((mv successp2 warnings walist)
            (vl-vardecllist-to-wirealist (cdr x) warnings))
           (successp (and successp1 successp2))
           (walist   (if successp1
                         (hons-acons (vl-vardecl->name (car x)) wires1 walist)
                       walist)))
        (mv successp warnings walist))))

  (local (in-theory (enable vl-vardecllist-to-wirealist)))

  (defthm vl-warninglist-p-of-vl-vardecllist-to-wirealist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-vardecllist-to-wirealist x warnings)))))

  (defthm vl-wirealist-p-of-vl-vardecllist-to-wirealist
    (implies (force (vl-vardecllist-p x))
             (vl-wirealist-p (mv-nth 2 (vl-vardecllist-to-wirealist x warnings)))))

  (defthm subsetp-equal-of-strip-cars-of-vl-vardecllist-to-wirealist
    (subsetp-equal (strip-cars (mv-nth 2 (vl-vardecllist-to-wirealist x warnings)))
                   (vl-vardecllist->names x))))


(defsection vl-module-wirealist
  :parents (vl-wirealist-p)
  :short "Safely generate the (fast) wirealist for a module."

  :long "<p><b>Signature:</b> @(call vl-module-wirealist) returns @('(mv
successp warnings walist)').</p>

<p>Note: this function is memoized and generates fast alists.  You should be
sure to clear its memo table so that these fast alists can be garbage
collected.</p>

<p>This function can fail, setting @('successp') to @('nil') and adding fatal
warnings, when:</p>

<ul>

<li>there's a problem with the module's namespace, i.e., the net/reg names
are not unique,</li>

<li>the range of some net/reg has not been resolved, or</li>

<li>some net/reg has arrdims (i.e., it's a \"2 dimensional array\" or
higher)</li>

</ul>

<p>But unless the failure is due to a namespace problem, the resulting wire
alist will be at least a partial wire alist for this module that has entries
for all of the wires that don't have problems.</p>

<p>A key property of this function is that the wire alist it generates binds
completely unique bits to all of the wires.  This is proven as the following
theorem:</p>

@(thm no-duplicatesp-equal-of-append-alist-vals-of-vl-module-wirealist)"

  (defund vl-module-wirealist (x warnings)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-warninglist-p warnings))))
    (b* (((vl-module x) x)

; Name uniqueness check.
;
; Note this uniqueness check is on the module's net and register names and NOT
; on the generated name lists.  This is a performance win since each name might
; expand into lots of bits.  This appears to be taking about 8% of the runtime
; in practice.
;
; I once thought that a fast-alist style check might be better than using
; uniquep.  Here is some code:
;
; (defun no-dupe-netdecls-names (x alist)
;   (declare (xargs :guard (vl-netdecllist-p x)))
;   (if (atom x)
;       (mv t alist)
;     (let ((name1 (vl-netdecl->name (car x))))
;       (if (hons-get name1 alist)
;           (mv nil alist)
;         (let ((alist (hons-acons name1 t alist)))
;           (no-dupe-netdecls-names (cdr x) alist))))))
;
; (defun no-dupe-regdecls-names (x alist)
;   (declare (xargs :guard (vl-regdecllist-p x)))
;   (if (atom x)
;       (mv t alist)
;     (let ((name1 (vl-regdecl->name (car x))))
;       (if (hons-get name1 alist)
;           (mv nil alist)
;         (let ((alist (hons-acons name1 t alist)))
;           (no-dupe-regdecls-names (cdr x) alist))))))
;
; But this was MUCH slower than uniquep in my benchmarks, even when building
; an appropriately-sized alist, even when all of the names were pre-honsed.
;
; BOZO it might be worth looking into how strings are handled in the honsing
; code and revisiting this.  In particular, when we look up a string right now,
; we have to do an EQUAL hash to find its canonical version, even if we're
; staring right at its canonical version.  It might be better to add another EQ
; hash table, say the STR-HT-EQ, that would associate canonical versions of
; strings with themselves.  Then, when checking if a string is honsed, we could
; first look in this EQ hash table, and only look in the EQL hash table if
; there has been a failure.  This would add some space overhead.  It would also
; cost (very slightly) more time when we initially hons strings, and make
; looking up non-honsed strings slightly more expensive.  But it might
; dramatically improve the performance of looking up honsed strings, which
; would give us a nice improvement here.
;
; BOZO this might also be due to fast-alist sentinel problems in previous
; versions of the Hons code, you may wish to revisit it!

         ((unless (mbe :logic
                       (uniquep (append (vl-netdecllist->names x.netdecls)
                                        (vl-vardecllist->names x.vardecls)))
                       :exec
                       (let* ((names (vl-netdecllist->names-exec x.netdecls nil))
                              (names (vl-vardecllist->names-exec x.vardecls names)))
                         (uniquep names))))
          (mv nil
              (cons (make-vl-warning :type :vl-namespace-error
                                     :msg "~m0 illegally redefines ~&1."
                                     :args (list x.name
                                                 (duplicated-members
                                                  (append (vl-netdecllist->names x.netdecls)
                                                          (vl-vardecllist->names x.vardecls))))
                                     :fatalp t
                                     :fn 'vl-modwire-alist)
                    warnings)
              nil))

         ((mv successp1 warnings net-walist)
          (vl-netdecllist-to-wirealist x.netdecls warnings))
         ((mv successp2 warnings reg-walist)
          (vl-vardecllist-to-wirealist x.vardecls warnings))

         ;; In practice this hons-shrink-alist shouldn't really be more
         ;; expensive than having used an accumulator, because most modules
         ;; have very few registers.
         (walist   (hons-shrink-alist reg-walist net-walist))

         ;; Walist stole the hash table for net-walist, but we still need
         ;; to free the reg-walist.
         (- (fast-alist-free reg-walist))
         (successp (and successp1 successp2)))
      (mv successp warnings walist)))

  (local (in-theory (enable vl-module-wirealist)))

  (defthm vl-warninglist-p-of-vl-module-wirealist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-module-wirealist x warnings)))))

  (defthm vl-wirealist-p-of-vl-module-wirealist
    (implies (force (vl-module-p x))
             (vl-wirealist-p (mv-nth 2 (vl-module-wirealist x warnings)))))

  (memoize 'vl-module-wirealist))


(defsection no-duplicatesp-equal-of-append-alist-vals-of-vl-module-wirealist

  (defthm equal-of-cons-rewrite
    (equal (equal (cons a b) x)
           (and (consp x)
                (equal (car x) a)
                (equal (cdr x) b))))

  (local (defthm append-alist-vals-removal
           (equal (append-alist-vals x)
                  (flatten (strip-cdrs x)))
           :hints(("Goal" :induct (len x)))))

  (local
   (defsection vardecls

     (defthm rcars
       (implies (no-duplicatesp-equal (vl-vardecllist->names x))
                (no-duplicatesp-equal
                 (strip-cars (mv-nth 2 (vl-vardecllist-to-wirealist x warnings)))))
       :hints(("Goal" :in-theory (enable vl-vardecllist-to-wirealist))))

     (local
      (defthm r0
        (implies (and (not (member-equal (vl-vardecl->name a)
                                         (vl-vardecllist->names x)))
                      ;(force (vl-vardecl-p a))
                      (consp x)
                      )
                 (not (equal (vl-vardecl->name a)
                             (vl-vardecl->name (first x)))))))

     (local
      (defthm r1
        (implies (and (force (not (equal (vl-vardecl->name a)
                                         (vl-vardecl->name b))))
                      (force (vl-vardecl-p a))
                      (force (vl-vardecl-p b)))
                 (not (intersectp-equal
                       (mv-nth 2 (vl-vardecl-msb-emodwires a warnings1))
                       (mv-nth 2 (vl-vardecl-msb-emodwires b warnings2)))))
        :hints(("Goal"
                :use ((:instance empty-intersect-of-vl-emodwires-by-basename
                                 (xname (vl-vardecl->name a))
                                 (yname (vl-vardecl->name b))
                                 (x (mv-nth 2 (vl-vardecl-msb-emodwires a warnings1)))
                                 (y (mv-nth 2 (vl-vardecl-msb-emodwires b warnings2)))))))))

     (local
      (defthm r2
        (let ((r-wires          (mv-nth 2 (vl-vardecl-msb-emodwires r warnings1)))
              (other-wire-lists (strip-cdrs (mv-nth 2 (vl-vardecllist-to-wirealist others warnings2)))))
          (implies (and (force (not (member-equal (vl-vardecl->name r)
                                                  (vl-vardecllist->names others))))
                        (force (vl-vardecl-p r))
                        (force (vl-vardecllist-p others)))
                   (empty-intersect-with-each-p r-wires
                                                other-wire-lists)))
        :hints(("Goal"
                :induct (vl-vardecllist-to-wirealist others warnings2)
                :in-theory (enable vl-vardecllist-to-wirealist)))))

     (defthm rcdrs
       (implies (and (no-duplicatesp-equal (vl-vardecllist->names x))
                     (force (vl-vardecllist-p x)))
                (no-duplicatesp-equal
                 (flatten (strip-cdrs (mv-nth 2 (vl-vardecllist-to-wirealist x warnings))))))
       :hints(("Goal"
               :in-theory (enable vl-vardecllist-to-wirealist)
               :induct (vl-vardecllist-to-wirealist x warnings))))))


  ;; Lemmas for netdecls... same as vardecls.

  (local
   (defsection netdecls

     (defthm ncars
       (implies (no-duplicatesp-equal (vl-netdecllist->names x))
                (no-duplicatesp-equal
                 (strip-cars (mv-nth 2 (vl-netdecllist-to-wirealist x warnings)))))
       :hints(("Goal" :in-theory (enable vl-netdecllist-to-wirealist))))

     (local
      (defthm n0
        (implies (and (not (member-equal (vl-netdecl->name a)
                                         (vl-netdecllist->names x)))
                      ;; (force (vl-netdecl-p a))
                      (force (consp x))
                      )
                 (not (equal (vl-netdecl->name a)
                             (vl-netdecl->name (first x)))))))

     (local
      (defthm n1
        (implies (and (force (not (equal (vl-netdecl->name a)
                                         (vl-netdecl->name b))))
                      (force (vl-netdecl-p a))
                      (force (vl-netdecl-p b)))
                 (not (intersectp-equal
                       (mv-nth 2 (vl-netdecl-msb-emodwires a warnings1))
                       (mv-nth 2 (vl-netdecl-msb-emodwires b warnings2)))))
        :hints(("Goal"
                :use ((:instance empty-intersect-of-vl-emodwires-by-basename
                                 (xname (vl-netdecl->name a))
                                 (yname (vl-netdecl->name b))
                                 (x (mv-nth 2 (vl-netdecl-msb-emodwires a warnings1)))
                                 (y (mv-nth 2 (vl-netdecl-msb-emodwires b warnings2)))))))))

     (local
      (defthm n2
        (let ((r-wires          (mv-nth 2 (vl-netdecl-msb-emodwires r warnings1)))
              (other-wire-lists (strip-cdrs (mv-nth 2 (vl-netdecllist-to-wirealist others warnings2)))))
          (implies (and (force (not (member-equal (vl-netdecl->name r)
                                                  (vl-netdecllist->names others))))
                        (force (vl-netdecl-p r))
                        (force (vl-netdecllist-p others)))
                   (empty-intersect-with-each-p r-wires
                                                other-wire-lists)))
        :hints(("Goal"
                :induct (vl-netdecllist-to-wirealist others warnings2)
                :in-theory (enable vl-netdecllist-to-wirealist)))))

     (defthm ncdrs
       (implies (and (no-duplicatesp-equal (vl-netdecllist->names x))
                     (force (vl-netdecllist-p x)))
                (no-duplicatesp-equal
                 (flatten (strip-cdrs (mv-nth 2 (vl-netdecllist-to-wirealist x warnings))))))
       :hints(("Goal"
               :in-theory (enable vl-netdecllist-to-wirealist)
               :induct (vl-netdecllist-to-wirealist x warnings))))))


  (local
   (defsection var/netdecls

; One more lemma to show there aren't any duplicates between the separate
; var/net declarations.

     (local
      (defthm rn-0
        (let ((wires (strip-cdrs (mv-nth 2 (vl-vardecllist-to-wirealist x warnings)))))
          (implies (force (vl-vardecllist-p x))
                   (subsetp-equal (vl-emodwirelist->basenames (flatten wires))
                                  (vl-vardecllist->names x))))
        :hints(("Goal"
                :induct (vl-vardecllist-to-wirealist x warnings)
                :in-theory (enable vl-vardecllist-to-wirealist))
               (set-reasoning))))

     (local
      (defthm rn-1
        (let ((wires (strip-cdrs (mv-nth 2 (vl-netdecllist-to-wirealist x warnings)))))
          (implies (force (vl-netdecllist-p x))
                   (subsetp-equal (vl-emodwirelist->basenames (flatten wires))
                                  (vl-netdecllist->names x))))
        :hints(("Goal"
                :induct (vl-netdecllist-to-wirealist x warnings)
                :in-theory (enable vl-netdecllist-to-wirealist))
               (set-reasoning))))

     (local
      (defthm rn-2
        (let ((nwires (strip-cdrs (mv-nth 2 (vl-netdecllist-to-wirealist nets warnings1))))
              (rwires (strip-cdrs (mv-nth 2 (vl-vardecllist-to-wirealist vars warnings2)))))
          (implies (and (force (not (intersectp-equal
                                     (vl-vardecllist->names vars)
                                     (vl-netdecllist->names nets))))
                        (force (vl-netdecllist-p nets))
                        (force (vl-vardecllist-p vars)))
                   (not (intersectp-equal
                         (vl-emodwirelist->basenames (flatten nwires))
                         (vl-emodwirelist->basenames (flatten rwires))))))))

     (local
      (defthm crock
        (implies (not (intersectp-equal (vl-emodwirelist->basenames x)
                                        (vl-emodwirelist->basenames y)))
                 (not (intersectp-equal x y)))
        :hints(("Goal" :induct (len x)))))

     (defthm var/netdecls
       (let ((nwires (strip-cdrs (mv-nth 2 (vl-netdecllist-to-wirealist nets warnings1))))
             (rwires (strip-cdrs (mv-nth 2 (vl-vardecllist-to-wirealist vars warnings2)))))
         (implies (and (force (not (intersectp-equal
                                    (vl-vardecllist->names vars)
                                    (vl-netdecllist->names nets))))
                       (force (vl-netdecllist-p nets))
                       (force (vl-vardecllist-p vars)))
                  (not (intersectp-equal (flatten nwires)
                                         (flatten rwires))))))))


; These decompose the main goal so that our lemmas apply:

  (local (defthm hons-assoc-equal-under-iff
           (implies (cons-listp x)
                    (iff (hons-assoc-equal a x)
                         (member-equal a (strip-cars x))))
           :hints(("Goal" :in-theory (enable hons-assoc-equal
                                             strip-cars)))))

  (local (defthm unique-hons-shrink-alist-is-revappend
           ;; Forcing this in general would be terrible, but for this proof
           ;; it's what we want to do.
           (implies (and (force (no-duplicatesp-equal (strip-cars x)))
                         (force (not (intersectp-equal (strip-cars x) (strip-cars y))))
                         (force (cons-listp x))
                         (force (cons-listp y)))
                    (equal (hons-shrink-alist x y)
                           (revappend x y)))
           :hints(("Goal" :in-theory (enable hons-shrink-alist)))))

  (local (in-theory (enable vl-module-wirealist)))

  (defthm no-duplicatesp-equal-of-append-alist-vals-of-vl-module-wirealist
    (implies (vl-module-p x)
             (let ((walist (mv-nth 2 (vl-module-wirealist x warnings))))
               (no-duplicatesp-equal (append-alist-vals walist))))))



(defsection vl-msb-constint-bitlist
  :parents (vl-msb-expr-bitlist)
  :short "Produce the @(see vl-emodwire-p)s for a @(see vl-constint-p)."

  :long "<p><b>Signature:</b> @(call vl-msb-constint-bitlist) returns @('(mv
successp warnings bits)').</p>

<p>In @('defm') commands, the symbols @('ACL2::t') and @('ACL2::f') are
interpreted as literal 1 and 0 bits.</p>

<p>We are given an atomic, constant integer expression.  This expression has
some width and value.  We return a <i>width</i>-long list of symbols
@('ACL2::T') or @('ACL2::F') that represent this <i>value</i>.</p>"

  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

  (defund vl-msb-constint-bitlist-aux (value acc)
    "Produce an MSB-ordered list of the bits for some value."
    (declare (xargs :guard (natp value)
                    :measure (nfix value)))
    (if (mbe :logic (zp value)
             :exec (= value 0))
        acc
      (let* ((floor2 (mbe :logic (floor value 2)
                          :exec (ash value -1)))
             (mod2   (mbe :logic (mod value 2)
                          :exec (rem value 2)))
             (bit    (if (= mod2 0)
                         'acl2::f
                       'acl2::t)))
        (vl-msb-constint-bitlist-aux floor2
                                     (cons bit acc)))))

  (defthm true-listp-of-vl-msb-constint-bitlist-aux
    (implies (true-listp acc)
             (true-listp (vl-msb-constint-bitlist-aux value acc)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable vl-msb-constint-bitlist-aux))))

  (defthm vl-emodwirelist-p-of-vl-msb-constint-bitlist-aux
    (implies (vl-emodwirelist-p acc)
             (vl-emodwirelist-p (vl-msb-constint-bitlist-aux value acc)))
    :hints(("Goal" :in-theory (enable vl-msb-constint-bitlist-aux))))


  (defund vl-msb-constint-bitlist (x warnings)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-atom-p x)
                                (vl-constint-p (vl-atom->guts x))
                                (vl-warninglist-p warnings))))
    (b* ((width (vl-atom->finalwidth x))
         (guts  (vl-atom->guts x))
         (value (vl-constint->value guts))

         ((unless width)
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "Cannot generate wires for ~a0 because it does not have ~
                         a finalwidth."
                   :args (list x)
                   :fatalp t
                   :fn 'vl-msb-constint-bitlist)))
            (mv nil (cons w warnings) nil)))

         (bits (vl-msb-constint-bitlist-aux value nil))
         (blen (length bits))

         ((when (equal blen width))
          ;; Already the right width.  No need to pad.
          (mv t warnings bits))

         ((when (< blen width))
          ;; Sometimes we need to pad with extra F bits to get to the
          ;; appropriate width.
          (mv t warnings
              (make-list-ac (- width blen) 'acl2::f bits)))

         ;; Else, more bits than the width permits?  This shouldn't ever happen
         ;; if our sizing code is right.
         (w (make-vl-warning :type :vl-programming-error
                             :msg "Produced too many wires for ~a0. ~
                                   Finalwidth: ~x1.  ~x2 Bits: ~x3."
                             :args (list x (vl-atom->finalwidth x) blen bits)
                             :fatalp t
                             :fn 'vl-msb-constint-bitlist)))

      (mv nil (cons w warnings) nil)))

  ;; Some basic unit tests.
  (local (assert!
          (let ((f 'acl2::f))
            (flet ((test-ok (width val expect)
                            (mv-let (successp warnings bits)
                              (vl-msb-constint-bitlist
                               (make-vl-atom :finalwidth width
                                             :finaltype :vl-unsigned
                                             :guts (make-vl-constint
                                                    :origwidth width
                                                    :origtype :vl-unsigned
                                                    :value val))
                               nil)
                              (and successp
                                   (not warnings)
                                   (equal bits expect)))))
                  (debuggable-and
                   (test-ok 8 0    (list f f f f   f f f f))
                   (test-ok 8 1    (list f f f f   f f f t))
                   (test-ok 8 15   (list f f f f   t t t t))
                   (test-ok 8 127  (list f t t t   t t t t))
                   (test-ok 8 128  (list t f f f   f f f f))

                   (test-ok 10 0   (list f f   f f f f   f f f f))
                   (test-ok 10 1   (list f f   f f f f   f f f t))
                   (test-ok 10 15  (list f f   f f f f   t t t t))
                   (test-ok 10 127 (list f f   f t t t   t t t t))
                   (test-ok 10 128 (list f f   t f f f   f f f f)))))))

  (defmvtypes vl-msb-constint-bitlist (booleanp nil true-listp))

  (local (in-theory (enable vl-msb-constint-bitlist)))

  (defthm vl-warninglist-p-of-vl-msb-constint-bitlist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-msb-constint-bitlist x warnings))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm true-listp-of-vl-msb-constint-bitlist-1
    (implies (true-listp warnings)
             (true-listp (mv-nth 1 (vl-msb-constint-bitlist x warnings))))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (disable (force)))))

  (local (defthm vl-emodwirelist-p-of-make-list-ac
           (implies (and (vl-emodwirelist-p ac)
                         (vl-emodwire-p val))
                    (vl-emodwirelist-p (make-list-ac n val ac)))))

  (defthm vl-emodwirelist-p-of-vl-msb-constint-bitlist
    (vl-emodwirelist-p (mv-nth 2 (vl-msb-constint-bitlist x warnings)))
    :hints(("Goal" :in-theory (disable (force))))))



(defsection vl-msb-wire-bitlist
  :parents (vl-msb-expr-bitlist)
  :short "Produce the @(see vl-emodwire-p)s for a @(see vl-id-p)."

  :long "<p><b>Signature:</b> @(call vl-msb-wire-bitlist) returns @('(mv
successp warnings bits)').</p>

<p>We are given an atomic, identifier expression.  This expression has some
width and refers to a particular wire.  We return a wires associated with this
name in MSB order.</p>"

  (defund vl-msb-wire-bitlist (x walist warnings)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-atom-p x)
                                (vl-wirealist-p walist)
                                (vl-id-p (vl-atom->guts x))
                                (vl-warninglist-p warnings))))
    (b* ((width (vl-atom->finalwidth x))
         (guts  (vl-atom->guts x))
         (name  (vl-id->name guts))

         ((unless (posp width))
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "Expected only sized expressions, but ~a0 does not ~
                         have a finalwidth."
                   :args (list x)
                   :fatalp t
                   :fn 'vl-msb-wire-bitlist)))
            (mv nil (cons w warnings) nil)))

         (wires (mbe :logic (list-fix (cdr (hons-get name walist)))
                     :exec  (cdr (hons-get name walist))))

         ((unless (consp wires))
          (b* ((w (make-vl-warning
                   :type :vl-bad-id
                   :msg "No wires for ~a0."
                   :args (list name)
                   :fatalp t
                   :fn 'vl-msb-wire-bitlist)))
            (mv nil (cons w warnings) nil)))

         (nwires (length wires))

         ((when (< width nwires))
          (b* ((w (make-vl-warning
                   :type :vl-programming-error
                   :msg "Produced too many wires for ~a0.  Finalwidth is ~x1, ~
                         but produced ~x2 bits: ~x3."
                   :args (list x (vl-atom->finalwidth x) nwires wires)
                   :fatalp t
                   :fn 'vl-msb-wire-bitlist)))
            (mv nil (cons w warnings) nil)))

         ((when (= nwires width))
          (mv t warnings wires))

         ;; else, we need to implicitly zero-extend or sign-extend the wire
         ;; based on its type; @(see vl-atom-welltyped-p).

         (type          (vl-atom->finaltype x))
         (extension-bit (if (eq type :vl-signed)
                            (car wires)
                          'acl2::f))
         (wires (append (replicate (- width nwires) extension-bit) wires)))

      (mv t warnings wires)))

  (local (in-theory (enable vl-msb-wire-bitlist)))

  (defmvtypes vl-msb-wire-bitlist (booleanp nil true-listp))

  (defthm true-listp-of-vl-msb-wire-bitlist-1
    (implies (true-listp warnings)
             (true-listp (mv-nth 1 (vl-msb-wire-bitlist x walist warnings))))
    :rule-classes :type-prescription)

  (defthm vl-warninglist-p-of-vl-msb-wire-bitlist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 1 (vl-msb-wire-bitlist x walist warnings))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-emodwirelist-p-of-vl-msb-wire-bitlist
    (implies (force (vl-wirealist-p walist))
             (vl-emodwirelist-p (mv-nth 2 (vl-msb-wire-bitlist x walist warnings))))))



(defsection vl-msb-partselect-bitlist
  :parents (vl-msb-expr-bitlist)
  :short "Produce the @(see vl-emodwire-p)s for a part-select."

  :long "<p><b>Signature:</b> @(call vl-msb-partselect-bitlist) returns @('(mv
successp warnings bits)').</p>

<p>We are given an part-select expression, @('x'), a wire alist, @('walist'),
and an @(see warnings) accumulator, @('warnings').  accumulator.  We attempt to
return the list of wires that correspond to this part select, in MSB order.  We
are careful to ensure that the range is resolved, the indices are in bounds,
and so on.</p>"

  (local (in-theory (enable hons-assoc-equal)))

  (defund vl-msb-partselect-bitlist (x walist warnings)
    (declare (xargs :guard (and (vl-expr-p x)
                                (not (vl-atom-p x))
                                (equal (vl-nonatom->op x) :vl-partselect-colon)
                                (vl-wirealist-p walist)
                                (vl-warninglist-p warnings))))
    (b* ((args  (vl-nonatom->args x))
         (from  (first args))
         (left  (second args))
         (right (third args))

         ((unless (and (vl-idexpr-p from)
                       (vl-expr-resolved-p left)
                       (vl-expr-resolved-p right)))
          (b* ((w (make-vl-warning
                   :type :vl-bad-expr
                   :msg "Expected a simple name and resolved indices, but ~
                         found ~a0."
                   :args (list x)
                   :fatalp t
                   :fn 'vl-msb-partselect-bitlist)))
            (mv nil (cons w warnings) nil)))

         (name  (vl-idexpr->name from))
         (left  (vl-resolved->val left))
         (right (vl-resolved->val right))

         (entry (hons-get name walist))
         ((unless entry)
          (b* ((w (make-vl-warning
                   :type :vl-bad-expr
                   :msg "No wire-alist entry for ~w0."
                   :args (list name)
                   :fatalp t
                   :fn 'vl-msb-partselect-bitlist)))
            (mv nil (cons w warnings) nil)))

         (wires (mbe :logic (list-fix (cdr entry))
                     :exec  (cdr entry)))

         (plain-name (vl-plain-wire-name name))

         ((when (equal wires (list plain-name)))

; Special case.  This is a select of a single, non-ranged wire.  The only valid
; possibility is that high and low are both zero, in which case we are choosing
; name[0:0] which is the same as name.

          (if (and (= left 0) (= right 0))

; BOZO probably we should not be doing this.  But I suspect things will break
; if we just remove this, so for now just add a non-fatal warning.  Hrmn, but
; what about the scalared and vectored keywords?  Ugh.

; If you fix this consider also the similar thing happening for bit-selects,
; and also fix the vl-expr-allwires function.

              (mv t
                  (cons (make-vl-warning
                         :type :vl-select-from-scalar
                         :msg "~a0: permitting selecting bit 0 from a scalar ~
                               wire, but this is probably wrong."
                         :args (list x)
                         :fatalp nil
                         :fn 'vl-msb-partselect-bitlist)
                      warnings)
                  wires)

            (mv nil
                (cons (make-vl-warning
                       :type :vl-bad-expr
                       :msg "~w0 is a lone wire, but found ~a1."
                       :args (list name x)
                       :fatalp t
                       :fn 'vl-msb-partselect-bitlist)
                      warnings)
                nil)))

; Otherwise, this is the ordinary case, and we are selecting some part of some
; ranged wire.  Since the wires in the walist are contiguous, we can check that
; the whole part is in bound by merely checking that both indices are found.

         (name[left]     (make-vl-emodwire :basename name :index left))
         (name[right]    (make-vl-emodwire :basename name :index right))
         ((unless (and (member name[left] wires)
                       (member name[right] wires)))
          (b* ((w (make-vl-warning
                   :type :vl-bad-expr
                   :msg "Select ~a0 is out of range; valid range is from ~
                         ~x1 to ~x2."
                   :args (list x (car wires) (car (last wires)))
                   :fatalp t
                   :fn 'vl-msb-partselect-bitlist)))
            (mv nil (cons w warnings) nil))))

; We're fine.  It seems easiest to just re-intern the symbols instead of
; extracting the appropriate slice out of the wire alist.

        (mv t warnings (vl-emodwires-from-msb-to-lsb name left right))))

  (local (in-theory (enable vl-msb-partselect-bitlist)))

  (defmvtypes vl-msb-partselect-bitlist (booleanp nil true-listp))

  (defthm true-listp-of-vl-msb-partselect-bitlist-1
    (implies (true-listp warnings)
             (true-listp (mv-nth 1 (vl-msb-partselect-bitlist x walist warnings))))
    :rule-classes :type-prescription)

  (defthm vl-warninglist-p-of-vl-msb-partselect-bitlist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-msb-partselect-bitlist x walist warnings)))))

  (defthm vl-emodwirelist-p-of-vl-msb-partselect-bitlist
    (vl-emodwirelist-p (mv-nth 2 (vl-msb-partselect-bitlist x walist warnings)))))



(defsection vl-msb-bitselect-bitlist
  :parents (vl-msb-expr-bitlist)
  :short "Produce the @(see vl-emodwire-p)s for a bit-select."

  :long "<p><b>Signature:</b> @(call vl-msb-bitselect-bitlist) returns @('(mv
successp warnings bits)').</p>

<p>We are given an bit-select expression, @('x'), a wire alist, @('walist'),
and an @(see warnings) accumulator, @('warnings').  accumulator.  We attempt to
return the list of wires that correspond to this bit select.  In practice this
will be a singleton wire, or nil on failure.  We are careful to ensure that the
selected bit is in bounds, etc.</p>"

  (local (in-theory (enable hons-assoc-equal)))

  (defund vl-msb-bitselect-bitlist (x walist warnings)
    (declare (xargs :guard (and (vl-expr-p x)
                                (not (vl-atom-p x))
                                (equal (vl-nonatom->op x) :vl-bitselect)
                                (vl-wirealist-p walist)
                                (vl-warninglist-p warnings))))
    (b* ((args  (vl-nonatom->args x))
         (from  (first args))
         (index (second args))

         ((unless (and (vl-idexpr-p from)
                       (vl-expr-resolved-p index)
                       (natp (vl-resolved->val index))))
          (mv nil
              (cons (make-vl-warning
                     :type :vl-bad-expr
                     :msg "Expected a simple name and resolved index, but ~
                           found a0."
                     :args (list x)
                     :fatalp t
                     :fn 'vl-msb-bitselect-bitlist)
                    warnings)
              nil))

         (name  (vl-idexpr->name from))
         (index (vl-resolved->val index))
         (entry (hons-get name walist))

         ((unless entry)
          (mv nil
              (cons (make-vl-warning
                     :type :vl-bad-expr
                     :msg "No wire-alist entry for ~w0."
                     :args (list name)
                     :fatalp t
                     :fn 'vl-msb-bitselect-bitlist)
                    warnings)
              nil))

         (wires (mbe :logic (list-fix (cdr entry))
                     :exec (cdr entry)))
         (plain-name (vl-plain-wire-name name))

         ((when (equal wires (list plain-name)))

; Special case.  This is a select of a single, non-ranged wire.  The only valid
; possibility is that the index is zero, in which case we are choosing name[0],
; which is the same as name.  BOZO think about this again.  Should maybe warn here.

          (if (= index 0)
              (mv t warnings wires)
            (mv nil
                (cons (make-vl-warning
                       :type :vl-bad-expr
                       :msg "~w0 is a lone wire, but found ~a1."
                       :args (list name x)
                       :fatalp t
                       :fn 'vl-msb-bitselect-bitlist)
                      warnings)
                nil)))

; Ordinary case.  We are selecting from some wire with a range.  Figure out
; what wire we want, and make sure it exists.

         (name[i] (make-vl-emodwire :basename name :index index))
         ((unless (member name[i] wires))
          (mv nil
              (cons (make-vl-warning
                     :type :vl-bad-expr
                     :msg "Select ~a0 is out of range: the valid bits are ~
                           ~s1 through ~s2."
                     :args (list x (car wires) (car (last wires)))
                     :fatalp t
                     :fn 'vl-msb-bitselect-bitlist)
                    warnings)
              nil)))

        (mv t warnings (list name[i]))))

  (local (in-theory (enable vl-msb-bitselect-bitlist)))

  (defmvtypes vl-msb-bitselect-bitlist (booleanp nil true-listp))

  (defthm true-listp-of-vl-msb-bitselect-bitlist-1
    (implies (true-listp warnings)
             (true-listp (mv-nth 1 (vl-msb-bitselect-bitlist x walist warnings))))
    :rule-classes :type-prescription)

  (defthm vl-warninglist-p-of-vl-msb-bitselect-bitlist
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-msb-bitselect-bitlist x walist warnings)))))

  (defthm vl-emodwirelist-p-of-vl-msb-bitselect-bitlist
    (vl-emodwirelist-p (mv-nth 2 (vl-msb-bitselect-bitlist x walist warnings)))))



(defsection vl-msb-replicate-bitlist
  :parents (vl-msb-expr-bitlist)
  :short "@(call vl-msb-replicate-bitlist) appends @('bits') onto itself
repeatedly, making @('n') copies of @('bits') as a single list."

    :long "<p>This is used for multiple concatenations, e.g., @('{4
{a,b,c}}').</p>"

  (defund vl-msb-replicate-bitlist (n bits)
    (declare (xargs :guard (and (natp n)
                                (true-listp bits))))
    (if (zp n)
        nil
      (append bits (vl-msb-replicate-bitlist (- n 1) bits))))

  (local (in-theory (enable vl-msb-replicate-bitlist)))

  (defthm true-listp-of-vl-msb-replicate-bitlist
    (true-listp (vl-msb-replicate-bitlist n bits))
    :rule-classes :type-prescription)

  (defthm vl-emodwirelist-p-of-vl-msb-replicate-bitlist
    (implies (vl-emodwirelist-p bits)
             (vl-emodwirelist-p (vl-msb-replicate-bitlist n bits))))

  (defthm len-of-vl-msb-replicate-bitlist
    (equal (len (vl-msb-replicate-bitlist n bits))
           (* (nfix n) (len bits))))

  ;; Simple unit tests.
  (local (assert!
          (let ((f 'acl2::f))
            (debuggable-and
             (equal (vl-msb-replicate-bitlist 0 (list t t f))
                    nil)
             (equal (vl-msb-replicate-bitlist 1 (list t t f))
                    (list t t f))
             (equal (vl-msb-replicate-bitlist 2 (list t t f))
                    (list t t f  t t f))
             (equal (vl-msb-replicate-bitlist 3 (list t t f))
                    (list t t f  t t f  t t f)))))))



(defsection vl-msb-expr-bitlist
  :parents (vl-wirealist-p)
  :short "Produce the E-language, MSB-ordered list of bits for an expression."

  :long "<p><b>Signature:</b> @(call vl-msb-expr-bitlist) returns @('(mv
successp warnings bitlist)')</p>

<p>When we translate module and gate instances into E, the arguments of the
instance are Verilog expressions, and we need to convert them into E-language
patterns.  By the end of our simplification process, we think that each such
expression should contain only:</p>

<ul>
 <li>Constant integers</li>
 <li>Weird integers</li>
 <li>Bit selects</li>
 <li>Part selects</li>
 <li>Concatenations</li>
 <li>Replications (multiconcats)</li>
</ul>

<p>This routine is intended to convert arbitrary expressions that include only
the above forms into a list of <b>MSB order</b> bits.</p>"

  (mutual-recursion

   (defund vl-msb-expr-bitlist (x walist warnings)
     (declare (xargs :guard (and (vl-expr-p x)
                                 (vl-wirealist-p walist)
                                 (vl-warninglist-p warnings))
                     :verify-guards nil
                     :hints(("Goal" :in-theory (disable (force))))
                     :measure (vl-expr-count x)))

     (if (vl-fast-atom-p x)
         (let ((guts (vl-atom->guts x)))
           (case (tag guts)
             (:vl-constint (vl-msb-constint-bitlist x warnings))
             (:vl-id       (vl-msb-wire-bitlist x walist warnings))
             (otherwise
              (mv nil
                  (cons (make-vl-warning :type :vl-unimplemented
                                         :msg "Need to add support for ~x0."
                                         :args (list (tag guts))
                                         :fatalp t
                                         :fn 'vl-msb-expr-bitlist)
                        warnings)
                  nil))))

       (let* ((op   (vl-nonatom->op x))
              (args (vl-nonatom->args x)))
         (case op
           ;; BOZO add additional length checks to the end of these
           ;; functions.
           (:vl-bitselect
            (vl-msb-bitselect-bitlist x walist warnings))
           (:vl-partselect-colon
            (vl-msb-partselect-bitlist x walist warnings))
           (:vl-concat
            (vl-msb-exprlist-bitlist args walist warnings))
           (:vl-multiconcat
            (b* (((unless (mbt (consp args)))
                  (prog2$
                   (er hard 'vl-msb-expr-bitlist
                       "Impossible case for termination")
                   (mv nil warnings nil)))

                 (mult   (first args))
                 (concat (second args))

                 ((unless (and (vl-expr-resolved-p mult)
                               (natp (vl-resolved->val mult))))
                  (mv nil
                      (cons (make-vl-warning
                             :type :vl-bad-expr
                             :msg "Multiple concatenation with unresolved multiplicity: ~a0."
                             :args (list x)
                             :fatalp t
                             :fn 'vl-msb-expr-bitlist)
                            warnings)
                      nil))

                 ((mv successp warnings bits)
                  (vl-msb-expr-bitlist concat walist warnings))

                 ((unless successp)
                  (mv successp warnings bits))

                 (replbits
                  (vl-msb-replicate-bitlist (vl-resolved->val mult) bits)))

              (mv t warnings replbits)))
           (otherwise
            (mv nil
                (cons (make-vl-warning :type :vl-unsupported
                                       :msg "Unsupported operator ~x0."
                                       :args (list op)
                                       :fatalp t
                                       :fn 'vl-msb-expr-bitlist)
                      warnings)
                nil))))))

   (defund vl-msb-exprlist-bitlist (x walist warnings)
     (declare (xargs :guard (and (vl-exprlist-p x)
                                 (vl-wirealist-p walist)
                                 (vl-warninglist-p warnings))
                     :measure (vl-exprlist-count x)))
     (if (atom x)
         (mv t warnings nil)
       (b* (((mv car-successp warnings car-bits)
             (vl-msb-expr-bitlist (car x) walist warnings))
            ((mv cdr-successp warnings cdr-bits)
             (vl-msb-exprlist-bitlist (cdr x) walist warnings)))
         (mv (and car-successp cdr-successp)
             warnings
             (append car-bits cdr-bits))))))

  (FLAG::make-flag vl-flag-msb-expr-bitlist
                   vl-msb-expr-bitlist
                   :flag-mapping ((vl-msb-expr-bitlist . expr)
                                  (vl-msb-exprlist-bitlist . list)))

  (defthm-vl-flag-msb-expr-bitlist
    (defthm true-listp-of-vl-msb-expr-bitlist-1
      (implies (true-listp warnings)
               (true-listp (mv-nth 1 (vl-msb-expr-bitlist x walist warnings))))
      :rule-classes :type-prescription
      :flag expr)
    (defthm true-listp-of-vl-msb-exprlist-bitlist-1
      (implies (true-listp warnings)
               (true-listp (mv-nth 1 (vl-msb-exprlist-bitlist x walist warnings))))
      :rule-classes :type-prescription
      :flag list)
    :hints(("Goal"
            :expand ((vl-msb-expr-bitlist x walist warnings)
                     (vl-msb-exprlist-bitlist x walist warnings)))))

  (defthm-vl-flag-msb-expr-bitlist
    (defthm true-listp-of-vl-msb-expr-bitlist-2
      (true-listp (mv-nth 2 (vl-msb-expr-bitlist x walist warnings)))
      :rule-classes :type-prescription
      :flag expr)
    (defthm true-listp-of-vl-msb-exprlist-bitlist-2
      (true-listp (mv-nth 2 (vl-msb-exprlist-bitlist x walist warnings)))
      :rule-classes :type-prescription
      :flag list)
    :hints(("Goal"
            :expand ((vl-msb-expr-bitlist x walist warnings)
                     (vl-msb-exprlist-bitlist x walist warnings)))))

  (defthm-vl-flag-msb-expr-bitlist
    (defthm vl-emodwirelist-p-of-vl-msb-expr-bitlist
      (implies (force (vl-wirealist-p walist))
               (vl-emodwirelist-p (mv-nth 2 (vl-msb-expr-bitlist x walist warnings))))
      :flag expr)
    (defthm symbol-listp-of-vl-msb-exprlist-bitlist
      (implies (force (vl-wirealist-p walist))
               (vl-emodwirelist-p (mv-nth 2 (vl-msb-exprlist-bitlist x walist warnings))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-msb-expr-bitlist x walist warnings)
                     (vl-msb-exprlist-bitlist x walist warnings)))))

  (defthm-vl-flag-msb-expr-bitlist
    (defthm vl-warninglist-p-of-vl-msb-expr-bitlist
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 (vl-msb-expr-bitlist x walist warnings))))
      :flag expr)
    (defthm vl-warninglist-p-of-vl-msb-exprlist-bitlist
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 (vl-msb-exprlist-bitlist x walist warnings))))
      :flag list)
    :hints(("Goal"
            :expand ((vl-msb-expr-bitlist x walist warnings)
                     (vl-msb-exprlist-bitlist x walist warnings)))))

  (verify-guards vl-msb-expr-bitlist))


