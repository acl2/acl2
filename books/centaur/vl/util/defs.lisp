; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

; defs.lisp
;
; This book is for definitions of general concepts.  Hopefully much of this
; can eventually be moved into proper libraries.
;
; This book is non-locally included.  Because of this, do NOT put theorems
; about general concepts which the ordinary ACL2 user may have written
; other, conflicting theorems about.

(include-book "cutil/top" :dir :system)
(include-book "tools/defconsts" :dir :system)
(include-book "unicode/two-nats-measure" :dir :system)
(include-book "unicode/list-defuns" :dir :system)
(include-book "centaur/bitops/integer-length" :dir :system)
(include-book "centaur/misc/alist-equiv" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "str/top" :dir :system)
(include-book "str/fast-cat" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))


(defxdoc undocumented
  :parents (vl)
  :short "Placeholder for undocumented topics.")


(defxdoc utilities
  :parents (vl)
  :short "Generic utilities that are unrelated to Verilog processing, but which
are provided by the VL books.")

(defxdoc transforms
  :parents (vl)
  :short "High-level transformations for rewriting and simplifying Verilog
modules.")

(defxdoc mlib
  :parents (vl)
  :short "<b>M</b>odule <b>Lib</b>rary -- A collection of various functions for
working with Verilog modules.")



(defsection *nls*
  :parents (utilities)
  :short "A string consisting of a newline character."

  (defconst *nls*
    (coerce (list #\Newline) 'string)))


(defsection set-equivp

  (local (include-book "centaur/misc/equal-sets" :dir :system))
  (set-enforce-redundancy t) ;; note: implicitly local

  #!ACL2
  (defun set-equivp (x y)
    (declare (xargs :guard (and (true-listp x)
                                (true-listp y))))
    (and (subsetp-equal x y)
         (subsetp-equal y x)))

  (defequiv set-equivp))



(defsection same-lengthp
  :parents (utilities)
  :short "@(call same-lengthp) is a fast way to compute <tt>(= (len x) (len
  y))</tt>."

  :long "<p>In the logic, @(call same-lengthp) is exactly <tt>(= (len x) (len
y))</tt>.  However, for greater efficiency, it walks down both lists together
and never does any arithmetic.  We leave <tt>same-lengthp</tt> enabled, and
reason about <tt>len</tt> instead.</p>"

  (defun same-lengthp (x y)
    (declare (xargs :guard t))
    (mbe :logic (equal (len x) (len y))
         :exec (if (consp x)
                   (and (consp y)
                        (same-lengthp (cdr x) (cdr y)))
                 (not (consp y))))))



(defsection redundant-mergesort
  :parents (utilities)
  :short "Same as <tt>mergesort</tt>, but avoids re-sorting lists that
are already sorted."

  :long "<p>In the logic, <tt>(redundant-mergesort x)</tt> is just
<tt>(mergesort x)</tt>.  But in the execution, it first checks to see if
<tt>x</tt> is already sorted, and if so returns <tt>x</tt> unchanged.</p>

<p>I use this function when I do not want to go to the trouble of
proving that some cons-based operation happens to produce a set.  In practice,
this should be much faster than a mergesort because checking <tt>(setp x)</tt>
is linear and requires no consing.</p>

<h3>Performance Warnings</h3>

<p>By default, <tt>redundant-mergesort</tt> is silent and will simply sort its
argument if necessary.  However, you can also instruct it to emit warnings.  A
typical example is:</p>

<code>
 (defun my-function (x)
    (let ((x-sort (redundant-mergesort x :warnp t :from 'my-function)))
       ...))
</code>

<p>Here, <tt>:warnp</tt> specifies that warnings should be printed when
<tt>x</tt> is not sorted.  The <tt>:from</tt> argument is used to indicate
where this call of <tt>redundant-mergesort</tt> originates, which may be
helpful in determining why the mergesort is not actually redundant.</p>"

  (defun redundant-mergesort-fn (x warnp from)
    (declare (xargs :guard (and (booleanp warnp)
                                (symbolp from)))
             (ignorable warnp from))
    (mbe :logic
         (mergesort x)
         :exec
         (if (setp x)
             x
           (prog2$
            (cond ((and warnp from)
                   (cw "; Redundant-mergesort given unsorted list by ~s0.~%" from))
                  (warnp
                   (cw "; Redundant-mergesort given unsorted list.~%"))
                  (t
                   nil))
            (mergesort x)))))

  (defmacro redundant-mergesort (x &key warnp from)
    `(redundant-mergesort-fn ,x ,warnp ,from)))




(defsection vl-maybe-integerp
  :parents (utilities)
  :short "Recognizer for integers and <tt>nil</tt>."

  :long "<p>@(call vl-maybe-integerp) is like an option type, where either there
is some integer value or nothing.</p>"

  (definlined vl-maybe-integerp (x)
    (declare (xargs :guard t))
    (or (not x)
        (integerp x)))

  (local (in-theory (enable vl-maybe-integerp)))

  (defthm vl-maybe-integerp-compound-recognizer
    (equal (vl-maybe-integerp x)
           (or (integerp x)
               (not x)))
    :rule-classes :compound-recognizer))



(defsection vl-maybe-natp
  :parents (utilities)
  :short "Recognizer for naturals and <tt>nil</tt>."

  :long "<p>@(call vl-maybe-natp) is like an option type, where either there
is some natural number value or nothing.</p>"

  (definlined vl-maybe-natp (n)
    (declare (xargs :guard t))
    (or (not n)
        (natp n)))

  (local (in-theory (enable vl-maybe-natp)))

  (defthm vl-maybe-natp-compound-recognizer
    (equal (vl-maybe-natp x)
           (or (not x)
               (and (integerp x)
                    (<= 0 x))))
    :rule-classes :compound-recognizer))



(defsection vl-maybe-posp
  :parents (utilities)
  :short "Recognizer for positive naturals and <tt>nil</tt>."

  :long "<p>@(call vl-maybe-posp) is like an option type, where either there
is some positive, natural number value or nothing.</p>"

  (definlined vl-maybe-posp (x)
    (declare (xargs :guard t))
    (or (not x)
        (posp x)))

  (local (in-theory (enable vl-maybe-posp)))

  (defthm vl-maybe-posp-compound-recognizer
    (equal (vl-maybe-posp x)
           (or (and (integerp x)
                    (< 0 x))
               (not x)))
    :rule-classes :compound-recognizer))



(defsection vl-maybe-string-p
  ;; BOZO name consistency with other functions here
  :parents (utilities)
  :short "Recognizer for strings and <tt>nil</tt>."

  :long "<p>@(call vl-maybe-string-p) is like an option type, where either
there is some string value or nothing.</p>"

  (definlined vl-maybe-string-p (x)
    (declare (xargs :guard t))
    (or (not x)
        (stringp x)))

  (local (in-theory (enable vl-maybe-string-p)))

  (defthm vl-maybe-string-p-compound-recognizer
    (equal (vl-maybe-string-p x)
           (or (not x)
               (stringp x)))
    :rule-classes :compound-recognizer))



(deflist nat-listp (x)
  (natp x)
  :elementp-of-nil nil
  :parents (utilities))



(deflist vl-maybe-nat-listp (x)
  (vl-maybe-natp x)
  :elementp-of-nil t
  :parents (utilities))

(defthm nat-listp-when-no-nils-in-vl-maybe-nat-listp
  (implies (and (not (member-equal nil x))
                (vl-maybe-nat-listp x))
           (nat-listp x))
  :hints(("Goal" :induct (len x))))




(defsection debuggable-and
  :parents (utilities)
  :short "Alternative to <tt>and</tt> that prints a message where it fails."

  :long "<p><tt>(debuggable-and ...)</tt> is the same as <tt>(and ...)</tt>,
but prints a message when any of the conjuncts fails.  For instance,</p>

<code>
VL !&gt;(debuggable-and (natp 3)
                     (symbolp 'foo)
                     (consp 4)
                     (symbolp 'bar))
Debuggable-and failure: (CONSP 4).
NIL
VL !&gt;
</code>

<p>This can be useful when writing unit tests, checking guards, etc.</p>"

  (defun debuggable-and-fn (args)
    (cond ((atom args)
           t)
          (t
           `(and (or ,(car args)
                     (cw "Debuggable-and failure: ~x0.~%" ',(car args)))
                 ,(debuggable-and-fn (cdr args))))))

  (defmacro debuggable-and (&rest args)
    (debuggable-and-fn args)))



(defsection make-lookup-alist
  :parents (utilities)
  :short "Make a fast-alist for use with @(see fast-memberp)."

  :long "<p>@(call make-lookup-alist) produces a fast-alist binding every
member of <tt>x</tt> to <tt>t</tt>.</p>

<p>Constructing a lookup alist allows you to use @(see fast-memberp) in lieu of
@(see member) or @(see member-equal), which may be quite a lot faster on large
lists.</p>

<p>Don't forget to free the alist after you are done using it, via
@(see flush-hons-get-hash-table-link).</p>"

  (defund make-lookup-alist (x)
    (declare (xargs :guard t))
    (if (consp x)
        (hons-acons (car x)
                    t
                    (make-lookup-alist (cdr x)))
      nil))

  (local (in-theory (enable make-lookup-alist)))

  (defthm alistp-of-make-lookup-alist
    (alistp (make-lookup-alist x)))

  (defthm hons-assoc-equal-of-make-lookup-alist
    (iff (hons-assoc-equal a (make-lookup-alist x))
         (member-equal a (double-rewrite x))))

  (defthm consp-of-make-lookup-alist
    (equal (consp (make-lookup-alist x))
           (consp x)))

  (defthm make-lookup-alist-under-iff
    (iff (make-lookup-alist x)
         (consp x)))

  (defthm strip-cars-of-make-lookup-alist
    (equal (strip-cars (make-lookup-alist x))
           (list-fix x)))

  (defthm alist-keys-of-make-lookup-alist
    (equal (alist-keys (make-lookup-alist x))
           (list-fix x))))



(defsection fast-memberp
  :parents (utilities)
  :short "Fast list membership using @(see make-lookup-alist)."

  :long "<p>In the logic, @(call fast-memberp) is just a list membership check;
we leave <tt>fast-memberp</tt> enabled and always reason about
<tt>member-equal</tt> instead.</p>

<p>However, our guard requires that <tt>alist</tt> is the result of running
@(see make-lookup-alist) on <tt>x</tt>.  Because of this, in the execution, the
call of @(see member-equal) call is instead carried out using @(see hons-get)
on the alist, and hence is a hash table lookup.</p>"

  (definline fast-memberp (a x alist)
    (declare (xargs :guard (equal alist (make-lookup-alist x)))
             (ignorable x alist))
    (mbe :logic (if (member-equal a x) t nil)
         :exec (if (hons-get a alist) t nil))))



(defsection all-equalp
  :parents (utilities)
  :short "@(call all-equalp) determines if every members of <tt>x</tt> is
equal to <tt>a</tt>."

  :long "<p>In the logic, we define <tt>all-equalp</tt> in terms of
<tt>repeat</tt>.</p>

<p>We usually leave this enabled and prefer to reason about <tt>repeat</tt>
instead.  On the other hand, we also sometimes disable it and reason about it
recursively, so we do prove a few theorems about it.</p>

<p>For better execution speed, we use a recursive definition that does no
consing.</p>"

  (defun all-equalp (a x)
    (declare (xargs :guard t
                    :guard-hints(("Goal" :in-theory (enable all-equalp repeat)))))
    (mbe :logic
         (equal (list-fix x) (repeat a (len x)))
         :exec
         (if (consp x)
             (and (equal a (car x))
                  (all-equalp a (cdr x)))
           t)))

  (defthm all-equalp-when-atom
    (implies (atom x)
             (all-equalp a x)))

  (defthm all-equalp-of-cons
    (equal (all-equalp a (cons b x))
           (and (equal a b)
                (all-equalp a x)))
    :hints(("Goal" :in-theory (enable repeat))))

  (local (in-theory (disable all-equalp)))

  (defthm car-when-all-equalp
    (implies (all-equalp a x)
             (equal (car x)
                    (if (consp x) a nil))))

  (defthm all-equalp-of-cdr-when-all-equalp
    (implies (all-equalp a x)
             (all-equalp a (cdr x))))

  (defthm all-equalp-of-append
    (equal (all-equalp a (append x y))
           (and (all-equalp a x)
                (all-equalp a y)))
    :hints(("Goal" :induct (len x))))

  (defthm all-equalp-of-rev
    (equal (all-equalp a (rev x))
           (all-equalp a x))
    :hints(("Goal" :induct (len x))))

  (defthm all-equalp-of-repeat
    (equal (all-equalp a (repeat b n))
           (or (equal a b)
               (zp n)))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm all-equalp-of-simpler-take
    (implies (all-equalp a x)
             (equal (all-equalp a (simpler-take n x))
                    (or (not a)
                        (<= (nfix n) (len x)))))
    :hints(("Goal" :in-theory (enable simpler-take))))

  (defthm all-equalp-of-nthcdr
    (implies (all-equalp a x)
             (all-equalp a (nthcdr n x)))
    :hints(("Goal" :in-theory (enable nthcdr))))

  (defthm member-equal-when-all-equalp
    (implies (all-equalp a x)
             (iff (member-equal b x)
                  (and (consp x)
                       (equal a b))))
    :hints(("Goal" :induct (len x)))))





(defsection remove-equal-without-guard
  :parents (utilities)
  :short "Same as <tt>remove-equal</tt>, but doesn't require
<tt>true-listp</tt>."

  :long "<p>In the logic, we define this function as <tt>remove-equal</tt> and
we leave it enabled.  You should never reason about it directly; reason about
<tt>remove-equal</tt> instead.</p>"

  (defun remove-equal-without-guard (a x)
    (declare (xargs :guard t))
    (mbe :logic (remove-equal a x)
         :exec (cond ((atom x)
                      nil)
                     ((equal a (car x))
                      (remove-equal-without-guard a (cdr x)))
                     (t
                      (cons (car x) (remove-equal-without-guard a (cdr x))))))))



(defsection all-have-len
  :parents (utilities)
  :short "@(call all-have-len) determines if every element of <tt>x</tt> has
length <tt>n</tt>."

  (defund all-have-len (x n)
    (declare (xargs :guard t))
    (if (consp x)
        (and (equal (len (car x)) n)
             (all-have-len (cdr x) n))
      t))

  (local (in-theory (enable all-have-len)))

  (defthm all-have-len-when-not-consp
    (implies (not (consp x))
             (all-have-len x n)))

  (defthm all-have-len-of-cons
    (equal (all-have-len (cons a x) n)
           (and (equal (len a) n)
                (all-have-len x n))))

  (defthm all-have-len-of-strip-cdrs
    (implies (and (not (zp n))
                  (all-have-len x n))
             (all-have-len (strip-cdrs x) (1- n)))
    :hints(("Goal" :in-theory (enable len))))

  (defthm alistp-when-all-have-len
    (implies (and (not (zp n))
                  (all-have-len x n))
             (equal (alistp x)
                    (true-listp x)))))



(defsection remove-from-alist
  :parents (utilities)
  :short "@(call remove-from-alist) removes all bindings for <tt>key</tt>
from <tt>alist</tt>."

  (defund remove-from-alist (key alist)
    (declare (xargs :guard (alistp alist)))
    (cond ((atom alist)
           nil)
          ((equal key (caar alist))
           (remove-from-alist key (cdr alist)))
          (t
           (cons (car alist)
                 (remove-from-alist key (cdr alist))))))

  (local (in-theory (enable remove-from-alist)))

  (defthm remove-from-alist-when-not-consp
    (implies (not (consp alist))
             (equal (remove-from-alist key alist)
                    nil)))

  (defthm remove-from-alist-of-cons
    (equal (remove-from-alist key (cons a x))
           (if (equal key (car a))
               (remove-from-alist key x)
             (cons a (remove-from-alist key x)))))

  (defthm alistp-of-remove-from-alist
    (implies (force (alistp alist))
             (alistp (remove-from-alist key alist)))))

(defsection vl-remove-keys
  :parents (utilities)
  :short "@(call vl-remove-keys) removes all bindings for the given <tt>keys</tt>
from <tt>alist</tt>."

  :long "<p><b>BOZO</b> name consistency with @(see remove-from-alist).</p>"

  (defund vl-remove-keys (keys x)
    (declare (xargs :guard (true-listp keys)))
    (cond ((atom x)
           nil)
          ((atom (car x))
           ;; bad alist convention
           (vl-remove-keys keys (cdr x)))
          ((member-equal (caar x) keys)
           (vl-remove-keys keys (cdr x)))
          (t
           (cons (car x) (vl-remove-keys keys (cdr x))))))

  (local (in-theory (enable vl-remove-keys)))

  (defthm vl-remove-keys-when-not-consp
    (implies (not (consp x))
             (equal (vl-remove-keys keys x)
                    nil)))

  (defthm vl-remove-keys-of-cons
    (equal (vl-remove-keys keys (cons a x))
           (if (atom a)
               (vl-remove-keys keys x)
             (if (member-equal (car a) (double-rewrite keys))
                 (vl-remove-keys keys x)
               (cons a (vl-remove-keys keys x))))))

  (defthm true-listp-of-vl-remove-keys
    (true-listp (vl-remove-keys keys x))
    :rule-classes :type-prescription)

  (defthm alistp-of-vl-remove-keys
    (alistp (vl-remove-keys keys x)))

  (defthm consp-of-car-of-vl-remove-keys
    (equal (consp (car (vl-remove-keys keys x)))
           (consp (vl-remove-keys keys x))))

  (defthm acl2-count-of-vl-remove-keys
    (<= (acl2-count (vl-remove-keys keys x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable acl2-count)))))




(defsection redundant-list-fix
  :parents (utilities)
  :short "@(call redundant-list-fix) is the same as <tt>(list-fix x)</tt>, but
avoids consing when <tt>x</tt> is already a true-listp."

  :long "<p>I sometimes want to <tt>list-fix</tt> something that I know is
almost certainly already a <tt>true-listp</tt> in practice.  In such cases,
<tt>redundant-list-fix</tt> may be a better choice than <tt>list-fix</tt>,
because checking <tt>true-listp</tt> is much cheaper than re-consing the
a list.</p>

<p>I leave this function enabled.  Logically it is just an alias for
<tt>list-fix</tt>, so you should never need to reason about it.</p>

@(def redundant-list-fix)"

  (defun redundant-list-fix (x)
    (declare (xargs :guard t))
    (mbe :logic (list-fix x)
         :exec (if (true-listp x)
                   x
                 (list-fix x)))))




(deflist string-list-listp (x)
  (string-listp x)
  :guard t
  :elementp-of-nil t
  :parents (utilities))


;; BOZO er --- why are these not in arithmetic??
(defthm prefixp-of-self
  (prefixp x x)
  :hints(("Goal" :in-theory (enable prefixp))))

(defthm transitivity-of-prefixp
  (implies (and (prefixp x y)
                (prefixp y z))
           (prefixp x z))
  :hints(("Goal" :in-theory (enable prefixp))))




(defsection longest-common-prefix
  :parents (utilities)
  :short "@(call longest-common-prefix) returns the longest list, <tt>p</tt>,
such that <tt>p</tt> is a prefix of both <tt>x</tt> and <tt>y</tt>, in the
sense of <tt>prefixp</tt>."

  :long "<p>See also @(see longest-common-prefix-list), which extends this
function to a list of lists.</p>"

  (defund longest-common-prefix (x y)
    (declare (xargs :guard t))
    (cond ((or (atom x)
               (atom y))
           nil)
          ((equal (car x) (car y))
           (cons (car x)
                 (longest-common-prefix (cdr x) (cdr y))))
          (t
           nil)))

  (local (in-theory (enable longest-common-prefix)))

  (defthm true-listp-of-longest-common-prefix
    (true-listp (longest-common-prefix x y))
    :rule-classes :type-prescription)

  (defthm string-listp-of-longest-common-prefix
    (implies (and (string-listp x)
                  (string-listp y))
             (string-listp (longest-common-prefix x y)))
    :hints(("Goal" :in-theory (enable longest-common-prefix))))

  (defthm longest-common-prefix-of-list-fix-left
    (equal (longest-common-prefix (list-fix x) y)
           (longest-common-prefix x y)))

  (defthm longest-common-prefix-of-list-fix-right
    (equal (longest-common-prefix x (list-fix y))
           (longest-common-prefix x y)))

  (defthm prefixp-of-longest-common-prefix-left
    (prefixp (longest-common-prefix x y) x))

  (defthm prefixp-of-longest-common-prefix-right
    (prefixp (longest-common-prefix x y) y))

  (defthm longest-common-prefix-preserves-prefixp
    (implies (prefixp p a)
             (prefixp (longest-common-prefix p b) a))
    :hints(("Goal" :in-theory (enable prefixp)))))



(defsection prefixp-of-each

  (deflist prefix-of-eachp (p x)
    (prefixp p x)
    :guard t
    :parents (utilities)
    :short "@(call prefix-of-eachp) returns true exactly when <tt>p</tt> is a
prefix of every member of <tt>x</tt>.")

  (defthm prefix-of-eachp-when-prefixp
    (implies (and (prefix-of-eachp a x)
                  (prefixp b a))
             (prefix-of-eachp b x))
    :hints(("Goal" :induct (len x))))

  (defthm prefix-of-eachp-when-prefixp-alt
    (implies (and (prefixp b a)
                  (prefix-of-eachp a x))
             (prefix-of-eachp b x))
    :hints(("Goal" :induct (len x)))))



(defsection longest-common-prefix-list
  :parents (utilities)
  :short "@(call longest-common-prefix-list) returns the longest list, <tt>p</tt>,
such that <tt>p</tt> is a prefix of every list in <tt>x</tt>."
  :long "<p>See also @(see longest-common-prefix).</p>"

  (defund longest-common-prefix-list (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (cdr x))
           (list-fix (car x)))
          (t
           (longest-common-prefix (first x)
                                  (longest-common-prefix-list (cdr x))))))

  (local (in-theory (enable longest-common-prefix-list)))

  (defthm true-listp-of-longest-common-prefix-list
    (true-listp (longest-common-prefix-list x))
    :rule-classes :type-prescription)

  (defthm string-listp-of-longest-common-prefix-list
    (implies (string-list-listp x)
             (string-listp (longest-common-prefix-list x))))

  (defthm longest-common-prefix-list-of-list-fix
    (equal (longest-common-prefix-list (list-fix x))
           (longest-common-prefix-list x)))

  (defthm prefix-of-eachp-of-longest-common-prefix-list
    (prefix-of-eachp (longest-common-prefix-list x) x)))



(defsection string-fix
  :parents (utilities)
  :short "@(call string-fix) is the identity function for strings."
  :long "<p>Note that we leave this function enabled.</p>"

  (definline string-fix (x)
    (declare (type string x))
    (mbe :logic (if (stringp x) x "")
         :exec x))

  (defthm stringp-of-string-fix
    (stringp (string-fix x))
    :rule-classes :type-prescription))



(defprojection symbol-list-names (x)
  (symbol-name x)
  :guard (symbol-listp x)
  :result-type string-listp
  :parents (utilities))


(defsection look-up-each

  ;; BOZO find me a home

  ;; (look-up-each (list a b c ...) alist)
  ;;    -->
  ;; (list (cdr (hons-assoc-equal a alist))
  ;;       (cdr (hons-assoc-equal b alist))
  ;;       (cdr (hons-assoc-equal c alist))
  ;;       ...)

  (defund look-up-each-fast (x fast-alist)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (let ((lookup (hons-get (car x) fast-alist)))
        (cons (if lookup
                  (cdr lookup)
                (er hard? 'look-up-each-fast "expected ~x0 to be bound.~%" (car x)))
              (look-up-each-fast (cdr x) fast-alist)))))

  (defund look-up-each (x alist)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic (if (atom x)
                    nil
                  (cons (cdr (hons-assoc-equal (car x) alist))
                        (look-up-each (cdr x) alist)))
         :exec
         (b* ((fal (make-fal alist (len alist)))
              (ret (look-up-each-fast x fal))
              (-   (fast-alist-free fal)))
           ret)))

  (local (in-theory (enable look-up-each look-up-each-fast)))

  (defthm look-up-each-fast-redefinition
    (equal (look-up-each-fast x alist)
           (look-up-each x alist)))

  (local (defthm l0
           (equal (hons-assoc-equal a (make-fal x y))
                  (or (hons-assoc-equal a x)
                      (hons-assoc-equal a y)))))

  (local (defthm l1
           (implies (atom tail)
                    (equal (look-up-each x (make-fal alist tail))
                           (look-up-each x alist)))))

  (verify-guards look-up-each)

  (defthm look-up-each-of-atom
    (implies (atom x)
             (equal (look-up-each x alist)
                    nil)))

  (defthm look-up-each-of-cons
    (equal (look-up-each (cons a x) alist)
           (cons (cdr (hons-assoc-equal a alist))
                 (look-up-each x alist))))

  (defthm true-listp-of-look-up-each
    (true-listp (look-up-each x alist))
    :rule-classes :type-prescription)

  (defthm len-of-look-up-each
    (equal (len (look-up-each x alist))
           (len x)))

  (defthm look-up-each-of-list-fix
    (equal (look-up-each (list-fix x) alist)
           (look-up-each x alist)))

  (defthm look-up-each-of-append
    (equal (look-up-each (append x y) alist)
           (append (look-up-each x alist)
                   (look-up-each y alist))))

  (defthm look-up-each-of-rev
    (equal (look-up-each (rev x) alist)
           (rev (look-up-each x alist))))

  (defthm symbol-listp-of-look-up-each
    (implies (symbol-listp (strip-cdrs alist))
             (symbol-listp (look-up-each x alist)))))


(deflist symbol-list-listp (x)
  (symbol-listp x)
  :guard t
  :elementp-of-nil t
  :parents (utilities))


(defsection vl-starname
  :parents (utilities)
  :short "@(call vl-starname) is given a string, say <tt>\"foo\"</tt>,
and return a symbol in the ACL2 package, e.g., <tt>ACL2::*foo*</tt>."

  :long "<p>Such names are the convention for naming modules in E.</p>"

  (definlined vl-starname (name)
    (declare (xargs :guard (stringp name)))
    (intern-in-package-of-symbol
     (coerce (cons #\* (str::append-chars name (list #\*))) 'string)
     'ACL2::foo))

  (local (in-theory (enable vl-starname)))

  (defthm symbolp-of-vl-starname
    (symbolp (vl-starname name))
    :rule-classes :type-prescription))



(defsection longer-than-p
  :parents (utilities)
  :short "@(call longer-than-p) determines if the list <tt>x</tt> is
longer than <tt>n</tt>."

  :long "<p>This can be slightly faster than <tt>(len x)</tt> when the
list is long and <tt>n</tt> is small.  We leave this function enabled
and reason about <tt>len</tt> instead.</p>"

  (local (defthm l0
           (equal (len (cdr x))
                  (if (consp x)
                      (+ -1 (len x))
                    0))))

  (defun longer-than-p (n x)
    (declare (xargs :guard (natp n)))
    (mbe :logic (< n (len x))
         :exec
         (cond ((zp n)
                (consp x))
               ((atom x)
                nil)
               (t
                (longer-than-p (+ -1 n) (cdr x)))))))


(deflist pos-listp (x)
  (posp x)
  :elementp-of-nil nil
  :parents (utilities))


(deflist true-list-listp (x)
  (true-listp x)
  :guard t
  :elementp-of-nil t
  :parents (utilities))




(defsection append-domains
  :parents (utilities)
  :short "@(call append-domains) appends all of the values from the alist
<tt>x</tt> into a single list."

  :long "<p>Our guard is merely <tt>t</tt>, but typically <tt>x</tt> is an
alist of <tt>(key . value)</tt> pairs where every <tt>value</tt> is a list of
elements.  We walk through the alist, appending together all of the elements of
each <tt>value</tt> into a single, flat list.</p>

<p>Note that we do not really treat <tt>x</tt> as an association list.  That
is, we will include the values from any \"shadowed pairs\" in the list.</p>"

  (defund append-domains-exec (x acc)
    (declare (xargs :guard t))
    (mbe :logic
         (if (atom x)
             acc
           (append-domains-exec (cdr x)
                                (revappend (cdar x) acc)))
         :exec
         (cond ((atom x)
                acc)
               ((atom (car x))
                (append-domains-exec (cdr x) acc))
               (t
                (append-domains-exec (cdr x)
                                     (revappend-without-guard (cdar x) acc))))))

  (local (in-theory (enable append-domains-exec)))

  (local (defthm true-listp-of-append-domains-exec
           (implies (true-listp acc)
                    (equal (true-listp (append-domains-exec x acc))
                           t))
           :rule-classes :type-prescription))

  (defun append-domains (x)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (append (cdar x) (append-domains (cdr x))))
         :exec (reverse (append-domains-exec x nil))))

  (local (in-theory (enable append-domains)))

  (defthm append-domains-exec-removal
    (equal (append-domains-exec x acc)
           (revappend (append-domains x) acc))
    :hints(("Goal" :induct (append-domains-exec x acc))))

  (verify-guards append-domains)

  (defthm append-domains-when-atom
    (implies (atom x)
             (equal (append-domains x)
                    nil)))

  (defthm append-domains-of-cons
    (equal (append-domains (cons a x))
           (append (cdr a) (append-domains x))))

  (defthm true-listp-of-append-domains
    (true-listp (append-domains x))
    :rule-classes :type-prescription)

  (defthm append-domains-of-append
    (equal (append-domains (append x y))
           (append (append-domains x) (append-domains y)))))



(defun fast-alist-free-each-alist-val (x)
  "Applies fast-alist-free to every value bound in the alist x."
  (declare (xargs :guard t))
  (mbe :logic nil
       :exec
       (cond ((atom x)
              nil)
             ((atom (car x))
              (fast-alist-free-each-alist-val (cdr x)))
             (t
              (prog2$ (fast-alist-free (cdar x))
                      (fast-alist-free-each-alist-val (cdr x)))))))


(defun free-list-of-fast-alists (x)
  "Applies fast-alist-free to every member of the list x."
  (declare (xargs :guard t))
  (mbe :logic nil
       :exec
       (if (atom x)
           nil
         (prog2$ (fast-alist-free (car x))
                 (free-list-of-fast-alists (cdr x))))))




(defsection vl-plural-p
  :parents (utilities)
  :short "@(call vl-plural-p) determines whether a description of a list should
be plural instead of singluar."

  :long "<p>Output sometimes needs to be customized depending on whether a list
contains only one element or many elements, e.g.,</p>

<ul>
 <li>Warning: foo, bar, and baz <b>are</b> mismatched <b>socks</b>, vs.</li>
 <li>Warning: foo <b>is a</b> mismatched <b>sock</b>.</li>
</ul>

<p>@(call vl-plural-p) is a stupid function to distinguish between the cases.
It returns true for a list like <tt>(foo bar baz)</tt> with more than one element,
or false for a list like <tt>(foo)</tt> with exactly one element.</p>

<p>We consider lists that have no elements to be plural.  This gives the proper
behavior in cases like:</p>

<ul>
 <li>0 <b>warnings</b> to report,</li>
 <li>1 <b>warning</b> to report,</li>
 <li>2 <b>warnings</b> to report,</li>
 <li>...</li>
</ul>"

  (definlined vl-plural-p (x)
    (declare (xargs :guard t))
    (mbe :logic (not (= (len x) 1))
         :exec (or (atom x)
                   (not (atom (cdr x)))))))



(defun tuplep (n x)
  (declare (xargs :guard (natp n)))
  (mbe :logic (and (true-listp x)
                   (equal (len x) n))
       :exec (and (true-listp x)
                  (= (length x) n))))

(deflist cons-listp (x)
  (consp x)
  :elementp-of-nil nil)

(deflist cons-list-listp (x)
  (cons-listp x)
  :elementp-of-nil t)





(defsection and*
  :parents (utilities)
  :short "<tt>and*</tt> is like <tt>and</tt> but is a (typically disabled) function."
  :long "<p>This is occasionally useful for avoiding case-splitting in theorems.</p>"

  (defund binary-and* (x y)
    (declare (xargs :guard t))
    (if x y nil))

  (defund and*-macro (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           t)
          ((atom (cdr x))
           (car x))
          (t
           `(binary-and* ,(car x)
                         ,(and*-macro (cdr x))))))

  (defmacro and* (&rest args)
    (and*-macro args))

  (add-binop and* binary-and*))



(defsection or*
  :parents (utilities)
  :short "<tt>or*</tt> is like <tt>or</tt> but is a (typically disabled) function."
  :long "<p>This is occasionally useful for avoiding case-splitting in theorems.</p>"

  (defund binary-or* (x y)
    (declare (xargs :guard t))
    (if x x y))

  (defund or*-macro (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (cdr x))
           (car x))
          (t
           `(binary-or* ,(car x)
                        ,(or*-macro (cdr x))))))

  (defmacro or* (&rest args)
    (or*-macro args))

  (add-binop or* binary-or*))


(defsection not*
  :parents (utilities)
  :short "<tt>not*</tt> is like <tt>not</tt> but is not built-in to ACL2 and is
typically disabled."
  :long "<p>This might occasionally be useful for avoiding case-splitting in
theorems.</p>"

  (defund not* (x)
    (declare (xargs :guard t))
    (not x)))




(defsection keys-boundp
  :parents (utilities)
  :short "@(call keys-boundp) determines if every key in <tt>keys</tt> is bound
in the alist <tt>alist</tt>."

  (defund keys-boundp-fal (keys alist)
    (declare (xargs :guard t))
    (if (atom keys)
        t
      (and (hons-get (car keys) alist)
           (keys-boundp-fal (cdr keys) alist))))

  (defund keys-boundp-slow-alist (keys alist)
    (declare (xargs :guard t))
    (if (atom keys)
        t
      (and (hons-assoc-equal (car keys) alist)
           (keys-boundp-slow-alist (cdr keys) alist))))

  (defund keys-boundp (keys alist)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom keys)
             t
           (and (hons-assoc-equal (car keys) alist)
                (keys-boundp (cdr keys) alist)))
         :exec
         (if (atom keys)
             t
           (if (and (acl2::worth-hashing keys)
                    (acl2::worth-hashing alist))
               (with-fast-alist alist (keys-boundp-fal keys alist))
             (keys-boundp-slow-alist keys alist)))))

  (local (in-theory (enable keys-boundp
                            keys-boundp-fal
                            keys-boundp-slow-alist)))

  (defthm keys-boundp-fal-removal
    (equal (keys-boundp-fal keys alist)
           (keys-boundp keys alist)))

  (defthm keys-boundp-slow-alist-removal
    (equal (keys-boundp-slow-alist keys alist)
           (keys-boundp keys alist)))

  (verify-guards keys-boundp)

  (defthm keys-boundp-when-atom
    (implies (atom keys)
             (equal (keys-boundp keys alist)
                    t)))

  (defthm keys-boundp-of-cons
    (equal (keys-boundp (cons a keys) alist)
           (and (hons-get a alist)
                (keys-boundp keys alist))))

  (defthm keys-boundp-of-list-fix
    (equal (keys-boundp (list-fix x) alist)
           (keys-boundp x alist)))

  (defthm keys-boundp-of-append
    (equal (keys-boundp (append x y) alist)
           (and (keys-boundp x alist)
                (keys-boundp y alist))))

  (defthm keys-boundp-of-rev
    (equal (keys-boundp (rev x) alist)
           (keys-boundp x alist)))

  (defthm keys-boundp-of-revappend
    (equal (keys-boundp (revappend x y) alist)
           (and (keys-boundp x alist)
                (keys-boundp y alist)))))