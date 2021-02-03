; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "emodwire")
(include-book "centaur/vl2014/util/merge-indices" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))


(defsection vl-emodwire-<

  (defund vl-emodwire-< (x y)
    (declare (xargs :guard (and (vl-emodwire-p x)
                                (vl-emodwire-p y))))
    (let ((xn (vl-emodwire->basename x))
          (yn (vl-emodwire->basename y)))
      (or (str::strnat< xn yn)
          (and (equal xn yn)
               (let ((xi (vl-emodwire->index x))
                     (yi (vl-emodwire->index y)))
                 (cond ((and xi yi) (< xi yi))
                       (yi          t)
                       (t           nil)))))))

  (local (in-theory (enable vl-emodwire-<)))

  (defthm vl-emodwire-<-irreflexive
    (not (vl-emodwire-< x x)))

  (defthm vl-emodwire-<-transitive
    (implies (and (vl-emodwire-< x y)
                  (vl-emodwire-< y z))
             (vl-emodwire-< x z))))


(defsection vl-emodwire-sort

  (acl2::defsort :compare< vl-emodwire-<
                 :comparablep vl-emodwire-p
                 :prefix vl-emodwire)

  (defthm vl-emodwire-list-p-removal
    (equal (vl-emodwire-list-p x)
           (vl-emodwirelist-p x))
    :hints(("Goal" :in-theory (enable vl-emodwire-list-p))))

  (defthm vl-emodwire-listp-of-vl-emodwire-sort
    (implies (force (vl-emodwirelist-p x))
             (vl-emodwirelist-p (vl-emodwire-sort x)))
    :hints(("Goal"
            :in-theory (disable vl-emodwire-sort-creates-comparable-listp)
            :use ((:instance vl-emodwire-sort-creates-comparable-listp
                             (acl2::x x)))))))



(defsection vl-verilogify-merged-indices
  :parents (vl-verilogify-emodwirelist)
  :short "Transform a merged index list into Verilog-style wire names."

  :long "<p>@(call vl-verilogify-merged-indices) takes @('name'), which should
be a string, and @('x'), a @('vl-merged-index-list-p') such as @(see
vl-merge-contiguous-indices) generates.  It produces a list of strings that
represent the Verilog bit- and part-selects of these indices from @('name').
For instance,</p>

@({
 (vl-verilogify-merged-indices \"foo\" '(1 (3 . 6) 8))
 -->
 (\"foo[1]\" \"foo[6:3]\" \"foo[8]\")
})"

  (local (in-theory (enable vl-merged-index-p)))

  (defund vl-verilogify-merged-indices (name x)
    (declare (xargs :guard (and (stringp name)
                                (vl-merged-index-list-p x))))
    (if (atom x)
        nil
      (cons
       (cond ((not (car x))
              ;; A nil index means the whole wire.
              name)
             ((natp (car x))
              ;; A single index, name[i]
              (cat name "[" (natstr (car x)) "]"))
             ((consp (car x))
              ;; A merged range, (low . high)
              (let ((low  (caar x))
                    (high (cdar x)))
                (cat name "[" (natstr high) ":" (natstr low) "]"))))
       (vl-verilogify-merged-indices name (cdr x)))))

  (local (in-theory (enable vl-verilogify-merged-indices)))

  (defthm string-listp-of-vl-verilogify-merged-indices
    (implies (and (force (stringp name))
                  (force (vl-merged-index-list-p x)))
             (string-listp (vl-verilogify-merged-indices name x)))))




(defund vl-verilogify-emodwirelist-2 (name x)
; Returns (MV NAME-INDICES REST-X)
;  NAME-INDICES: indices of all wires with NAME at the front of the list.
;  REST-X: remainder of X after the wires with this NAME.
  (declare (xargs :guard (and (stringp name)
                              (vl-emodwirelist-p x))))
  (cond ((atom x)
         (mv nil x))
        ((equal name (vl-emodwire->basename (car x)))
         (mv-let (matches2 rest)
           (vl-verilogify-emodwirelist-2 name (cdr x))
           (mv (cons (vl-emodwire->index (car x)) matches2) rest)))
        (t
         (mv nil x))))

(defthm vl-verilogify-emodwirelist-2-basics
  (implies (and (force (stringp name))
                (force (vl-emodwirelist-p x)))
           (let ((result (vl-verilogify-emodwirelist-2 name x)))
             (and (vl-maybe-nat-listp (mv-nth 0 result))
                  (vl-emodwirelist-p (mv-nth 1 result)))))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-2))))

(defthm acl2-count-of-vl-verilogify-emodwirelist-2-weak
  (<= (acl2-count (mv-nth 1 (vl-verilogify-emodwirelist-2 name x)))
      (acl2-count x))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-2))))

(defthm acl2-count-of-vl-verilogify-emodwirelist-2-strong
  (implies (and (consp x)
                (equal name (vl-emodwire->basename (car x))))
           (< (acl2-count (mv-nth 1 (vl-verilogify-emodwirelist-2 name x)))
              (acl2-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-2))))



(defund vl-verilogify-emodwirelist-1 (name x)
  ;; Returns (MV STRING-LIST REST-X)
  (declare (xargs :guard (and (stringp name)
                              (vl-emodwirelist-p x))))
  (b* (((mv indices rest-x)
        (vl-verilogify-emodwirelist-2 name x))
       (merged-indices (vl-merge-contiguous-indices indices))
       (verilog-names
        (vl-verilogify-merged-indices name merged-indices)))
    (mv verilog-names rest-x)))

(defthm vl-verilogify-emodwirelist-1-basics
  (implies (and (force (stringp name))
                (force (vl-emodwirelist-p x)))
           (let ((result (vl-verilogify-emodwirelist-1 name x)))
             (and (string-listp (mv-nth 0 result))
                  (vl-emodwirelist-p (mv-nth 1 result)))))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-1))))

(defthm acl2-count-of-vl-verilogify-emodwirelist-1-weak
  (<= (acl2-count (mv-nth 1 (vl-verilogify-emodwirelist-1 name x)))
      (acl2-count x))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-1))))

(defthm acl2-count-of-vl-verilogify-emodwirelist-1-strong
  (implies (and (consp x)
                (equal name (vl-emodwire->basename (car x))))
           (< (acl2-count (mv-nth 1 (vl-verilogify-emodwirelist-1 name x)))
              (acl2-count x)))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-1))))


(defund vl-verilogify-emodwirelist-0 (x)
  ;; Returns a string list
  ;; We assume X is already sorted.
  (declare (xargs :guard (vl-emodwirelist-p x)))
  (if (atom x)
      nil
    (b* ((name (vl-emodwire->basename (car x)))
         ((mv first-strings rest-x)
          (vl-verilogify-emodwirelist-1 name x))
         (rest-strings
          (vl-verilogify-emodwirelist-0 rest-x)))
      (append first-strings rest-strings))))

(defthm string-listp-of-vl-verilogify-emodwirelist-0
  (implies (force (vl-emodwirelist-p x))
           (string-listp (vl-verilogify-emodwirelist-0 x)))
  :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist-0))))


(defsection vl-verilogify-emodwirelist
  :parents (vl-wirealist-p)
  :short "Merge a list of @(see vl-emodwire-p)s into Verilog-style names."

  (defund vl-verilogify-emodwirelist (x)
    (declare (xargs :guard (vl-emodwirelist-p x)))
    (vl-verilogify-emodwirelist-0 (vl-emodwire-sort (list-fix x))))

  (defthm string-listp-of-vl-verilogify-emodwirelist
    (implies (force (vl-emodwirelist-p x))
             (string-listp (vl-verilogify-emodwirelist x)))
    :hints(("Goal" :in-theory (enable vl-verilogify-emodwirelist))))

  (local
   (assert! (equal
             (vl-verilogify-emodwirelist
              #!ACL2
              '(|foo[0]| |bar[18]| |foo[3]| |bar[0]|
                |foo[4]| |foo[5]| |bar[5]| |bar[17]|))
             (list "bar[0]" "bar[5]" "bar[18:17]"
                   "foo[0]" "foo[5:3]")))))



(defund vl-verilogify-symbols (x)
  (declare (xargs :guard (symbol-listp x)))
  (if (vl-emodwirelist-p x)
      (vl-verilogify-emodwirelist x)
    (prog2$
     (cw "Note: in vl-verilogify-symbols, symbols are not all emod wires!~%")
     (symbol-list-names x))))

(defthm string-listp-of-vl-verilogify-symbols
  (implies (force (symbol-listp x))
           (string-listp (vl-verilogify-symbols x)))
  :hints(("Goal" :in-theory (enable vl-verilogify-symbols))))
