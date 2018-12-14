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

(include-book "std/strings/printtree-fty" :dir :system)
(include-book "std/strings/cat" :dir :system)

(defmacro def-alias (new orig)
  `(progn (defmacro ,new (&rest args) (cons ',orig args))
          (add-macro-alias ,new ,orig)))

(def-alias vl-printed-p str::printable-p)
(def-alias vl-printed-fix str::printable-fix)
(def-alias vl-printed-equiv str::printable-equiv)
(def-alias vl-printedlist-p str::printtree-p)
(def-alias vl-printedtree-p str::printtree-p)
(def-alias vl-printedlist-fix str::printtree-fix)
(def-alias vl-printedtree-fix str::printtree-fix)
(def-alias vl-printedlist-equiv str::printtree-equiv)
(def-alias vl-printedtree-equiv str::printtree-equiv)

(defsection vl-printedlist-p
  (defthm vl-printedlist-p-when-character-listp
    (implies (character-listp x)
             (vl-printedlist-p x))
    :hints(("Goal" :induct (len x)
            :expand ((vl-printedlist-p x)
                     (vl-printedtree-p (car x))))))

  (defthm vl-printedlist-p-when-string-listp
    (implies (string-listp x)
             (vl-printedlist-p x))
    :hints(("Goal" :induct (len x)
            :expand ((vl-printedlist-p x)
                     (vl-printedtree-p (car x))))))

  (defthm vl-printedlist-p-of-make-list-ac
    (implies (and (vl-printed-p x)
                  (force (vl-printedlist-p y)))
             (vl-printedlist-p (make-list-ac n x y)))
    :hints(("Goal" :induct (len x)
            :expand ((vl-printedlist-p x)
                     (vl-printedtree-p (car x))
                     (vl-printedtree-p x)))))

  (defthm vl-printedlist-p-of-append
    (implies (and (vl-printedlist-p a)
                  (vl-printedlist-p b))
             (vl-printedlist-p (append a b))))

  (defthm vl-printedlist-p-of-rev
    (implies (vl-printedlist-p x)
             (vl-printedlist-p (rev x)))
    :hints(("Goal" :in-theory (enable rev))))

  (defthm vl-printedlist-p-of-revappend
    (implies (and (vl-printedlist-p x)
                  (vl-printedlist-p y))
             (vl-printedlist-p (revappend x y)))
    :hints (("goal" :induct (revappend x y))))


  (defthm vl-printedlist-p-of-repeat
    (implies (vl-printedlist-p x)
             (vl-printedlist-p (repeat n x)))
    :hints(("Goal" :in-theory (enable repeat))))

  (defthm vl-printedlist-p-of-revappend-chars
    (implies (vl-printedlist-p acc)
             (vl-printedlist-p (str::revappend-chars x acc)))
    :hints(("Goal" :in-theory (e/d (str::revappend-chars)
                                   (acl2::revappend-removal))))))

(define vl-printedlist->chars ((x vl-printedlist-p)
                               acc)
  :returns (chars character-listp :hyp (character-listp acc))
  :guard-hints (("goal" :in-theory (enable str::printtree-p)))
  (if (atom x)
      (str::append-chars (str::printable->str x) acc)
    (vl-printedlist->chars (cdr x)
                           (vl-printedlist->chars (car x) acc))))

(def-alias vl-printedlist->string str::printtree->str)


(defthm vl-printedlist-p-of-cons-printed
  (implies (and (vl-printed-p x)
                (vl-printedlist-p y))
           (vl-printedlist-p (cons x y)))
  :hints(("Goal" :in-theory (enable vl-printedtree-p))))

(defthm vl-printedlist-p-of-cons-printedlist
  (implies (and (vl-printedlist-p x)
                (vl-printedlist-p y))
           (vl-printedlist-p (cons x y)))
  :hints(("Goal" :in-theory (enable vl-printedtree-p))))



(defthm vl-printedlist-fix-of-cons-printed
  (implies (vl-printed-p x)
           (equal (vl-printedlist-fix (cons x y))
                  (cons x (vl-printedlist-fix y))))
  :hints(("Goal" :in-theory (enable vl-printedtree-p))))

(defthm vl-printedlist-fix-of-cons-printedlist
  (implies (vl-printedlist-p x)
           (equal (vl-printedlist-fix (cons x y))
                  (cons x (vl-printedlist-fix y))))
  :hints(("Goal" :in-theory (enable vl-printedtree-p))))
