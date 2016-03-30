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

(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "tools/include-raw" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(define vl-printed-p (x)
  :parents (vl-printedlist)
  :short "Recognize a printed object (string or character)."
  (or (characterp x)
      (stringp x))
  ///
  (defthm vl-printed-p-cr
    (equal (vl-printed-p x)
           (or (characterp x)
               (stringp x)))
    :rule-classes :compound-recognizer
    :hints(("Goal" :in-theory (enable vl-printed-p))))

  (defthm vl-printed-p-by-backchaining
    (implies (or (characterp x)
                 (stringp x))
             (vl-printed-p x))))

(define vl-printed-fix
  :parents (vl-printed-p)
  :short "Fixing function for @(see vl-printed-p) objects."
  ((x vl-printed-p))
  :returns (x-fix vl-printed-p)
  :inline t
  (mbe :logic (if (vl-printed-p x)
                  x
                "")
       :exec x)
  ///
  (defthm vl-printed-fix-when-vl-printed-p
    (implies (vl-printed-p x)
             (equal (vl-printed-fix x)
                    x))))

(fty::deffixtype vl-printed
  :pred vl-printed-p
  :fix vl-printed-fix
  :equiv vl-printed-equiv
  :define t
  :forward t)

(fty::deftypes vl-printedlist
  (fty::defflexsum vl-printedtree
    (:leaf
     :cond (and (atom x) x)
     :fields ((elt :type vl-printed :acc-body x))
     :ctor-body elt)
    (:list
     :cond t
     :fields ((list :type vl-printedlist :acc-body x))
     :ctor-body list)
    :measure (two-nats-measure (acl2-count x) 1))
  (fty::deflist vl-printedlist :elt-type vl-printedtree :true-listp t
    :measure (two-nats-measure (acl2-count x) 0)
    :short "A list of strings/characters (and, recursively, printedlists) to print in reverse order."
    :long "<p>Useful for formatting a long string to print.  Also the basis of
the @(see ps) printer-state stobj.</p>"))

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

  (defthm vl-printedlist-p-of-revappend-chars
    (implies (vl-printedlist-p acc)
             (vl-printedlist-p (str::revappend-chars x acc)))
    :hints(("Goal" :in-theory (enable str::revappend-chars)
            :induct (len x)
            :expand ((vl-printedlist-p x)
                     (vl-printedtree-p (car x)))))))



(define vl-printedlist-length ((x vl-printedlist-p)
                               (acc natp))
  :returns (len natp :rule-classes :type-prescription)
  :parents (vl-printedlist-p)
  :short "Compute the total length of the list, in characters."
  :long "<p>This is different than ordinary @(see len) because any strings
within the list may have their own lengths.</p>"
  :measure (vl-printedlist-count x)
  :ruler-extenders (:lambdas)
  (b* ((x (vl-printedlist-fix x))
       ((when (atom x))
        (lnfix acc))
       (x1 (car x))
       (acc (vl-printedtree-case x1
              :leaf (+ (if (characterp x1.elt) 1 (length x1.elt)) (lnfix acc))
              :list (vl-printedlist-length x1.list acc))))
    (vl-printedlist-length (cdr x) acc)))



(define vl-printedlist-peek
  ((x vl-printedlist-p "The printed list, which we assume is in reverse order!"))
  :returns (maybe-char (or (not maybe-char)
                           (characterp maybe-char))
                       :rule-classes :type-prescription)
  :parents (vl-printedlist-p)
  :short "Extract the last character that was printed."
  :long "<p>This is generally useful for things like <i>insert a space unless
we just printed a newline</i>, etc.</p>"
  :measure (vl-printedlist-count x)
  :ruler-extenders :all
  (and (consp x)
       (or (let ((x1 (vl-printedtree-fix (car x))))
             (vl-printedtree-case x1
               :leaf (if (characterp x1.elt)
                         x1.elt
                       (let ((len (length x1.elt)))
                         (if (zp len)
                             ;; Degenerate case where we printed an empty string, look
                             ;; further.
                             nil
                           (char x1.elt (1- len)))))
               :list (vl-printedlist-peek x1.list)))
           (vl-printedlist-peek (cdr x)))))

(define vl-printedlist->chars ((x vl-printedlist-p)
                               acc)
  :returns (chars character-listp :hyp (character-listp acc))
  :parents (vl-ps->chars)
  :short "Convert a printed list (in reverse order) into characters (in proper
  order)."
  :measure (vl-printedlist-count x)
  (b* (((when (atom x))
        acc)
       (x1 (vl-printedtree-fix (car x))))
    (vl-printedtree-case x1
      :leaf (if (characterp x1.elt)
                ;; Prefer to test characterp instead of stringp, since characters are
                ;; immediates in CCL.
                (vl-printedlist->chars (cdr x) (cons x1.elt acc))
              ;; Subtle: the printedlist are in reverse order, but the strings within it are
              ;; in proper order, so we need to use append-chars instead of
              ;; revappend-chars here.
              (vl-printedlist->chars (cdr x) (str::append-chars x1.elt acc)))
      :list (vl-printedlist->chars (cdr x)
                                   (vl-printedlist->chars x1.list acc)))))

(define vl-printedlist->string ((x vl-printedlist-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (vl-printedlist)
  :short "@('(vl-printedlist->string)') returns the printed characters as a
string in the proper, non-reversed, printed order."
  :long "<p>This is logically just @('(implode (vl-printedlist->chars))'), but we
install a more efficient definition under the hood in raw Lisp.</p>"
  (implode (vl-printedlist->chars x nil))
  ///
  (defttag vl-optimize)
  ;; (depends-on "printedlist-fast.lsp")
  (acl2::include-raw "printedlist-fast.lsp")

  (defttag nil))


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

(in-theory (disable vl::vl-printedlist-p-of-cons
                    vl::vl-printedlist-fix-of-cons))
