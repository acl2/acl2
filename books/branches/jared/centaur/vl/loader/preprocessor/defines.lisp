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
(include-book "../../util/defs")
(include-book "../../util/echars")
(local (include-book "../../util/arithmetic"))

(fty::defalist vl-defines
  :key-type stringp
  :val-type vl-echarlist-p
  :true-listp t)

(defalist vl-defines-p (x)
  :key (stringp x)
  :val (vl-echarlist-p x)
  :keyp-of-nil nil
  :valp-of-nil t
  :true-listp t
  :parents (preprocessor)
  :short "Alist for definitions."

  :long "<p>We keep track of the @('`defines') which have been issued using a
simple alist that maps strings to their values.  Each value is an @(see
vl-echarlist-p) of the characters in the definition.</p>

<p>This model is too simple to support macros with arguments, but it is adequate
for simple macros.</p>"
  :already-definedp t)

(defthm vl-defines-p-of-remove-from-alist
  (implies (vl-defines-p x)
           (vl-defines-p (remove-from-alist key x)))
  :hints(("Goal" :in-theory (enable vl-defines-p))))


(define vl-lookup-in-defines ((name stringp)
                              (x    vl-defines-p))
  :parents (vl-defines-p)
  :short "@(call vl-lookup-in-defines) looks up a string in a @(see
vl-defines-p)."

  :long "<p>We introduce @('vl-lookup-in-defines') instead of just using
@('hons-assoc-equal') because its stronger guard is good for type checking.
But for reasoning, we just leave this function enabled and reason
about@('hons-assoc-equal') instead.</p>

<p>Note that the defines aren't a fast alist and we aren't using @('hons-get');
we're just using @('hons-assoc-equal') as our normal form.</p>"
  :enabled t

  (hons-assoc-equal name x))


(define vl-compressed-defines-p (x)
  :parents (preprocessor)
  :short "Compact alternative to @(see vl-defines-p), mainly intended for use
in serialization."
  :returns bool

  :long "<p>An @(see vl-defines-p) structure is especially verbose because it
represents each definition as a list of @(see vl-echar-p)s, which have their
own location, etc.  We implement a simple compression scheme that allows us to
pack a @(see vl-defines-p) into a more compact, string-based structure.  We can
later decompress these defines, except perhaps for the exact location
data.</p>"

  (if (atom x)
      (eq x nil)
    (and (tuplep 3 (car x))
         (stringp (first (car x)))
         (stringp (second (car x)))
         (vl-location-p (third (car x)))
         (vl-compressed-defines-p (cdr x)))))

(local (in-theory (enable vl-compressed-defines-p)))

(define vl-compress-defines
  :parents (vl-compressed-defines-p)
  ((x vl-defines-p))
  :returns (compressed vl-compressed-defines-p :hyp :fguard)
  (if (atom x)
      nil
    (cons (list (caar x)
                (vl-echarlist->string (cdar x))
                (if (consp (cdar x))
                    (vl-echar->loc (car (cdar x)))
                  *vl-fakeloc*))
          (vl-compress-defines (cdr x)))))

(define vl-uncompress-defines
  :parents (vl-compressed-defines-p)
  ((x vl-compressed-defines-p))
  :returns (uncompressed vl-defines-p :hyp :fguard)
  (b* (((when (atom x))
        nil)
       (entry (car x))
       (name  (first entry))
       (str   (second entry))
       ((vl-location loc) (third entry))
       (chars (vl-echarlist-from-str str
                                     :filename loc.filename
                                     :line loc.line
                                     :col loc.col)))
    (cons (cons name chars)
          (vl-uncompress-defines (cdr x)))))

(define vl-make-initial-defines ((x string-listp))
  :returns (defs vl-defines-p)
  :parents (vl-defines-p)
  :short "Simple way to build a @(see vl-defines-p) that @('`define')s a list
of names to @('1')."

  (if (atom x)
      nil
    (cons (cons (string-fix (car x)) (vl-echarlist-from-str "1"))
          (vl-make-initial-defines (cdr x)))))

