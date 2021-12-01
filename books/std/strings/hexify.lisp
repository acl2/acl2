; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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

(in-package "STR")
(include-book "coerce")
(include-book "std/util/bstar" :dir :system)
(local (include-book "explode-atom"))
(local (include-book "arithmetic"))
(local (in-theory (disable explode-atom)))

(defsection insert-underscores
  :parents (hexify)

  (defund insert-underscores (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           x)
          ((equal (mod (len x) 4) 0)
           (list* #\_ (car x) (insert-underscores (cdr x))))
          (t
           (list* (car x) (insert-underscores (cdr x))))))

  (local (in-theory (enable insert-underscores)))

  (defthm character-listp-of-insert-underscores
    (implies (force (character-listp x))
             (character-listp (insert-underscores x)))))

(defsection hexify
  :parents (hex)
  :short "Convert numbers into readable hex strings."

  :long "<p>@(call hexify) is a dumb but useful printing utility for displaying
numbers in hex.  It is typically used in @(see cw) statements, e.g.,:</p>

@({
    ACL2 !> (cw \"foo is ~s0~%\" (str::hexify (1- (expt 2 32))))
    foo is #uxFFFF_FFFF
    NIL
    ACL2 !>
})

<p>The @('#ux') is for compatibility with the @(see acl2::sharp-u-reader).</p>

<p>See also @(see nat-to-dec-string) which converts numbers into decimal strings (without
underscores) and @(see binify) which is like @('hexify') but for binary instead
of hex.</p>

<h3>Usage</h3>

<p>@(call hexify) always returns a @(see stringp).</p>

<p>@('x') must be an integer, string, or symbol; otherwise a @(see hard-error)
will be caused.</p>

<p>Normally @('x') is an integer.  In this case, we convert it into an
msb-first hex string with an underscore inserted every four characters.  This
makes it easier to read long values.</p>

<p>When @('x') is a string we just return it unchanged.</p>

<p>When @('x') is a symbol we just return its name.</p>"

  (defun hexify (x)
    (declare (xargs :guard t))
    (cond ((integerp x)
           (b* ((xsign (< x 0))
                (xabs (abs x))
                (chars (explode-atom xabs 16)) ;; looks like BEEF...
                (nice-chars (list* #\# #\u #\x
                                   (append (and xsign '(#\-))
                                           (cons (first chars)
                                                 (insert-underscores (nthcdr 1 chars)))))))
             (implode nice-chars)))
          ((symbolp x)
           (symbol-name x))
          ((stringp x)
           x)
          (t
           (prog2$ (er hard? 'hexify "Unexpected argument ~x0.~%" x)
                   "")))))


(defsection hexify-width
  :parents (hex)
  :short "Convert numbers into readable hex strings, fixing the number of digits printed"

  :long "<p>@(call hexify-width) produces output just like @(see hexify), but when printing an integer
it always prints the given number of digits.  When the number to be printed is longer, it truncates the more significant digits, and when it is shorter, it pads with 0s.</p>

@({
    ACL2 !> (cw \"foo is ~s0~%\" (str::hexify-width (1- (expt 2 32)) 12))
    foo is #ux0000_FFFF_FFFF
    NIL
    ACL2 !>
})

<p>The @('#ux') is for compatibility with the @(see acl2::sharp-u-reader).</p>"

  (local (defthm character-listp-of-cons
           (equal (character-listp (cons a b))
                  (and (characterp a) (character-listp b)))))

  (local (defthm character-listp-of-cdr
           (implies (character-listp x)
                    (character-listp (cdr x)))))

  (local (defthm character-listp-of-nthcdr
           (implies (character-listp x)
                    (character-listp (nthcdr n x)))))

  (defun hexify-width (x width)
    (declare (xargs :guard (posp width)
                    :guard-hints (("goal" :in-theory (disable character-listp)))))
    (b* ((width (mbe :logic (if (posp width) width 1) :exec width)))
      (cond ((integerp x)
             (b* ((xsign (< x 0))
                  (xabs (abs x))
                  (chars (explode-atom xabs 16)) ;; looks like BEEF...
                  (fixed-chars (cond ((<= width (len chars)) (nthcdr (- (len chars) width) chars))
                                     (t (append (make-list (- width (len chars)) :initial-element #\0)
                                                chars))))
                  (nice-chars (list* #\# #\u #\x
                                     (append (and xsign '(#\-))
                                             (cons (first fixed-chars)
                                                   (insert-underscores (nthcdr 1 fixed-chars)))))))
               (implode nice-chars)))
            ((symbolp x)
             (symbol-name x))
            ((stringp x)
             x)
            (t
             (prog2$ (er hard? 'hexify-width "Unexpected argument ~x0.~%" x)
                     ""))))))



(defsection binify
  :parents (binary)
  :short "Convert numbers into readable binary strings."
  :long "<p>@(call binify) is identical to @(see str::hexify) except that it
produces binary output instead of hex output.</p>"

  (defun binify (x)
    (declare (xargs :guard t))
    (cond ((integerp x)
           (b* ((xsign (< x 0))
                (xabs (abs x))
                (chars (explode-atom xabs 2))
                (nice-chars (list* #\# #\u #\b
                                   (append (and xsign '(#\-))
                                           (cons (first chars)
                                                 (insert-underscores (nthcdr 1 chars)))))))
             (implode nice-chars)))
          ((symbolp x)
           (symbol-name x))
          ((stringp x)
           x)
          (t
           (prog2$ (er hard? 'binify "Unexpected argument ~x0.~%" x)
                   "")))))


(defsection binify-width
  :parents (binary)
  :short "Convert numbers into readable binary strings, fixing the number of digits printed"

  :long "<p>@(call binify) is identical to @(see str::hexify-width) except that
it produces binary output instead of hex output.</p>"

  (local (defthm character-listp-of-cons
           (equal (character-listp (cons a b))
                  (and (characterp a) (character-listp b)))))

  (local (defthm character-listp-of-cdr
           (implies (character-listp x)
                    (character-listp (cdr x)))))

  (local (defthm character-listp-of-nthcdr
           (implies (character-listp x)
                    (character-listp (nthcdr n x)))))

  (defun binify-width (x width)
    (declare (xargs :guard (posp width)
                    :guard-hints (("goal" :in-theory (disable character-listp)))))
    (b* ((width (mbe :logic (if (posp width) width 1) :exec width)))
      (cond ((integerp x)
             (b* ((xsign (< x 0))
                  (xabs (abs x))
                  (chars (explode-atom xabs 2)) ;; looks like 10010010...
                  (fixed-chars (cond ((<= width (len chars)) (nthcdr (- (len chars) width) chars))
                                     (t (append (make-list (- width (len chars)) :initial-element #\0)
                                                chars))))
                  (nice-chars (list* #\# #\u #\b
                                     (append (and xsign '(#\-))
                                             (cons (first fixed-chars)
                                                   (insert-underscores (nthcdr 1 fixed-chars)))))))
               (implode nice-chars)))
            ((symbolp x)
             (symbol-name x))
            ((stringp x)
             x)
            (t
             (prog2$ (er hard? 'binify-width "Unexpected argument ~x0.~%" x)
                     ""))))))
