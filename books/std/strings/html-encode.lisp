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
(include-book "cat")
(include-book "std/util/bstar" :dir :system)
(include-book "misc/definline" :dir :system)  ;; bozo
(local (include-book "misc/assert" :dir :system))
(local (include-book "arithmetic"))

(defsection html-encoding
  :parents (std/strings)
  :short "Routines to encode HTML entities, e.g., @('<') becomes @('&lt;')."

  :long "<p>In principle, our conversion routines may not be entirely
legitimate in the sense of some precise HTML specification, because we do not
account for non-printable characters or other similarly unlikely garbage in the
input.  But it seems like what we implement is pretty reasonable, and handles
most ordinary characters.</p>

<p>Note that we convert @('#\\Newline') characters into the sequence
@('<br/>#\\Newline').  This may not be the desired behavior in certain
applications, but seems basically reasonable for converting plain text into
HTML.</p>")

(defmacro html-space ()    (list 'quote (coerce "&nbsp;" 'list)))
(defmacro html-newline ()  (list 'quote (append (coerce "<br/>" 'list) (list #\Newline))))
(defmacro html-less ()     (list 'quote (coerce "&lt;"   'list)))
(defmacro html-greater ()  (list 'quote (coerce "&gt;"   'list)))
(defmacro html-amp ()      (list 'quote (coerce "&amp;"  'list)))
(defmacro html-quote ()    (list 'quote (coerce "&quot;" 'list)))

(define html-encode-char-basic
  :parents (html-encoding)
  :short "HTML encode a single character (simple version, no column/tabsize support)."
  ((x   characterp "Character to encode.")
   (acc            "Accumulator for output characters, reverse order."))
  :returns
  (new-acc character-listp :hyp (character-listp acc))
  :split-types t
  :inline t
  (declare (type character x))
  (b* (((the character x)
        (mbe :logic (char-fix x)
             :exec x)))
    (case x
      ;; Cosmetic: avoid inserting &nbsp; unless the last char is a space or
      ;; newline.  This makes the HTML a little easier to read.
      (#\Space   (if (or (atom acc)
                         (eql (car acc) #\Space)
                         (eql (car acc) #\Newline))
                     (revappend (html-space) acc)
                   (cons #\Space acc)))
      (#\Newline (revappend (html-newline) acc))
      (#\<       (revappend (html-less) acc))
      (#\>       (revappend (html-greater) acc))
      (#\&       (revappend (html-amp) acc))
      (#\"       (revappend (html-quote) acc))
      (otherwise (cons x acc)))))

(define html-encode-chars-basic-aux
  :parents (html-encoding)
  :short "Convert a character list into HTML (simple version, no column/tabsize support)."
  ((x       character-listp "The characters to convert.")
   (acc                     "Accumulator for output characters, reverse order."))
  :returns
  (new-acc character-listp :hyp (character-listp acc))
  (b* (((when (atom x))
        acc)
       (acc (html-encode-char-basic (car x) acc)))
    (html-encode-chars-basic-aux (cdr x) acc)))

(define html-encode-string-basic-aux
  :parents (html-encoding)
  :short "Convert a string into HTML (simple version, no column/tabsize support)."
  ((x  stringp             "String we're encoding.")
   (n  natp                "Current position in @('x').  Should typically start as 0.")
   (xl (eql xl (length x)) "Precomputed length of @('x').")
   (acc                    "Accumulator for output characters, reverse order."))
  :guard (<= n xl)
  :enabled t
  :measure (nfix (- (nfix xl) (nfix n)))
  :verify-guards nil
  :split-types t
  (declare (type unsigned-byte n xl))
  (mbe :logic
       (html-encode-chars-basic-aux (nthcdr n (explode x)) acc)
       :exec
       (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                        :exec (eql n xl)))
             acc)
            (acc (html-encode-char-basic (char x n) acc))
            ((the unsigned-byte n)
             (mbe :logic (+ 1 (lnfix n))
                  :exec (+ 1 n))))
         (html-encode-string-basic-aux x n xl acc)))
  ///
  (verify-guards html-encode-string-basic-aux
    :hints(("Goal" :in-theory (enable html-encode-chars-basic-aux)))))

(define html-encode-string-basic
  :parents (html-encoding)
  :short "Convert a string into HTML."
  ((x stringp))
  :returns (html-string stringp :rule-classes :type-prescription)
  (rchars-to-string
   (html-encode-string-basic-aux x 0 (length x) nil)))

(define repeated-revappend ((n natp) x y)
  :parents (html-encoding)
  (if (zp n)
      y
    (repeated-revappend (- n 1) x (acl2::revappend-without-guard x y)))
  ///
  (defthm character-listp-of-repeated-revappend
    (implies (and (character-listp x)
                  (character-listp y))
             (character-listp (repeated-revappend n x y)))))

(define distance-to-tab ((col     natp)
                         (tabsize posp))
  :parents (html-encoding)
  :inline t
  :split-types t
  (declare (type unsigned-byte col tabsize))
  (mbe :logic
       (nfix (- tabsize (rem col tabsize)))
       :exec
       (- tabsize
          (the unsigned-byte (rem col tabsize))))
  :prepwork
  ((local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))))

(define html-encode-chars-aux
  :parents (html-encoding)
  :short "Convert a character list into HTML."

  ((x       character-listp "The characters to convert.")
   (col     natp            "Current column number.")
   (tabsize posp            "Width of tab characters.")
   (acc                     "Accumulator for output characters, reverse order."))
  :returns
  (mv (new-col natp :rule-classes :type-prescription
               "Updated column number after printing @('x').")
      (new-acc character-listp :hyp (character-listp acc)
               "Updated output."))
  :split-types t
  (declare (type unsigned-byte col tabsize))
  (b* (((when (atom x))
        (mv (lnfix col) acc))
       ((the character char1) (mbe :logic (char-fix (car x))
                                   :exec (car x)))
       ((the unsigned-byte new-col)
        (cond ((eql char1 #\Newline) 0)
              ((eql char1 #\Tab)     (+ col (distance-to-tab col tabsize)))
              (t                     (+ 1 col))))
       (acc (case char1
              ;; Cosmetic: avoid inserting &nbsp; unless the last char is a
              ;; space or newline.  This makes the HTML a little easier to
              ;; read.
              (#\Space   (if (or (atom acc)
                                 (eql (car acc) #\Space)
                                 (eql (car acc) #\Newline))
                             (revappend (html-space) acc)
                           (cons #\Space acc)))
              (#\Newline (revappend (html-newline) acc))
              (#\<       (revappend (html-less) acc))
              (#\>       (revappend (html-greater) acc))
              (#\&       (revappend (html-amp) acc))
              (#\"       (revappend (html-quote) acc))
              (#\Tab     (repeated-revappend (distance-to-tab col tabsize) (html-space) acc))
              (otherwise (cons char1 acc)))))
    (html-encode-chars-aux (cdr x) new-col tabsize acc)))

(define html-encode-string-aux
  :parents (html-encoding)
  :short "Convert a string into HTML."
  ((x       stringp  "String we're encoding.")
   (n       natp     "Current position in @('x').  Should typically start as 0.")
   (xl      (eql xl (length x)))
   (col     natp)
   (tabsize posp)
   (acc))
  :guard (<= n xl)
  :returns
  (mv (new-col natp :rule-classes :type-prescription)
      (new-acc character-listp :hyp (character-listp acc)))
  :split-types t
  (declare (type string x)
           (type unsigned-byte n xl col tabsize))
  :measure (nfix (- (nfix xl) (nfix n)))
  :long "<p>This is similar to @(see html-encode-chars-aux), but encodes part
of a the string @('x') instead of a character list.</p>"
  :verify-guards nil

  (mbe :logic (html-encode-chars-aux (nthcdr n (explode x)) col tabsize acc)
       :exec
       (b* (((when (mbe :logic (zp (- (length (str-fix x)) (nfix n)))
                        :exec (eql n xl)))
             (mv (lnfix col) acc))
            (char1   (char x n))
            (new-col (cond ((eql char1 #\Newline) 0)
                           ((eql char1 #\Tab)     (+ col (distance-to-tab col tabsize)))
                           (t                     (+ 1 col))))
            (acc (case char1
                   ;; Cosmetic: avoid inserting &nbsp; unless the last char is a
                   ;; space or newline.  This makes the HTML a little easier to
                   ;; read.
                   (#\Space   (if (or (atom acc)
                                      (eql (car acc) #\Space)
                                      (eql (car acc) #\Newline))
                                  (revappend (html-space) acc)
                                (cons #\Space acc)))
                   (#\Newline (revappend (html-newline) acc))
                   (#\<       (revappend (html-less) acc))
                   (#\>       (revappend (html-greater) acc))
                   (#\&       (revappend (html-amp) acc))
                   (#\"       (revappend (html-quote) acc))
                   (#\Tab     (repeated-revappend (distance-to-tab col tabsize) (html-space) acc))
                   (otherwise (cons char1 acc)))))
         (html-encode-string-aux x (+ 1 (lnfix n)) xl new-col tabsize acc)))
  ///
  (verify-guards html-encode-string-aux
    :hints(("Goal" :in-theory (enable html-encode-chars-aux)))))

(define html-encode-string
  :parents (html-encoding)
  :short "@(call html-encode-string) converts the string @('x') into HTML, and
returns the result as a new string."
  ((x       stringp)
   (tabsize posp))
  :returns
  (html-encoded stringp :rule-classes :type-prescription)
  (b* (((mv ?col acc) (html-encode-string-aux x 0 (length x) 0 tabsize nil)))
    (rchars-to-string acc)))


