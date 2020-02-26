; ACL2 String Library
; Copyright (C) 2009-2016 Centaur Technology
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
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "arithmetic"))
(local (std::add-default-post-define-hook :fix))

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

(local (xdoc::set-default-parents html-encoding))

(xdoc::order-subtopics html-encoding
                       (html-encode-string
                        html-encode-string-basic))

(defmacro html-space ()    (list 'quote (coerce "&nbsp;" 'list)))
(defmacro html-newline ()  (list 'quote (append (coerce "<br/>" 'list) (list #\Newline))))
(defmacro html-less ()     (list 'quote (coerce "&lt;"   'list)))
(defmacro html-greater ()  (list 'quote (coerce "&gt;"   'list)))
(defmacro html-amp ()      (list 'quote (coerce "&amp;"  'list)))
(defmacro html-quote ()    (list 'quote (coerce "&quot;" 'list)))

(define html-encode-char-basic
  :short "HTML encode a single character (simple version, no tab support)."
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
  :short "Convert a string into HTML (simple version, no tab support)."
  ((x  stringp             "String we're encoding.")
   (n  natp                "Current position in @('x').  Should typically start as 0.")
   (xl (eql xl (length x)) "Precomputed length of @('x').")
   (acc                    "Accumulator for output characters, reverse order."))
  :guard (<= n xl)
  :enabled t
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (nfix (- (nfix xl) (nfix n)))
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
  :short "Convert a string into HTML (simple version, no tab support)."
  ((x stringp))
  :returns (html-string stringp :rule-classes :type-prescription)
  (rchars-to-string
   (html-encode-string-basic-aux x 0 (length x) nil)))

(define repeated-revappend ((n natp) x y)
  :parents (html-encode-push)
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
  :parents (html-encode-push)
  :inline t
  :split-types t
  (declare (type unsigned-byte col tabsize))
  (mbe :logic
       (b* ((col (nfix col))
            (tabsize (acl2::pos-fix tabsize)))
         (nfix (- tabsize (rem col tabsize))))
       :exec
       (- tabsize
          (the unsigned-byte (rem col tabsize))))
  :prepwork ((local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
             (local (in-theory (disable rem)))))

(define html-encode-next-col
  :parents (html-encode-push)
  :short "Compute where we'll be after printing a character, accounting for tab
          sizes and newlines."
  ((char1 characterp "Character to be printed.")
   (col   natp       "Current column number before printing char1.")
   (tabsize posp))
  :returns (new-col natp :rule-classes :type-prescription
                    "New column number after printing char1.")
  :inline t
  (b* ((char1 (mbe :logic (char-fix char1) :exec char1))
       (col   (lnfix col)))
    (cond ((eql char1 #\Newline) 0)
          ((eql char1 #\Tab)     (+ col (distance-to-tab col tabsize)))
          (t                     (+ 1 col)))))

(define html-encode-push
  :short "HTML encode a single character, with column/tabsize support."
  ((char1   characterp "Character to be printed.")
   (col     natp       "Current column number before printing char1 (for tab computations).")
   (tabsize posp)
   (acc                "Reverse order characters we're building."))
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* (((the character char1) (mbe :logic (char-fix char1)
                                   :exec char1)))
    (case char1
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

(define html-encode-chars-aux
  :short "Convert a character list into HTML.  Outputs to an accumulator.
Tracks the column number to handle tab characters."
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
       ;; Warning: order is important here for proper column tracking
       (acc (html-encode-push (car x) col tabsize acc))
       (col (html-encode-next-col (car x) col tabsize)))
    (html-encode-chars-aux (cdr x) col tabsize acc)))

(define html-encode-string-aux
  :short "Core of converting strings into HTML, output to an accumulator."
  ((x       stringp  "String we're encoding.")
   (n       natp     "Current position in @('x').  Should typically start as 0.")
   (xl      (eql xl (length x)))
   (col     natp     "Current column we're printing to.")
   (tabsize posp)
   (acc))
  :guard (<= n xl)
  :returns
  (mv (new-col natp :rule-classes :type-prescription)
      (new-acc character-listp :hyp (character-listp acc)))
  :split-types t
  (declare (type string x)
           (type unsigned-byte n xl col tabsize))
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (nfix (- (nfix xl) (nfix n)))
  :long "<p>This is similar to @(see html-encode-chars-aux), but encodes part
of a the string @('x') instead of a character list.</p>"
  ;; This has such a nice logical definition that we may as well leave it
  ;; enabled.
  :enabled t
  :verify-guards nil
  (mbe :logic (html-encode-chars-aux (nthcdr n (explode x)) col tabsize acc)
       :exec
       (b* (((when (mbe :logic (zp (- (length (str-fix x)) (nfix n)))
                        :exec (eql n xl)))
             (mv (lnfix col) acc))
            (char1   (char x n))
            ;; Warning: order is important here for proper column tracking
            (acc (html-encode-push char1 col tabsize acc))
            (col (html-encode-next-col char1 col tabsize)))
         (html-encode-string-aux x (+ 1 (lnfix n)) xl col tabsize acc)))
  ///
  (verify-guards html-encode-string-aux
    :hints(("Goal" :in-theory (enable html-encode-chars-aux)))))

(define html-encode-string
  :short "@(call html-encode-string) converts the string @('x') into HTML, and
returns the result as a new string.  Tracks the column number to handle tab
characters."
  ((x       stringp)
   (tabsize posp))
  :returns
  (html-encoded stringp :rule-classes :type-prescription)
  (b* ((x (mbe :logic (str-fix x) :exec x))
       ((mv ?col acc) (html-encode-string-aux x 0 (length x) 0 tabsize nil)))
    (rchars-to-string acc)))
