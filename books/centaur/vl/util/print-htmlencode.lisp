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
(include-book "std/strings/cat" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))
(local (include-book "arithmetic"))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (in-theory (enable acl2::arith-equiv-forwarding)))
(local (std::add-default-post-define-hook :fix))

(defsection html-encoding
  :parents (utilities)
  :short "Routines to encode HTML entities such as @('<') and @('&') into
@('&lt;'), @('&amp;'), etc."

  :long "<p>In principle, this conversion may not be entirely legitimate in the
sense of any particular HTML specification, since ACL2 strings might contain
non-printable characters or other similarly unlikely garbage.  But it seems
like what we implement is pretty reasonable.</p>

<p>We convert newline characters into the sequence @('<br/>#\Newline').  This
may not be the desired behavior in certain applications, but is very convenient
for what we are trying to accomplish in VL.</p>")

(local (xdoc::set-default-parents html-encoding))

(defval *vl-html-&nbsp*   (explode "&nbsp;"))
(defval *vl-html-newline* (append (explode "<br/>") (list #\Newline)))
(defval *vl-html-&lt*     (explode "&lt;"))
(defval *vl-html-&gt*     (explode "&gt;"))
(defval *vl-html-&amp*    (explode "&amp;"))
(defval *vl-html-&quot*   (explode "&quot;"))


(define repeated-revappend ((n natp) x y)
  (if (zp n)
      y
    (repeated-revappend (- n 1) x (revappend-without-guard x y)))
  ///
  (defthm character-listp-of-repeated-revappend
    (implies (and (character-listp x)
                  (character-listp y))
             (character-listp (repeated-revappend n x y)))))


(define vl-distance-to-tab ((col natp)
                            (tabsize posp))
  :returns (distance natp :rule-classes :type-prescription)
  :inline t
  (mbe :logic
       (b* ((col     (nfix col))
            (tabsize (acl2::pos-fix tabsize)))
         (nfix (- tabsize (mod col tabsize))))
       :exec
       (- tabsize (rem col tabsize)))
  :prepwork
  ((local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
   (local (in-theory (disable mod rem)))))


(define vl-html-encode-next-col
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
    (cond ((eql char1 #\Newline)
           0)
          ((eql char1 #\Tab)
           (+ col (vl-distance-to-tab col tabsize)))
          (t
           (+ 1 col)))))

(define vl-html-encode-push
  :short "Print the HTML encoding of a character."
  ((char1   characterp "Character to be printed.")
   (col     natp       "Current column number before printing char1 (for tab computations).")
   (tabsize posp)
   (acc                "Reverse order characters we're building."))
  :returns (new-acc character-listp :hyp (character-listp acc))
  (b* ((char1 (mbe :logic (char-fix char1) :exec char1))
       (col   (lnfix col)))
    (case char1
      ;; Cosmetic: avoid inserting &nbsp; unless the last char is a
      ;; space or newline.  This makes the HTML a little easier to
      ;; read.
      (#\Space   (if (or (atom acc)
                         (eql (car acc) #\Space)
                         (eql (car acc) #\Newline))
                     (revappend *vl-html-&nbsp* acc)
                   (cons #\Space acc)))
      (#\Newline (revappend *vl-html-newline* acc))
      (#\<       (revappend *vl-html-&lt* acc))
      (#\>       (revappend *vl-html-&gt* acc))
      (#\&       (revappend *vl-html-&amp* acc))
      (#\"       (revappend *vl-html-&quot* acc))
      (#\Tab     (repeated-revappend (vl-distance-to-tab col tabsize)
                                     *vl-html-&nbsp* acc))
      (otherwise (cons char1 acc)))))

(define vl-html-encode-chars-aux
  :short "Print an HTML-encoded character-list."
  ((x       character-listp "Characters we're transforming into HTML.")
   (col     natp            "Current column number we're at.")
   (tabsize posp)
   (acc     "Characters being accumulated in reverse order."))
  :returns
  (mv (new-col natp :rule-classes :type-prescription
               "Updated column number.")
      (new-acc "Updated accumulator with the HTML encoding of X."
               character-listp :hyp (character-listp acc)))
  (b* (((when (atom x))
        (mv (lnfix col) acc))
       (char1 (mbe :logic (char-fix (car x))
                   :exec (car x)))
       ;; Warning: order is important here for proper column tracking
       (acc (vl-html-encode-push char1 col tabsize acc))
       (col (vl-html-encode-next-col char1 col tabsize)))
    (vl-html-encode-chars-aux (cdr x) col tabsize acc)))

(define vl-html-encode-string-aux
  :short "Print an HTML encoded string, efficiently, without exploding it."
  ((x stringp)
   (n natp)
   (xl (eql xl (length x)))
   (col natp)
   (tabsize posp)
   acc)
  :guard (<= n xl)
  :returns (mv new-col new-acc)
  :long "<p>We just leave this enabled since its logical definition is so simple.</p>"
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (nfix (- (nfix xl) (nfix n)))
  (declare (type string x)
           (type integer n xl col tabsize))
  :split-types t
  :hooks nil
  :verify-guards nil
  :enabled t
  (mbe :logic
       (vl-html-encode-chars-aux (nthcdr n (explode x))
                                 col tabsize acc)
       :exec
       (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                        :exec (eql n xl)))
             (mv (lnfix col) acc))
            (char1 (char x n))
            ;; Warning: order is important here for proper column tracking
            (acc (vl-html-encode-push char1 col tabsize acc))
            (col (vl-html-encode-next-col char1 col tabsize)))
         (vl-html-encode-string-aux x (+ 1 (lnfix n)) xl col tabsize acc)))
  ///
  (local (in-theory (enable vl-html-encode-string-aux
                            vl-html-encode-chars-aux)))
  (verify-guards vl-html-encode-string-aux))

(define vl-html-encode-string
  :short "Convenient routine for HTML encoding a string."
  ((x       stringp "The string to HTML encode.")
   (tabsize posp    "Desired width for tabs (e.g., 8)."))
  (declare (type string x)
           (type unsigned-byte tabsize))
  :split-types t
  :returns (html-x stringp :rule-classes :type-prescription)
  (b* (((mv ?col acc)
        (vl-html-encode-string-aux x 0 (length x) 0 tabsize nil)))
    (str::rchars-to-string acc)))
