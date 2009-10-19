; ACL2 String Library
; Copyright (C) 2009 Centaur Technology
; Contact: jared@cs.utexas.edu
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "STR")
(include-book "tools/bstar" :dir :system)
(local (include-book "make-event/assert" :dir :system))
(local (include-book "arithmetic"))

; HTML Encoding
;
; We now implement some routines to encode HTML entities such as < and & into
; the &lt;, &amp;, etc.
;
; In principle, this conversion may not be entirely legitimate in the sense of
; any particular HTML specification, since X might contain non-printable
; characters or other similarly unlikely garbage.  But it seems like what we
; implement is pretty reasonable.
;
; We convert #\Newline characters into the sequence <br/>#\Newline.  This may
; not be the desired behavior in certain applications, but is very convenient
; for what we are trying to accomplish in VL.

(defconst *html-space*    (coerce "&nbsp;" 'list))
(defconst *html-newline*  (append (coerce "<br/>" 'list) (list #\Newline)))
(defconst *html-less*     (coerce "&lt;"   'list))
(defconst *html-greater*  (coerce "&gt;"   'list))
(defconst *html-amp*      (coerce "&amp;"  'list))
(defconst *html-quote*    (coerce "&quot;" 'list))


(defund repeated-revappend (n x y)
  (declare (xargs :guard (and (natp n)
                              (true-listp x))))
  (if (zp n)
      y
    (repeated-revappend (- n 1) x (revappend x y))))

(defthm character-listp-of-repeated-revappend
  (implies (and (character-listp x)
                (character-listp y))
           (character-listp (repeated-revappend n x y)))
  :hints(("Goal" :in-theory (enable repeated-revappend))))

(encapsulate
 ()
 (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

 (defund distance-to-tab (col tabsize)
   (declare (xargs :guard (and (natp col) 
                               (posp tabsize))))
   (mbe :logic
        (nfix (- tabsize (rem col tabsize)))
        :exec 
        (- tabsize (rem col tabsize)))))
 


(defund html-encode-chars-aux (x col tabsize acc)
  (declare (xargs :guard (and (character-listp x)
                              (natp col)
                              (posp tabsize)
                              (character-listp acc))))

; Inputs:
;
;   - X, a list of characters which we are currently transforming into HTML.
;   - Col, our current column
;   - Acc, an ordinary character list, onto which we accumulate the encoded
;     HTML, in reverse order.
;
; We return (mv col' acc'), where col' is the new column number and acc is
; an updated accumulator that includes the HTML encoding of X in reverse.

  (if (atom x)
      (mv (mbe :logic (nfix col) :exec col)
          acc)
    (let ((char1 (car x)))
      (html-encode-chars-aux
       (cdr x)
       (cond ((eql char1 #\Newline)
              0)
             ((eql char1 #\Tab)
              (+ col (distance-to-tab col tabsize)))
             (t
              (+ 1 col)))
       tabsize
       (case char1
         ;; Cosmetic: avoid inserting &nbsp; unless the last char is a 
         ;; space or newline.  This makes the HTML a little easier to 
         ;; read.
         (#\Space   (if (or (atom acc)
                            (eql (car acc) #\Space)
                            (eql (car acc) #\Newline))
                        (revappend *html-space* acc)
                      (cons #\Space acc)))
         (#\Newline (revappend *html-newline* acc))
         (#\<       (revappend *html-less* acc))
         (#\>       (revappend *html-greater* acc))
         (#\&       (revappend *html-amp* acc))
         (#\"       (revappend *html-quote* acc))
         (#\Tab     (repeated-revappend (distance-to-tab col tabsize) *html-space* acc))
         (otherwise (cons char1 acc)))))))

(defund html-encode-string-aux (x n xl col tabsize acc)
  (declare (xargs :guard (and (stringp x)
                              (natp n)
                              (natp xl)
                              (natp col)
                              (posp tabsize)
                              (character-listp acc)
                              (<= n xl)
                              (= xl (length x)))
                  :measure (nfix (- (nfix xl) (nfix n))))
           (type string x)
           (type integer n xl col tabsize))
  (if (mbe :logic (zp (- (nfix xl) (nfix n)))
           :exec (= n xl))
      (mv (mbe :logic (nfix col) :exec col)
          acc)
    (let ((char1 (char x n)))
      (html-encode-string-aux
       x 
       (mbe :logic (+ 1 (nfix n)) :exec (+ 1 n))
       xl 
       (cond ((eql char1 #\Newline)
              0)
             ((eql char1 #\Tab)
              (+ col (distance-to-tab col tabsize)))
             (t
              (+ 1 col)))
       tabsize
       (case char1
         ;; Cosmetic: avoid inserting &nbsp; unless the last char is a 
         ;; space or newline.  This makes the HTML a little easier to 
         ;; read.
         (#\Space   (if (or (atom acc)
                            (eql (car acc) #\Space)
                            (eql (car acc) #\Newline))
                        (revappend *html-space* acc)
                      (cons #\Space acc)))
         (#\Newline (revappend *html-newline* acc))
         (#\<       (revappend *html-less* acc))
         (#\>       (revappend *html-greater* acc))
         (#\&       (revappend *html-amp* acc))
         (#\"       (revappend *html-quote* acc))
         (#\Tab     (repeated-revappend (distance-to-tab col tabsize) *html-space* acc))
         (otherwise (cons char1 acc)))
       ))))

;; Bleh.  Should probably prove they are equal, but whatever.
(local (ACL2::assert! (b* ((x "blah
tab:	  <boo> & \"foo\" blah blah")
                     ((mv str-col str-ans)
                      (html-encode-string-aux x 0 (length x) 0 8 nil))
                     ((mv char-col char-ans)
                      (html-encode-chars-aux (coerce x 'list) 0 8 nil))
                     (- (cw "~s0~%" (coerce (reverse str-ans) 'string))))
                    (and (equal str-col char-col)
                         (equal str-ans char-ans)))))

(defthm natp-of-html-encode-chars-aux
  (natp (mv-nth 0 (html-encode-chars-aux x col tabsize acc)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable html-encode-chars-aux))))

(defthm natp-of-html-encode-string-aux
  (natp (mv-nth 0 (html-encode-string-aux x n xl col tabsize acc)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable html-encode-string-aux))))

(defthm character-listp-of-html-encode-chars-aux
  (implies (and (character-listp x)
                (natp col)
                (character-listp acc))
           (character-listp (mv-nth 1 (html-encode-chars-aux x col tabsize acc))))
  :hints(("Goal" :in-theory (enable html-encode-chars-aux))))

(defthm character-listp-of-html-encode-string-aux
  (implies (and (stringp x)
                (natp n)
                (natp xl)
                (natp col)
                (character-listp acc)
                (<= n xl)
                (= xl (length x)))
           (character-listp (mv-nth 1 (html-encode-string-aux x n xl col tabsize acc))))
  :hints(("Goal" :in-theory (enable html-encode-string-aux))))



(defund html-encode-string (x tabsize)
  (declare (xargs :guard (and (stringp x)
                              (posp tabsize)))
           (type string x)
           (type integer tabsize))
  (mv-let (col acc)
          (html-encode-string-aux x 0 (length x) 0 tabsize nil)
          (declare (ignore col))
          (reverse (coerce acc 'string))))

(defthm stringp-of-html-encode-string 
  (stringp (html-encode-string x tabsize))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable html-encode-string))))

