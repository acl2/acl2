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
(include-book "char-case")
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "arithmetic"))

(define ichareqv ((x :type character)
                  (y :type character))
  :returns (bool)
  :parents (equivalences cases)
  :short "Case-insensitive character equivalence test."
  :long "<p>@(call ichareqv) determines if @('x') and @('y') are equivalent
when interpreted as characters without regard to case.  For instance,
upper-case C is equivalent to lower-case c under this relation.</p>

<p>ACL2 has a built-in version of this function, @(see char-equal), but it is
irritating to use because it has @(see standard-char-p) guards.  In contrast,
@('ichareqv') works on arbitrary characters, with some loss of efficiency.</p>"

  :inline t
  (eql (downcase-char x) (downcase-char y))
  ///
  (defequiv ichareqv)
  (defrefinement chareqv ichareqv)

  (encapsulate
    ()
    (local (defthmd l1
             (implies (equal (upcase-char x)
                             (upcase-char y))
                      (equal (downcase-char x)
                             (downcase-char y)))
             :hints(("Goal"
                     :in-theory (disable downcase-char-of-upcase-char)
                     :use ((:instance downcase-char-of-upcase-char (x x))
                           (:instance downcase-char-of-upcase-char (x y)))))))

    (local (defthmd l2
             (implies (equal (downcase-char x)
                             (downcase-char y))
                      (equal (upcase-char x)
                             (upcase-char y)))
             :hints(("Goal"
                     :in-theory (disable upcase-char-of-downcase-char)
                     :use ((:instance upcase-char-of-downcase-char (x x))
                           (:instance upcase-char-of-downcase-char (x y)))))))

    (defthm equal-of-upcase-char-and-upcase-char
      (equal (equal (upcase-char x) (upcase-char y))
             (ichareqv x y))
      :hints(("Goal" :use ((:instance l1)
                           (:instance l2))))))

  (defcong ichareqv equal (downcase-char x) 1)
  (defcong ichareqv equal (upcase-char x) 1)
  (defcong ichareqv equal (upcase-char-str x) 1)
  (defcong ichareqv equal (downcase-char-str x) 1))



(define icharlisteqv ((x character-listp)
                      (y character-listp))
  :returns (bool)
  :parents (equivalences cases)
  :short "Case-insensitive character-list equivalence test."

  :long "<p>@(call icharlisteqv) determines if @('x') and @('y') are
case-insensitively equivalent character lists.  That is, @('x') and @('y') must
have the same length and their elements must be @(see ichareqv) to one
another.</p>

<p>See also @(see charlisteqv) for a case-sensitive alternative.</p>"

  (if (consp x)
      (and (consp y)
           (ichareqv (car x) (car y))
           (icharlisteqv (cdr x) (cdr y)))
    (atom y))
  ///
  (defequiv icharlisteqv)

  (defrefinement charlisteqv icharlisteqv
    :hints(("Goal" :in-theory (enable chareqv))))

  (defcong icharlisteqv ichareqv     (car x)      1)
  (defcong icharlisteqv icharlisteqv (cdr x)      1)
  (defcong ichareqv     icharlisteqv (cons a x)   1)
  (defcong icharlisteqv icharlisteqv (cons a x)   2)
  (defcong icharlisteqv equal        (len x)      1)
  (defcong icharlisteqv icharlisteqv (list-fix x) 1)
  (defcong icharlisteqv ichareqv     (nth n x)    2)
  (defcong icharlisteqv icharlisteqv (nthcdr n x) 2)
  (defcong icharlisteqv icharlisteqv (take n x)   2)
  (defcong icharlisteqv icharlisteqv (append x y) 1)
  (defcong icharlisteqv icharlisteqv (append x y) 2)
  (defcong icharlisteqv icharlisteqv (rev x) 1)
  (defcong icharlisteqv icharlisteqv (revappend x y) 2)
  (defcong icharlisteqv icharlisteqv (revappend x y) 1)
  (defcong icharlisteqv icharlisteqv (make-character-list x) 1)

  (defthm icharlisteqv-when-not-consp-left
    (implies (not (consp x))
             (equal (icharlisteqv x y)
                    (atom y))))

  (defthm icharlisteqv-when-not-consp-right
    (implies (not (consp y))
             (equal (icharlisteqv x y)
                    (atom x))))

  (defthm icharlisteqv-of-cons-right
    (equal (icharlisteqv x (cons a y))
           (and (consp x)
                (ichareqv (car x) (double-rewrite a))
                (icharlisteqv (cdr x) (double-rewrite y)))))

  (defthm icharlisteqv-of-cons-left
    (equal (icharlisteqv (cons a x) y)
           (and (consp y)
                (ichareqv (double-rewrite a) (car y))
                (icharlisteqv (double-rewrite x) (cdr y)))))

  (defthm icharlisteqv-when-not-same-lens
    (implies (not (equal (len x) (len y)))
             (not (icharlisteqv x y)))))


(define istreqv ((x :type string)
                 (y :type string))
  :returns bool
  :parents (equivalences cases)
  :short "Case-insensitive string equivalence test."

  :long "<p>@(call istreqv) determines if @('x') and @('y') are
case-insensitively equivalent strings.  That is, @('x') and @('y') must have
the same length and their elements must be @(see ichareqv) to one another.</p>

<p>Logically this is identical to</p>

@({
 (icharlisteqv (explode x) (explode y))
})

<p>But we use a more efficient implementation which avoids coercing the
strings into lists.</p>

<p>NOTE: for reasoning, we leave this function enabled and prefer to work with
@(see icharlisteqv) of the coerces as our normal form.</p>"
  :inline t
  :enabled t

  (mbe :logic
       (icharlisteqv (explode x) (explode y))
       :exec
       (b* (((the (integer 0 *) xl) (length x))
            ((the (integer 0 *) yl) (length y)))
         (and (eql xl yl)
              (istreqv-aux x y 0 xl))))

  :prepwork
  ((defund istreqv-aux (x y n l)
     (declare (type string x)
              (type string y)
              (type (integer 0 *) n)
              (type (integer 0 *) l)
              (xargs :guard (and (natp n)
                                 (natp l)
                                 (equal (length x) l)
                                 (equal (length y) l)
                                 (<= n l))
                     :measure (nfix (- (nfix l) (nfix n)))
                     :guard-hints (("Goal" :in-theory (enable ichareqv)))))
     (mbe :logic
          (if (zp (- (nfix l) (nfix n)))
              t
            (and (ichareqv (char x n) (char y n))
                 (istreqv-aux x y (+ (nfix n) 1) l)))
          :exec
          (if (eql n l)
              t
            (and (ichareqv (the character (char x n))
                           (the character (char y n)))
                 (istreqv-aux x y
                              (the (integer 0 *) (+ 1 n))
                              l)))))

   (local (defthm lemma
            (implies (and (< n (len x))
                          (not (ichareqv (nth n x) (nth n y))))
                     (not (icharlisteqv (nthcdr n x) (nthcdr n y))))))

   (local (defthm lemma2
            (implies (and (< n (len x))
                          (equal (len x) (len y))
                          (ichareqv (nth n x) (nth n y)))
                     (equal (icharlisteqv (nthcdr n x) (nthcdr n y))
                            (icharlisteqv (cdr (nthcdr n x)) (cdr (nthcdr n y)))))))

   (defthm istreqv-aux-removal
     (implies (and (stringp x)
                   (stringp y)
                   (natp n)
                   (<= n l)
                   (= l (length x))
                   (= l (length y)))
              (equal (istreqv-aux x y n l)
                     (icharlisteqv (nthcdr n (explode x))
                                   (nthcdr n (explode y)))))
     :hints(("Goal"
             :in-theory (enable istreqv-aux)
             :induct (istreqv-aux x y n l)))))

  ///
  (defequiv istreqv)
  (defrefinement streqv istreqv)

  (defcong istreqv ichareqv (char x n) 1)
  (defcong istreqv icharlisteqv (explode x) 1)
  (defcong istreqv istreqv (string-append x y) 1)
  (defcong istreqv istreqv (string-append x y) 2))


