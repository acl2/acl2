; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "defs")
(include-book "unicode/take" :dir :system)
(include-book "make-event/assert" :dir :system)
(local (include-book "arithmetic"))



(defxdoc extended-characters
  :parents (loader)
  :short "Characters with additional annotations."
  :long "<p>Our lexer (and preprocessor) operate on lists of \"extended
characters\", which associate regular characterp objects with their origin in
the Verilog source code.</p>")



(defaggregate vl-location
  (filename line col)
  :tag :vl-location
  :legiblep nil
  :require ((stringp-of-vl-location->filename (stringp filename))
            (posp-of-vl-location->line        (posp line))
            (natp-of-vl-location->col         (natp col)))
  :parents (extended-characters)
  :short "Representation of a point in a source file."
  :long "<p>Each vl-location-p represents some location in a source code file.
These locations are attached to characters and module items to provide context
during error reporting.</p>")

(defthm stringp-of-vl-location->line-tp
  (implies (force (vl-location-p x))
           (stringp (vl-location->filename x)))
  :rule-classes :type-prescription)

(defthm posp-of-vl-location->line-tp
  (implies (force (vl-location-p x))
           (posp (vl-location->line x)))
  :rule-classes :type-prescription)

(defthm natp-of-vl-location->col-tp
  (implies (force (vl-location-p x))
           (natp (vl-location->line x)))
  :rule-classes :type-prescription)



(defsection *vl-fakeloc*
  :parents (vl-location)
  :short "A \"fake\" @(see vl-location-p) which we use when generating our
own @(see extended-characters) and module items."

  (defconst *vl-fakeloc*
    (vl-location "[[[ fake location ]]]" 1 0)))




(defsection vl-location-string
  :parents (vl-location)
  :short "Convert an @(see vl-location-p) into a string."
  :long "<p>@(call vl-location-string) is often useful in generating warning
or error messages.  It converts a @(see vl-location-p) object into a string
of the form <i>filename:line:col</i>.</p>"

  (defund vl-location-string (loc)
    (declare (xargs :guard (vl-location-p loc)))
    (str::cat (vl-location->filename loc)
              ":"
              (str::natstr (vl-location->line loc))
              ":"
              (str::natstr (vl-location->col loc))))

  (defthm stringp-of-vl-location-string
    (stringp (vl-location-string loc))
    :rule-classes :type-prescription))


(defsection vl-location-between-p
  :parents (vl-location)
  :short "@(call vl-location-between-p) is true exactly when <tt>x</tt> is in
the same file as <tt>min</tt> and <tt>max</tt>, and inclusively falls between
these bounds."

  (defund vl-location-between-p (x min max)
    (declare (xargs :guard (and (vl-location-p x)
                                (vl-location-p min)
                                (vl-location-p max))))

; Is the location X in the same file as MIN and MAX, and does it, inclusively,
; fall within these bounds?

    (let ((x-filename   (vl-location->filename x))
          (x-line       (vl-location->line x))
          (x-col        (vl-location->col x))

          (min-filename (vl-location->filename min))
          (min-line     (vl-location->line min))
          (min-col      (vl-location->col min))

          (max-filename (vl-location->filename max))
          (max-line     (vl-location->line max))
          (max-col      (vl-location->col max)))

      (and (equal x-filename min-filename)
           (equal x-filename max-filename)

           (or (< min-line x-line)
               (and (= min-line x-line)
                    (<= min-col x-col)))

           (or (< x-line max-line)
               (and (= x-line max-line)
                    (<= x-col max-col)))))))



(defaggregate vl-echar
  (char loc)
  :tag :vl-echar
  :legiblep nil
  :require ((characterp-of-vl-echar->char      (characterp char))
            (vl-location-p-of-vl-echar->loc    (vl-location-p loc)))
  :parents (extended-characters)
  :short "An annotated character."
  :long "<p>Each <tt>vl-echar-p</tt> associates its <tt>char</tt> with a @(see
vl-location-p) that says where the character was read from.</p>")



; Once upon a time we took special measures to print warnings if this function
; was given long lists, because this was useful in debugging some performance
; problems related to the execution of guards.  But we no longer think this is
; necessary, and so we return to the simple definition.

(deflist vl-echarlist-p (x)
  (vl-echar-p x)
  :elementp-of-nil nil
  :parents (extended-characters))

(defsection vl-echarlist->chars

  (defprojection vl-echarlist->chars (x)
    (vl-echar->char x)
    :guard (vl-echarlist-p x)
    :nil-preservingp t
    :result-type character-listp
    :parents (extended-characters))

; Not sure why I wanted this other form.
  (defthm vl-echarlist->chars-of-simpler-take
    (equal (vl-echarlist->chars (simpler-take n x))
           (simpler-take n (vl-echarlist->chars x))))

  (in-theory (disable simpler-take-of-vl-echarlist->chars))
  (theory-invariant (incompatible (:rewrite simpler-take-of-vl-echarlist->chars)
                                  (:rewrite vl-echarlist->chars-of-simpler-take))))



(defsection vl-echarlist->string
  :parents (extended-characters)
  :short "Transform a @(see vl-echarlist-p) to a string."

  :long "<p>Logically, this function just runs @(see vl-echarlist->chars) and
coerces the result to a string; we typically leave it enabled.</p>

<p>Under the hood, in Common Lisp, we install a faster definition that avoids
creating an intermediate list and instead just builds a string directly.  This
notably saves a lot of memory when we build @(see vl-filemap-p)s.</p>"

  (defun vl-echarlist->string (x)
    (declare (xargs :guard (vl-echarlist-p x)))
    (coerce (vl-echarlist->chars x) 'string))

  (defttag vl-optimize)
  (acl2::progn!
   (set-raw-mode t)

   (declaim (inline vl-echarlist->string))
   (defun vl-echarlist->string (x)
     (let ((len (len x)))
       (cond ((equal len 0)
              "")
             (t
              (let ((ret (make-string len))
                    (last (- len 1)))
                (loop for i from 0 to last
                      do
                      (setf (char ret i) (vl-echar->char (car x)))
                      (setq x (cdr x)))
                ret))))))
  (defttag nil))




(defsection vl-change-echarlist-locations
  :parents (extended-characters)
  :short "Override the locations of characters."
  :long "<p>@(call vl-change-echarlist-locations) is given a list of extended
characters, <tt>x</tt>, and a location, <tt>loc</tt>.  It changes the location
of every character in <tt>x</tt> to <tt>loc</tt>.</p>

<p>This funny operation is used in the preprocessor to make <tt>`define</tt>
handling more sensible.</p>"

  (defund vl-change-echarlist-locations (x loc)
    (declare (xargs :guard (and (vl-echarlist-p x)
                                (vl-location-p loc))))
    (if (consp x)
        (cons (change-vl-echar (car x) :loc loc)
              (vl-change-echarlist-locations (cdr x) loc))
      nil))

  (local (in-theory (enable vl-change-echarlist-locations)))

  (defthm vl-echarlist-p-of-vl-change-echarlist-locations
    (implies (and (force (vl-echarlist-p x))
                  (force (vl-location-p loc)))
             (vl-echarlist-p (vl-change-echarlist-locations x loc)))))




(defsection vl-echarlist-from-chars
  :parents (extended-characters)
  :short "Transform an ordinary character list into a @(see vl-echarlist-p)."

  :long "<p><tt>vl-echarlist-from-chars</tt> transforms a character list into
an extended character list.  It properly handles the incrementing of line and
column numbers, but note that it assigns every character the same source type.</p>

<p>We implement <tt>vl-echarlist-from-chars</tt> as a macro wrapper for the
function @(srclink vl-echarlist-from-chars-aux).</p>

<p>@(call vl-echarlist-from-chars)</p>

<ul>
<li><tt>x</tt> is the list of characters to convert.</li>
<li><tt>filename</tt> will be used as the filename for every character.</li>
<li><tt>line</tt> is the starting line.</li>
<li><tt>col</tt> is the starting column.</li>
</ul>

<p>Note that we actually optimize this function using <tt>nreverse</tt> for
better performance.</p>"

  (defund vl-echarlist-from-chars-aux (x filename line col acc)
    (declare (xargs :guard (and (character-listp x)
                                (stringp filename)
                                (posp line)
                                (natp col)
                                (vl-echarlist-p acc))))

; At one point I considered a fixnum-optimized version of this function, to
; avoid the arbitrary-precision calls of +.  In CCL, there was virtually no
; performance difference between the two versions, and, furthermore, if you
; have to call (length x) in the wrapper to determine if it's safe to use the
; fixnum version, it ends up being slower on a medium-size example.  So, now I
; am not bothering to do any kind of fixnum nonsense.

  (if (consp x)
      (vl-echarlist-from-chars-aux
       (cdr x)
       filename
       (if (eql (car x) #\Newline) (+ 1 line) line)
       (if (eql (car x) #\Newline) 0 (+ 1 col))
       (cons (make-vl-echar :char (car x)
                            :loc (vl-location filename line col))
             acc))
    acc))

  (local (in-theory (enable vl-echarlist-from-chars-aux)))

  (defthm true-listp-of-vl-echarlist-from-chars-aux
    (equal (true-listp (vl-echarlist-from-chars-aux x filename line col acc))
           (true-listp acc)))

  (defund vl-echarlist-from-chars-fn (x filename line col)
    (declare (xargs :guard (and (character-listp x)
                                (stringp filename)
                                (posp line)
                                (natp col))
                    :verify-guards nil))
    (mbe :logic (if (atom x)
                    nil
                  (cons (make-vl-echar :char (car x)
                                       :loc (vl-location filename line col))
                        (vl-echarlist-from-chars-fn
                         (cdr x) filename
                         (if (eql (car x) #\Newline) (+ 1 line) line)
                         (if (eql (car x) #\Newline) 0 (+ 1 col)))))
         :exec (reverse (vl-echarlist-from-chars-aux x filename line col nil))))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-echarlist-from-chars-aux ACL2::*never-profile-ht*) t)
   (defun vl-echarlist-from-chars-fn (x filename line col)
     (ACL2::nreverse (vl-echarlist-from-chars-aux x filename line col nil))))
  (defttag nil)

  (defthm true-listp-of-vl-echarlist-from-chars-fn
    (true-listp (vl-echarlist-from-chars-fn x filename line col))
    :rule-classes :type-prescription)

  (local (in-theory (enable vl-echarlist-from-chars-fn)))

  (defthm vl-echarlist->chars-of-vl-echarlist-from-chars-fn
    (equal (vl-echarlist->chars (vl-echarlist-from-chars-fn x filename line col))
           (list-fix x)))

  (defthm vl-echarlist-p-of-vl-echarlist-from-chars-fn
    (implies (and (force (character-listp x))
                  (force (stringp filename))
                  (force (posp line))
                  (force (natp col)))
             (vl-echarlist-p (vl-echarlist-from-chars-fn x filename line col))))

  (defthm vl-echarlist-from-chars-aux-removal
    (implies (force (true-listp acc))
             (equal (vl-echarlist-from-chars-aux x filename line col acc)
                    (revappend (vl-echarlist-from-chars-fn x filename line col)
                               acc))))

  (verify-guards vl-echarlist-from-chars-fn)

  (defmacro vl-echarlist-from-chars (x &key
                                       (filename '"[internal character list]")
                                       (line '1)
                                       (col '0))
    `(vl-echarlist-from-chars-fn ,x ,filename ,line ,col))

  (add-macro-alias vl-echarlist-from-chars vl-echarlist-from-chars-fn))




(defsection vl-echarlist-from-str
  :parents (extended-characters)
  :short "Transform an ordinary <tt>stringp</tt> into a @(see vl-echarlist-p)."

  :long "<p><tt>vl-echarlist-from-str</tt> is like @(see
vl-echarlist-from-chars), but operates on an ACL2 string instead of a character
list.</p>

@(call vl-echarlist-from-str)

<p>We go to some lengths to be able to more efficiently construct an echarlist
from a string.  The simplest approach to this would be:</p>

<ol>
 <li>coerce the string into a list</li>
 <li>call vl-echarlist-from-chars on the resulting list</li>
</ol>

<p>The above is our logical definition, and hence we leave this function enabled
and reason about @(see vl-echarlist-from-chars) instead.</p>

<p>For better efficiency, we avoid the coerce and process the string directly.
Also note that we actually use <tt>nreverse</tt> here.</p>"

  (defund vl-echarlist-from-str-aux (x n xl filename line col acc)
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (equal xl (length x))
                                (<= n xl)
                                (stringp filename)
                                (posp line)
                                (natp col)
                                (vl-echarlist-p acc))
                    :measure (nfix (- (nfix xl) (nfix n))))
             (type string x filename)
             (type integer n xl line col))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (= n xl))
        acc
      (let ((char (char (the string x) n)))
        (vl-echarlist-from-str-aux (the string x)
                                   (mbe :logic (+ 1 (nfix n)) :exec (+ 1 n))
                                   xl
                                   filename
                                   (if (eql char #\Newline) (+ 1 line) line)
                                   (if (eql char #\Newline) 0 (+ 1 col))
                                   (cons (make-vl-echar :char char
                                                        :loc (vl-location filename line col))
                                         acc)))))

  (defthm true-listp-of-vl-echarlist-from-str-aux
    (equal (true-listp (vl-echarlist-from-str-aux x n xl filename line col acc))
           (true-listp acc))
    :hints(("Goal" :in-theory (enable vl-echarlist-from-str-aux))))

  (defund vl-echarlist-from-str-nice (x n xl filename line col)
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (equal xl (length x))
                                (<= n xl)
                                (stringp filename)
                                (posp line)
                                (natp col))
                    :measure (nfix (- (nfix xl) (nfix n)))
                    :verify-guards nil)
             (type string x filename)
             (type integer n xl line col))
    (mbe :logic (if (zp (- (nfix xl) (nfix n)))
                    nil
                  (let ((char (char x n)))
                    (cons (make-vl-echar :char char
                                         :loc (vl-location filename line col))
                          (vl-echarlist-from-str-nice
                           x (+ 1 (nfix n)) xl filename
                           (if (eql char #\Newline) (+ 1 line) line)
                           (if (eql char #\Newline) 0 (+ 1 col))))))
         :exec (reverse (vl-echarlist-from-str-aux x n xl filename line col nil))))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-echarlist-from-str-aux ACL2::*never-profile-ht*) t)
   (defun vl-echarlist-from-str-nice (x n xl filename line col)
     (ACL2::nreverse (vl-echarlist-from-str-aux x n xl filename line col nil))))
  (defttag nil)

  (defthm vl-echarlist-from-str-aux-correct
    (implies (true-listp acc)
             (equal (vl-echarlist-from-str-aux x n xl filename line col acc)
                    (revappend (vl-echarlist-from-str-nice x n xl filename line col)
                               acc)))
    :hints(("Goal"
            :in-theory (enable vl-echarlist-from-str-aux
                               vl-echarlist-from-str-nice)
            :induct (vl-echarlist-from-str-aux x n xl filename line col acc))))

  (verify-guards vl-echarlist-from-str-nice
    :hints(("Goal" :in-theory (enable vl-echarlist-from-str-nice))))

  (defthm vl-echarlist-from-str-nice-correct
    (implies (force (stringp x))
             (equal (vl-echarlist-from-str-nice x n (len (coerce x 'list))
                                                filename line col)
                    (vl-echarlist-from-chars-fn (nthcdr n (coerce x 'list))
                                                filename line col)))
    :hints(("Goal" :in-theory (enable vl-echarlist-from-str-nice
                                      vl-echarlist-from-chars-fn))))

  (defun vl-echarlist-from-str-fn (x filename line col)
    (declare (xargs :guard (and (stringp x)
                                (stringp filename)
                                (posp line)
                                (natp col)))
             (type string x filename)
             (type integer line col))
    (mbe :logic (vl-echarlist-from-chars-fn (coerce x 'list) filename line col)
         :exec (vl-echarlist-from-str-nice x 0 (length (the string x))
                                           filename line col)))

  (defmacro vl-echarlist-from-str (x &key
                                     (filename '"[internal string]")
                                     (line '1)
                                     (col '0))
    `(vl-echarlist-from-str-fn ,x ,filename ,line ,col)))




(defsection vl-echar-digit-value
  :parents (extended-characters)
  :short "@(call vl-echar-digit-value) interprets the extended character
<tt>x</tt> as a base-<tt>radix</tt> digit, or returns <tt>nil</tt> if
<tt>x</tt> is not a valid digit in this base."

  (defund vl-echar-digit-value (x radix)
    (declare (xargs :guard (and (vl-echar-p x)
                                (integerp radix)
                                (<= 2 radix)
                                (<= radix 36))))
    (digit-char-p (vl-echar->char x) radix))

  (local (in-theory (enable vl-echar-digit-value)))

  (defthm natp-of-vl-echar-digit-value
    (implies (vl-echar-digit-value x radix)
             (and (natp (vl-echar-digit-value x radix))
                  (integerp (vl-echar-digit-value x radix))
                  (<= 0 (vl-echar-digit-value x radix))))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary (or (not (vl-echar-digit-value x radix))
                                   (and (integerp (vl-echar-digit-value x radix))
                                        (<= 0 (vl-echar-digit-value x radix))))))))



(defsection vl-echarlist-unsigned-value
  :parents (extended-characters)
  :short "@(call vl-echarlist-unsigned-value) interprets the extended
character list <tt>x</tt> as a base-<tt>radix</tt> number, or returns
<tt>nil</tt> if <tt>x</tt> is invalid."

  (defund vl-echarlist-unsigned-value-aux (x radix n)
    (declare (xargs :guard (and (vl-echarlist-p x)
                                (integerp radix)
                                (<= 2 radix)
                                (<= radix 36)
                                (equal n (len x)))))
    (if (consp x)
        (let ((car-digit (vl-echar-digit-value (car x) radix)))
          (if (not car-digit)
              nil
            (let ((cdr-value (vl-echarlist-unsigned-value-aux (cdr x) radix (1- n))))
              (if (not cdr-value)
                  nil
                (+ (* (expt radix (1- n)) car-digit)
                   cdr-value)))))
      0))

  (defund vl-echarlist-unsigned-value (x radix)
    ;; We see if X is made up entirely of base RADIX digits.  If so, we return
    ;; the number represented by X, treating the digits as if they are written
    ;; with the most significant digit first.  For instance, an echarlist whose
    ;; string is "987" has, in base 10, an unsigned-value of 987.  Otherwise,
    ;; if there are any invalid digits, we return NIL.
    (declare (xargs :guard (and (vl-echarlist-p x)
                                (integerp radix)
                                (<= 2 radix)
                                (<= radix 36))))
    (if (not (consp x))
        nil
      (vl-echarlist-unsigned-value-aux x (nfix radix) (len x))))

  (local (in-theory (enable vl-echarlist-unsigned-value)))

  (encapsulate
   ()
   (local (defthm lemma
            (implies (and (integerp radix)
                          (<= 0 radix)
                          (equal n (len x))
                          (vl-echarlist-unsigned-value-aux x radix n))
                     (natp (vl-echarlist-unsigned-value-aux x radix n)))
            :hints(("Goal" :in-theory (enable vl-echarlist-unsigned-value-aux)))))

   (defthm natp-of-vl-echarlist-unsigned-value-aux
     (implies (vl-echarlist-unsigned-value x radix)
              (and (natp (vl-echarlist-unsigned-value x radix))
                   (integerp (vl-echarlist-unsigned-value x radix))
                   (<= 0 (vl-echarlist-unsigned-value x radix))))
     :rule-classes ((:rewrite)
                    (:type-prescription
                     :corollary (or (not (vl-echarlist-unsigned-value x radix))
                                    (and (integerp (vl-echarlist-unsigned-value x radix))
                                         (<= 0 (vl-echarlist-unsigned-value x radix))))))))

  (defthm vl-echarlist-unsigned-value-when-not-consp
    (implies (not (consp x))
             (equal (vl-echarlist-unsigned-value x radix)
                    nil)))

  (defthm type-of-vl-echarlist-unsigned-value
    (or (not (vl-echarlist-unsigned-value x radix))
        (natp (vl-echarlist-unsigned-value x radix)))
    :rule-classes :type-prescription)

  ;; Some unit tests to make sure the damn thing works right.
  (assert! (not (vl-echarlist-unsigned-value (vl-echarlist-from-str "") 10)))
  (assert! (not (vl-echarlist-unsigned-value (vl-echarlist-from-str "Hello") 10)))

  (assert! (equal 0 (vl-echarlist-unsigned-value (vl-echarlist-from-str "0") 10)))
  (assert! (equal 0 (vl-echarlist-unsigned-value (vl-echarlist-from-str "0") 13)))
  (assert! (equal 0 (vl-echarlist-unsigned-value (vl-echarlist-from-str "000") 2)))
  (assert! (equal 0 (vl-echarlist-unsigned-value (vl-echarlist-from-str "00000") 16)))

  (assert! (equal 12345 (vl-echarlist-unsigned-value (vl-echarlist-from-str "12345") 10)))
  (assert! (equal #o12345 (vl-echarlist-unsigned-value (vl-echarlist-from-str "12345") 8)))
  (assert! (equal #x12345 (vl-echarlist-unsigned-value (vl-echarlist-from-str "12345") 16)))

  (assert! (equal #b010101 (vl-echarlist-unsigned-value (vl-echarlist-from-str "010101") 2)))
  (assert! (equal #o010101 (vl-echarlist-unsigned-value (vl-echarlist-from-str "010101") 8)))
  (assert! (equal 010101 (vl-echarlist-unsigned-value (vl-echarlist-from-str "010101") 10)))
  (assert! (equal #x010101 (vl-echarlist-unsigned-value (vl-echarlist-from-str "010101") 16))))





;; Dumb unit checks to make sure vl-echarlist->string seems to be working
;; right.

(assert! (equal (vl-echarlist->string (vl-echarlist-from-str "")) ""))
(assert! (equal (vl-echarlist->string (vl-echarlist-from-str "foo")) "foo"))


#||

(defparameter *foo*
  (vl::vl-echarlist-from-str
   "this is a relatively small string for trying out vl-echarlist->string."))

;; Without vl-echarlist->string optimization,  2.09 seconds, 1.408 GB allocated
;; With optimization, 1.49 seconds, 288 MB allocatd.

(progn (gc$)
       (time$ (loop for i from 1 to 1000000 do
                    (vl::vl-echarlist->string *foo*))))

||#
