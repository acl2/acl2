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
(include-book "centaur/bitops/portcullis" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/util/defval" :dir :system)
(local (include-book "std/testing/assert-bang" :dir :system))
(local (std::add-default-post-define-hook :fix))

(defsection vl-linecol
  :parents (vl-location)
  :short "Packed representation of a line number and column number."
  :long "<p>Semantically a @('vl-linecol') is nothing more than a product type
whose fields are a line number and a column number.  The line number is a @(see
posp) and the column number is a @(see natp).  We provide the usual @(see
defprod) style interface for accessing this kind of structure.</p>

<p>For efficiency, we pack line/column numbers together into a single integer,
which saves one cons per location.  This can save a lot of memory when
processing large files.</p>"
  :autodoc nil

  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

  (local (defthmd l0
           (implies (and (unsigned-byte-p 30 line)
                         (unsigned-byte-p 22 col))
                    (unsigned-byte-p 52 (logior col (ash line 22))))))

  (local (defthm l1
           (implies (and (unsigned-byte-p 30 line)
                         (unsigned-byte-p 22 col))
                    (< (logior col (ash line 22))
                       4503599627370496))
           :hints(("goal"
                   :in-theory (disable bitops::unsigned-byte-p-of-logior
                                       bitops::unsigned-byte-p-of-ash)
                   :use ((:instance l0))))))

  (define vl-linecol-p (x)
    :parents (vl-linecol)
    :short "Recognizer for @(see vl-linecol) structures."
    (if (integerp x)
        ;; [LINE : 30 bits, COL : 22 bits]
        (and (<= 0 x)
             (< 0 (ash x -22)) ;; "posp of line"
             (< x (expt 2 52)))
      ;; (LINE . COL) in case they somehow don't fit.
      (and (consp x)
           (posp (car x))
           (natp (cdr x))
           ;; Something must be too big, or we should use the packed representation.
           (or (<= (expt 2 30) (car x))
               (<= (expt 2 22) (cdr x))))))

  (local (in-theory (enable vl-linecol-p)))

  (define vl-linecol-fix ((x vl-linecol-p))
    :returns (x-fix vl-linecol-p)
    :parents (vl-linecol)
    :short "Fixing function for @(see vl-linecol) structures."
    :inline t
    (mbe :logic (if (vl-linecol-p x)
                    x
                  (ash 1 22))
         :exec x)
    ///
    (defthm vl-linecol-fix-when-vl-linecol-p
      (implies (vl-linecol-p x)
               (equal (vl-linecol-fix x)
                      x))))

  (local (in-theory (enable vl-linecol-fix)))

  (define vl-linecol ((line posp)
                      (col  natp))
    :returns (linecol vl-linecol-p)
    :parents nil
    :inline t ;; should only really be called from vl-location
    (b* ((line (mbe :logic (pos-fix line) :exec line))
         (col  (lnfix col))
         ((when (and (< (the (integer 0 *) line) (expt 2 30))
                     (< (the (integer 0 *) col)  (expt 2 22))))
          ;; Usual case: things are small enough to be packed up nicely
          (the (unsigned-byte 52)
               (logior (the (unsigned-byte 52) (ash (the (unsigned-byte 30) line) 22))
                       (the (unsigned-byte 22) col)))))
      ;; Degenerate case: something too big, just make a cons structure
      (cons line col)))

  (local (in-theory (enable vl-linecol)))

  (define vl-linecol->line ((x vl-linecol-p))
    :parents (vl-linecol)
    :returns (line posp :rule-classes :type-prescription)
    :inline t
    (b* ((x (vl-linecol-fix x))
         ((when (consp x))
          (car x)))
      (the (unsigned-byte 30)
           (ash (the (unsigned-byte 52) x) -22)))
    ///
    (defthm vl-linecol->line-of-vl-linecol
      (equal (vl-linecol->line (vl-linecol line col))
             (pos-fix line))
      :hints((acl2::equal-by-logbitp-hammer))))

  (define vl-linecol->col ((x vl-linecol-p))
    :parents (vl-linecol)
    :returns (col natp :rule-classes :type-prescription)
    :inline t
    (b* ((x (vl-linecol-fix x))
         ((when (consp x))
          (cdr x)))
      (logand (the (unsigned-byte 52) x) (1- (expt 2 22))))
    ///
    (defthm vl-linecol->col-of-vl-linecol
      (equal (vl-linecol->col (vl-linecol line col))
             (nfix col))
      :hints((acl2::equal-by-logbitp-hammer))))

  (local (defthm xx1
           (implies (and (< x (expt 2 52))
                         (natp x))
                    (< (acl2::logtail 22 x) (expt 2 30)))
           :rule-classes :linear
           :hints(("Goal"
                   :in-theory (disable bitops::unsigned-byte-p-of-logtail)
                   :use ((:instance bitops::unsigned-byte-p-of-logtail
                          (acl2::size 22)
                          (acl2::size1 30)
                          (acl2::i x)
                          ))))))

  (local (defthm xx2
           (implies (and (< x (expt 2 52))
                         (natp x))
                    (< (acl2::loghead 22 x) (expt 2 22)))
           :rule-classes :linear
           :hints(("Goal"
                   :in-theory (disable bitops::unsigned-byte-p-of-loghead)
                   :use ((:instance bitops::unsigned-byte-p-of-loghead
                          (acl2::size 22)
                          (acl2::size1 22)
                          (acl2::i x)
                          ))))))

  (defthm vl-linecol-of-fields
    (equal (vl-linecol (vl-linecol->line x)
                       (vl-linecol->col x))
           (vl-linecol-fix x))
    :hints (("goal" :in-theory (enable vl-linecol->line vl-linecol->col))
            (acl2::equal-by-logbitp-hammer)))

  (local (in-theory (disable vl-linecol-p vl-linecol vl-linecol-fix)))

  (deffixtype vl-linecol
    :pred vl-linecol-p
    :fix  vl-linecol-fix
    :equiv vl-linecol-equiv
    :define t
    :forward t)

  (local (in-theory (enable vl-linecol->line
                            vl-linecol->col)))

  (deffixequiv vl-linecol->line)
  (deffixequiv vl-linecol->col)

  (make-event
   ;; Emulate defaggregate stuff
   (let ((name 'vl-linecol)
         (fields '(line col)))
     `(progn
        ,(std::da-make-maker name fields nil)
        ,(std::da-make-changer name fields nil)
        ,(std::da-make-binder name fields))))

  ;; Rudimentary testing of defaggregate stuff
  (local
   (progn
     (assert! (b* ((lc (make-vl-linecol :line 5 :col 17))
                   ((vl-linecol lc) lc))
                (and (equal lc.line 5)
                     (equal lc.col 17))))
     (assert! (b* ((lc (make-vl-linecol :line 99 :col 100))
                   (lc (change-vl-linecol lc :line 199))
                   ((vl-linecol lc) lc))
                (and (equal lc.line 199)
                     (equal lc.col 100)))))))


(defsection vl-location
  :parents (extended-characters)
  :short "Representation of a point in a source file."
  :long "<p>A @('vl-location') structure represents some location in a source
code file.  These locations are attached to characters and module items to
provide context during error reporting.</p>

<p>Historically, @('vl-location') was an ordinary, tagged @(see defprod) with
three fields: a filename, line number, and column number.  Because there are
many locations, this representation used a lot of memory.</p>

<p>We now instead represent locations using a custom structure, essentially of
the form:</p>

@({    (linecol . (:vl-location . filename))   })

<p>Where the line and column number typically are only a single fixnum; see
@(see vl-linecol).  It looks like this takes 2 conses, but we @(see hons) the
@('(:vl-location . filename)') pair so that we only need one such cons per
file.  So for all practical purposes, each @('vl-location') really only costs
us a single cons.</p>

<p>Despite this fancy representation, the interface to locations still acts as
though it is a @(see defprod) with just a filename, line, and column number.
You can use the ordinary @(see b*) binders and make/change macros to access and
create locations, as you would expect.</p>

<p>A downside of this representation is that @('vl-location') structures are no
longer very readable when you encounter them in traces, etc.  However, the
@(':vl-location') tag is still there, which allows @(see vl-fmt) to understand
when it has encountered a location, and to print these locations in a readable
way.</p>"

  :autodoc nil

  (define vl-location-p (x)
    :parents (vl-location)
    :short "Recognizer for @(see vl-location) structures."
    :inline t
    (and (consp x)
         (consp (cdr x))
         (eq (cadr x) :vl-location)
         (vl-linecol-p (car x))
         (stringp (cddr x)))
    ///
    (defthm consp-when-vl-location-p
      (implies (vl-location-p x)
               (consp x))
      :rule-classes :compound-recognizer))

  (local (in-theory (enable vl-location-p)))

  (define vl-location ((filename stringp)
                       (line posp)
                       (col natp))
    :returns (loc vl-location-p)
    (b* ((line (mbe :logic (pos-fix line) :exec line))
         (col  (lnfix col))
         (filename (mbe :logic (str-fix filename) :exec filename)))
      (cons (vl-linecol line col)
            (hons :vl-location filename))))

  (local (in-theory (enable vl-location)))

  (define vl-location-fix ((x vl-location-p))
    :parents (vl-location)
    :short "Fixing function for @(see vl-location) structures."
    :returns (loc vl-location-p)
    :inline t
    (mbe :logic (if (vl-location-p x)
                    x
                  (vl-location "" 1 0))
         :exec x)
    ///
    (defthm vl-location-fix-when-vl-location-p
      (implies (vl-location-p x)
               (equal (vl-location-fix x)
                      x))))

  (local (in-theory (enable vl-location-fix)))

  (define vl-location->filename ((x vl-location-p))
    :returns (filename stringp :rule-classes :type-prescription)
    :parents (vl-location)
    :short "Get the filename from a @(see vl-location)."
    :inline t
    (cddr (vl-location-fix x))
    ///
    (defthm vl-location->filename-of-vl-location
      (equal (vl-location->filename (vl-location filename line col))
             (str-fix filename))))

  (define vl-location->line ((x vl-location-p))
    :returns (line posp :rule-classes :type-prescription)
    :parents (vl-location)
    :short "Get the line number from a @(see vl-location)."
    :inline t
    (vl-linecol->line (car (vl-location-fix x)))
    ///
    (defthm vl-location->line-of-vl-location
      (equal (vl-location->line (vl-location filename line col))
             (pos-fix line))))

  (define vl-location->col ((x vl-location-p))
    :returns (col natp :rule-classes :type-prescription)
    :parents (vl-location)
    :short "Get the column number from a @(see vl-location)."
    :inline t
    (vl-linecol->col (car (vl-location-fix x)))
    ///
    (defthm vl-location->col-of-vl-location
      (equal (vl-location->col (vl-location filename line col))
             (nfix col))))

  (defthm vl-location-of-fields
    (equal (vl-location (vl-location->filename x)
                        (vl-location->line x)
                        (vl-location->col x))
           (vl-location-fix x))
    :hints (("goal" :in-theory (enable vl-location->filename
                                       vl-location->line
                                       vl-location->col))))

  (local (in-theory (disable vl-location-p vl-location vl-location-fix)))

  (deffixtype vl-location
    :pred vl-location-p
    :fix  vl-location-fix
    :equiv vl-location-equiv
    :define t
    :forward t)

  (local (in-theory (enable vl-location->filename
                            vl-location->line
                            vl-location->col)))

  (deffixequiv vl-location->filename)
  (deffixequiv vl-location->line)
  (deffixequiv vl-location->col)

  (make-event
   ;; Emulate defaggregate stuff
   (let ((name 'vl-location)
         (fields '(filename line col)))
     `(progn
        ,(std::da-make-maker name fields nil)
        ,(std::da-make-changer name fields nil)
        ,(std::da-make-binder name fields))))

  ;; Rudimentary testing of defaggregate stuff
  (local
   (progn
     (assert! (b* ((loc (make-vl-location :filename "foo" :line 5 :col 17))
                   ((vl-location loc) loc))
                (and (equal loc.filename "foo")
                     (equal loc.line 5)
                     (equal loc.col 17))))
     (assert! (b* ((loc (make-vl-location :filename "blah" :line 99 :col 100))
                   (loc (change-vl-location loc :line 199 :filename "mess"))
                   ((vl-location loc) loc))
                (and (equal loc.filename "mess")
                     (equal loc.line 199)
                     (equal loc.col 100)))))))

(defval *vl-fakeloc*
  :parents (vl-location)
  :short "A \"fake\" @(see vl-location-p) which we use when generating our
own @(see extended-characters) and module items."

  (vl-location "[[[ fake location ]]]" 1 0))

(fty::deflist vl-locationlist
  :elt-type vl-location
  :parents (vl-location))


(define vl-location-string ((loc vl-location-p))
  :parents (vl-location)
  :short "Convert an @(see vl-location-p) into a string."
  :long "<p>@(call vl-location-string) is often useful in generating warning
or error messages.  It converts a @(see vl-location-p) object into a string
of the form <i>filename:line:col</i>.</p>"
  :returns (str stringp :rule-classes :type-prescription)
  (cat (vl-location->filename loc)
       ":"
       (natstr (vl-location->line loc))
       ":"
       (natstr (vl-location->col loc))))


(define vl-location-between-p ((x vl-location-p)
                               (min vl-location-p)
                               (max vl-location-p))
  :parents (vl-location)
  :short "@(call vl-location-between-p) is true exactly when @('x') is in the
same file as @('min') and @('max'), and inclusively falls between these
bounds."

  (b* (((vl-location x) x)
       ((vl-location low) min) ;; bozo awful symbol problems with min/max
       ((vl-location high) max))

      (and (equal x.filename low.filename)
           (equal x.filename high.filename)

           (or (< low.line x.line)
               (and (eql low.line x.line)
                    (<= low.col x.col)))

           (or (< x.line high.line)
               (and (eql x.line high.line)
                    (<= x.col high.col))))))
