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
(include-book "../util/defs")
(include-book "../util/echars")
(local (include-book "../util/arithmetic"))

(fty::defalist vl-filemap
  :key-type stringp
  :val-type stringp
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :parents (vl-load)
  :short "Mapping of source files to their contents."

  :long "<p>It is occasionally useful to gain direct access to the source text,
even before preprocessing has occurred.  Our file loading functions, such as
@(see vl-load), can optionally produce a <b>file map</b>, which is an alist
that associates each file name to its contents (represented as a string).</p>

<p>We previously represented the contents of each file as a list of @(see
extended-characters).  An advantage of extended characters was that file maps
were cheaper to construct because we already had the list of characters
available from our file-reading functions.  Using strings, we have to pay some
extra price for coercing the characters.</p>

<p>On the other hand, strings are more compact in memory and are generally
faster to serialize and load than extended characters.  When we began to
develop the VL server, these properties seemed quite attractive.</p>

<p>You might ask why we introduce file maps at all instead of just using alists
binding filenames to content strings.  Our basic motivation is to make it more
easy to change the representation of a filemap in the future, should we decide
that we need either more control or flexibility in the underlying
representation.</p>")


(define vl-string-findloc-aux
  :parents (vl-string-findloc)
  ((x     stringp             "The string to search.")
   (n     natp                "Our current position in @('x').")
   (xl    (eql xl (length x)) "Precomputed length of @('x').")
   (cline posp                "Current line number, corresponding to @('n').")
   (ccol  natp                "Current column number, corresponding to @('n'),
                               <i>except</i>: we don't bother to track this until
                               we reach the desired line.")
   (tline posp                "Target line number we're looking for.")
   (tcol  natp                "Target column number we're looking for."))
  :guard (<= n xl)
  :returns
  (offset maybe-natp :rule-classes :type-prescription
          "@('nil') indicates a failure to find the desired location; otherwise
           the position of the target line/column number.")
  :measure (nfix (- (nfix xl) (nfix n)))
  (b* (((when (and (eql cline tline) (eql ccol tcol))) ;; found, done
        (lnfix n))
       ((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                   :exec (eql n xl)))
        ;; End of string, didn't find loc.
        nil)
       (curr (char x n)))
    (cond
     ((< cline tline)
      ;; Not even at the right line yet.  Don't bother maintaining ccol.
      (let ((new-n     (+ 1 (lnfix n)))
            (new-cline (if (eql curr #\Newline) (+ 1 cline) cline)))
        (vl-string-findloc-aux x new-n xl new-cline 0 tline tcol)))

     ((> cline tline)
      ;; Went too far
      nil)

     ((< ccol tcol)
      ;; Right line, not the right char yet.
      (let ((new-n     (+ 1 (lnfix n)))
            (new-cline (if (eql curr #\Newline) (+ 1 cline) cline))
            (new-ccol  (if (eql curr #\Newline) 0 (+ 1 ccol))))
        (vl-string-findloc-aux x new-n xl new-cline new-ccol tline tcol)))

     (t
      ;; Right line, but went too far.
      nil)))
  ///
  (defthm type-of-vl-string-findloc-aux
    (or (natp (vl-string-findloc-aux x n xl cline ccol tline tcol))
        (not (vl-string-findloc-aux x n xl cline ccol tline tcol)))
    :rule-classes :type-prescription)

  (defthm bounds-of-vl-string-findloc-aux-1
    (implies (and (natp n)
                  (natp xl)
                  (<= n xl))
             (and (<= 0 (vl-string-findloc-aux x n xl cline ccol tline tcol))
                  (<= (vl-string-findloc-aux x n xl cline ccol tline tcol) xl)))
    :rule-classes :linear)

  (defthm bounds-of-vl-string-findloc-aux-2
    (implies (and (vl-string-findloc-aux x n xl cline ccol tline tcol)
                  (natp n)
                  (natp xl)
                  (<= n xl))
             (<= n (vl-string-findloc-aux x n xl cline ccol tline tcol)))
    :rule-classes :linear))


(define vl-string-findloc
  :parents (vl-location)
  :short "Traverse a string to determine the position of a @(see
vl-location-p)."

  ((x   stringp        "A string, which should contain the full contents of
                        the file indicated by @('loc').  Typically this is
                        gotten from a @(see vl-filemap-p).")
   (loc vl-location-p  "The location we're looking for."))

  :returns
  (offset maybe-natp :rule-classes :type-prescription
          "The position of this location as an offset into @('x'), or @('nil')
           if the location is not found, e.g., because it refers to a
           line/column number that are too large.")
  (b* ((xl    (length (string-fix x)))
       (tline (vl-location->line loc))
       (tcol  (vl-location->col loc)))
    (vl-string-findloc-aux x 0 xl 1 0 tline tcol))
  ///
  (defthm bounds-of-vl-string-findloc
    (and (<= 0 (vl-string-findloc x loc))
         (<= (vl-string-findloc x loc) (len (explode x))))
    :rule-classes :linear))


(define vl-location-before-nofilename ((x vl-location-p)
                                       (y vl-location-p))
  :parents (vl-string-between-locs)
  (b* (((vl-location x) x)
       ((vl-location y) y))
    (or (< x.line y.line)
        (and (eql x.line y.line)
             (< x.col y.col)))))

(local (in-theory (enable maybe-stringp)))

(define vl-string-between-locs
  :parents (vl-location)
  :short "Given a string, extract all text that occurs between two @(see
vl-location-p)s."
  ((x    "String to extract text from.  Typically this should be extracted
          from a @(see vl-filemap-p).  We assume it has the contents of the
          whole file."
         stringp)
   (loc1 "Some location in the file; we ignore the filename but assume it
          refers to a file whose contents are @('x')."
         vl-location-p)
   (loc2 "Some other location, treated similarly, may come before or after
          @('loc1')."
         vl-location-p))
  :returns (text maybe-stringp :rule-classes :type-prescription)
  :long "<p>If both locations refer to valid places in @('x'), we return the
substring of @('x') that falls between these locations, inclusively.  Otherwise
we return nil.</p>"

    (b* ((x (string-fix x))
         ((mv loc1 loc2)
          (if (vl-location-before-nofilename loc1 loc2)
              (mv loc1 loc2)
            (mv loc2 loc1)))
         (xl     (length x))

         (tline1 (vl-location->line loc1))
         (tcol1  (vl-location->col loc1))
         (pos1   (vl-string-findloc-aux x 0 xl 1 0 tline1 tcol1))
         ((unless pos1)
          nil)

         (tline2 (vl-location->line loc2))
         (tcol2  (vl-location->col loc2))
         (pos2   (vl-string-findloc-aux x pos1 xl tline1 tcol1 tline2 tcol2))
         ((unless pos2)
          nil))

      (subseq x pos1 pos2)))

