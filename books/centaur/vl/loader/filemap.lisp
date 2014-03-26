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
(include-book "../util/defs")
(include-book "../util/echars")
(local (include-book "../util/arithmetic"))

(defsection vl-filemap-p
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
develop the @(see vl-server), these properties seemed quite attractive.</p>

<p>You might ask why we introduce file maps at all.  After all, a file map is
very similar to an alist that satisfies @(see vl-string-keys-p) and @(see
vl-string-values-p).  Our basic motivation is to make it more easy to change
the representation of a filemap in the future, should we decide that we need
either more control or flexibility in the underlying representation.</p>"

  (defund vl-filemap-p (x)
    (declare (xargs :guard t))
    (if (atom x)
        (not x)
      (and (consp (car x))
           (stringp (caar x))
           (stringp (cdar x))
           (vl-filemap-p (cdr x)))))

  (defthm vl-filemap-p-when-not-consp
    (implies (not (consp x))
             (equal (vl-filemap-p x)
                    (not x)))
    :hints(("Goal" :in-theory (enable vl-filemap-p))))

  (defthm vl-filemap-p-of-cons
    (equal (vl-filemap-p (cons a x))
           (and (consp a)
                (stringp (car a))
                (stringp (cdr a))
                (vl-filemap-p x)))
    :hints(("Goal" :in-theory (enable vl-filemap-p))))

  (defthm alistp-when-vl-filemap-p
    (implies (vl-filemap-p x)
             (alistp x))
    :hints(("Goal" :induct (len x))))

  (defthm stringp-of-cdr-of-hons-assoc-equal-when-vl-filemap-p
    (implies (vl-filemap-p x)
             (equal (stringp (cdr (hons-assoc-equal a x)))
                    (if (hons-assoc-equal a x)
                        t
                      nil)))
    :hints(("Goal" :in-theory (enable hons-assoc-equal))))

  (defthm vl-filemap-p-of-append
    (implies (and (force (vl-filemap-p x))
                  (force (vl-filemap-p y)))
             (vl-filemap-p (append x y)))
    :hints(("Goal" :induct (len x))))

  (defthm vl-filemap-p-of-rev
    (implies (force (vl-filemap-p x))
             (vl-filemap-p (rev x)))
    :hints(("Goal" :induct (len x)))))


(defsection vl-string-findloc
  :parents (vl-location-p)
  :short "Traverse a string to determine the position of a @(see
vl-location-p)."

  :long "<p><b>Signature:</b> @(call vl-string-findloc) returns a natural
number or nil.</p>

<p>@('x') is a string and @('loc') is a @(see vl-location-p).  We assume that
@('x') contains the entire contents of the file named by @('loc'); typically
@('x') might be obtained from a @(see vl-filemap-p).  We return the index of
@('loc') within @('x'), or NIL if such a location is not in @('x').</p>"

  (defund vl-string-findloc-aux (x n xl cline ccol tline tcol)
    ;; X - the string to search
    ;; N - the current position in X
    ;; XL - the length of X
    ;;
    ;; CLINE and CCOL - current line and col corresponding to N, except
    ;; that we don't actually maintain CCOL until TLINE is found.
    ;;
    ;; TLINE and TCOL - target line and col we are trying to find
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (posp cline)
                                (natp ccol)
                                (posp tline)
                                (natp tcol)
                                (= xl (length x))
                                (<= n xl))
                    :measure (nfix (- (nfix xl) (nfix n)))))
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
        nil))))

  (local (in-theory (enable vl-string-findloc-aux)))

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
    :rule-classes :linear)

  (defund vl-string-findloc (x loc)
    (declare (xargs :guard (and (stringp x)
                                (vl-location-p loc))))
    (let ((xl    (length x))
          (tline (vl-location->line loc))
          (tcol  (vl-location->col loc)))
      (vl-string-findloc-aux x 0 xl 1 0 tline tcol)))

  (local (in-theory (enable vl-string-findloc)))

  (defthm type-of-vl-string-findloc
    (or (natp (vl-string-findloc x loc))
        (not (vl-string-findloc x loc)))
    :rule-classes :type-prescription)

  (defthm bounds-of-vl-string-findloc
    (implies (stringp x)
             (and (<= 0 (vl-string-findloc x loc))
                  (<= (vl-string-findloc x loc) (len (explode x)))))
    :rule-classes :linear))



(defsection vl-string-between-locs
  :parents (vl-location-p)
  :short "Given a string, extract all text that occurs between two @(see
vl-location-p)s."

  :long "<p><b>Signature:</b> @(call vl-string-between-locs) returns a string
or nil.</p>

<p>@('x') is a string; @('loc1') and @('loc2') are @(see vl-location-p)s, which
may be in any order.  The filenames of @('loc1') and @('loc2') are ignored but
generally should be the same.  We expect that @('x') corresponds to the entire
contents of this file; typically @('x') might be obtained from a @(see
vl-filemap-p).</p>

<p>If both locations are within @('x'), we compute their locations as in @(see
vl-string-findloc) and return the substring of @('x') that falls between these
locations, inclusive.  Otherwise we return nil.</p>"

  (defund vl-location-before-nofilename (x y)
    (declare (xargs :guard (and (vl-location-p x)
                                (vl-location-p y))))
    (b* (((vl-location x) x)
         ((vl-location y) y))
        (or (< x.line y.line)
            (and (= x.line y.line)
                 (< x.col y.col)))))

  (defund vl-string-between-locs (x loc1 loc2)
    (declare (xargs :guard (and (stringp x)
                                (vl-location-p loc1)
                                (vl-location-p loc2))))
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

  (defthm stringp-of-vl-string-between-locs
    (or (stringp (vl-string-between-locs x loc1 loc2))
        (not (vl-string-between-locs x loc1 loc2)))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable vl-string-between-locs)))))
