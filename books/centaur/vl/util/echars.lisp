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

;; This showed up in the critical path, so we try to reduce our dependencies
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/strings/cat" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "centaur/nrev/pure" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (include-book "misc/assert" :dir :system))

(local (defthm integerp-when-natp
         (implies (natp x)
                  (integerp x))))

(local (defthm negative-when-natp
  (implies (natp x)
           (equal (< x 0)
                  nil))))


(defxdoc extended-characters
  :parents (loader)
  :short "Characters with additional annotations."

  :long "<p>Our lexer (and preprocessor) operate on lists of \"extended
characters\", which associate regular characterp objects with their origin in
the Verilog source code.</p>

<p>We represent these origins using @(see vl-location-p) structures, which
simply have a file name, line number, and column number.  We represent each
extended character as an @(see vl-echar-p), a structure that associates a
character with its location.</p>")


(defaggregate vl-location
  :parents (extended-characters)
  :short "Representation of a point in a source file."
  :tag :vl-location
  :legiblep nil

  ((filename stringp :rule-classes :type-prescription)
   (line     posp    :rule-classes :type-prescription)
   (col      natp    :rule-classes :type-prescription))

  :long "<p>Each vl-location-p represents some location in a source code file.
These locations are attached to characters and module items to provide context
during error reporting.</p>")


(defsection *vl-fakeloc*
  :parents (vl-location-p)
  :short "A \"fake\" @(see vl-location-p) which we use when generating our
own @(see extended-characters) and module items."

  (defconst *vl-fakeloc*
    (vl-location "[[[ fake location ]]]" 1 0)))



(define vl-location-string ((loc vl-location-p))
  :parents (vl-location-p)
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
  :parents (vl-location-p)
  :short "@(call vl-location-between-p) is true exactly when @('x') is in the
same file as @('min') and @('max'), and inclusively falls between these
bounds."

  (b* (((vl-location x) x)
       ((vl-location low) min) ;; bozo awful symbol problems with min/max
       ((vl-location high) max))

      (and (equal x.filename low.filename)
           (equal x.filename high.filename)

           (or (< low.line x.line)
               (and (int= low.line x.line)
                    (<= low.col x.col)))

           (or (< x.line high.line)
               (and (int= x.line high.line)
                    (<= x.col high.col))))))



(defsection vl-echar-p
  :parents (extended-characters)
  :short "Representation of a single extended character."

  :long "<p>Historically, a @('vl-echar-p') was an ordinary aggregate with a
character and a location.  This was nice and simple, but required a lot of
memory.  Here is a back-of-the-napkin analysis, where the underlying cons-tree
representation of each echar is understood as:</p>

@({
    vl-echar ::=  (char . (:vl-location . (filename . (line . col)))))
})

<p>Assume we need no extra overhead to represent the filename, line, or column.
This is fair: typically whole giant sets of echars all have their filename
pointing to the same string, so we don't need extra memory for the file name.
Furthermore, the line and column number are always fixnums in practice, i.e.,
they are immediates that don't take any extra space.  Then, the memory required
for each echar is:</p>

@({
    4 conses = 128 bits * 4 = 512 bits = 64 bytes
})

<p>But since echars generally go in a list, we basically also need 1 extra cons
per character to join it to the rest of the list.  So, the total overhead just
for echars is really more like 80 bytes.  In short, to read a file with N bytes
in it we need 80N bytes of memory, so if we want to process a 100 MB Verilog
file we need 8 GB of space!  (It's actually worse than this, because that's
just the cost of reading the characters in the first place.  After that we have
to preprocess them, which is basically an echarlist-to-echarlist
transformation.  Preprocessing doesn't need to deeply copy the echars
themselves, but it is still going to deeply copy the list, which means an 16
bytes of overhead.  So we're up to 9.6 GB for a 100 MB file before reaching a
good place where we can garbage collect.</p>

<p>To reduce this overhead, we now use a more efficient encoding scheme.</p>

<h3>Encoding Scheme</h3>

<p>We will use a simple encoding that allows us to represent almost any
practical echar as a single cons of an immediate onto a filename pointer.  We
will assume we can represent any unsigned 60-bit number as a fixnum, which is
true in 64-bit CCL.  This seems like plenty of space.  We divide it up, rather
arbitrarily, as follows:</p>

<ul>
<li>8-bit character code, so we can represent any character code</li>
<li>30-bit line number, so our maximum line number is ~1 billion</li>
<li>22-bit column number, so our maximum column number is ~4 million</li>
</ul>

<p>It is hard to imagine hitting these limits in practice, but as a fallback we
will simply allow any characters from locations outside this range to be
represented as cons structures with line, column, and character code
components.  This is no worse than our former representation, and means that
the interface for constructing echars can be kept simple and bounds-free.</p>

@(def vl-echar-p)"

  :autodoc nil

  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))
  (local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))

  (local (defthmd l0
           (implies (and (unsigned-byte-p 8 code)
                         (unsigned-byte-p 30 line)
                         (unsigned-byte-p 22 col))
                    (unsigned-byte-p 60 (logior code (ash col 8) (ash line 30))))))

  (local (defthm l1
           (implies (and (unsigned-byte-p 8 code)
                         (unsigned-byte-p 30 line)
                         (unsigned-byte-p 22 col))
                    (< (logior code (ash col 8) (ash line 30))
                       1152921504606846976))
           :hints(("goal"
                   :in-theory (disable ACL2::UNSIGNED-BYTE-P-OF-LOGIOR
                                       ACL2::UNSIGNED-BYTE-P-OF-ASH)
                   :use ((:instance l0))))))

  (define vl-echarpack-p (x)
    :parents (vl-echar-p)
    :short "Packed up LINE, COL, and CHAR-CODE in a single fixnum."
    (if (integerp x)
        ;; [LINE : 30 bits, COL : 22 bits, CHAR-CODE : 8 bits]
        (and (<= 0 x)
             (< 0 (ash x -30)) ;; "posp of line"
             (< x (expt 2 60)))
      ;; ((LINE . COL) . CHAR-CODE)
      (and (consp x)
           (consp (car x))
           (posp (caar x))
           (natp (cdar x))
           (unsigned-byte-p 8 (cdr x)))))

  (local (in-theory (enable vl-echarpack-p)))

  (define vl-echarpack ((code (unsigned-byte-p 8 code))
                        (line posp)
                        (col  natp))
    :parents (vl-echarpack-p)
    :inline t ;; should only really be called from vl-echar
    (declare (type (unsigned-byte 8) code))
    (if (and (< (the (integer 0 *) line) (expt 2 30))
             (< (the (integer 0 *) col)  (expt 2 22)))
        ;; Usual case: things are small enough to be packed up nicely
        (let* ((line-shift (the (unsigned-byte 60) (ash (the (unsigned-byte 30) line) 30)))
               (col-shift  (the (unsigned-byte 30) (ash (the (unsigned-byte 22) col) 8))))
          (the (unsigned-byte 60)
            (logior (the (unsigned-byte 60)
                      (logior (the (unsigned-byte 60) line-shift)
                              (the (unsigned-byte 30) col-shift)))
                    (the (unsigned-byte 8) code))))
      ;; Degenerate case: something too big, just make a cons structure
      (cons (cons line col) code))
    ///
    (defthm vl-echarpack-p-of-vl-echarpack
      (implies (and (force (unsigned-byte-p 8 code))
                    (force (posp line))
                    (force (natp col)))
               (vl-echarpack-p (vl-echarpack code line col)))))

  (local (in-theory (enable vl-echarpack)))

  (define vl-echarpack->code ((x vl-echarpack-p))
    :parents (vl-echarpack-p)
    :returns (code (unsigned-byte-p 8 code)
                   :hyp :fguard
                   :rule-classes ((:rewrite)
                                  (:type-prescription :corollary
                                                      (implies (vl-echarpack-p x)
                                                               (natp (vl-echarpack->code x))))
                                  (:linear :corollary
                                           (implies (vl-echarpack-p x)
                                                    (< (vl-echarpack->code x) 256)))))
    :inline t
    (if (consp x)
        (the (unsigned-byte 8) (cdr x))
      (the (unsigned-byte 8)
        (logand (the (unsigned-byte 60) x) #xFF)))
    ///
    (defthm vl-echarpack->code-of-vl-echarpack
      (implies (and (force (unsigned-byte-p 8 code))
                    (force (natp line))
                    (force (natp col)))
               (equal (vl-echarpack->code (vl-echarpack code line col))
                      code))
      :hints((acl2::equal-by-logbitp-hammer))))

  (define vl-echarpack->line ((x vl-echarpack-p))
    :parents (vl-echarpack-p)
    :returns (line posp
                   :hyp :fguard
                   :rule-classes :type-prescription)
    :inline t
    (if (consp x)
        (the (integer 0 *) (caar x))
      (the (unsigned-byte 30)
        (ash (the (unsigned-byte 60) x) -30)))
    ///
    (defthm vl-echarpack->line-of-vl-echarpack
      (implies (and (force (unsigned-byte-p 8 code))
                    (force (natp line))
                    (force (natp col)))
               (equal (vl-echarpack->line (vl-echarpack code line col))
                      line))))

  (define vl-echarpack->col ((x vl-echarpack-p))
    :parents (vl-echarpack-p)
    :returns (col natp
                  :hyp :fguard
                  :rule-classes :type-prescription)
    :inline t
    (if (consp x)
        (the (integer 0 *) (cdar x))
      (the (unsigned-byte 60)
        (logand (the (unsigned-byte 22) (1- (expt 2 22)))
                (the (unsigned-byte 52)
                  (ash (the (unsigned-byte 60) x) -8)))))
    ///
    (defthm vl-echarpack->col-of-vl-echarpack
      (implies (and (force (unsigned-byte-p 8 code))
                    (force (natp line))
                    (force (natp col)))
               (equal (vl-echarpack->col (vl-echarpack code line col))
                      col))))

  (local (in-theory (disable vl-echarpack-p vl-echarpack)))

  (define vl-echar-p (x)
    (and (consp x)
         (stringp (car x)) ;; Filename
         (vl-echarpack-p (cdr x))))

  (local (in-theory (enable vl-echar-p)))

  (defthm booleanp-of-vl-echar-p
    (booleanp (vl-echar-p x))
    :rule-classes :type-prescription)

  (defthm consp-when-vl-echar-p
    (implies (vl-echar-p x)
             (consp x))
    :rule-classes :compound-recognizer)

  (define vl-echar ((char characterp)
                    (loc  vl-location-p))
    :returns (echar vl-echar-p :hyp :fguard)
    :parents (vl-echar-p)
    :short "High-level constructor for an @(see vl-echar-p)."
    :long "<p>See @(see make-vl-echar-fast) for a faster alternative.</p>"
    (b* (((vl-location loc) loc))
      (cons loc.filename
            (vl-echarpack (the (unsigned-byte 8) (char-code char))
                          loc.line
                          loc.col))))

  (local (in-theory (enable vl-echar)))

  (define make-vl-echar-fast (&key
                              (char     characterp)
                              (filename stringp)
                              (line     posp)
                              (col      natp))
    :parents (vl-echar-p)
    :short "Fast creation of extended characters that bypasses constructing
            @(see vl-location) objects."
    :enabled t
    :inline t
    (mbe :logic
         (vl-echar char (make-vl-location :filename filename
                                          :line line
                                          :col col))
         :exec
         (cons filename
               (vl-echarpack (the (unsigned-byte 8) (char-code char))
                             line col))))

  (defthm vl-echar-under-iff
    (iff (vl-echar char loc)
         t))

  (define vl-echar->char ((x vl-echar-p))
    :returns (char characterp
                   :rule-classes :type-prescription
                   :hyp :fguard)
    :parents (vl-echar-p)
    :short "High-level accessor: get the character from an @(see vl-echar-p)."
    :inline t
    (the character
      (code-char (the (unsigned-byte 8) (vl-echarpack->code (cdr x)))))
    ///
    (defthm vl-echar->char-of-vl-echar
      (implies (and (force (characterp char))
                    (force (vl-location-p loc)))
               (equal (vl-echar->char (vl-echar char loc))
                      char))))

  (define vl-echar->loc ((x vl-echar-p))
    :returns (loc vl-location-p :hyp :fguard)
    :parents (vl-echar-p)
    :short "High-level accessor: get the location from an @(see vl-echar-p)."
    :long "<p>Note that this has to construct a @(see vl-location-p) object.</p>"
    (make-vl-location :filename (car x)
                      :line (vl-echarpack->line (cdr x))
                      :col  (vl-echarpack->col (cdr x)))
    ///
    (local (defthm m0
             (implies (and (force (characterp char))
                           (force (vl-location-p loc)))
                      (equal (vl-echar->loc (vl-echar char loc))
                             (make-vl-location
                              :filename (vl-location->filename loc)
                              :line     (vl-location->line loc)
                              :col      (vl-location->col loc))))))

    (local (defthm m1
             (implies (and (vl-location-p x)
                           (vl-location-p y))
                      (equal (equal x y)
                             (b* (((vl-location x) x)
                                  ((vl-location y) y))
                               (and (equal x.filename y.filename)
                                    (equal x.line y.line)
                                    (equal x.col y.col)))))
             :hints(("Goal" :in-theory (enable vl-location-p
                                               vl-location
                                               vl-location->filename
                                               vl-location->line
                                               vl-location->col)))))

    (defthm vl-echar->loc-of-vl-echar
      (implies (and (force (characterp char))
                    (force (vl-location-p loc)))
               (equal (vl-echar->loc (vl-echar char loc))
                      loc))))

  (make-event
   ;; Emulate defaggregate stuff
   (let ((name 'vl-echar)
         (fields '(char loc)))
     `(progn
        ,(std::da-make-maker-fn name fields nil)
        ,(std::da-make-maker name fields)
        ,(std::da-make-changer-fn name fields)
        ,(std::da-make-changer name fields)
        ,(std::da-make-binder name fields))))

  ;; Rudimentary testing of defaggregate stuff
  (local
   (progn
     (assert! (equal (vl-echar->char (make-vl-echar :char #\a :loc *vl-fakeloc*)) #\a))
     (assert! (equal (vl-echar->loc (make-vl-echar :char #\a :loc *vl-fakeloc*)) *vl-fakeloc*))
     (assert! (b* ((c (make-vl-echar :char #\a :loc *vl-fakeloc*))
                   ((vl-echar c) c))
                (and (equal c.char #\a)
                     (equal c.loc *vl-fakeloc*))))
     (assert! (b* ((c (make-vl-echar :char #\a :loc *vl-fakeloc*))
                   (c (change-vl-echar c :char #\b))
                   ((vl-echar c) c))
                (and (equal c.char #\b)
                     (equal c.loc *vl-fakeloc*)))))))



; Once upon a time we took special measures to print warnings if this function
; was given long lists, because this was useful in debugging some performance
; problems related to the execution of guards.  But we no longer think this is
; necessary, and so we return to the simple definition.

(deflist vl-echarlist-p (x)
  (vl-echar-p x)
  :elementp-of-nil nil
  :parents (extended-characters))

(defprojection vl-echarlist->chars (x)
  (vl-echar->char x)
  :guard (vl-echarlist-p x)
  :nil-preservingp nil
  :result-type character-listp
  :parents (extended-characters)
  :rest
  ;; Previously this was nil-preserving and defprojection added a rule like
  ;; this automatically (with no hyp).  The defprojection rule went the other
  ;; way.  I'm not sure why I wanted the rule to go this way.  If we extend
  ;; defprojection to add the other rule, we'll need to mark them as
  ;; incompatible, disable its rule, etc.
  ((defthm vl-echarlist->chars-of-take
     (implies (force (<= (nfix n) (len x)))
              (equal (vl-echarlist->chars (take n x))
                     (take n (vl-echarlist->chars x))))
     :hints(("Goal" :in-theory (enable acl2::take-redefinition))))))



(define vl-echarlist->string ((x vl-echarlist-p))
  :parents (extended-characters)
  :short "Transform a @(see vl-echarlist-p) to a string."

  :long "<p>Logically, this function just runs @(see vl-echarlist->chars) and
coerces the result to a string; we typically leave it enabled.</p>

<p>Under the hood, in Common Lisp, we install a faster definition that avoids
creating an intermediate list and instead just builds a string directly.  This
notably saves a lot of memory when we build @(see vl-filemap-p)s.</p>"

  :enabled t
  (implode (vl-echarlist->chars x))

  ///

  (defttag vl-optimize)
  (acl2::progn!
   (set-raw-mode t)
   (defun vl-echarlist->string (x)
     (let ((len (len x)))
       (declare (fixnum len))
       (cond ((eql len 0)
              "")
             (t
              (let* ((ret  (make-string len))
                     (last (- len 1)))
                (declare (fixnum last))
                (loop for i fixnum from 0 to last do
                      (setf (char ret i) (vl-echar->char (car x)))
                      (setq x (cdr x)))
                ret))))))
  (defttag nil))


(define vl-change-echarlist-locations ((x vl-echarlist-p)
                                       (loc vl-location-p))
  :returns (ans vl-echarlist-p :hyp :fguard)
  :parents (extended-characters)
  :short "Override the locations of characters."
  :long "<p>@(call vl-change-echarlist-locations) is given a list of extended
characters, @('x'), and a location, @('loc').  It changes the location of every
character in @('x') to @('loc').</p>

<p>This funny operation is used in the preprocessor to make @('`define')
handling more sensible.</p>"

  (if (consp x)
      (cons (change-vl-echar (car x) :loc loc)
            (vl-change-echarlist-locations (cdr x) loc))
    nil))

(define vl-echarlist-from-chars-aux ((x character-listp)
                                     (filename stringp)
                                     (line posp :type (integer 0 *))
                                     (col natp :type (integer 0 *))
                                     nrev)
  :split-types t
  :parents (vl-echarlist-from-chars)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (echar (make-vl-echar-fast :char (car x)
                                  :filename filename
                                  :line line
                                  :col col))
       (nrev  (nrev-push echar nrev))
       ((the character c) (car x))
       (line  (if (eql c #\Newline)
                  (the (integer 0 *) (+ 1 line))
                line))
       (col   (if (eql c #\Newline)
                  0
                (the (integer 0 *) (+ 1 col)))))
    (vl-echarlist-from-chars-aux (cdr x) filename line col nrev)))

(define vl-echarlist-from-chars
  ((x character-listp "The characters to convert")
   &key
   ((filename stringp  "Filename for every echar we build")
    '"[internal character list]")
   ((line posp "Starting line") '1)
   ((col natp "Starting column") '0))
  :returns (ans vl-echarlist-p :hyp :fguard)
  :parents (extended-characters)
  :short "Transform an ordinary character list into a @(see vl-echarlist-p)."
  (mbe :logic
       (b* (((when (atom x))
             nil)
            (echar (make-vl-echar-fast :char (car x)
                                       :filename filename
                                       :line line
                                       :col col))
            (line (if (eql (car x) #\Newline) (+ 1 line) line))
            (col  (if (eql (car x) #\Newline) 0 (+ 1 col))))
         (cons echar
               (vl-echarlist-from-chars-fn (cdr x) filename line col)))
       :exec (with-local-nrev
              (vl-echarlist-from-chars-aux x filename line col nrev)))
  :verify-guards nil
  ///
  (never-memoize vl-echarlist-from-chars-aux)

  (defthm true-listp-of-vl-echarlist-from-chars-fn
    (true-listp (vl-echarlist-from-chars-fn x filename line col))
    :rule-classes :type-prescription)

  (defthm vl-echarlist->chars-of-vl-echarlist-from-chars-fn
    (implies (and (force (character-listp x))
                  (force (stringp filename))
                  (force (posp line))
                  (force (natp col)))
             (equal (vl-echarlist->chars (vl-echarlist-from-chars-fn x filename line col))
                    x)))

  (local (in-theory (enable vl-echarlist-from-chars-aux)))

  (defthm vl-echarlist-from-chars-aux-removal
    (equal (vl-echarlist-from-chars-aux x filename line col acc)
           (append acc (vl-echarlist-from-chars-fn x filename line col))))

  (verify-guards vl-echarlist-from-chars-fn))



(define vl-echarlist-from-str-aux
  :parents (vl-echarlist-from-str)
  ((x        stringp)
   (n        natp)
   (xl       (equal xl (length x)))
   (filename stringp)
   (line     posp)
   (col      natp)
   nrev)
  :guard (<= n xl)
  :measure (nfix (- (nfix xl) (nfix n)))
  :split-types t
  (declare (type string x filename)
           (type (integer 0 *) n xl line col))
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                   :exec (eql n xl)))
        (nrev-fix nrev))
       ((the character char) (char x n))
       (echar (make-vl-echar-fast :char char
                                  :filename filename
                                  :line line
                                  :col col))
       (nrev (nrev-push echar nrev))
       (line (if (eql char #\Newline)
                 (the (integer 0 *) (+ 1 line))
               line))
       (col  (if (eql char #\Newline)
                 0
               (the (integer 0 *) (+ 1 col)))))
    (vl-echarlist-from-str-aux (the string x)
                               (the (integer 0 *) (+ 1 (lnfix n)))
                               xl filename line col nrev)))

(define vl-echarlist-from-str-nice
  :parents (vl-echarlist-from-str)
  ((x        stringp)
   (n        natp)
   (xl       (equal xl (length x)))
   (filename stringp)
   (line     posp)
   (col      natp))
  :guard (<= n xl)
  :split-types t
  :measure (nfix (- (nfix xl) (nfix n)))
  :verify-guards nil
  (declare (type string x filename)
           (type integer n xl line col))
  (mbe :logic (if (zp (- (nfix xl) (nfix n)))
                  nil
                (let ((char (char x n)))
                  (cons (make-vl-echar-fast :char char
                                            :filename filename
                                            :line line
                                            :col col)
                        (vl-echarlist-from-str-nice
                         x (+ 1 (nfix n)) xl filename
                         (if (eql char #\Newline) (+ 1 line) line)
                         (if (eql char #\Newline) 0 (+ 1 col))))))
       :exec (with-local-nrev
              (vl-echarlist-from-str-aux x n xl filename line col nrev)))
  ///
  (defthm vl-echarlist-from-str-aux-correct
    (equal (vl-echarlist-from-str-aux x n xl filename line col acc)
           (append acc (vl-echarlist-from-str-nice x n xl filename line col)))
    :hints(("Goal"
            :in-theory (enable vl-echarlist-from-str-aux)
            :induct (vl-echarlist-from-str-aux x n xl filename line col acc))))

  (verify-guards vl-echarlist-from-str-nice)

  (defthm vl-echarlist-from-str-nice-correct
    (equal (vl-echarlist-from-str-nice x n (len (explode x)) filename line col)
           (vl-echarlist-from-chars-fn (nthcdr n (explode x)) filename line col))
    :hints(("Goal" :in-theory (enable nthcdr
                                      vl-echarlist-from-str-nice
                                      vl-echarlist-from-chars-fn)))))


(define vl-echarlist-from-str
  :parents (extended-characters)
  :short "Transform an ordinary @('stringp') into a @(see vl-echarlist-p)."
  ((x        stringp)
   &key
   ((filename stringp) '"[internal string]")
   ((line     posp)    '1)
   ((col      natp)    '0))
  :returns echarlist

  :long "<p>This is like @(see vl-echarlist-from-chars), but we process an ACL2
string instead of a character list.</p>

<p>We go to some lengths to be able to more efficiently construct an echarlist
from a string.  The simplest approach to this would be:</p>

<ol>
 <li>coerce the string into a list</li>
 <li>call @(see vl-echarlist-from-chars) on the resulting list</li>
</ol>

<p>The above is our logical definition, and hence we leave this function
enabled and reason about @(see vl-echarlist-from-chars) instead.  But for
better efficiency, we avoid the coerce and process the string directly.</p>"

  :enabled t
  (mbe :logic (vl-echarlist-from-chars-fn (explode x) filename line col)
       :exec (vl-echarlist-from-str-nice x 0
                                         (length (the string x))
                                         filename line col)))


(define vl-echar-digit-value ((x vl-echar-p)
                              (radix (and (integerp radix)
                                          (<= 2 radix)
                                          (<= radix 36))))
  :parents (extended-characters)
  :short "@(call vl-echar-digit-value) interprets the extended character @('x')
as a base-@('radix') digit, or returns @('nil') if @('x') is not a valid digit
in this base."

  (digit-char-p (vl-echar->char x) radix)

  ///

  (defthm natp-of-vl-echar-digit-value
    (let ((ret (vl-echar-digit-value x radix)))
      (implies ret
               (and (natp ret)
                    (integerp ret)
                    (<= 0 ret))))
    :rule-classes ((:rewrite)
                   (:type-prescription
                    :corollary (or (not (vl-echar-digit-value x radix))
                                   (and (integerp (vl-echar-digit-value x radix))
                                        (<= 0 (vl-echar-digit-value x radix))))))))



(define vl-echarlist-unsigned-value-aux ((x vl-echarlist-p)
                                         (radix (and (integerp radix)
                                                     (<= 2 radix)
                                                     (<= radix 36)))
                                         (n (equal n (len x))))
  :parents (vl-echarlist-unsigned-value)

  (b* (((when (atom x))
        0)
       (car-digit (vl-echar-digit-value (car x) radix))
       ((unless car-digit)
        nil)
       (cdr-value (vl-echarlist-unsigned-value-aux (cdr x) radix (1- n)))
       ((unless cdr-value)
        nil))
    (+ (* (expt radix (1- n)) car-digit)
       cdr-value)))

(define vl-echarlist-unsigned-value ((x vl-echarlist-p)
                                     (radix (and (integerp radix)
                                                 (<= 2 radix)
                                                 (<= radix 36))))
  :parents (extended-characters)
  :short "@(call vl-echarlist-unsigned-value) interprets the extended character
list @('x') as a base-@('radix') number, or returns @('nil') if @('x') is
invalid."

  :long "<p>We see if X is made up entirely of base RADIX digits.  If so, we
return the number represented by X, treating the digits as if they are written
with the most significant digit first.  For instance, an echarlist whose string
is \"987\" has, in base 10, an unsigned-value of 987.  Otherwise, if there are
any invalid digits, we return NIL.</p>"

  (if (not (consp x))
      nil
    (vl-echarlist-unsigned-value-aux x (lnfix radix) (len x)))

  ///

  (local (defthm natp-expt
           (implies (and (natp a)
                         (natp b))
                    (natp (expt a b)))
           :rule-classes :type-prescription))

  (local (defthm lemma
           (implies (and (integerp radix)
                         (<= 0 radix)
                         (equal n (len x))
                         (vl-echarlist-unsigned-value-aux x radix n))
                    (natp (vl-echarlist-unsigned-value-aux x radix n)))
           :hints(("Goal" :in-theory (e/d (vl-echarlist-unsigned-value-aux)
                                          (expt))))))

  (defthm natp-of-vl-echarlist-unsigned-value-aux
    (implies (vl-echarlist-unsigned-value x radix)
             (and (natp (vl-echarlist-unsigned-value x radix))
                  (integerp (vl-echarlist-unsigned-value x radix))
                  (<= 0 (vl-echarlist-unsigned-value x radix))))
    :rule-classes
    ((:rewrite)
     (:type-prescription
      :corollary (or (not (vl-echarlist-unsigned-value x radix))
                     (and (integerp (vl-echarlist-unsigned-value x radix))
                          (<= 0 (vl-echarlist-unsigned-value x radix)))))))

  (defthm vl-echarlist-unsigned-value-when-not-consp
    (implies (not (consp x))
             (equal (vl-echarlist-unsigned-value x radix)
                    nil)))

  (defthm type-of-vl-echarlist-unsigned-value
    (or (not (vl-echarlist-unsigned-value x radix))
        (natp (vl-echarlist-unsigned-value x radix)))
    :rule-classes :type-prescription)

  (local
   (progn
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
     (assert! (equal #x010101 (vl-echarlist-unsigned-value (vl-echarlist-from-str "010101") 16)))


     ;; Dumb unit checks to make sure vl-echarlist->string seems to be working
     ;; right.

     (assert! (equal (vl-echarlist->string (vl-echarlist-from-str "")) ""))
     (assert! (equal (vl-echarlist->string (vl-echarlist-from-str "foo")) "foo")))))


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
