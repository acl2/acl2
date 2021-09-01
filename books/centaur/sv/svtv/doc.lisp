; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "SV")
(include-book "structure")
(include-book "expand")
(include-book "std/strings/pretty" :dir :system)
(include-book "std/strings/html-encode" :dir :system)
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/strings/explode-nonnegative-integer" :dir :system))

(defsection svtv-doc
  :parents (svex-stvs)
  :short "Automatic documentation support for svex symbolic test vectors."

  :long "<p>Symbolic test vectors are integrated into @(see xdoc::xdoc) so that you
can generate attractive explanations of your setup.  This is often useful when
communicating with logic designers.</p>

<p><b>NOTE</b>: the topics here cover how we generate this documentation.  If
you just want to document your own SVTVs, you don't need to know about any of
this&mdash;just give a @(':parents'), @(':short'), or @(':long') argument to
@(see defstv).</p>

<p>These functions don't do much error checking.  We expect that we only are
going to generate documentation after successfully processing the SVTV, so we
generally just expect things to be well-formed at this point.</p>

<p>The XML we generate is not documented in @(see xdoc::xdoc)'s @(see
xdoc::markup), and is not supported by tools like @(':xdoc').  How these new
tags get rendered into HTML is controlled by, e.g.,
@('xdoc/fancy/render.xsl').</p>")

(local (xdoc::set-default-parents svtv-doc))

(define stv-name-to-xml (name acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :short "Encode the name of an STV line."
  (b* (((when (stringp name))
        ;; It already looks like a Verilog name, so this is easy enough.
        (b* (((mv ?col acc)
              (str::html-encode-string-aux name 0 (length name) 0 8 acc)))
          acc))
       ;; Complex name.  This is probably awful.  For now just turn it into
       ;; a string using the pretty printer.  Do something better here if we
       ;; ever care.
       (str (str::pretty name))
       ((mv ?col acc)
        (str::html-encode-string-aux str 0 (length str) 0 8 acc)))
    acc))

(define 4vec-to-bitwise-chars ((upper integerp) (lower integerp) (width natp))
  :returns (chars character-listp)
  (b* (((when (zp width)) nil)
       (width (1- width))
       (up (logbitp width upper))
       (low (logbitp width lower))
       (char (if up
                 (if low
                     #\1
                   #\x)
               (if low
                   #\z
                 #\0))))
    (cons char (4vec-to-bitwise-chars upper lower width))))

(define 4vec-to-hex-char ((upper natp) (lower natp))
  :guard (and (< upper 16) (< lower 16))
  :returns (hex-char characterp)
  (b* ((upper (lnfix upper))
       (lower (lnfix lower)))
    (cond ((eql upper lower)
           (if (< upper 10)
               (code-char (+ (char-code #\0) upper))
             (code-char (+ (char-code #\A) (- upper 10)))))
          ((and (eql upper #xf) (eql lower #x0))
           ;; all bits X
           #\X)
          ((and (eql upper #x0) (eql lower #xf))
           ;; all bits Z
           #\Z)
          ((eql 0 (logand upper (lognot lower)))
           ;; some bits Z, no bits X
           #\z)
          (t
           ;; some bits x, maybe z too
           #\x))))


(local (include-book "centaur/bitops/ihsext-basics" :dir :system))

(local
 (encapsulate nil
   (local (include-book "centaur/bitops/ihs-extensions" :dir :system))
   (local (in-theory (enable* bitops::ihsext-bounds-thms)))
   (local (in-theory (disable bitops::ash-1-removal)))
   (local (in-theory (disable (tau-system)
                              bitops::loghead-identity
                              bitops::logsquash-cancel)))

   (local (defun ind (n width)
            (if (zp n)
                width
              (ind (1- n) (logcdr width)))))

   (local (defthm minus-of-logcons-0
            (equal (- (bitops::logcons b i))
                   (+ 1 (bitops::logcons (bitops::b-not b) (lognot i))))
            :hints(("Goal" :in-theory (enable bitops::minus-to-lognot)))))

   (local (defthm expand-+
            (implies (and (integerp width) (integerp i))
                     (equal (+ 1 width (bitops::logcons 1 i))
                            (bitops::logcons (bitops::logcar width)
                                           (+ 1 (bitops::logcdr width) i))))
            :hints (("goal" :use ((:instance bitops::+-of-logcons-with-cin
                                   (bitops::cin 1)
                                   (bitops::b1 (bitops::logcar width))
                                   (bitops::r1 (bitops::logcdr width))
                                   (bitops::b2 1)
                                   (bitops::r2 i)))
                     :in-theory (disable bitops::+-of-logcons-with-cin)))))

   (local (defthm logsquash-linear
            (implies (and (integerp a) (integerp b)
                          (<= a b))
                     (<= (bitops::logsquash n a) (bitops::logsquash n b)))
            :hints(("Goal" :in-theory (enable* bitops::logsquash**
                                               bitops::ihsext-inductions)))
            :rule-classes :linear))

   (local (defthm logsquash-linear-2
            (implies (integerp a)
                     (<= (bitops::logsquash n (+ -1 a)) (bitops::logsquash n a)))
            :rule-classes :linear))

   (local (in-theory (disable logsquash-linear)))

   (local (defthm logsquash-when-loghead-0
            (implies (equal 0 (bitops::loghead n a))
                     (equal (bitops::logsquash n a)
                            (ifix a)))
            :hints(("Goal" :in-theory (enable* bitops::logsquash**
                                               bitops::loghead**
                                               bitops::ihsext-inductions)))))

   (local (defthm logcar-gte-0
            (not (< (logcar x) 0))))

   (local (defthm width-mask-bound
            (implies (posp width)
                     (and (<= (+ width
                                 (- (bitops::logsquash n (+ -1 width))))
                              (ash 1 (nfix n)))
                          (implies (not (equal 0 (bitops::loghead n width)))
                                   (< (+ width
                                         (- (bitops::logsquash n (+ -1 width))))
                                      (ash 1 (nfix n))))))
            :hints (("goal" :induct (ind n width)
                     :expand ((:free (w) (bitops::logsquash n w))
                              (:free (w) (bitops::loghead n w))
                              (ash 1 n))
                     :in-theory (enable lognot)))
            :rule-classes :linear))

   (local (Defthm expt-2-monotonic-2
            (implies (and (integerp a) (integerp b)
                          (<= a b))
                     (<= (expt 2 a) (expt 2 b)))
            :hints(("Goal" :in-theory (enable bitops::expt-2-monotonic)
                    :cases ((< a b))))
            :rule-classes (:rewrite :linear)))

   (defthm loghead-by-width-mask
     (implies (posp width)
              (< (loghead (+ width (- (bitops::logsquash n (+ -1 width)))) i)
                 (expt 2 (ash 1 (nfix n)))))
     :hints (("goal" :use ((:instance expt-2-monotonic-2
                            (a (+ width (- (bitops::logsquash n (+ -1 width)))))
                            (b (ash 1 (nfix n)))))
              :in-theory (e/d ()
                              (expt-2-monotonic-2
                               ))))
     :rule-classes :linear)))

(define 4vec-to-hex-chars ((upper integerp) (lower integerp) (width natp))
  :prepwork ((local (in-theory (enable* bitops::ihsext-bounds-thms))))
  :measure (nfix width)
  :returns (chars character-listp)
  (b* (((when (zp width)) nil)
       (offset (logand (1- width) -4))
       (nbits (- width offset))
       (up (loghead nbits (logtail offset upper)))
       (low (loghead nbits (logtail offset lower))))
    (cons (4vec-to-hex-char up low)
          (4vec-to-hex-chars upper lower offset))))

(define 4vec-to-xml-chars ((x 4vec-p))
  :returns (chars character-listp)
  (if (2vec-p x)
      (b* ((val (2vec->val x))
           (val (loghead (integer-length val) val)))
        (if (< val 10)
            (str::nat-to-dec-chars val)
          (list* #\0 #\x (str::nat-to-hex-chars val))))
    ;; We have non-Boolean digits.  Print bitwise if small enough, otherwise hex.
    (b* (((4vec x) x)
         (len (max (integer-length x.upper) (integer-length x.lower)))
         ((when (and (<= len 6)
                     (<= (integer-length x.lower) 6)))
          (list* #\0 #\b (4vec-to-bitwise-chars x.upper x.lower len))))
      (list* #\0 #\x (4vec-to-hex-chars x.upper x.lower len)))))



(define stv-entry-to-xml ((entry     "The value that the user gave, originally.")
                          (expansion "Its expanded out value, a sexpr list."
                                     (or (not expansion)
                                         (svtv-entry-p expansion)))
                          acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :short "Encode a single value from an STV line."
  (cond ((4vec-p expansion)
         (revappend (4vec-to-xml-chars expansion) acc))

        ((svtv-dontcare-p entry)
         ;; Just skipping these seems nicest.
         acc)

        ((symbolp entry)
         (b* ((acc (str::revappend-chars "<b>" acc))
              ((mv ?col acc)
               (str::html-encode-string-aux (symbol-name entry) 0
                                            (length (symbol-name entry))
                                            0 8 acc))
              (acc (str::revappend-chars "</b>" acc)))
           acc))

        ((svtv-condoverride-p entry)
         ;; BOZO this is probably broken
         (b* (((svtv-condoverride entry))
              ((unless (And (symbolp entry.value)
                            (symbolp entry.test)))
               acc)
              (acc (str::revappend-chars "<b>" acc))
              ((mv ?col acc)
               (str::html-encode-string-aux (symbol-name entry.value) 0
                                            (length (symbol-name entry.value))
                                            0 8 acc))
              (acc (str::revappend-chars "</b>" acc)))
           acc))

        (t (raise "Bad entry in stv line: ~x0." entry))))

(define stv-entries-to-xml ((entries "The original entries for this line.")
                            (expansions "The expanded entries for this line."
                                        svtv-entrylist-p)
                            acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :short "Encode all the values from an STV line."
  (b* (((when (atom entries))
        acc)
       (acc (str::revappend-chars "<stv_entry>" acc))
       (acc (stv-entry-to-xml (car entries)
                              (and (consp expansions)
                                   (car expansions))
                              acc))
       (acc (str::revappend-chars "</stv_entry>" acc)))
    (stv-entries-to-xml (cdr entries)
                        (and (consp expansions)
                             (cdr expansions))
                        acc)))

(define stv-line-to-xml
  ((line      "Original line, with name, given by the user."
              true-listp)
   (expansion "Fully expanded line, with name, after STV processing"
              (or (not expansion)
                  (svtv-line-p expansion)))
   acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :short "Encode one full line from the STV into XML for XDOC."
  (b* ((acc (str::revappend-chars "<stv_line>" acc))
       (acc (str::revappend-chars "<stv_name>" acc))
       (acc (stv-name-to-xml (car line) acc))
       (acc (str::revappend-chars "</stv_name>" acc))
       (acc (stv-entries-to-xml (cdr line)
                                (and expansion
                                     (svtv-line->entries expansion))
                                acc))
       (acc (str::revappend-chars "</stv_line>" acc))
       (acc (cons #\Newline acc)))
    acc))

(define stv-lines-to-xml ((lines      true-list-listp)
                          (expansions svtv-lines-p)
                          acc)
  :returns (acc character-listp :hyp (character-listp acc))
  (b* (((when (atom lines))
        acc)
       ((cons expansion1 rest-expansions) (if (atom expansions)
                                              (cons nil nil)
                                            expansions))
       (acc (stv-line-to-xml (car lines) expansion1 acc)))
    (stv-lines-to-xml (cdr lines) rest-expansions acc)))

(define stv-labels-to-xml ((labels symbol-listp)
                           acc)
  :returns (acc character-listp :hyp (character-listp acc))
  (b* (((when (atom labels))
        acc)
       (acc (str::revappend-chars "<stv_label>" acc))
       (acc (if (car labels)
                (str::revappend-chars (symbol-name (car labels)) acc)
              acc))
       (acc (str::revappend-chars "</stv_label>" acc)))
    (stv-labels-to-xml (cdr labels) acc)))

(define stv-repeat-last-entry ((line true-listp)
                               (nphases natp))
  :returns (new-line true-listp)
  (b* ((line (list-fix line))
       (llen (len line))
       ;; Adding 1 to nphases because the line includes its name, which
       ;; isn't a phase.
       (nphases (+ 1 nphases))
       ((unless (<= llen nphases))
        (er hard? 'stv-repeat-last-entry
            "Number of phases is too small: line ~x0, nphases ~x1" line nphases))
       ((when (= llen nphases))
        line)
       (last-entry (car (last line)))
       (new-tail   (repeat (- nphases llen) last-entry)))
    (append line new-tail)))

(define stv-repeat-last-entries ((lines true-list-listp)
                                 (nphases natp))
  :returns (new-lines true-list-listp)
  (if (atom lines)
      nil
    (cons (stv-repeat-last-entry (car lines) nphases)
          (stv-repeat-last-entries (cdr lines) nphases))))

(define svtv-to-xml ((svtv   svtv-p)
                     (labels symbol-listp))
  :returns (encoding (or (stringp encoding)
                         (not encoding))
                     :rule-classes :type-prescription)
  :short "Top-level routine to generate a nice XML description of an STV."
  :ignore-ok t

  (b* (((svtv svtv))

       (acc nil)
       (acc (str::revappend-chars "<stv>" acc))
       (acc (if labels
                (b* ((acc (str::revappend-chars "<stv_labels>" acc))
                     ;; Initial empty label for above the signals list.
                     (acc (str::revappend-chars "<stv_label></stv_label>" acc))
                     (acc (stv-labels-to-xml labels acc))
                     (acc (str::revappend-chars "</stv_labels>" acc)))
                  acc)
              acc))
       (acc (cons #\Newline acc))

       (acc (str::revappend-chars "<stv_inputs>" acc))
       (acc (cons #\Newline acc))

       ;; Grab the expanded input lines, since they'll have the resolved tilde
       ;; (~) entries.  We don't need to expand the output, internal, or
       ;; override lines.
       (acc (stv-lines-to-xml (stv-repeat-last-entries svtv.orig-ins svtv.nphases)
                              svtv.expanded-ins acc))
       (acc (str::revappend-chars "</stv_inputs>" acc))
       (acc (cons #\Newline acc))

       (acc (str::revappend-chars "<stv_overrides>" acc))
       (acc (cons #\Newline acc))
       (acc (stv-lines-to-xml (stv-repeat-last-entries svtv.orig-overrides svtv.nphases)
                              svtv.expanded-overrides acc))
       (acc (str::revappend-chars "</stv_overrides>" acc))

       (acc (str::revappend-chars "<stv_outputs>" acc))
       (acc (cons #\Newline acc))
       (acc (stv-lines-to-xml (stv-repeat-last-entries svtv.orig-outs svtv.nphases)
                              nil acc))
       (acc (str::revappend-chars "</stv_outputs>" acc))
       (acc (cons #\Newline acc))

       (acc (str::revappend-chars "<stv_internals>" acc))
       (acc (cons #\Newline acc))
       (acc (stv-lines-to-xml (stv-repeat-last-entries svtv.orig-internals svtv.nphases)
                              nil acc))
       (acc (str::revappend-chars "</stv_internals>" acc))
       (acc (cons #\Newline acc))

       (acc (cons #\Newline acc))

       (acc (str::revappend-chars "</stv>" acc)))
    (str::rchars-to-string acc)))

#||
(svtv-to-xml (iu::ius-basic-run) '(l1 l2 l3))
||#
