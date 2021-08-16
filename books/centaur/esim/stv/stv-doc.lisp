; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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


; stv-doc.lisp -- documentation generation for STVs
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "stv-widen")
(include-book "std/strings/stringify" :dir :system)
(include-book "centaur/vl2014/util/print-htmlencode" :dir :system)
(local (include-book "std/typed-lists/character-listp" :dir :system))
(local (include-book "std/strings/explode-nonnegative-integer" :dir :system))

(defsection stv-doc
  :parents (symbolic-test-vectors)
  :short "Automatic documentation support for symbolic test vectors."

  :long "<p>Symbolic test vectors are integrated into @(see xdoc) so that you
can generate attractive explanations of your setup.  This is often useful when
communicating with logic designers.</p>

<p><b>NOTE</b>: the topics here cover how we generate this documentation.  If
you just want to document your own STVs, you don't need to know about any of
this&mdash;just give a @(':parents'), @(':short'), or @(':long') argument to
@(see defstv).</p>

<p>These functions don't do much error checking.  We expect that we only are
going to generate documentation after successfully processing the STV, so we
generally just expect things to be well-formed at this point.</p>

<p>The XML we generate is not documented in @(see xdoc)'s @(see xdoc::markup),
and is not supported by tools like @(':xdoc').  How these new tags get rendered
into HTML is controlled by, e.g., @('xdoc/fancy/render.xsl').</p>")


(local (defthm natp-of-vl-html-encode-string-aux
         (natp (mv-nth 0 (vl2014::VL-HTML-ENCODE-STRING-AUX X N XL COL TABSIZE ACC)))
         :rule-classes :type-prescription))

(local (defthm character-listp-of-vl-html-encode-string-aux
         (implies (character-listp acc)
                  (character-listp (mv-nth 1 (vl2014::VL-HTML-ENCODE-STRING-AUX X N XL COL TABSIZE ACC))))))

(local (in-theory (disable vl2014::vl-html-encode-string-aux)))

(define stv-name-bits-to-xml ((bits true-listp)
                              (col  natp)
                              acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :parents (stv-doc)
  :short "Encode the name of an STV line, when the name is a list of E bits."
  :long "<p>This is really horrible, but it doesn't matter since nobody would
ever actually use a list of E bits to name their input.</p>"
  (b* (((when (atom bits))
        acc)
       ;; Print the name of this bit
       (name1 (stringify (car bits)))
       ((mv col acc)
        (vl2014::vl-html-encode-string-aux name1 0 (length name1) (lnfix col) 8 acc))
       ;; Print ", " if there are more bits.
       ((mv col acc)
        (if (atom (cdr bits))
            (mv col acc)
          (mv (+ col 2) (list* #\Space #\, acc)))))
    ;; Print the rest of the bit names.
    (stv-name-bits-to-xml (cdr bits) col acc)))

(define stv-name-to-xml (name acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :parents (stv-doc)
  :short "Encode the name of an STV line."
  (cond ((stringp name)
         ;; It already looks like a Verilog name, so this is easy enough.
         (b* (((mv ?col acc)
               (vl2014::vl-html-encode-string-aux name 0 (length name) 0 8 acc)))
           acc))
        ((true-listp name)
         ;; probably awful
         (b* ((acc (cons #\{ acc))
              (acc (stv-name-bits-to-xml name 1 acc))
              (acc (cons #\} acc)))
           acc))
        (t
         (raise "Bad name for stv line: ~x0." name))))

(define stv-entry-to-xml ((entry     "The value that the user gave, originally.")
                          (expansion "Its expanded out value, a sexpr list.")
                          acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :parents (stv-doc)
  :short "Encode a single value from an STV line."
  (cond ((natp entry)
         (if (< entry 10)
             ;; As a special nicety, write values under 10 without any
             ;; leading prefixes.
             (revappend (str::nat-to-dec-chars entry) acc)
           ;; For any larger constants, write them in hex.  I'll use a 0x
           ;; prefix instead of a #x prefix, since it's probably more widely
           ;; understood (e.g., by logic designers)
           (let* ((pound-x-hex-digits (explode-atom+ entry 16 t))           ;; #x1000
                  (zero-x-hex-digits  (cons #\0 (cdr pound-x-hex-digits)))) ;; 0x1000
             (revappend zero-x-hex-digits acc))))

        ((eq entry 'x)
         (cons #\X acc))

        ((eq entry :ones)
         ;; BOZO maybe want to take the width and expand this out into the
         ;; actual constant we're using?
         (str::revappend-chars "<i>ones</i>" acc))

        ((eq entry '~)
         (cond ((equal expansion (list *4vt-sexpr*))
                (cons #\1 acc))
               ((equal expansion (list *4vf-sexpr*))
                (cons #\0 acc))
               (t
                (progn$ (raise "Expansion of ~ should be 1 or 0.")
                        acc))))

        ((eq entry '_)
         ;; Just skipping these seems nicest.
         acc)

        ((symbolp entry)
         (b* ((acc (str::revappend-chars "<b>" acc))
              ((mv ?col acc)
               (vl2014::vl-html-encode-string-aux (symbol-name entry) 0
                                              (length (symbol-name entry))
                                              0 8 acc))
              (acc (str::revappend-chars "</b>" acc)))
           acc))

        (t
         (raise "Bad entry in stv line: ~x0." entry))))

(define stv-entries-to-xml ((entries "The original entries for this line.")
                            (expansions "The expanded entries for this line."
                                        true-listp)
                            acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :parents (stv-doc)
  :short "Encode all the values from an STV line."
  (b* (((when (atom entries))
        acc)
       (acc (str::revappend-chars "<stv_entry>" acc))
       (acc (stv-entry-to-xml (car entries) (car expansions) acc))
       (acc (str::revappend-chars "</stv_entry>" acc)))
    (stv-entries-to-xml (cdr entries) (cdr expansions) acc)))

(define stv-line-to-xml
  ((line      "Original line, with name, given by the user."
              true-listp)
   (expansion "Fully expanded line, with name, after STV processing"
              true-listp)
   acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :parents (stv-doc)
  :short "Encode one full line from the STV into XML for XDOC."
  (b* ((acc (str::revappend-chars "<stv_line>" acc))
       (acc (str::revappend-chars "<stv_name>" acc))
       (acc (stv-name-to-xml (car line) acc))
       (acc (str::revappend-chars "</stv_name>" acc))
       (acc (stv-entries-to-xml (cdr line) (cdr expansion) acc))
       (acc (str::revappend-chars "</stv_line>" acc))
       (acc (cons #\Newline acc)))
    acc))

(define stv-lines-to-xml ((lines      true-list-listp)
                          (expansions true-list-listp)
                          acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :parents (stv-doc)
  (b* (((when (atom lines))
        acc)
       (acc (stv-line-to-xml (car lines) (car expansions) acc)))
    (stv-lines-to-xml (cdr lines) (cdr expansions) acc)))

(define stv-labels-to-xml ((labels symbol-listp)
                           acc)
  :returns (acc character-listp :hyp (character-listp acc))
  :parents (stv-doc)
  (b* (((when (atom labels))
        acc)
       (acc (str::revappend-chars "<stv_label>" acc))
       (acc (if (car labels)
                (str::revappend-chars (symbol-name (car labels)) acc)
              acc))
       (acc (str::revappend-chars "</stv_label>" acc)))
    (stv-labels-to-xml (cdr labels) acc)))

(define stv-to-xml ((stv    stvdata-p)
                    (cstv   compiled-stv-p)
                    (labels symbol-listp))
  :returns (encoding (or (stringp encoding)
                         (not encoding))
                     :rule-classes :type-prescription)
  :parents (stv-doc)
  :short "Top-level routine to generate a nice XML description of an STV."

  (b* (;; Widen all the lines so the table will be filled.
       (stv        (stv-widen stv))
       ((stvdata stv) stv)

       ;; Grab the expanded input lines, since they'll have the resolved tilde
       ;; (~) entries.  We don't need to expand the output, internal, or
       ;; override lines.
       (ex-ins  (compiled-stv->expanded-ins cstv))
       ((unless (true-list-listp ex-ins))
        (raise "Expanded inputs aren't a true-list-listp?"))

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
       (acc (stv-lines-to-xml stv.inputs ex-ins acc))
       (acc (str::revappend-chars "</stv_inputs>" acc))
       (acc (cons #\Newline acc))

       (acc (str::revappend-chars "<stv_outputs>" acc))
       (acc (cons #\Newline acc))
       (acc (stv-lines-to-xml stv.outputs nil acc))
       (acc (str::revappend-chars "</stv_outputs>" acc))
       (acc (cons #\Newline acc))

       (acc (str::revappend-chars "<stv_internals>" acc))
       (acc (cons #\Newline acc))
       (acc (stv-lines-to-xml stv.internals nil acc))
       (acc (str::revappend-chars "</stv_internals>" acc))
       (acc (cons #\Newline acc))

       (acc (str::revappend-chars "<stv_overrides>" acc))
       (acc (cons #\Newline acc))
       (acc (stv-lines-to-xml stv.overrides nil acc))
       (acc (str::revappend-chars "</stv_overrides>" acc))
       (acc (cons #\Newline acc))

       (acc (str::revappend-chars "</stv>" acc)))
    (str::rchars-to-string acc)))
