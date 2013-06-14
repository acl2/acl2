; ESIM Symbolic Hardware Simulator
; Copyright (C) 2010-2012 Centaur Technology
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


; stv-doc.lisp -- documentation generation for STVs
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "stv-util")
(include-book "stv-widen")
(include-book "str/stringify" :dir :system)
(include-book "centaur/vl/util/print-htmlencode" :dir :system)
(local (include-book "std/typed-lists/character-listp" :dir :system))

(defund stv-name-bits-to-xml (bits col acc)
  ;; Probably horrible way to print out individual bits, if the user writes that
  ;; sort of thing
  (declare (xargs :guard (and (true-listp bits)
                              (natp col))))
  (b* (((when (atom bits))
        acc)
       ;; Print the name of this bit
       (name1 (stringify (car bits)))
       ((mv col acc)
        (vl::vl-html-encode-string-aux name1 0 (length name1) col 8 acc))
       ;; Print ", " if there are more bits.
       ((mv col acc)
        (if (atom (cdr bits))
            (mv col acc)
          (mv (+ col 2) (list* #\Space #\, acc)))))
    ;; Print the rest of the bit names.
    (stv-name-bits-to-xml (cdr bits) col acc)))

(defthm character-listp-of-stv-name-bits-to-xml
  (implies (and (character-listp acc)
                (natp col))
           (character-listp (stv-name-bits-to-xml bits col acc)))
  :hints(("Goal" :in-theory (enable stv-name-bits-to-xml))))

(defund stv-name-to-xml (name acc)
  (declare (xargs :guard t))
  (cond ((stringp name)
         ;; It already looks like a Verilog name, so this is easy enough.
         (b* (((mv ?col acc)
               (vl::vl-html-encode-string-aux name 0 (length name) 0 8 acc)))
           acc))
        ((true-listp name)
         ;; probably awful
         (b* ((acc (cons #\{ acc))
              (acc (stv-name-bits-to-xml name 1 acc))
              (acc (cons #\} acc)))
           acc))
        (t
         (er hard? 'stv-name-to-xml "Bad name for stv line: ~x0." name))))

(defthm character-listp-of-stv-name-to-xml
  (implies (character-listp acc)
           (character-listp (stv-name-to-xml name acc)))
  :hints(("Goal" :in-theory (enable stv-name-to-xml))))

(defund stv-entry-to-xml (entry expansion acc)
  (declare (xargs :guard t))
  (cond ((natp entry)
         (if (< entry 10)
             ;; As a special nicety, write values under 10 without any
             ;; leading prefixes.
             (revappend (str::natchars entry) acc)
           ;; For any larger constants, write them in hex.  I'll use a 0x
           ;; prefix instead of a #x prefix, since it's probably more widely
           ;; understood.
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
                (progn$ (er hard? 'stv-entry-to-xml "Expansion of ~ should be 1 or 0.")
                        acc))))

        ((eq entry '_)
         ;; Just skipping these seems nicest.
         acc)

        ((symbolp entry)
         (b* ((acc (str::revappend-chars "<b>" acc))
              ((mv ?col acc)
               (vl::vl-html-encode-string-aux (symbol-name entry) 0
                                              (length (symbol-name entry))
                                              0 8 acc))
              (acc (str::revappend-chars "</b>" acc)))
           acc))

        (t
         (er hard? 'stv-entry-to-xml
             "Bad entry in stv line: ~x0." entry))))

(defthm character-listp-of-stv-entry-to-xml
  (implies (character-listp acc)
           (character-listp (stv-entry-to-xml entry expansion acc)))
  :hints(("Goal" :in-theory (enable stv-entry-to-xml))))

(defund stv-entries-to-xml (entries expansions acc)
  (declare (xargs :guard (true-listp expansions)))
  (b* (((when (atom entries))
        acc)
       (acc (str::revappend-chars "<stv_entry>" acc))
       (acc (stv-entry-to-xml (car entries) (car expansions) acc))
       (acc (str::revappend-chars "</stv_entry>" acc)))
    (stv-entries-to-xml (cdr entries) (cdr expansions) acc)))

(defthm character-listp-of-stv-entries-to-xml
  (implies (character-listp acc)
           (character-listp (stv-entries-to-xml entries expansions acc)))
  :hints(("Goal" :in-theory (enable stv-entries-to-xml))))

(defund stv-line-to-xml (line expansion acc)
  (declare (xargs :guard (and (true-listp line)
                              (true-listp expansion))))
  (b* ((acc (str::revappend-chars "<stv_line>" acc))
       (acc (str::revappend-chars "<stv_name>" acc))
       (acc (stv-name-to-xml (car line) acc))
       (acc (str::revappend-chars "</stv_name>" acc))
       (acc (stv-entries-to-xml (cdr line) (cdr expansion) acc))
       (acc (str::revappend-chars "</stv_line>" acc))
       (acc (cons #\Newline acc)))
    acc))

(defthm character-listp-of-stv-line-to-xml
  (implies (character-listp acc)
           (character-listp (stv-line-to-xml line expansion acc)))
  :hints(("Goal" :in-theory (enable stv-line-to-xml))))

(defund stv-lines-to-xml (lines expansions acc)
  (declare (xargs :guard (and (true-list-listp lines)
                              (true-list-listp expansions))))
  (b* (((when (atom lines))
        acc)
       (acc (stv-line-to-xml (car lines) (car expansions) acc)))
    (stv-lines-to-xml (cdr lines) (cdr expansions) acc)))

(defthm character-listp-of-stv-lines-to-xml
  (implies (character-listp acc)
           (character-listp (stv-lines-to-xml lines expansions acc)))
  :hints(("Goal" :in-theory (enable stv-lines-to-xml))))


(defund stv-labels-to-xml (labels acc)
  (declare (xargs :guard (symbol-listp labels)))
  (b* (((when (atom labels))
        acc)
       (acc (str::revappend-chars "<stv_label>" acc))
       (acc (if (car labels)
                (str::revappend-chars (symbol-name (car labels)) acc)
              acc))
       (acc (str::revappend-chars "</stv_label>" acc)))
    (stv-labels-to-xml (cdr labels) acc)))

(defthm character-listp-of-stv-labels-to-xml
  (implies (character-listp acc)
           (character-listp (stv-labels-to-xml labels acc)))
  :hints(("Goal" :in-theory (enable stv-labels-to-xml))))



(defund stv-to-xml (stv cstv labels)
  (declare (xargs :guard (and (stvdata-p stv)
                              (compiled-stv-p cstv)
                              (symbol-listp labels))))
  (b* (;; Widen all the lines so the table will be filled.
       (stv        (stv-widen stv))
       ((stvdata stv) stv)

       ;; Grab the expanded input lines, since they'll have the resolved tilde
       ;; (~) entries.  We don't need to expand the output or internal lines.
       (ex-ins    (compiled-stv->expanded-ins cstv))
       ((unless (true-list-listp ex-ins))
        (er hard? 'stv-to-xml "Expanded inputs aren't a true-list-listp?"))

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

       (acc (str::revappend-chars "<stv_initials>" acc))
       (acc (cons #\Newline acc))
       (acc (stv-lines-to-xml stv.initial nil acc))
       (acc (str::revappend-chars "</stv_initials>" acc))
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

       (acc (str::revappend-chars "</stv>" acc)))
    (reverse (coerce acc 'string))))

(defthm stringp-of-stv-to-xml
  (or (stringp (stv-to-xml stv expansion labels))
      (not (stv-to-xml stv expansion labels)))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable stv-to-xml))))


