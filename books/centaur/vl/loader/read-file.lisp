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
(include-book "../util/echars")
(include-book "std/io/base" :dir :system)
(local (include-book "std/io/open-input-channel" :dir :system))
(local (include-book "std/io/read-byte" :dir :system))
(local (include-book "std/io/close-input-channel" :dir :system))
(local (include-book "../util/arithmetic"))
(set-state-ok t)

(local (in-theory (disable acl2::file-measure-of-read-byte$-rw)))

(defsection vl-read-file-aux
  :parents (vl-read-file)
  :short "Main loop for reading characters from a file."

  :long "<p><b>Signature:</b> @(call vl-read-file-aux) returns @('(mv data
state)').</p>

<p>We read bytes from the channel until EOF is encountered, turning them into
characters via ACL2's @('code-char') function.  We remembers the name of the
file, and keeps track of a line and column number, in order to generate the
proper @(see vl-location-p) for each extended character we produced.</p>

<p>This function is tail recursive and accumulates the resulting extended
characters into @('acc').  See @(see vl-read-file-spec) for a non
tail-recursive alternative, which is more useful for reasoning.</p>"

  (defund vl-read-file-aux (channel state filename line col acc)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state)
                                (stringp filename)
                                (posp line)
                                (natp col)
                                (true-listp acc))
                    :measure (file-measure channel state)))
    (b* (((unless (mbt (state-p state)))
          (mv nil state))
         ((mv byte state)
          (read-byte$ channel state))
         ((when (eq byte nil)) ;; EOF
          (mv acc state))
         (char      (code-char (the (unsigned-byte 8) byte)))
         (echar     (make-vl-echar :char char
                                   :loc (vl-location filename line col)))
         (newlinep  (eql char #\Newline))
         (next-line (if newlinep (+ 1 line) line))
         (next-col  (if newlinep 0 (+ 1 col))))
      (vl-read-file-aux channel state filename next-line next-col
                        (cons echar acc)))))



(defsection vl-read-file-spec
  :parents (vl-read-file)
  :short "Logically nice description of reading characters from a file."

  :long "<p>@(call vl-read-file-spec) is a logically nicer description of the
loop performed by @(see vl-read-file-aux).</p>

<p>Note that although the @(':exec') definition is close to what we really use,
we actually optimize this function even more, using @('nreverse').</p>"

  (defund vl-read-file-spec (channel state filename line col)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state)
                                (stringp filename)
                                (posp line)
                                (natp col))
                    :measure (file-measure channel state)
                    :verify-guards nil))
    (mbe :logic
         (b* (((unless (state-p state))
               (mv nil state))
              ((mv byte state)
               (read-byte$ channel state))
              ((when (eq byte nil)) ;; EOF
               (mv nil state))
              (char      (code-char (the (unsigned-byte 8) byte)))
              (echar     (make-vl-echar :char char
                                        :loc (vl-location filename line col)))
              (newlinep  (eql char #\Newline))
              (next-line (if newlinep (+ 1 line) line))
              (next-col  (if newlinep 0 (+ 1 col)))
              ((mv rest state)
               (vl-read-file-spec channel state filename next-line next-col)))
           (mv (cons echar rest) state))
         :exec
         (mv-let (acc state)
                 (vl-read-file-aux channel state filename line col nil)
                 (mv (reverse acc) state))))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (setf (gethash 'vl-read-file-aux ACL2::*never-profile-ht*) t)
   (defun vl-read-file-spec (channel state filename line col)
     (mv-let (acc state)
             (vl-read-file-aux channel state filename line col nil)
             (mv (nreverse acc) state))))
  (defttag nil)

  (local (in-theory (enable vl-read-file-spec
                            vl-read-file-aux)))

  (defthm true-listp-of-vl-read-file-spec
    (true-listp (mv-nth 0 (vl-read-file-spec channel state filename line col)))
    :rule-classes :type-prescription)

  (local (defthm lemma-decompose-aux
           (equal (vl-read-file-aux channel state filename line col acc)
                  (list (mv-nth 0 (vl-read-file-aux channel state filename line col acc))
                        (mv-nth 1 (vl-read-file-aux channel state filename line col acc))))
           :rule-classes nil))

  (local (defthm lemma-decompose-spec
           (equal (vl-read-file-spec channel state filename line col)
                  (list (mv-nth 0 (vl-read-file-spec channel state filename line col))
                        (mv-nth 1 (vl-read-file-spec channel state filename line col))))
           :rule-classes nil))

  (local (defthm lemma-data-equiv
           (implies (and (state-p1 state)
                         (symbolp channel)
                         (open-input-channel-p1 channel :byte state)
                         (true-listp acc))
                    (equal (mv-nth 0 (vl-read-file-aux channel state filename line col acc))
                           (revappend (mv-nth 0 (vl-read-file-spec channel state filename line col))
                                      acc)))))

  (local (defthm lemma-state-equiv
           (equal (mv-nth 1 (vl-read-file-aux channel state filename line col acc))
                  (mv-nth 1 (vl-read-file-spec channel state filename line col)))))

  (local (defthm lemma-equiv
           (implies (and (state-p1 state)
                         (symbolp channel)
                         (open-input-channel-p1 channel :byte state))
                    (equal (vl-read-file-aux channel state filename line col nil)
                           (list
                            (reverse (mv-nth 0 (vl-read-file-spec channel state filename line col)))
                            (mv-nth 1 (vl-read-file-spec channel state filename line col)))))
           :hints(("Goal"
                   :in-theory (disable vl-read-file-aux vl-read-file-spec)
                   :use ((:instance lemma-decompose-aux (acc nil))
                         (:instance lemma-decompose-spec)
                         (:instance lemma-data-equiv (acc nil)))))))


  (verify-guards vl-read-file-spec)

  (defthm vl-read-file-spec-preserves-state
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (state-p1 (mv-nth 1 (vl-read-file-spec channel state filename line col)))))

  (defthm vl-read-file-spec-preserves-open-input-channel-p1
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (open-input-channel-p1 channel :byte
                                    (mv-nth 1 (vl-read-file-spec channel state filename line col)))))

  (defthm vl-echarlist-p-of-vl-read-file-spec
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (stringp filename))
                  (force (posp line))
                  (force (natp col)))
             (vl-echarlist-p (mv-nth 0 (vl-read-file-spec channel state filename line col))))))





(defsection vl-read-file
  :parents (loader)
  :short "Read the entire contents of a file into a list of extended
characters."

  :long "<p><b>Signature:</b> @(call vl-read-file) returns @('(mv result
state)').</p>

<p>This is a low-level function for reading files.  It attempts to read the
file specified by the string @('filename'), and return its contents as a list
of @(see extended-characters).  In the process, each character is annotated
with its location (see @(see vl-location-p)).</p>

<p>If there is an error opening the file, @('result') will be an ACL2 string
indicating that an error has occurred.  <b>BOZO</b> this is a poor way to
handle errors.  We should probably add a @('successp') return value
instead.</p>

<p>We originally styled this function after @('read-file-characters') from the
Unicode library (which, despite being part of the \"Unicode\" library, actually
only reads normal ACL2 characters.)  We later decided to switch to a
@('read-byte$') based approach, because it simply seems more reliable than
@('read-char$').  In particular, the Lisp implementation might be trying to use
Unicode, and we don't want ACL2 to get confused if it sees some odd
character.</p>"

  (defund vl-read-file (filename state)
    (declare (xargs :guard (and (state-p state)
                                (stringp filename))))
    (b* (((mv channel state)
          (open-input-channel filename :byte state))
         ((unless channel)
          (mv "Error opening file." state))
         ((mv data state)
          (vl-read-file-spec channel state filename 1 0))
         (state
          (close-input-channel channel state)))
        (mv data state)))

  (local (in-theory (enable vl-read-file)))

  (defthm vl-read-file-preserves-state
    (implies (and (force (state-p1 state))
                  (force (stringp filename)))
             (state-p1 (mv-nth 1 (vl-read-file filename state)))))

  (defthm vl-echarlist-p-of-vl-read-file-on-success
    (implies (and (not (stringp (mv-nth 0 (vl-read-file filename state))))
                  (force (state-p1 state))
                  (force (stringp filename)))
             (vl-echarlist-p (mv-nth 0 (vl-read-file filename state)))))

  (defthm true-listp-of-vl-read-file-on-success
    (equal (stringp (mv-nth 0 (vl-read-file filename state)))
           (not (true-listp (mv-nth 0 (vl-read-file filename state)))))))

