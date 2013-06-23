; Standard IO Library
; read-file-characters.lisp -- originally part of the Unicode library
; Copyright (C) 2005-2013 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.

(in-package "ACL2")
(include-book "file-measure")
(include-book "std/lists/list-defuns" :dir :system)
(include-book "str/char-fix" :dir :system)
(local (include-book "base"))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(set-state-ok t)

(defsection read-char$-all
  :parents (read-file-characters)
  :short "@(call read-char$-all) reads all remaining characters from a file."

  :long "<p>This is the main loop inside @(see read-file-characters).  It reads
everything in the file, but doesn't handle opening or closing the file.</p>"

  (defund tr-read-char$-all (channel state acc)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :character state))
                    :measure (file-measure channel state)))
    (b* (((unless (mbt (state-p state)))
          (mv acc state))
         ((mv char state) (read-char$ channel state))
         ((unless char)
          (mv acc state))
         (acc (cons (mbe :logic (str::char-fix char) :exec char) acc)))
      (tr-read-char$-all channel state acc)))

  (defund read-char$-all (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :character state))
                    :measure (file-measure channel state)
                    :verify-guards nil))
    (mbe :logic
         (b* (((unless (state-p state))
               (mv nil state))
              ((mv char state) (read-char$ channel state))
              ((unless char)
               (mv nil state))
              ((mv rest state) (read-char$-all channel state)))
           (mv (cons (str::char-fix char) rest) state))
         :exec
         (b* (((mv contents state)
               (tr-read-char$-all channel state nil)))
           (mv (reverse contents) state))))

  (local (in-theory (enable tr-read-char$-all
                            read-char$-all)))

  (local (defthm lemma-decompose-impl
           (equal (tr-read-char$-all channel state acc)
                  (list (mv-nth 0 (tr-read-char$-all channel state acc))
                        (mv-nth 1 (tr-read-char$-all channel state acc))))
           :rule-classes nil))

  (local (defthm lemma-decompose-spec
           (equal (read-char$-all channel state)
                  (list (mv-nth 0 (read-char$-all channel state))
                        (mv-nth 1 (read-char$-all channel state))))
           :rule-classes nil))

  (local (defthm lemma-data-equiv
           (equal (mv-nth 0 (tr-read-char$-all channel state acc))
                  (revappend (mv-nth 0 (read-char$-all channel state)) acc))))

  (local (defthm lemma-state-equiv
           (equal (mv-nth 1 (tr-read-char$-all channel state acc))
                  (mv-nth 1 (read-char$-all channel state)))))

  (defthm true-listp-of-read-char$-all
    (true-listp (mv-nth 0 (read-char$-all channel state)))
    :rule-classes :type-prescription)

  (defthm tr-read-char$-all-removal
    (equal (tr-read-char$-all channel state nil)
           (mv (rev (mv-nth 0 (read-char$-all channel state)))
               (mv-nth 1 (read-char$-all channel state))))
    :hints(("Goal" :in-theory (disable tr-read-char$-all read-char$-all)
            :use ((:instance lemma-decompose-impl (acc nil))
                  (:instance lemma-decompose-spec)
                  (:instance lemma-data-equiv (acc nil))))))

  (verify-guards read-char$-all)

  (defthm state-p1-of-read-char$-all
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :character state)))
             (state-p1 (mv-nth 1 (read-char$-all channel state)))))

  (defthm open-input-channel-p1-of-read-char$-all
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :character state)))
             (open-input-channel-p1 channel
                                    :character
                                    (mv-nth 1 (read-char$-all channel state)))))

  (defthm character-listp-of-read-char$-all
    (character-listp (mv-nth 0 (read-char$-all channel state)))))



(defsection read-file-characters
  :parents (std/io)
  :short "Read an entire file into a @(see character-listp)."

  :long "<p><b>Signature:</b> @(call read-file-characters) returns @('(mv contents state)').</p>

<p>On success, @('contents') is a @(see character-listp) that contains all of
the characters in the file.</p>

<p>On failure, e.g., perhaps @('filename') does not exist, @('contents') will
be a @(see stringp) saying that we failed to open the file.</p>"

  (defund read-file-characters (filename state)
    "Returns (MV ERRMSG/CHARS STATE)"
    (declare (xargs :guard (and (state-p state)
                                (stringp filename))))
    (b* ((filename (mbe :logic (if (stringp filename) filename "")
                        :exec filename))
         ((mv channel state)
          (open-input-channel filename :character state))
         ((unless channel)
          (mv (concatenate 'string "Error opening file " filename) state))
         ((mv contents state)
          (read-char$-all channel state))
         (state (close-input-channel channel state)))
      (mv contents state)))

  (local (in-theory (enable read-file-characters)))

  (defthm state-p1-of-read-file-characters
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (read-file-characters filename state)))))

  (defthm character-listp-of-read-file-characters
    (let ((contents (mv-nth 0 (read-file-characters filename state))))
      (equal (character-listp contents)
             (not (stringp contents)))))

  (defthm type-of-read-file-characters
    (or (true-listp (mv-nth 0 (read-file-characters filename state)))
        (stringp (mv-nth 0 (read-file-characters filename state))))
    :rule-classes :type-prescription))


(defsection read-file-characters-rev
  :parents (std/io)
  :short "Read an entire file into a @(see character-listp), but in reverse
order!"

  :long "<p>This goofy function is just like @(see read-file-characters) except
that the characters are returned in reverse.</p>

<p>This is faster than read-file-characters because we avoid the cost of
reversing the accumulator, and thus require half as many conses.</p>

<p>Note: that we just leave this function enabled.  Logically it's just the
reverse of @(see read-file-characters).</p>"

  (local (in-theory (enable read-file-characters)))

  (defun read-file-characters-rev (filename state)
    (declare (xargs :guard (and (state-p state)
                                (stringp filename))))
    (mbe :logic
         (b* (((mv contents state)
               (read-file-characters filename state)))
           (if (stringp contents)
               ;; Error reading file
               (mv contents state)
             (mv (rev contents) state)))
         :exec
         (b* (((mv channel state)
               (open-input-channel filename :character state))
              ((unless channel)
               (mv (concatenate 'string "Error opening file " filename) state))
              ((mv contents state)
               (tr-read-char$-all channel state nil))
              (state (close-input-channel channel state)))
           (mv contents state)))))

