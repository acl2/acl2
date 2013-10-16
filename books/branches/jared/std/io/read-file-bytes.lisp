; Standard IO Library
; read-file-bytes.lisp -- originally part of the Unicode library
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
(include-book "std/typed-lists/unsigned-byte-listp" :dir :system)
(local (include-book "base"))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(set-state-ok t)


(defsection read-byte$-all
  :parents (read-file-bytes)
  :short "@(call read-byte$-all) reads all remaining bytes from a file."

  :long "<p>This is the main loop inside @(see read-file-bytes).  It reads
everything in the file, but doesn't handle opening or closing the file.</p>"

  (defund tr-read-byte$-all (channel state acc)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))
                    :measure (file-measure channel state)))
    (b* (((unless (mbt (state-p state)))
          (mv acc state))
         ((mv byte state) (read-byte$ channel state))
         ((unless byte)
          (mv acc state))
         (acc (cons (mbe :logic (if (unsigned-byte-p 8 byte)
                                    byte
                                  0)
                         :exec byte)
                    acc)))
      (tr-read-byte$-all channel state acc)))

  (defund read-byte$-all (channel state)
    (declare (xargs :guard (and (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))
                    :measure (file-measure channel state)
                    :verify-guards nil))
    (mbe :logic
         (b* (((unless (state-p state))
               (mv nil state))
              ((mv byte state) (read-byte$ channel state))
              ((unless byte)
               (mv nil state))
              ((mv rest state) (read-byte$-all channel state))
              (byte (if (unsigned-byte-p 8 byte) byte 0)))
           (mv (cons byte rest) state))
         :exec
         (b* (((mv contents state)
               (tr-read-byte$-all channel state nil)))
           (mv (reverse contents) state))))

  (local (in-theory (enable tr-read-byte$-all
                            read-byte$-all)))

  (local (defthm lemma-decompose-impl
           (equal (tr-read-byte$-all channel state acc)
                  (list (mv-nth 0 (tr-read-byte$-all channel state acc))
                        (mv-nth 1 (tr-read-byte$-all channel state acc))))
           :rule-classes nil))

  (local (defthm lemma-decompose-spec
           (equal (read-byte$-all channel state)
                  (list (mv-nth 0 (read-byte$-all channel state))
                        (mv-nth 1 (read-byte$-all channel state))))
           :rule-classes nil))

  (local (defthm lemma-data-equiv
           (equal (mv-nth 0 (tr-read-byte$-all channel state acc))
                  (revappend (mv-nth 0 (read-byte$-all channel state)) acc))))

  (local (defthm lemma-state-equiv
           (equal (mv-nth 1 (tr-read-byte$-all channel state acc))
                  (mv-nth 1 (read-byte$-all channel state)))))

  (defthm tr-read-byte$-all-removal
    (equal (tr-read-byte$-all channel state nil)
           (mv (rev (mv-nth 0 (read-byte$-all channel state)))
               (mv-nth 1 (read-byte$-all channel state))))
    :hints(("Goal" :in-theory (disable tr-read-byte$-all read-byte$-all)
            :use ((:instance lemma-decompose-impl (acc nil))
                  (:instance lemma-decompose-spec)
                  (:instance lemma-data-equiv (acc nil))))))

  (defthm true-listp-of-read-byte$-all
    (true-listp (mv-nth 0 (read-byte$-all channel state)))
    :rule-classes :type-prescription)

  (verify-guards read-byte$-all)

  (defthm state-p1-of-read-byte$-all
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (state-p1 (mv-nth 1 (read-byte$-all channel state)))))

  (defthm open-input-channel-p1-of-read-byte$-all
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (open-input-channel-p1 channel :byte
                                    (mv-nth 1 (read-byte$-all channel state)))))

  (defthm integer-listp-of-read-byte$-all
    (integer-listp (mv-nth 0 (read-byte$-all channel state))))

  (defthm nat-listp-of-read-byte$-all
    (nat-listp (mv-nth 0 (read-byte$-all channel state))))

  (defthm unsigned-byte-listp-of-read-byte$-all
    (unsigned-byte-listp 8 (mv-nth 0 (read-byte$-all channel state)))))






(defsection read-file-bytes
  :parents (std/io)
  :short "Read an entire file into a list of (unsigned) bytes."

  :long "<p><b>Signature:</b> @(call read-file-bytes) returns @('(mv contents
state)').</p>

<p>On success, @('contents') is a list of bytes, 0-255, which captures the
contents of the file.</p>

<p>On failure, e.g., perhaps @('filename') does not exist, @('contents') will
be a @(see stringp) saying that we failed to open the file.</p>"

  (defund read-file-bytes (filename state)
    "Returns (MV ERRMSG/BYTES STATE)"
    (declare (xargs :guard (and (state-p state)
                                (stringp filename))))
    (b* ((filename (mbe :logic (if (stringp filename) filename "")
                        :exec filename))
         ((mv channel state)
          (open-input-channel filename :byte state))
         ((unless channel)
          (mv (concatenate 'string "Error opening file " filename)
              state))
         ((mv data state)
          (read-byte$-all channel state))
         (state (close-input-channel channel state)))
      (mv data state)))

  (local (in-theory (enable read-file-bytes)))

  (defthm state-p1-of-read-file-bytes
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (read-file-bytes filename state)))))

  (defthm integer-listp-of-read-file-bytes
    (equal (integer-listp (mv-nth 0 (read-file-bytes filename state)))
           (not (stringp (mv-nth 0 (read-file-bytes filename state))))))

  (defthm nat-listp-of-read-file-bytes
    (equal (nat-listp (mv-nth 0 (read-file-bytes filename state)))
           (not (stringp (mv-nth 0 (read-file-bytes filename state))))))

  (defthm unsigned-byte-listp-of-read-file-bytes
    (equal (unsigned-byte-listp 8 (mv-nth 0 (read-file-bytes filename state)))
           (not (stringp (mv-nth 0 (read-file-bytes filename state))))))

  (defthm type-of-read-file-bytes
    (or (true-listp (mv-nth 0 (read-file-bytes filename state)))
        (stringp (mv-nth 0 (read-file-bytes filename state))))
    :rule-classes :type-prescription))

