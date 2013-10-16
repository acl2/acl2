; Standard IO Library
; nthcdr-bytes.lisp -- originally part of the Unicode library
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
(include-book "read-file-bytes")
(local (include-book "base"))
(local (include-book "tools/mv-nth" :dir :system))
(set-state-ok t)

(defsection nthcdr-bytes
  :parents (std/io)
  :short "Skip past some number of bytes in an open file."
  :long "<p>@(call nthcdr-bytes) is like @(see nthcdr) for an @(':byte') input
channel.  That is, it just reads @('n') bytes and ignores them, returning the
updated state.</p>

<p>This is notably useful as a way to express the post-state after @(see
take-bytes).</p>"

  (defund nthcdr-bytes (n channel state)
    (declare (xargs :guard (and (natp n)
                                (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((when (zp n))
          state)
         ((mv ?byte state)
          (read-byte$ channel state)))
      (nthcdr-bytes (- n 1) channel state)))

  (local (in-theory (enable nthcdr-bytes)))

  (defthm state-p1-of-nthcdr-bytes
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (state-p1 (nthcdr-bytes n channel state)))
    :hints(("Goal" :in-theory (enable nthcdr-bytes))))

  (defthm open-input-channel-p1-of-nthcdr-bytes
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (open-input-channel-p1 channel :byte (nthcdr-bytes n channel state)))
    :hints(("Goal" :in-theory (enable nthcdr-bytes))))

  (defthm read-byte$-all-of-nthcdr-bytes
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (equal (mv-nth 0 (read-byte$-all channel (nthcdr-bytes n channel state)))
                    (nthcdr n (mv-nth 0 (read-byte$-all channel state)))))
    :hints(("Goal"
            :in-theory (enable nthcdr-bytes nthcdr read-byte$-all)
            :induct (nthcdr-bytes n channel state))))

  ;; BOZO these are really hideous!

  (defthm nthcdr-bytes-1
    (equal (nthcdr-bytes 1 channel state)
           (mv-nth 1 (read-byte$ channel state)))
    :hints(("Goal"
            :in-theory (enable nthcdr-bytes)
            :expand ((nthcdr-bytes 1 channel state)))))

  (defthm nthcdr-bytes-2
    (equal (nthcdr-bytes 2 channel state)
           (mv-nth 1 (read-byte$ channel
                                 (mv-nth 1 (read-byte$ channel state)))))
    :hints(("Goal" :in-theory (enable nthcdr-bytes))))

  (defthm nthcdr-bytes-3
    (equal (nthcdr-bytes 3 channel state)
           (mv-nth 1 (read-byte$
                      channel
                      (mv-nth 1 (read-byte$
                                 channel
                                 (mv-nth 1 (read-byte$ channel state)))))))
    :hints(("Goal" :in-theory (enable nthcdr-bytes))))

  (defthm nthcdr-bytes-4
    (equal (nthcdr-bytes 4 channel state)
           (mv-nth 1 (read-byte$
                      channel
                      (mv-nth 1 (read-byte$
                                 channel
                                 (mv-nth 1 (read-byte$
                                            channel
                                            (mv-nth 1 (read-byte$ channel state)))))))))
    :hints(("Goal" :in-theory (enable nthcdr-bytes))))

  (defthm nthcdr-bytes-measure-weak
    (implies (and (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (<= (file-measure channel (nthcdr-bytes n channel state))
                 (file-measure channel state)))
    :rule-classes (:rewrite :linear)
    :hints(("Goal" :in-theory (enable nthcdr-bytes))))

  (defthm nthcdr-bytes-measure-strong
    (implies (and (mv-nth 0 (read-byte$ channel state))
                  (not (zp n))
                  (force (state-p1 state))
                  (force (open-input-channel-p1 channel :byte state))
                  (force (symbolp channel)))
             (< (file-measure channel (nthcdr-bytes n channel state))
                (file-measure channel state)))
    :rule-classes (:rewrite :linear)
    :hints(("Goal" :in-theory (enable nthcdr-bytes)))))
