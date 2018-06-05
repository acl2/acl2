; Standard IO Library
; take-bytes.lisp -- originally part of the Unicode library
; Copyright (C) 2005-2013 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "read-file-bytes")
(include-book "nthcdr-bytes")
(local (include-book "base"))
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(set-state-ok t)

(defsection take-bytes
  :parents (std/io)
  :short "Read the first @('n') bytes from an open file."
  :long "<p>@(call take-bytes) is like @(see take) for an @(':byte') input
channel.  That is, it just reads @('n') bytes and returns them as a list,
and also returns the updated state.</p>"

  (defund take-bytes (n channel state)
    (declare (xargs :guard (and (natp n)
                                (state-p state)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))))
    (b* (((when (zp n))
          (mv nil state))
         ((mv a state)
          (read-byte$ channel state))
         ((mv x state)
          (take-bytes (1- n) channel state)))
      (mv (cons a x) state)))

  (local (in-theory (enable take-bytes nthcdr-bytes)))

  (defthm state-p1-of-take-bytes
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (state-p1 (mv-nth 1 (take-bytes n channel state)))))

  (defthm open-input-channel-p1-of-take-bytes
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (open-input-channel-p1 channel :byte
                                    (mv-nth 1 (take-bytes n channel state)))))

  (defthm mv-nth0-of-take-bytes
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (equal (mv-nth 0 (take-bytes n channel state))
                    (take n (mv-nth 0 (read-byte$-all channel state)))))
    :hints(("Goal"
            :in-theory (enable take-redefinition read-byte$-all repeat)
            :induct (take-bytes n channel state))))

  (defthm mv-nth1-of-take-bytes$
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (equal (mv-nth 1 (take-bytes n channel state))
                    (nthcdr-bytes n channel state)))))
