; Standard IO Library
; read-file-lines-no-newlines.lisp -- a variant of read-file-lines
; Copyright (C) 2005-2013 Kookamara LLC, 2016 Kestrel Technology
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
; Changed by: Eric Smith <eric.smith@kestrel.edu>

(in-package "ACL2")
(include-book "file-measure")
(include-book "std/lists/list-defuns" :dir :system)
(include-book "std/strings/cat" :dir :system)
(local (include-book "base"))
(local (include-book "std/lists/revappend" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))

(defsection read-file-lines-no-newlines-aux
  :parents (read-file-lines-no-newlines)
  :short "Tail recursive implementation of @(see read-file-lines-no-newlines)."
  :long "<p>@(call read-file-lines-no-newlines-aux) returns @('(mv lines state)')
        where @('lines') is in reverse order.</p>
<ul>
<li>@('line') is a character list, the current line in reverse order</li>
<li>@('lines') are a string list, the previously read lines in reverse order</li>
<li>@('channel') is the @(':byte') channel we're reading from</li>
</ul>"

  (defund read-file-lines-no-newlines-aux (line lines channel state)
    (declare (xargs :guard (and (character-listp line)
                                (string-listp lines)
                                (symbolp channel)
                                (open-input-channel-p channel :byte state))
                    :stobjs state
                    :measure (file-measure channel state)))
    (b* (((unless (mbt (state-p state)))
          (mv lines state))
         ((mv byte state)
          (read-byte$ channel state))
         ((unless byte)
          (let ((lines (cons (str::rchars-to-string line) lines)))
            (mv lines state)))
         ((the character char) (code-char (the (unsigned-byte 8) byte))))
        (if (eql char #\Newline)
            (let ((lines (cons (str::rchars-to-string line) lines)))
              (read-file-lines-no-newlines-aux nil ;next line initially empty
                                               lines channel state))
          (let ((line (cons char line)))
            (read-file-lines-no-newlines-aux line lines channel state)))))

  (local (in-theory (enable read-file-lines-no-newlines-aux)))

  (defthm state-p1-of-read-file-lines-no-newlines-aux
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (b* (((mv ?lines state)
                   (read-file-lines-no-newlines-aux line lines channel state)))
               (state-p1 state))))

  (defthm open-input-channel-p1-of-read-file-lines-no-newlines-aux
    (implies (and (force (state-p1 state))
                  (force (symbolp channel))
                  (force (open-input-channel-p1 channel :byte state)))
             (b* (((mv ?lines state)
                   (read-file-lines-no-newlines-aux line lines channel state)))
               (open-input-channel-p1 channel :byte state))))

  (defthm string-listp-of-read-file-lines-no-newlines-aux
    (implies (force (string-listp lines))
             (string-listp
              (mv-nth 0 (read-file-lines-no-newlines-aux line lines channel state)))))

  (defthm true-listp-of-read-file-lines-no-newlines-aux
    (equal (true-listp (mv-nth 0 (read-file-lines-no-newlines-aux line lines channel state)))
           (true-listp lines))))



(defsection read-file-lines-no-newlines
  :parents (std/io)
  :short "Read an entire file into a list of lines (strings), omitting
  newline characters from the resuting strings"
  :long "<p><b>Signature:</b> @(call read-file-lines-no-newlines) returns @('(mv contents state)').</p>

<p>On success, @('contents') is a @(see string-listp) that contains each line
of the file, with all newline characters removed (unlike @(see read-file-lines)).  A
line of the file that contains only a newline character will be represented by an
empty string in this list.</p>

<p>On failure, e.g., perhaps @('filename') does not exist, @('contents') will
be a @(see stringp) saying that we failed to open the file.</p>

<p><b>BOZO</b> This currently just looks for individual newline characters,
i.e., @('#\\Newline'), sometimes called @('\\n').  It might be desirable to
change how it works to somehow support @('\\r\\n') or whatever other
carriage-return stuff people use on platforms like Windows.</p>"

  (defund read-file-lines-no-newlines (filename state)
    "Returns (MV ERRMSG/LINES STATE)"
    (declare (xargs :guard (stringp filename)
                    :stobjs state))
    (b* ((filename (mbe :logic (if (stringp filename) filename "")
                        :exec filename))
         ((mv channel state)
          (open-input-channel filename :byte state))
         ((unless channel)
          (mv (concatenate 'string "Error opening file " filename) state))
         ((mv data state)
          (read-file-lines-no-newlines-aux nil nil channel state))
         (state (close-input-channel channel state)))
      (mv (reverse data) state)))

  (local (in-theory (enable read-file-lines-no-newlines)))

  (defthm state-p1-of-read-file-lines-no-newlines
    (implies (force (state-p1 state))
             (state-p1 (mv-nth 1 (read-file-lines-no-newlines filename state)))))

  (local (defthm crock
           (implies (string-listp x)
                    (string-listp (rev x)))))

  (defthm string-listp-of-read-file-lines-no-newlines
    (equal (string-listp (mv-nth 0 (read-file-lines-no-newlines filename state)))
           (not (stringp (mv-nth 0 (read-file-lines-no-newlines filename state)))))))
