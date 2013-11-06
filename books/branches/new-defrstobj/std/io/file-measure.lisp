; Standard IO Library
; file-measure.lisp -- originally part of the Unicode library
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
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; History.  Jared wrote an initial version of this function for the Unicode
; books.  Sol then extended it with a hack that allows us to prove it
; decreasing without assuming state-p1 in the object case.  (Really it's just a
; workaround for the fact that read-object checks (cdr entry) as a substitute
; for (consp (cdr entry)) to find whether there are objects remaining.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(local (include-book "system/f-put-global" :dir :system))

(defsection file-measure
  :parents (std/io)
  :short "A measure for admitting functions that read from files."

  :long "<p><b>Signature:</b> @(call file-measure) returns a natural
number.</p>

<ul>

<li>@('channel') may be any symbol but is typically an open input channel.</li>

<li>@('state-state') is typically the ACL2 @(see state).</li>

</ul>

<p>This is a @(see logic)-mode function, but its logical definition is tricky;
see @(see logical-story-of-io).  The basic gist is that it returns how many
objects are left in the channel and hence how many functions can still be
read.</p>

<p>This function is only meant to be used to admit functions, and cannot be
executed on the real ACL2 @(see state).</p>"

  (defun file-measure (channel state-state)
    (declare (xargs :guard (and (symbolp channel)
                                (state-p1 state-state))))
    (+ (len (cddr (assoc-equal channel (open-input-channels state-state))))
       (if (consp (cddr (assoc-equal channel (open-input-channels state-state))))
           (if (cdr (last (cddr (assoc-equal channel (open-input-channels
                                                      state-state))))) 1 0)
         (if (cddr (assoc-equal channel (open-input-channels state-state))) 1 0))))

  (defthm file-measure-of-read-byte$-weak
    (<= (file-measure channel (mv-nth 1 (read-byte$ channel state)))
        (file-measure channel state))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-byte$-strong
    (implies (mv-nth 0 (read-byte$ channel state))
             (< (file-measure channel (mv-nth 1 (read-byte$ channel state)))
                (file-measure channel state)))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-byte$-rw
    (implies (mv-nth 0 (read-byte$ channel state))
             (equal (file-measure channel (mv-nth 1 (read-byte$ channel state)))
                    (+ -1 (file-measure channel state)))))

  (defthm file-measure-of-read-char$-weak
    (<= (file-measure channel (mv-nth 1 (read-char$ channel state)))
        (file-measure channel state))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-char$-strong
    (implies (mv-nth 0 (read-char$ channel state))
             (< (file-measure channel (mv-nth 1 (read-char$ channel state)))
                (file-measure channel state)))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-char$-rw
    (implies (mv-nth 0 (read-char$ channel state))
             (equal (file-measure channel (mv-nth 1 (read-char$ channel state)))
                    (1- (file-measure channel state)))))

  (defthm file-measure-of-read-object-weak
    (<= (file-measure channel (mv-nth 2 (read-object channel state)))
        (file-measure channel state))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-object-strong
    (implies (not (mv-nth 0 (read-object channel state)))
             (< (file-measure channel (mv-nth 2 (read-object channel state)))
                (file-measure channel state)))
    :rule-classes (:rewrite :linear))

  (defthm file-measure-of-read-object-rw
    (implies (not (mv-nth 0 (read-object channel state)))
             (equal (file-measure channel (mv-nth 2 (read-object channel state)))
                    (1- (file-measure channel state))))))
