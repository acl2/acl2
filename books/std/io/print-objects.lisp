; ACL2 Standard Library
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "file-measure")
(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs" :dir :system)
(local (include-book "base"))
(set-state-ok t)

(defund serialize-characterp (c)
  ;; BOZO redundant with base.lisp
  (declare (xargs :guard t))
  (or (not c)
      (equal c #\Z)
      (equal c #\Y)))

(local (defthm boundp-global-is-boundp-global1
         (equal (boundp-global x state)
                (boundp-global1 x state))
         :hints(("Goal" :in-theory (enable boundp-global)))))

(local (defthm open-output-channel-p-is-open-output-channel-p1
         (equal (open-output-channel-p x type state)
                (open-output-channel-p1 x type state))
         :hints(("Goal" :in-theory (enable open-output-channel-p)))))

(local (defthm state-p-is-state-p1
         (equal (state-p x)
                (state-p1 x))
         :hints(("Goal" :in-theory (enable state-p)))))

(local (in-theory (disable print-object$
                           set-serialize-character
                           acl2::get-serialize-character
                           state-p
                           STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1
                           open-output-channel-p
                           boundp-global
                           open-output-channel-p1
                           boundp-global1
                           w)))

(local (defthm normalize-get-serialize-character
         ;; Because why WOULDN'T you introduce abstractions and then write
         ;; macros that don't use them...
         (equal (get-global 'acl2::serialize-character state)
                (acl2::get-serialize-character state))
         :hints(("Goal" :in-theory (enable acl2::get-serialize-character)))))




(define print-legibly-aux
  :parents (print-legibly print-compressed)
  :short "Wrapper for @(see print-object$) that handles setting up @(see
serialize) compression."
  ((obj "The object to print.")
   (serialize-okp booleanp)
   (channel (and (symbolp channel)
                 (open-output-channel-p channel :object state)))
   state)
  :returns state
  :long "<p>ACL2's @(see print-object$) is hard to use directly in logic mode
because the serialize-character interface is pretty baroque.  We can only set
the serialize character to particular good values.  But nothing tells us it's a
good value to begin with, and the @('with-serialize-character') macro tries to
restore it to whatever it was, which might be a bad value.</p>

<p>At any rate, this is a wrapper that works around these issues by setting the
serialize character to something sensible if it's invalid to begin with, and by
not trying to serialize in a non-hons enabled image.</p>"

  :prepwork ((local (in-theory (enable acl2::serialize-characterp))))
  (b* ((state
        ;; Force the serialize character to be valid to begin with.
        (if (and (boundp-global 'serialize-character state)
                 (serialize-characterp (get-serialize-character state)))
            state
          (set-serialize-character nil state)))

       ((mv err ?val state)
        ;; Bah, the awful with-serialize-character macro insists on returning
        ;; a value triple and can't even take an IF as its character...
        (if serialize-okp
            (with-serialize-character #\Z
              (let ((state (print-object$ obj channel state)))
                (mv nil nil state)))
          (with-serialize-character nil
            (let ((state (print-object$ obj channel state)))
              (mv nil nil state)))))

       ((when err)
        (impossible)
        state))
    state)
  ///
  (defthm state-p1-of-print-legibly-aux
    (let ((ret (print-legibly-aux obj serialize-okp channel state)))
      (implies (and (state-p1 state)
                    (symbolp channel)
                    (open-output-channel-p1 channel :object state))
               (state-p1 ret))))

  (defthm open-output-channel-p1-of-print-legibly-aux
    (let ((ret (print-legibly-aux obj serialize-okp channel state)))
      (implies (and (state-p1 state)
                    (symbolp channel)
                    (open-output-channel-p1 channel :object state))
               (open-output-channel-p1 channel :object ret)))))

(define print-legibly
  :parents (std/io print-object$ serialize)
  :short "Wrapper for @(see print-object$) that ensures @(see serialize)
compression is disabled."
  ((obj "The object to print.")
   &optional
   ((channel (and (symbolp channel)
                  (open-output-channel-p channel :object state))
             "An open @(':output') channel.")
    'channel)
   (state 'state))
  :returns state
  :long "<p>When writing to an @(':object') stream, ACL2 can print objects in a
@(see serialize)d format that provides compression when there is a lot of
structure sharing, but which is hard for humans to read.</p>

<p>Using @('print-legibly') ensures that your object will be printed without
this compression.</p>

<p>See also @(see print-compressed).</p>"
  (print-legibly-aux obj nil channel state)
  ///
  (defthm state-p1-of-print-legibly
    (let ((ret (print-legibly obj channel state)))
      (implies (and (state-p1 state)
                    (symbolp channel)
                    (open-output-channel-p1 channel :object state))
               (state-p1 ret))))

  (defthm open-output-channel-p1-of-print-legibly
    (let ((ret (print-legibly obj channel state)))
      (implies (and (state-p1 state)
                    (symbolp channel)
                    (open-output-channel-p1 channel :object state))
               (open-output-channel-p1 channel :object ret)))))

(define print-compressed
  :parents (std/io print-object$ serialize)
  :short "Wrapper for @(see print-object$) that ensures @(see serialize)
compression is enabled (if supported)."
  ((obj "The object to print.")
   &optional
   ((channel (and (symbolp channel)
                  (open-output-channel-p channel :object state))
             "An open @(':output') channel.")
    'channel)
   (state 'state))
  :returns state
  :long "<p>When writing to an @(':object') stream, ACL2 can print objects in a
@(see serialize)d format that provides compression when there is a lot of
structure sharing, but which is hard for humans to read.</p>

<p>Using @('print-compressed') ensures that, on @(see hons-enabled) versions of
ACL2 (which is all versions), your object will be printed with this compression
enabled.  The resulting object typically looks like @('#Z...') in the file,
where @('...') is a binary blob that makes no sense to humans.  These objects
can later be read back in by ACL2's @(see read-object).</p>"
  (print-legibly-aux obj t channel state)
  ///
  (defthm state-p1-of-print-compressed
    (let ((ret (print-compressed obj channel state)))
      (implies (and (state-p1 state)
                    (symbolp channel)
                    (open-output-channel-p1 channel :object state))
               (state-p1 ret))))

  (defthm open-output-channel-p1-of-print-compressed
    (let ((ret (print-compressed obj channel state)))
      (implies (and (state-p1 state)
                    (symbolp channel)
                    (open-output-channel-p1 channel :object state))
               (open-output-channel-p1 channel :object ret)))))

#||
(b* (((mv channel state) (open-output-channel "temp.lsp" :object state))
     (state (print-legibly (list :Hello :World)))
     (state (print-compressed (list :Goodbye :Moon)))
     (state (print-legibly (list :End :Notes)))
     (state (close-output-channel channel state)))
  state)
||#
