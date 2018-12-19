; ACL2 Standard Library
; Copyright (C) 2017 Keshav Kini
;
; Contact: Keshav Kini <keshav.kini@gmail.com>
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
; Original author: Keshav Kini <keshav.kini@gmail.com>

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)


; Here is a small theory tweak we need:

(local (in-theory (disable nth update-nth)))

; And here is a random lemma we need:

(local
 (defthm assoc-after-remove1-assoc
   ;; borrowed from projects/filesystems/file-system-lemmas.lisp --
   ;; should probably be in std/alists somewhere, I guess?
   (implies (not (equal name1 name2))
            (equal (assoc-equal name1 (remove1-assoc name2 alist))
                   (assoc-equal name1 alist)))))


; And now here is the main part of the book.

(defsection open-channel-lemmas
  :parents (std/io)
  :short "Lemmas about when various @(see state)-modifying functions
  do and don't affect the list of open channels."

  :long
  "<p>When programming with I/O, you may need to write functions that
      modify state in some way (perhaps by doing I/O) and exit
      returning a state which has some channels open, perhaps for
      further reading and writing later in your program.  Then, to
      prove guard theorems elsewhere, you'll need returns theorems
      about your function showing that those channels are open, either
      because they were open before the function ran and the function
      didn't close them, or because the function itself opened
      them.</p>

   <p>This book contains lemmas that can help you prove such returns
      theorems.  For each built-in I/O function, there is a lemma
      saying that, under appropriate hypotheses, it doesn't close your
      open input or output channels.</p>"

; Here are the builtins about which we're proving the lemmas:

  (local (in-theory (enable open-input-channel
                            open-output-channel
                            close-input-channel
                            close-output-channel
                            read-char$
                            read-byte$
                            read-object
                            princ$
                            write-byte$
                            print-object$
                            set-serialize-character)))

; Lemmas for other state-modifying builtins might be useful too, but I
; figured I had to stop somewhere, so I decided to limit this book to
; the functions mentioned in :DOC io.  I suppose you could add to this
; book the corresponding lemmas about other built-in functions as
; well, as you find yourself needing them.


; NOTE: Four of the lemmas below have a weird hypothesis, written in
; upper case.  These hypotheses should be unnecessary when dealing
; with the real ACL2 state, but currently `state-p1' does not
; sufficiently precisely describe the real ACL2 state for this
; knowledge to be accessible via `state-p1'.

; If the definition of `state-p1' is strengthened in the future, a
; (state-p1 state) hypothesis could be added where necessary, and
; these weird hypotheses could be removed, as demonstrated in the
; commented out "desired versions" of the theorems.

; See also the entry "Strengthen state-p so that channel info has
; file-clocks that don't exceed file-clock." in the file
; books/system/to-do.txt .

;;;;;;;;;;;;;;;;
;;;; Open input channels stay open
;;;;;;;;;;;;;;;;

  "<p>First are lemmas about @('open-input-channel-p1').</p>"

  (defthm open-input-channel-p1-under-open-input-channel
    ;; Desired version:
    ;; (implies (and (state-p1 state)
    ;;               (open-input-channel-p1 channel type state))
    ;;          (b* (((mv & state)
    ;;                (open-input-channel fname other-type state)))
    ;;            (open-input-channel-p1 channel type state)))
    (implies (open-input-channel-p1 channel type state)
             (b* (((mv other-channel state)
                   (open-input-channel fname other-type state)))
               (implies (IMPLIES (EQUAL OTHER-CHANNEL CHANNEL)
                                 (EQUAL OTHER-TYPE TYPE))
                        (open-input-channel-p1 channel type state)))))

  (defthm open-input-channel-p1-under-open-output-channel
    (implies (open-input-channel-p1 channel type state)
             (b* (((mv & state)
                   (open-output-channel fname other-type state)))
               (open-input-channel-p1 channel type state))))

  (defthm open-input-channel-p1-under-close-input-channel
    ;; Desired version:
    ;; (implies (and (state-p1 state)
    ;;               (open-input-channel-p1 channel type state))
    ;;          (b* ((state (close-input-channel other-channel state)))
    ;;            (iff (open-input-channel-p1 channel type state)
    ;;                 (not (equal channel other-channel)))))
    (implies (and (open-input-channel-p1 channel type state)
                  (NOT (EQUAL CHANNEL OTHER-CHANNEL)))
             (b* ((state (close-input-channel other-channel state)))
               (open-input-channel-p1 channel type state))))

  (defthm open-input-channel-p1-under-close-output-channel
    (implies (open-input-channel-p1 channel type state)
             (b* ((state (close-output-channel other-channel state)))
               (open-input-channel-p1 channel type state))))

  (defthm open-input-channel-p1-under-read-char$
    (implies (open-input-channel-p1 channel type state)
             (b* (((mv & state) (read-char$ other-channel state)))
               (open-input-channel-p1 channel type state))))

  (defthm open-input-channel-p1-under-read-byte$
    (implies (open-input-channel-p1 channel type state)
             (b* (((mv & state) (read-byte$ other-channel state)))
               (open-input-channel-p1 channel type state))))

  (defthm open-input-channel-p1-under-read-object
    (implies (open-input-channel-p1 channel type state)
             (b* (((mv & & state) (read-object other-channel state)))
               (open-input-channel-p1 channel type state))))

  (defthm open-input-channel-p1-under-princ$
    (implies (open-input-channel-p1 channel type state)
             (b* ((state (princ$ x other-channel state)))
               (open-input-channel-p1 channel type state))))

  (defthm open-input-channel-p1-under-write-byte$
    (implies (open-input-channel-p1 channel type state)
             (b* ((state (write-byte$ byte other-channel state)))
               (open-input-channel-p1 channel type state))))

  (defthm open-input-channel-p1-under-print-object$
    (implies (open-input-channel-p1 channel type state)
             (b* ((state (print-object$ byte other-channel state)))
               (open-input-channel-p1 channel type state))))

  (defthm open-input-channel-p1-under-set-serialize-character
    (implies (open-input-channel-p1 channel type state)
             (b* ((state (set-serialize-character c state)))
               (open-input-channel-p1 channel type state))))


;;;;;;;;;;;;;;;;
;;;; Open output channels stay open
;;;;;;;;;;;;;;;;

  "<p>Next are lemmas about @('open-output-channel-p1').</p>"

  (defthm open-output-channel-p1-under-open-input-channel
    (implies (open-output-channel-p1 channel type state)
             (b* (((mv & state)
                   (open-input-channel fname other-type state)))
               (open-output-channel-p1 channel type state))))

  (defthm open-output-channel-p1-under-open-output-channel
    ;; Desired version:
    ;; (implies (and (state-p1 state)
    ;;               (open-output-channel-p1 channel type state))
    ;;          (b* (((mv & state)
    ;;                (open-output-channel fname other-type state)))
    ;;            (open-output-channel-p1 channel type state)))
    (implies (open-output-channel-p1 channel type state)
             (b* (((mv other-channel state)
                   (open-output-channel fname other-type state)))
               (implies (IMPLIES (EQUAL OTHER-CHANNEL CHANNEL)
                                 (EQUAL OTHER-TYPE TYPE))
                        (open-output-channel-p1 channel type state)))))

  (defthm open-output-channel-p1-under-close-input-channel
    (implies (open-output-channel-p1 channel type state)
             (b* ((state (close-input-channel other-channel state)))
               (open-output-channel-p1 channel type state))))

  (defthm open-output-channel-p1-under-close-output-channel
    ;; Desired version:
    ;; (implies (and (state-p1 state)
    ;;               (open-output-channel-p1 channel type state))
    ;;          (b* ((state (close-output-channel other-channel state)))
    ;;            (iff (open-output-channel-p1 channel type state)
    ;;                 (not (equal channel other-channel)))))
    (implies (and (open-output-channel-p1 channel type state)
                  (NOT (EQUAL CHANNEL OTHER-CHANNEL)))
             (b* ((state (close-output-channel other-channel state)))
               (open-output-channel-p1 channel type state))))

  (defthm open-output-channel-p1-under-read-char$
    (implies (open-output-channel-p1 channel type state)
             (b* (((mv & state) (read-char$ other-channel state)))
               (open-output-channel-p1 channel type state))))

  (defthm open-output-channel-p1-under-read-byte$
    (implies (open-output-channel-p1 channel type state)
             (b* (((mv & state) (read-byte$ other-channel state)))
               (open-output-channel-p1 channel type state))))

  (defthm open-output-channel-p1-under-read-object
    (implies (open-output-channel-p1 channel type state)
             (b* (((mv & & state) (read-object other-channel state)))
               (open-output-channel-p1 channel type state))))

  (defthm open-output-channel-p1-under-princ$
    (implies (open-output-channel-p1 channel type state)
             (b* ((state (princ$ x other-channel state)))
               (open-output-channel-p1 channel type state))))

  (defthm open-output-channel-p1-under-write-byte$
    (implies (open-output-channel-p1 channel type state)
             (b* ((state (write-byte$ byte other-channel state)))
               (open-output-channel-p1 channel type state))))

  (defthm open-output-channel-p1-under-print-object$
    (implies (open-output-channel-p1 channel type state)
             (b* ((state (print-object$ byte other-channel state)))
               (open-output-channel-p1 channel type state))))

  (defthm open-output-channel-p1-under-set-serialize-character
    (implies (open-output-channel-p1 channel type state)
             (b* ((state (set-serialize-character c state)))
               (open-output-channel-p1 channel type state)))))
