; Documentation for output-theory.lisp
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc file-output-theory
  :short "Simple file output theory"
  :parents (io-utilities)
  :long
  (xdoc::topstring
   (xdoc::@{} "
(local (include-book \"kestrel/utilities/io/output-theory\" :dir :system))
")
   (xdoc::p
    "You can use this book to enable a simple theory that makes it easy to write
     guard-verified, logic mode ACL2 functions that do character output to a file.")
   (xdoc::p
    "A common pattern is to open a character output channel to a file,
     write some strings to it, and close it.  There usually isn't much
     value in enabling rewrite rules for functions that write strings to an
     open channel.  But without that, a caller must be able to verify that
     the output function keeps the channel open and returns @(tsee state),
     so it is good to define theorems about those properties.")
   (xdoc::p
    "Without going into detail about the pitfalls of other approaches,
     we proceed directly to an example pattern that uses @('state-p') and
     @('open-output-channel-p') and avoids the bootstrapping versions
     @('state-p1') and @('open-output-channel-p1').")
   (xdoc::@{} "
(include-book \"std/util/define\" :dir :system)
(local (include-book \"kestrel/utilities/io/output-theory\" :dir :system))

(define use-princ ((str stringp)
                   (co symbolp)
                   state)
  :guard (open-output-channel-p co :character state)
  :stobjs state
  :returns state
  (b* ((state (princ$ \"Starting Output...\" co state))
       (state (princ$ str co state))
       (state (princ$ \"...end of output.\" co state)))
    state)
  ///
  (defthm state-p-of-use-princ
    (let ((ret (use-princ str channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (state-p ret))))
  (defthm open-output-channel-p-of-use-princ
    (let ((ret (use-princ tr channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (open-output-channel-p channel :character ret)))))

(define use-princ-to-file ((str stringp)
                           (filename stringp)
                           state)
  :stobjs state
  :returns state
  (mv-let (co state)
      (open-output-channel filename :character state)
    (if (not (open-output-channel-p co :character state))
        state
      (b* ((state (use-princ str co state)))
        (close-output-channel co state))))
  ///
  (defthm state-p-of-use-princ-to-file
    (let ((ret (use-princ-to-file tr filename state)))
      (implies (and (stringp str)
                    (stringp fn)
                    (state-p state))
               (state-p ret)))))
")
   (xdoc::p
    "The I/O functions currently supported are:")
   (xdoc::ul
    (xdoc::li "@(tsee open-output-channel), when given the @(':character') argument")
    (xdoc::li "@(tsee open-output-channel-p)")
    (xdoc::li "@(tsee princ$)")
    (xdoc::li "@('prin1$')")
    (xdoc::li "@(tsee close-output-channel)"))))
