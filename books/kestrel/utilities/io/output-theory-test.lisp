; Simple regression tests for output-theory.lisp
;
; Copyright (C) 2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/define" :dir :system)
(local (include-book "kestrel/utilities/io/output-theory" :dir :system))

(define use-princ ((str stringp)
                   (co symbolp)
                   state)
  :guard (open-output-channel-p co :character state)
  :stobjs state
  :returns state
  (b* ((state (princ$ "Starting Output..." co state))
       (state (princ$ str co state))
       (state (princ$ "...end of output." co state)))
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

(define use-prin1 ((str stringp)
                   (co symbolp)
                   state)
  :guard (open-output-channel-p co :character state)
  :stobjs state
  :returns state
  (b* ((state (princ$ "Starting Output..." co state))
       (state (prin1$ str co state))
       (state (princ$ "...end of output." co state)))
    state)
  ///
  (defthm state-p-of-use-prin1
    (let ((ret (use-prin1 str channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (state-p ret))))
  (defthm open-output-channel-p-of-use-prin1
    (let ((ret (use-prin1 tr channel state)))
      (implies (and (state-p state)
                    (symbolp channel)
                    (open-output-channel-p channel :character state))
               (open-output-channel-p channel :character ret)))))

(define use-prin1-to-file ((str stringp)
                           (filename stringp)
                           state)
  :stobjs state
  :returns state
  (mv-let (co state)
      (open-output-channel filename :character state)
    (if (not (open-output-channel-p co :character state))
        state
      (b* ((state (use-prin1 str co state)))
        (close-output-channel co state))))
  ///
  (defthm state-p-of-use-prin1-to-file
    (let ((ret (use-prin1-to-file tr filename state)))
      (implies (and (stringp str)
                    (stringp fn)
                    (state-p state))
               (state-p ret)))))
