; Copyright (C) 1997  Computational Logic, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; dump-events.lisp  --  file-dumping utility for ACL2

; Originally written by Matt Kaufmann at Computational Logic, Inc.
; Although this file seems to work with ACL2 Release 2.0, it should be
; viewed as providing a capability that may prove useful in using
; ACL2 but _not_ as code that can be trusted to the extent that the
; ACL2 system prover may be trusted.

; To certify this book:
; (certify-book "dump-events").

(in-package "ACL2")
(set-state-ok t)

(program)

(defmacro dump-events (filename &optional (earlier-cd '0) (later-cd ':x))
 ":Doc-Section miscellaneous

  dump events to a file~/

  ~bv[]
  Examples:
  (include-book \"misc/dump-events\" :dir :system)
  (dump-events \"xxx\")        ; dump all user events to file xxx
  (dump-events \"xxx\" :x-2)   ; dump the last two events to file xxx
  (dump-events \"xxx\" 2 :x-1) ; dump all events from after command 2
                             ; up through the next-to-last command
  ~ev[]~/

  General Form:
  ~bv[]
  (dump-events dumpfile
               &optional earlier-command-desc later-command-desc)
  ~ev[]
  where the form of the optional command descriptors is explained
  elsewhere; ~pl[command-descriptor].  All events strictly after 
  the first command descriptor up through the second, which by default
  are ~c[0] and ~c[:x] (thus indicating that all user events should be
  dumped to the dumpfile), are written to the indicated dumpfile.  In
  addition, an extra form is written to the top of the dumpfile:
  (in-package \"ACL2\").  This makes it convenient to use the dumpfile
  as a source file for ACL2 in a later session.

  Each event that was originally executed underneath ~ilc[LOCAL] will
  be placed inside ~ilc[LOCAL] in the dumpfile.

  The dumpfile will be overwritten if it already exists."
  `(dump-events-fn ,filename ',earlier-cd ',later-cd state))

(defun dump-events-fn1 (earlier-wrld later-wrld acc in-local-flg)
  (cond
   ((equal earlier-wrld later-wrld)
    acc)
   (t (let ((tuple (car later-wrld)))
        (case-match
         tuple
         (('COMMAND-LANDMARK 'GLOBAL-VALUE & ':LOGIC 'LOCAL . &)
          (dump-events-fn1 earlier-wrld (cdr later-wrld) acc t))
         (('COMMAND-LANDMARK 'GLOBAL-VALUE & 'LOCAL . &)
          (dump-events-fn1 earlier-wrld (cdr later-wrld) acc t))
         (('COMMAND-LANDMARK 'GLOBAL-VALUE . &)
          (dump-events-fn1 earlier-wrld (cdr later-wrld) acc nil))
         (('EVENT-LANDMARK 'GLOBAL-VALUE n (& . &) . ev)
          (cond ((integerp n)
                 (dump-events-fn1 earlier-wrld (cdr later-wrld)
                                  (cons (if in-local-flg
                                            (list 'local ev)
                                          ev)
                                        acc)
                                  in-local-flg))
                (t (dump-events-fn1 earlier-wrld (cdr later-wrld) acc
                                    in-local-flg))))
         (('EVENT-LANDMARK 'GLOBAL-VALUE n . ev)
          (cond ((integerp n)
                 (dump-events-fn1 earlier-wrld (cdr later-wrld)
                                  (cons (if in-local-flg
                                            (list 'local ev)
                                          ev)
                                        acc)
                                  in-local-flg))
                (t (dump-events-fn1 earlier-wrld (cdr later-wrld) acc
                                    in-local-flg))))
         (& (dump-events-fn1 earlier-wrld (cdr later-wrld) acc
                             in-local-flg)))))))

(defun fmt-lst (lst chan state)
  (cond
   ((endp lst) state)
   (t (pprogn (fms "~q0" (list (cons #\0 (car lst))) chan state nil)
              (fmt-lst (cdr lst) chan state)))))

(defun dump-events-fn (filename earlier-cd later-cd state)
  (let ((wrld (w state)))
    (er-let*
     ((earlier-wrld (er-decode-cd earlier-cd wrld 'dump-events state))
      (later-wrld (er-decode-cd later-cd wrld 'dump-events state)))
     (cond ((<= (length later-wrld)
                (length earlier-wrld))
            (er soft 'dump-events
                "The command descriptor ~p0 does not refer to a later (longer) ~
                 world than does the command descriptor ~p1."
                later-cd earlier-cd))
           (t (mv-let (chan state)
                      (open-output-channel filename :character state)
                      (pprogn
                       (fms "(in-package ~p0)~%"
                            (list (cons #\0 (f-get-global 'current-package
                                                          state)))
                            chan state nil)
                       (fmt-lst
                        (dump-events-fn1 earlier-wrld later-wrld nil nil)
                        chan state)
                       (close-output-channel chan state)
                       (value :invisible))))))))
