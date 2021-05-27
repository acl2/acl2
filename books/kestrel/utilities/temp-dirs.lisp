; Utilities for dealing with temporary directories
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "get-process-id")
(include-book "get-username")
(include-book "std/util/bstar" :dir :system)

(in-theory (disable mv-nth)) ;make local?

(defttag temp-dirs) ; due to the sys-call+

(defconst *system-temp-dir-no-slash* "/tmp")
(defconst *system-temp-dir-with-slash* (string-append *system-temp-dir-no-slash* "/"))

;; Returns (mv temp-dir-name state).  In error cases, we return
;; *system-temp-dir-no-slash* to be safe.
(defund choose-temp-dir-name (state)
  (declare (xargs :stobjs state))
  (b* (((mv username state) (get-username state))
       ((when (not (stringp username)))
        (er hard? 'choose-temp-dir-name "Bad user name")
        (mv *system-temp-dir-no-slash* state))
       ((mv pid state) (get-process-id state))
       ((when (not (stringp pid)))
        (er hard? 'choose-temp-dir-name "Bad pid")
        (mv *system-temp-dir-no-slash* state))
       (temp-dir-name (concatenate 'string *system-temp-dir-with-slash* username "/TEMP-" pid)))
    (mv temp-dir-name state)))

(defthm stringp-of-mv-nth-0-of-choose-temp-dir-name
  (stringp (mv-nth 0 (choose-temp-dir-name state)))
  :hints (("Goal" :in-theory (enable choose-temp-dir-name))))

(defthm state-p1-of-mv-nth-1-of-choose-temp-dir-name
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (choose-temp-dir-name state))))
  :hints (("Goal" :in-theory (enable choose-temp-dir-name))))

;; Returns (mv temp-dir-name state).  Retrieves or creates a name for a temp dir
;; by combining the username and the process id.  The result is something like
;; /tmp/ewsmith/TEMP-12345, where 12345 is the PID.  Stores the result in the
;; state global 'temp-dir-for-this-process so that subsequent calls of this are
;; fast.  The process-id is used to avoid clashes between different ACL2
;; processes.  The username is used to avoid permission problems on the dirs.
(defund temp-dir-name (state)
  (declare (xargs :stobjs state))
  (if (boundp-global 'temp-dir-for-this-process state)
      (let ((temp-dir-name (f-get-global 'temp-dir-for-this-process state)))
        (if (not (stringp temp-dir-name))
            (prog2$ (er hard? 'temp-dir-name "Bad stored temp dir name.")
                    (mv *system-temp-dir-no-slash* state))
          (mv temp-dir-name state)))
    ;; Make a temp dir name and record it in a state global:
    (mv-let (temp-dir-name state)
      (choose-temp-dir-name state)
      (let ((state (f-put-global 'temp-dir-for-this-process temp-dir-name state)))
        (mv temp-dir-name state)))))

(defthm stringp-of-mv-nth-0-of-temp-dir-name
  (stringp (mv-nth 0 (temp-dir-name state)))
  :hints (("Goal" :in-theory (enable temp-dir-name))))

(defthm state-p1-of-mv-nth-1-of-temp-dir-name
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (temp-dir-name state))))
  :hints (("Goal" :in-theory (enable temp-dir-name))))

;; Returns (mv temp-dir-name state). Uses the state global
;; 'temp-dir-for-this-process.  Makes the temp dir if it doesn't already exist.
(defund maybe-make-temp-dir (state)
  (declare (xargs :stobjs state))
  (if (boundp-global 'temp-dir-exists state) ;; we only look at whether the global is bound, not its value
      (temp-dir-name state)
    (mv-let
      (temp-dir-name state)
      (temp-dir-name state)
      ;;make sure the parent directory of the temp-dir (e.g., /tmp) exists: ;;TODO; Skip this step?
      (mv-let ;(cw "(Using temporary directory ~x0.)~%" temp-dir-name)
        (erp val state)
        (sys-call* "mkdir" (list "-p" temp-dir-name) state)
        (declare (ignore erp val)) ;todo: check erp
        (let ((state (f-put-global 'temp-dir-exists t state)))
          (mv temp-dir-name state))))))

(defthm stringp-of-mv-nth-0-of-maybe-make-temp-dir
  (stringp (mv-nth 0 (maybe-make-temp-dir state)))
  :hints (("Goal" :in-theory (enable maybe-make-temp-dir))))

(defthm state-p1-of-mv-nth-1-of-maybe-make-temp-dir
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (maybe-make-temp-dir state))))
  :hints (("Goal" :in-theory (enable maybe-make-temp-dir))))

;; Disallow anything that could confuse the rm -rf command (whitespace, dots, etc.)
(defun temp-dir-chars-okp (chars)
  (declare (xargs :guard (character-listp chars)))
  (if (endp chars)
      t
    (let ((char (first chars)))
      (and (standard-char-p char)
           (or (alpha-char-p char)
               (digit-char-p char)
               (eql char  #\-)
               (eql char  #\_)
               (eql char  #\/))
           (temp-dir-chars-okp (rest chars))))))

;; Remove the temp dir whose name is stored in the state global (if the dir
;; exists).  Returns state.  The temp dir may go in and out of existence (e.g.,
;; on different calls to make-event) and the state global 'temp-dir-exists
;; tracks its state).
(defun maybe-remove-temp-dir (state)
  (declare (xargs :stobjs state))
  (if (not (boundp-global 'temp-dir-exists state))
      (progn$ ;; (cw "No temp dir to remove.")
       state)
    (mv-let (temp-dir-name state)
      (temp-dir-name state)
      ;; Makes sure that the rm command doesn't do anything bad:
      (if (not (and (stringp temp-dir-name)
                    (let ((temp-dir-chars (coerce temp-dir-name 'list))
                          (expected-prefix (coerce *system-temp-dir-with-slash* 'list)))
                      (and (temp-dir-chars-okp temp-dir-chars)
                           (equal expected-prefix
                                  (take (len expected-prefix) temp-dir-chars))))))
          (prog2$ (er hard? 'maybe-remove-temp-dir "Bad temp dir name: ~x0." temp-dir-name)
                  state)
        (progn$
         ;; (cw "(Removing temporary directory ~x0." temp-dir-name)
         (mv-let (erp val state)
           (sys-call* "rm" `("-rf" ,temp-dir-name) state)
           (declare (ignore erp val)) ;todo: check erp?
           (let ((state (makunbound-global 'temp-dir-exists state)))
             (prog2$ (cw ")~%")
                     state))))))))
