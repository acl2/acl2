; Utilities to write string-trees to files
;
; Copyright (C) 2017-2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This file requires a trust tag because of the use of open-output-channel!.

(local (include-book "kestrel/file-io-light/princ-dollar" :dir :system))
(local (include-book "kestrel/file-io-light/open-output-channel-bang" :dir :system))
(include-book "string-trees")
(local (include-book "w"))

(defttag file-io!)

(local (in-theory (disable state-p w)))

;; Writes all the strings in STRING-TREE to CHANNEL, skipping any leaves that
;; are nil.  Returns state.
(defund write-string-tree-to-channel (string-tree channel state)
  (declare (xargs :stobjs state
                  :guard (and (string-treep string-tree)
                              (symbolp channel)
                              (open-output-channel-p channel :character state))
                  :verify-guards nil ;done below
                  ))
  (if (atom string-tree)
      (if (stringp string-tree)
          (princ$ string-tree channel state) ;fixme call something faster? (e.g., something that only works for strings)?
        state)
    (pprogn (write-string-tree-to-channel (car string-tree) channel state)
            (write-string-tree-to-channel (cdr string-tree) channel state))))

;; I think I have to prove these 2 facts together
(local
 (defthm statep-and-open-output-channel-p-of-write-string-tree-to-channel
   (implies (and (open-output-channel-p channel :character state)
                 (symbolp channel)
                 (state-p state))
            (and (state-p (write-string-tree-to-channel string-tree channel state))
                 (open-output-channel-p channel :character (write-string-tree-to-channel string-tree channel state))))
   :hints (("Goal" :in-theory (enable write-string-tree-to-channel)))))

(defthm open-output-channel-p-of-write-string-tree-to-channel
  (implies (and (open-output-channel-p channel :character state)
                (symbolp channel)
                (state-p state))
           (open-output-channel-p channel :character (write-string-tree-to-channel string-tree channel state))))

(defthm statep-of-write-string-tree-to-channel
  (implies (and (open-output-channel-p channel :character state)
                (symbolp channel)
                (state-p state))
           (state-p (write-string-tree-to-channel string-tree channel state))))

(defthmd open-output-channel-p-forward-to-open-output-channel-p-1
  (implies (open-output-channel-p channel typ state)
           (open-output-channel-p1 channel typ state))

  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable OPEN-OUTPUT-CHANNEL-P))))

(verify-guards write-string-tree-to-channel :hints (("Goal" :in-theory (enable open-output-channel-p-forward-to-open-output-channel-p-1))))

(defthm w-of-write-string-tree-to-channel
  (equal (w (write-string-tree-to-channel string-tree channel state))
         (w state))
  :hints (("Goal" :in-theory (enable write-string-tree-to-channel))))

;(in-theory (disable OPEN-OUTPUT-CHANNEL-ANY-P1))

;why?
(defthm open-output-channel-p1-becomes-open-output-channel-p
  (equal (open-output-channel-p1 channel typ state)
         (open-output-channel-p channel typ state))
  :hints (("Goal" :in-theory (enable OPEN-OUTPUT-CHANNEL-P))))

;can be called from a make-event or clause processor because open-output-channel! is used (but requires a trust-tag)
;returns (mv erp state)
(defund write-string-tree! (string-tree fname ctx state)
  (declare (xargs :stobjs state
                  :guard (and (string-treep string-tree)
                              (stringp fname))))
  (mv-let (channel state)
    (open-output-channel! fname :character state)
    (if (not channel)
        (prog2$ (er hard? ctx "Unable to open file ~s0 for :character output." fname)
                (mv t state))
      (if (eq channel 'acl2-output-channel::standard-character-output-0) ;todo: prove that this doesn't happen
          (prog2$ (er hard? ctx "Unexpected output channel name: ~x0." fname)
                  (mv t state))
        (pprogn (write-string-tree-to-channel string-tree channel state)
                (close-output-channel channel state)
                (mv nil state))))))

(defthm w-of-mv-nth-1-of-write-string-tree!
  (equal (w (mv-nth 1 (write-string-tree! string-tree fname ctx state)))
         (w state))
  :hints (("Goal" :in-theory (e/d (write-string-tree!) (open-output-channels
                                                        update-file-clock
                                                        update-open-output-channels
                                                        update-written-files)))))
