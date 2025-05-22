; Utilities to write string-trees to files
;
; Copyright (C) 2017-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This file requires a trust tag because of the use of open-output-channel!.

(include-book "string-trees")
(local (include-book "kestrel/file-io-light/princ-dollar" :dir :system))
(local (include-book "kestrel/file-io-light/open-output-channel-bang" :dir :system))
(local (include-book "kestrel/file-io-light/open-output-channel-p" :dir :system))
(local (include-book "kestrel/file-io-light/close-output-channel" :dir :system))
(local (include-book "w"))
(local (include-book "state"))

(defttag file-io!)

(local (in-theory (disable state-p w open-output-channel-p)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

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
 (defthm state-p-and-open-output-channel-p-of-write-string-tree-to-channel
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
           (open-output-channel-p channel :character (write-string-tree-to-channel string-tree channel state)))
  :hints (("Goal" :in-theory (enable))))

(defthm state-p-of-write-string-tree-to-channel
  (implies (and (open-output-channel-p channel :character state)
                (symbolp channel)
                (state-p state))
           (state-p (write-string-tree-to-channel string-tree channel state))))

(verify-guards write-string-tree-to-channel)

(defthm w-of-write-string-tree-to-channel
  (equal (w (write-string-tree-to-channel string-tree channel state))
         (w state))
  :hints (("Goal" :in-theory (enable write-string-tree-to-channel))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;can be called from a make-event or clause processor because open-output-channel! is used (but requires a trust-tag)
;returns (mv erp state)
(defund write-string-tree! (string-tree fname ctx state)
  (declare (xargs :stobjs state
                  :guard (and (string-treep string-tree)
                              (stringp fname))

                  :guard-hints (("Goal" :in-theory (enable open-output-channel-p1-becomes-open-output-channel-p)))))
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

(defthm state-p-of-mv-nth-1-of-write-string-tree!
  (implies (state-p state)
           (state-p (mv-nth 1 (write-string-tree! string-tree fname ctx state))))
  :hints (("Goal" :in-theory (e/d (write-string-tree! open-output-channel-p1-becomes-open-output-channel-p)
                                  (open-output-channels
                                   update-file-clock
                                   update-open-output-channels
                                   update-written-files
                                   written-files-p
                                   file-clock-p
                                   written-file)))))
