; A lightweight function to read the ACL2 objects in a file.
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "open-input-channel"))
(local (include-book "close-input-channel"))
(local (include-book "read-object"))
(local (include-book "channels"))
(local (include-book "kestrel/utilities/state" :dir :system))

(local (in-theory (disable update-open-input-channels
                           open-input-channels
                           open-input-channel-any-p1
                           read-object
                           state-p)))

;; Returns (mv objects state).
(defund read-objects-from-channel-aux (channel acc state)
  (declare (xargs :guard (and (symbolp channel)
                              (open-input-channel-p channel :object state)
                              (true-listp acc))
                  :stobjs state
                  :measure (len (cddr (assoc-equal channel (open-input-channels state))) ;;(channel-contents channel state)
                                )
                  :guard-hints (("Goal" :in-theory (enable open-input-channel-p)))))
  (if (not (mbt (and (open-input-channel-p channel :object state) ; for termination
                     (state-p state))))
      (mv nil state)
    (mv-let (eof maybe-object state)
      (read-object channel state)
      (if eof
          (mv (reverse acc) state)
        (read-objects-from-channel-aux channel (cons maybe-object acc) state)))))

(defthm state-p1-of-mv-nth-1-of-read-objects-from-channel-aux
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (read-objects-from-channel-aux channel acc state))))
  :hints (("Goal" :in-theory (enable read-objects-from-channel-aux))))

(defthm state-p-of-mv-nth-1-of-read-objects-from-channel-aux
  (implies (state-p state)
           (state-p (mv-nth 1 (read-objects-from-channel-aux channel acc state))))
  :hints (("Goal" :in-theory (enable read-objects-from-channel-aux))))

(defthm open-input-channel-any-p1-of-mv-nth-1-of-read-objects-from-channel-aux
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel :object state))
           (open-input-channel-any-p1 channel (mv-nth 1 (read-objects-from-channel-aux channel acc state))))
  :hints (("Goal" :in-theory (enable read-objects-from-channel-aux
                                     open-input-channel-any-p1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv objects state).
(defund read-objects-from-channel (channel state)
  (declare (xargs :guard (and (symbolp channel)
                              (open-input-channel-p channel :object state))
                  :stobjs state))
  (read-objects-from-channel-aux channel nil state))

(defthm state-p1-of-mv-nth-1-of-read-objects-from-channel
  (implies (state-p1 state)
           (state-p1 (mv-nth 1 (read-objects-from-channel channel state))))
  :hints (("Goal" :in-theory (enable read-objects-from-channel))))

(defthm state-p-of-mv-nth-1-of-read-objects-from-channel
  (implies (state-p state)
           (state-p (mv-nth 1 (read-objects-from-channel channel state))))
  :hints (("Goal" :in-theory (enable read-objects-from-channel))))

(defthm open-input-channel-any-p1-of-mv-nth-1-of-read-objects-from-channel
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel :object state))
           (open-input-channel-any-p1 channel (mv-nth 1 (read-objects-from-channel channel state))))
  :hints (("Goal" :in-theory (enable read-objects-from-channel))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A wrapper that returns an error triple, (mv erp objects state).  Errors seem
;; to cause aborts rather than being returned, so ERP is always nil.
(defund read-objects-from-channel-error-triple (channel state)
  (declare (xargs :guard (and (symbolp channel)
                              (open-input-channel-p channel :object state))
                  :stobjs state))
  (mv-let (objects state)
    (read-objects-from-channel channel state)
    (mv nil objects state)))

(defthm state-p1-of-mv-nth-2-of-read-objects-from-channel-error-triple
  (implies (state-p1 state)
           (state-p1 (mv-nth 2 (read-objects-from-channel-error-triple channel state))))
  :hints (("Goal" :in-theory (enable read-objects-from-channel-error-triple))))

(defthm state-p-of-mv-nth-2-of-read-objects-from-channel-error-triple
  (implies (state-p state)
           (state-p (mv-nth 2 (read-objects-from-channel-error-triple channel state))))
  :hints (("Goal" :in-theory (enable read-objects-from-channel-error-triple))))

(defthm open-input-channel-any-p1-of-mv-nth-2-of-read-objects-from-channel-error-triple
  (implies (and (state-p1 state)
                (open-input-channel-p1 channel :object state))
           (open-input-channel-any-p1 channel (mv-nth 2 (read-objects-from-channel-error-triple channel state))))
  :hints (("Goal" :in-theory (enable read-objects-from-channel-error-triple))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp objects state) where either ERP is non-nil (meaning an error
;; occurred) or else OBJECTS are the ACL2 objects in the file.
;; The package used for symbols read from the file that don't have explicit
;; packages is the current package, but see read-objects-from-file-with-pkg.
(defund read-objects-from-file (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (if (not channel)
        ;; Error:
        (mv `(:could-not-open-channel ,filename) nil state)
      (mv-let (objects state)
        (read-objects-from-channel channel state)
        (let ((state (close-input-channel channel state)))
          (mv nil ; no error
              objects
              state))))))

(defthm state-p-of-mv-nth-2-of-read-objects-from-file
  (implies (and (stringp filename)
                (state-p state))
           (state-p (mv-nth 2 (read-objects-from-file filename state))))
  :hints (("Goal" :in-theory (enable read-objects-from-file))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp objects state) where either ERP is non-nil (meaning an error
;; occurred) or else OBJECTS are the ACL2 objects in the file.  PKG indicates
;; which package to use for symbols read from the file that don't have explicit
;; packages (:current means use the current package).
(defund read-objects-from-file-with-pkg (filename pkg state)
  (declare (xargs :guard (and (stringp filename)
                              (or (eq :current pkg)
                                  (stringp pkg)))
                  :mode :program ;todo because of the state-global-let*
                  :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (if (not channel)
        ;; Error:
        (mv `(:could-not-open-channel ,filename) nil state)
      (mv-let (erp objects state)
        (if (eq :current pkg)
            (read-objects-from-channel-error-triple channel state)
          (state-global-let* ((current-package pkg)) ; gets undone upon abort
                             (read-objects-from-channel-error-triple channel state)))
        (declare (ignore erp)) ; always nil
        (let ((state (close-input-channel channel state)))
          (mv nil ; no error
              objects
              state))))))

;; (defthm state-p-of-mv-nth-2-of-read-objects-from-file-with-pkg
;;   (implies (and (stringp filename)
;;                 (state-p state))
;;            (state-p (mv-nth 2 (read-objects-from-file-with-pkg filename pkg state))))
;;   :hints (("Goal" :in-theory (enable read-objects-from-file))))
