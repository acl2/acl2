; A variant of read-objects-from-file that uses the given package for the symbols
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "read-objects-from-channel")
(local (include-book "open-input-channel"))
(local (include-book "close-input-channel"))

;; TODO: Complete the proofs below

;; (local (include-book "kestrel/utilities/state" :dir :system))
;; (local (include-book "system/error1-support" :dir :system))
;; (local (include-book "system/fmt-support" :dir :system))
;; (local (in-theory (disable CHK-CURRENT-PACKAGE PUT-GLOBAL SET-CURRENT-PACKAGE-STATE error1)))

(verify-termination chk-current-package)
(verify-termination set-current-package)
(verify-termination set-current-package-state)
;; (verify-guards chk-current-package) ; fails
;; (verify-guards set-current-package)
;; (verify-guards set-current-package-state)

;; Returns (mv erp objects state) where either ERP is non-nil (meaning an error
;; occurred) or else OBJECTS are the ACL2 objects in the file.  PKG indicates
;; which package to use for symbols read from the file that don't have explicit
;; packages (:current means use the current package).
(defund read-objects-from-file-with-pkg (filename pkg state)
  (declare (xargs :guard (and (stringp filename)
                              (or (eq :current pkg)
                                  (stringp pkg)))
                  :verify-guards nil ;todo because of SET-CURRENT-PACKAGE-STATE
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

;; Attempt to prove some properties of read-objects-from-file-with-pkg (in-progress):

;; (thm
;;   (equal (global-table (mv-nth '1 (fmt1 str alist col channel state evisc-tuple)))
;;          (global-table state))
;;   :hints (("Goal" :in-theory (enable global-table fmt1 fmt0))))

;; (defthm state-p1-of-mv-nth-2-of-error1
;;   (implies (state-p1 state)
;;            (state-p1 (mv-nth 2 (error1 ctx summary str alist state))))
;;   :hints (("Goal" :in-theory (enable error1 ; todo
;;                                      fmt1! ; todo
;;                                      put-global ; todo
;;                                      UPDATE-GLOBAL-TABLE))))

;; (local
;;   (defthm state-p1-of-SET-CURRENT-PACKAGE-STATE
;;     (implies (state-p1 state)
;;              (STATE-P1  (SET-CURRENT-PACKAGE-STATE val state)))
;;     :hints (("Goal" :in-theory (enable SET-CURRENT-PACKAGE-STATE CHK-CURRENT-PACKAGE)))))

;; (defthm state-p1-of-mv-nth-2-of-read-objects-from-file-with-pkg
;;   (implies (and (stringp filename)
;;                 (state-p1 state))
;;            (state-p1 (mv-nth 2 (read-objects-from-file-with-pkg filename pkg state))))
;;   :hints (("Goal" :in-theory (enable read-objects-from-file-with-pkg))))

;; (defthm state-p-of-mv-nth-2-of-read-objects-from-file-with-pkg
;;   (implies (and (stringp filename)
;;                 (state-p state))
;;            (state-p (mv-nth 2 (read-objects-from-file-with-pkg filename pkg state))))
;;   :hints (("Goal" :in-theory (enable read-objects-from-file))))
