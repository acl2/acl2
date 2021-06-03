; Rules about the ACL2 state
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Organize this stuff, possibly moving some to other files
;; TODO: Name conflicts with std?
;; TODO: Add missing theorems here
;; TODO: Disable all the state functions

;; See also books/system/update-state.lisp.

(local (include-book "channels"))
(local (include-book "kestrel/lists-light/len" :dir :system))

;; Disable predicates on state components (TODO: Add more)
(in-theory (disable open-channels-p
                    ordered-symbol-alistp
                    all-boundp
                    32-bit-integer-listp
                    file-clock-p
                    read-files-p
                    readable-files-p
                    writeable-files-p
                    written-files-p
                    ;; so the rules below fire:
                    boundp-global
                    boundp-global1))

(local (in-theory (disable assoc-equal nth update-nth)))

;; since the state is a true-list
(defthm true-listp-of-update-open-input-channels
  (implies (true-listp st)
           (true-listp (update-open-input-channels x st)))
  :hints (("Goal" :in-theory (enable update-open-input-channels))))

;; since the state is a true-list
(defthm true-listp-of-update-file-clock
  (implies (true-listp st)
           (true-listp (update-file-clock x st)))
  :hints (("Goal" :in-theory (enable update-file-clock))))

;; since the state is a true-list
(defthm true-listp-of-update-read-files
  (implies (true-listp st)
           (true-listp (update-read-files x st)))
  :hints (("Goal" :in-theory (enable update-read-files))))


(defthm len-of-update-open-input-channels
  (implies (state-p1 state)
           (equal (len (update-open-input-channels x state))
                  (len state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm len-of-update-file-clock
  (implies (state-p1 state)
           (equal (len (update-file-clock x state))
                  (len state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm len-of-update-read-files
  (implies (state-p1 state)
           (equal (len (update-read-files x state))
                  (len state)))
  :hints (("Goal" :in-theory (enable state-p1))))

;; Conjuncts of state-p

(defthm read-files-p-of-read-files
  (implies (state-p1 state)
           (read-files-p (read-files state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm readable-files-p-of-readable-files
  (implies (state-p1 state)
           (readable-files-p (readable-files state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm open-channels-p-of-open-input-channels
  (implies (state-p1 state)
           (open-channels-p (open-input-channels state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm file-clock-p-of-file-clock
  (implies (state-p1 state)
           (file-clock-p (file-clock state)))
  :hints (("Goal" :in-theory (enable state-p1))))




;; Read-over-write theorems for states (different fields)

(defthm global-table-of-update-open-input-channels
  (equal (global-table (update-open-input-channels x st))
         (global-table st)))

(defthm global-table-of-update-file-clock
  (equal (global-table (update-file-clock x st))
         (global-table st)))

(defthm readable-files-of-update-open-input-channels
  (equal (readable-files (update-open-input-channels x st))
         (readable-files st)))

(defthm readable-files-of-update-file-clock
  (equal (readable-files (update-file-clock x st))
         (readable-files st)))

(defthm big-clock-entry-of-update-open-input-channels
  (equal (big-clock-entry (update-open-input-channels x st))
         (big-clock-entry st)))

(defthm big-clock-entry-of-update-file-clock
  (equal (big-clock-entry (update-file-clock x st))
         (big-clock-entry st)))

(defthm writeable-files-of-update-open-input-channels
  (equal (writeable-files (update-open-input-channels x st))
         (writeable-files st)))

(defthm writeable-files-of-update-file-clock
  (equal (writeable-files (update-file-clock x st))
         (writeable-files st)))

(defthm file-clock-of-update-open-input-channels
  (equal (file-clock (update-open-input-channels x st))
         (file-clock st)))

(defthm written-files-of-update-open-input-channels
  (equal (written-files (update-open-input-channels x st))
         (written-files st)))

(defthm written-files-of-update-file-clock
  (equal (written-files (update-file-clock x st))
         (written-files st)))

(defthm idates-of-update-open-input-channels
  (equal (idates (update-open-input-channels x st))
         (idates st)))

(defthm idates-of-update-file-clock
  (equal (idates (update-file-clock x st))
         (idates st)))

(defthm t-stack-of-update-open-input-channels
  (equal (t-stack (update-open-input-channels x st))
         (t-stack st)))

(defthm t-stack-of-update-file-clock
  (equal (t-stack (update-file-clock x st))
         (t-stack st)))

(defthm 32-bit-integer-stack-of-update-open-input-channels
  (equal (32-bit-integer-stack (update-open-input-channels x st))
         (32-bit-integer-stack st)))

(defthm 32-bit-integer-stack-of-update-file-clock
  (equal (32-bit-integer-stack (update-file-clock x st))
         (32-bit-integer-stack st)))

(defthm user-stobj-alist1-of-update-open-input-channels
  (equal (user-stobj-alist1 (update-open-input-channels x st))
         (user-stobj-alist1 st)))

(defthm user-stobj-alist1-of-update-file-clock
  (equal (user-stobj-alist1 (update-file-clock x st))
         (user-stobj-alist1 st)))

(defthm acl2-oracle-of-update-open-input-channels
  (equal (acl2-oracle (update-open-input-channels x st))
         (acl2-oracle st)))

(defthm acl2-oracle-of-update-file-clock
  (equal (acl2-oracle (update-file-clock x st))
         (acl2-oracle st)))

(defthm read-files-of-update-open-input-channels
  (equal (read-files (update-open-input-channels x st))
         (read-files st)))

(defthm read-files-of-update-file-clock
  (equal (read-files (update-file-clock x st))
         (read-files st)))

(defthm open-output-channels-of-update-open-input-channels
  (equal (open-output-channels (update-open-input-channels x st))
         (open-output-channels st)))

(defthm open-output-channels-of-update-file-clock
  (equal (open-output-channels (update-file-clock x st))
         (open-output-channels st)))

(defthm open-input-channels-of-update-file-clock
  (equal (open-input-channels (update-file-clock x st))
         (open-input-channels st)))

(defthm list-all-package-names-lst-of-update-open-input-channels
  (equal (list-all-package-names-lst (update-open-input-channels x st))
         (list-all-package-names-lst st)))

(defthm list-all-package-names-lst-of-update-file-clock
  (equal (list-all-package-names-lst (update-file-clock x st))
         (list-all-package-names-lst st)))

(defthm global-table-of-update-read-files
  (equal (global-table (update-read-files x st))
         (global-table st)))

(defthm readable-files-of-update-read-files
  (equal (readable-files (update-read-files x st))
         (readable-files st)))

(defthm big-clock-entry-of-update-read-files
  (equal (big-clock-entry (update-read-files x st))
         (big-clock-entry st)))

(defthm writeable-files-of-update-read-files
  (equal (writeable-files (update-read-files x st))
         (writeable-files st)))

(defthm file-clock-of-update-read-files
  (equal (file-clock (update-read-files x st))
         (file-clock st)))

(defthm written-files-of-update-read-files
  (equal (written-files (update-read-files x st))
         (written-files st)))

(defthm idates-of-update-read-files
  (equal (idates (update-read-files x st))
         (idates st)))

(defthm t-stack-of-update-read-files
  (equal (t-stack (update-read-files x st))
         (t-stack st)))

(defthm 32-bit-integer-stack-of-update-read-files
  (equal (32-bit-integer-stack (update-read-files x st))
         (32-bit-integer-stack st)))

(defthm user-stobj-alist1-of-update-read-files
  (equal (user-stobj-alist1 (update-read-files x st))
         (user-stobj-alist1 st)))

(defthm acl2-oracle-of-update-read-files
  (equal (acl2-oracle (update-read-files x st))
         (acl2-oracle st)))

(defthm open-output-channels-of-update-read-files
  (equal (open-output-channels (update-read-files x st))
         (open-output-channels st)))

(defthm open-input-channels-of-update-read-files
  (equal (open-input-channels (update-read-files x st))
         (open-input-channels st)))



(defthm list-all-package-names-lst-of-update-read-files
  (equal (list-all-package-names-lst (update-read-files x st))
         (list-all-package-names-lst st)))

;; read-over-write rules (same field)

(defthm file-clock-of-update-file-clock
  (equal (file-clock (update-file-clock x state))
         x))

(defthm open-input-channels-of-update-open-input-channels
  (equal (open-input-channels (update-open-input-channels x state))
         x))


(defthm read-files-of-update-read-files
  (implies (state-p1 state)
           (equal (read-files (update-read-files x state))
                  x))
  :hints (("Goal" :in-theory (enable read-files update-read-files))))

(defthm file-clock-p-of-+-of-1
  (implies (file-clock-p x)
           (file-clock-p (+ 1 x)))
  :hints (("Goal" :in-theory (enable file-clock-p))))

;; implied by open-channels-p
(defthm ordered-symbol-alistp-of-open-input-channels
  (implies (state-p1 state)
           (ordered-symbol-alistp (open-input-channels state))))

;; implied by open-channels-p
(defthm open-channel-listp-of-open-input-channels
  (implies (state-p1 state)
           (open-channel-listp (open-input-channels state)))
  :hints (("Goal" :in-theory (enable state-p1))))

;; Stuff about readable-files:

(defthm true-list-of-cdr-of-assoc-equal-of-readable-files
  (implies (readable-files-p readable-files)
           (true-listp (cdr (assoc-equal key readable-files))))
  :hints (("Goal" :in-theory (enable readable-files-p))))

(defthm typed-io-listp-of-cdr-of-assoc-equal-of-readable-files
  (implies (and (readable-files-p readable-files)
                (equal typ (second key)))
           (typed-io-listp (cdr (assoc-equal key readable-files)) typ))
  :hints (("Goal" :in-theory (enable readable-files-p member-equal assoc-equal))))

;; DISABLE the accessors and updaters of the fields of state:
(in-theory (disable open-input-channels
                    open-output-channels
                    global-table
                    t-stack
                    32-bit-integer-stack
                    big-clock-entry
                    idates
                    acl2-oracle
                    file-clock
                    readable-files
                    written-files
                    read-files
                    writeable-files
                    list-all-package-names-lst
                    user-stobj-alist1
                    ;; updaters:
                    update-open-input-channels
                    update-open-output-channels
                    update-global-table
                    update-t-stack
                    update-32-bit-integer-stack
                    update-big-clock-entry
                    update-idates
                    update-acl2-oracle
                    update-file-clock
                    ;; update-readable-files
                    update-written-files
                    update-read-files
                    ;; update-writeable-files
                    update-list-all-package-names-lst
                    update-user-stobj-alist1))

;move up?
(defthm state-p1-of-update-open-input-channels
  (implies (state-p1 state)
           (equal (state-p1 (update-open-input-channels x state))
                  (open-channels-p x)))
  :hints (("Goal" :in-theory (e/d (state-p1)
                                  ()))))

(defthm state-p1-of-update-read-files
  (implies (state-p1 state)
           (equal (state-p1 (update-read-files x state))
                  (read-files-p x)))
  :hints (("Goal" :in-theory (e/d (state-p1)
                                  (true-listp)))))

(defthm state-p1-of-update-file-clock
  (implies (state-p1 state)
           (equal (state-p1 (update-file-clock x state))
                  (file-clock-p x)))
  :hints (("Goal" :in-theory (e/d (state-p1)
                                  (true-listp)))))

(defthm read-files-p-of-cons
  (equal (read-files-p (cons item read-files))
         (and (read-file-listp1 item)
              (read-files-p read-files)))
  :hints (("Goal" :in-theory (enable read-files-p))))

(local
 (defthm integerp-of-+
   (implies (and (integerp x)
                 (integerp y))
            (integerp (+ x y)))))

(defthmd integerp-when-file-clock-p
  (implies (file-clock-p file-clock)
           (integerp file-clock))
  :hints (("Goal" :in-theory (enable file-clock-p))))

;todo: move to channels.lisp, but that depends on this so first separate out the basic stuff in this book
(defthm state-p1-of-close-input-channel
  (implies (and (symbolp channel)
                (open-input-channel-p1 channel typ state) ;type is a free var
                (member-equal typ '(:byte :character :object))
                (state-p1 state))
           (state-p1 (close-input-channel channel state)))
  :hints (("Goal" :in-theory (enable close-input-channel
                                     stringp-of-caddr-when-channel-headerp
                                     integerp-of-cadddr-when-channel-headerp
                                     integerp-when-file-clock-p))))

;avoids free var
(defthm state-p1-of-close-input-channel-alt
  (implies (and (symbolp channel)
                (open-input-channel-any-p1 channel state)
                (state-p1 state))
           (state-p1 (close-input-channel channel state)))
  :hints (("Goal" :in-theory (e/d (open-input-channel-any-p1)
                                  (open-input-channel-p1)))))

(local (in-theory (disable true-listp))) ;prevent induction

(local
 (defthm assoc-equal-when-all-boundp
  (implies (and (all-boundp alist1 alist2) ; alist1 is a free var
                (member-equal key (strip-cars alist1)))
           (assoc-equal key alist2))
  :hints (("Goal" :in-theory (enable assoc-equal all-boundp member-equal)))))

;; todo: these are true for anything in *initial-global-table*?:

(defthm boundp-global1-of-system-books-dir-when-state-p1
  (implies (state-p1 state)
           (boundp-global1 'system-books-dir state))
  :hints (("Goal" :in-theory (enable state-p1 boundp-global1))))

;; The conclusion matches the guard of get-global
(defthm assoc-equal-of-system-books-dir-and-global-table-when-state-p1
  (implies (state-p1 state)
           (assoc-equal 'system-books-dir (global-table state)))
  :hints (("Goal" :in-theory (enable state-p1))))

;; (defthm boundp-global-of-system-books-dir-when-state-p1
;;   (implies (state-p state)
;;            (boundp-global 'system-books-dir state))
;;   :hints (("Goal" :in-theory (enable state-p1))))

(defthm boundp-global-of-system-books-dir-when-state-p
  (implies (state-p state)
           (boundp-global 'system-books-dir state))
  :hints (("Goal" :in-theory (enable state-p state-p1 boundp-global))))
