; Rules about the ACL2 state
;
; Copyright (C) 2021-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Organize this stuff, possibly moving some to other files
;; TODO: Name conflicts with std?
;; TODO: Add missing theorems here

;; See also books/system/update-state.lisp.

;move?
(defthm written-files-p-of-cons
   (equal (written-files-p (cons file files))
          (and (written-file file)
               (written-files-p files)))
   :hints (("Goal" :in-theory (enable written-files-p))))

(deftheory state-field-accessors
  '(open-input-channels
    open-output-channels
    global-table
    idates
    acl2-oracle
    file-clock
    readable-files
    written-files
    read-files
    writeable-files
    user-stobj-alist1)
  :redundant-okp t)

(deftheory state-field-updaters
  '(update-open-input-channels
    update-open-output-channels
    update-global-table
    update-idates
    update-acl2-oracle
    update-file-clock
    ;; update-readable-files
    update-written-files
    update-read-files
    ;; update-writeable-files
    update-user-stobj-alist1)
  :redundant-okp t)

;; Disable predicates on state components (TODO: Add more)
(in-theory (disable open-channels-p
                    ordered-symbol-alistp
                    all-boundp
                    file-clock-p
                    read-files-p
                    readable-files-p
                    writeable-files-p
                    written-files-p
                    ;; so the rules below fire:
                    boundp-global
                    boundp-global1
                    w
                    ;; Disable the accessors and updaters of the fields of state:
                    state-field-accessors
                    state-field-updaters
                    ;; Disable the state predicates
                    state-p
                    state-p1))

(local (in-theory (disable assoc-equal nth update-nth true-listp)))

;; since the state is a true-list
(defthm true-listp-of-update-open-input-channels
  (implies (true-listp st)
           (true-listp (update-open-input-channels x st)))
  :hints (("Goal" :in-theory (enable update-open-input-channels))))

;; since the state is a true-list
(defthm true-listp-of-update-open-output-channels
  (implies (true-listp st)
           (true-listp (update-open-output-channels x st)))
  :hints (("Goal" :in-theory (enable update-open-output-channels))))

;; since the state is a true-list
(defthm true-listp-of-update-file-clock
  (implies (true-listp st)
           (true-listp (update-file-clock x st)))
  :hints (("Goal" :in-theory (enable update-file-clock))))

;; since the state is a true-list
(defthm true-listp-of-update-global-table
  (implies (true-listp st)
           (true-listp (update-global-table x st)))
  :hints (("Goal" :in-theory (enable update-global-table))))

;; since the state is a true-list
(defthm true-listp-of-update-read-files
  (implies (true-listp st)
           (true-listp (update-read-files x st)))
  :hints (("Goal" :in-theory (enable update-read-files))))

;; since the state is a true-list
(defthm true-listp-of-update-written-files
  (implies (true-listp st)
           (true-listp (update-written-files x st)))
  :hints (("Goal" :in-theory (enable update-written-files))))

(defthm len-of-update-open-input-channels
  (implies (state-p1 state)
           (equal (len (update-open-input-channels x state))
                  (len state)))
  :hints (("Goal" :in-theory (enable update-open-input-channels state-p1))))

(defthm len-of-update-open-output-channels
  (implies (state-p1 state)
           (equal (len (update-open-output-channels x state))
                  (len state)))
  :hints (("Goal" :in-theory (enable update-open-output-channels state-p1))))

(defthm len-of-update-file-clock
  (implies (state-p1 state)
           (equal (len (update-file-clock x state))
                  (len state)))
  :hints (("Goal" :in-theory (enable update-file-clock state-p1))))

(defthm len-of-update-global-table
  (implies (state-p1 state)
           (equal (len (update-global-table x state))
                  (len state)))
  :hints (("Goal" :in-theory (enable update-global-table state-p1))))

(defthm len-of-update-read-files
  (implies (state-p1 state)
           (equal (len (update-read-files x state))
                  (len state)))
  :hints (("Goal" :in-theory (enable update-read-files state-p1))))

(defthm len-of-update-written-files
  (implies (state-p1 state)
           (equal (len (update-written-files x state))
                  (len state)))
  :hints (("Goal" :in-theory (enable update-written-files state-p1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conjuncts of state-p

;; TODO: Think about the rule-classes for these:

(defthm read-files-p-of-read-files
  (implies (state-p1 state)
           (read-files-p (read-files state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm written-files-p-of-written-files
  (implies (state-p1 state)
           (written-files-p (written-files state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm readable-files-p-of-readable-files
  (implies (state-p1 state)
           (readable-files-p (readable-files state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm open-channels-p-of-open-input-channels
  (implies (state-p1 state)
           (open-channels-p (open-input-channels state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm open-channels-p-of-open-output-channels
  (implies (state-p1 state)
           (open-channels-p (open-output-channels state)))
  :hints (("Goal" :in-theory (enable state-p1))))

; Matt K. addition:
(defthm state-p1-forward-to-true-listp-acl2-oracle
  (implies (state-p1 state)
           (true-listp (acl2-oracle state)))
  :hints (("Goal" :in-theory (enable state-p1)))
  :rule-classes :forward-chaining)

(defthm file-clock-p-of-file-clock
  (implies (state-p1 state)
           (file-clock-p (file-clock state)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm natp-of-file-clock
  (implies (state-p1 state)
           (natp (file-clock state)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm writeable-files-p-of-writeable-files
  (implies (state-p1 state)
           (writeable-files-p (writeable-files state)))
  :hints (("Goal" :in-theory (enable state-p1))))



;; Read-over-write theorems for states (different fields)

;; TODO: Organize these, and get the complete set
(encapsulate ()
  (local (in-theory (enable state-field-accessors state-field-updaters)))

  (defthm global-table-of-update-open-input-channels
    (equal (global-table (update-open-input-channels x st))
           (global-table st)))

  (defthm global-table-of-update-open-output-channels
    (equal (global-table (update-open-output-channels x st))
           (global-table st)))

; Matt K. addition:
  (defthm global-table-of-update-acl2-oracle
    (equal (global-table (update-acl2-oracle x st))
           (global-table st)))

  (defthm global-table-of-update-file-clock
    (equal (global-table (update-file-clock x st))
           (global-table st)))

  (defthm readable-files-of-update-open-input-channels
    (equal (readable-files (update-open-input-channels x st))
           (readable-files st)))

  (defthm readable-files-of-update-open-output-channels
    (equal (readable-files (update-open-output-channels x st))
           (readable-files st)))

  (defthm readable-files-of-update-file-clock
    (equal (readable-files (update-file-clock x st))
           (readable-files st)))

  (defthm readable-files-of-update-global-table
    (equal (readable-files (update-global-table x st))
           (readable-files st)))

  (defthm writeable-files-of-update-open-input-channels
    (equal (writeable-files (update-open-input-channels x st))
           (writeable-files st)))

  (defthm writeable-files-of-update-open-output-channels
    (equal (writeable-files (update-open-output-channels x st))
           (writeable-files st)))

  (defthm writeable-files-of-update-file-clock
    (equal (writeable-files (update-file-clock x st))
           (writeable-files st)))

  (defthm writeable-files-of-update-global-table
    (equal (writeable-files (update-global-table x st))
           (writeable-files st)))

  (defthm file-clock-of-update-open-input-channels
    (equal (file-clock (update-open-input-channels x st))
           (file-clock st)))

  (defthm file-clock-of-update-open-output-channels
    (equal (file-clock (update-open-output-channels x st))
           (file-clock st)))

  (defthm file-clock-of-update-global-table
    (equal (file-clock (update-global-table x st))
           (file-clock st)))

  (defthm written-files-of-update-open-input-channels
    (equal (written-files (update-open-input-channels x st))
           (written-files st)))

  (defthm written-files-of-update-open-output-channels
    (equal (written-files (update-open-output-channels x st))
           (written-files st)))

  (defthm written-files-of-update-file-clock
    (equal (written-files (update-file-clock x st))
           (written-files st)))

  (defthm idates-of-update-open-input-channels
    (equal (idates (update-open-input-channels x st))
           (idates st)))

  (defthm idates-of-update-open-output-channels
    (equal (idates (update-open-output-channels x st))
           (idates st)))

  (defthm idates-of-update-file-clock
    (equal (idates (update-file-clock x st))
           (idates st)))

  (defthm user-stobj-alist1-of-update-open-input-channels
    (equal (user-stobj-alist1 (update-open-input-channels x st))
           (user-stobj-alist1 st)))

  (defthm user-stobj-alist1-of-update-open-output-channels
    (equal (user-stobj-alist1 (update-open-output-channels x st))
           (user-stobj-alist1 st)))

  (defthm user-stobj-alist1-of-update-file-clock
    (equal (user-stobj-alist1 (update-file-clock x st))
           (user-stobj-alist1 st)))

  (defthm user-stobj-alist1-of-update-global-table
    (equal (user-stobj-alist1 (update-global-table x st))
           (user-stobj-alist1 st)))

  (defthm acl2-oracle-of-update-open-input-channels
    (equal (acl2-oracle (update-open-input-channels x st))
           (acl2-oracle st)))

  (defthm acl2-oracle-of-update-open-output-channels
    (equal (acl2-oracle (update-open-output-channels x st))
           (acl2-oracle st)))

  (defthm acl2-oracle-of-update-file-clock
    (equal (acl2-oracle (update-file-clock x st))
           (acl2-oracle st)))

  (defthm acl2-oracle-of-update-global-table
    (equal (acl2-oracle (update-global-table x st))
           (acl2-oracle st)))

  (defthm read-files-of-update-open-input-channels
    (equal (read-files (update-open-input-channels x st))
           (read-files st)))

  (defthm read-files-of-update-open-output-channels
    (equal (read-files (update-open-output-channels x st))
           (read-files st)))

  (defthm read-files-of-update-file-clock
    (equal (read-files (update-file-clock x st))
           (read-files st)))

  (defthm read-files-of-update-global-table
    (equal (read-files (update-global-table x st))
           (read-files st)))

  (defthm read-files-of-update-written-files
    (equal (read-files (update-written-files x st))
           (read-files st)))

  (defthm open-output-channels-of-update-open-input-channels
    (equal (open-output-channels (update-open-input-channels x st))
           (open-output-channels st)))

  (defthm open-output-channels-of-update-file-clock
    (equal (open-output-channels (update-file-clock x st))
           (open-output-channels st)))

  (defthm open-output-channels-of-update-global-table
    (equal (open-output-channels (update-global-table x st))
           (open-output-channels st)))

;move?
  (defthm open-output-channels-of-put-global
    (equal (open-output-channels (put-global key value st))
           (open-output-channels st)))

  (defthm open-input-channels-of-update-file-clock
    (equal (open-input-channels (update-file-clock x st))
           (open-input-channels st)))

  (defthm open-input-channels-of-update-global-table
    (equal (open-input-channels (update-global-table x st))
           (open-input-channels st)))

  (defthm open-input-channels-of-update-open-output-channels
    (equal (open-input-channels (update-open-output-channels x st))
           (open-input-channels st)))

; Matt K. addition:
  (defthm open-input-channels-of-update-acl2-oracle
    (equal (open-input-channels (update-acl2-oracle x st))
           (open-input-channels st)))

  (defthm global-table-of-update-read-files
    (equal (global-table (update-read-files x st))
           (global-table st)))

  (defthm global-table-of-update-written-files
    (equal (global-table (update-written-files x st))
           (global-table st)))

  (defthm global-table-of-update-open-output-channels
    (equal (global-table (update-open-output-channels x st))
           (global-table st)))

  (defthm readable-files-of-update-read-files
    (equal (readable-files (update-read-files x st))
           (readable-files st)))

  (defthm writeable-files-of-update-read-files
    (equal (writeable-files (update-read-files x st))
           (writeable-files st)))

  (defthm file-clock-of-update-read-files
    (equal (file-clock (update-read-files x st))
           (file-clock st)))

  (defthm written-files-of-update-read-files
    (equal (written-files (update-read-files x st))
           (written-files st)))

  (defthm readable-files-of-update-written-files
    (equal (readable-files (update-written-files x st))
           (readable-files st)))

  (defthm writeable-files-of-update-written-files
    (equal (writeable-files (update-written-files x st))
           (writeable-files st)))

  (defthm file-clock-of-update-written-files
    (equal (file-clock (update-written-files x st))
           (file-clock st)))

  (defthm written-files-of-update-global-table
    (equal (written-files (update-global-table x st))
           (written-files st)))

  (defthm idates-of-update-read-files
    (equal (idates (update-read-files x st))
           (idates st)))

  (defthm idates-of-update-written-files
    (equal (idates (update-written-files x st))
           (idates st)))

  (defthm idates-of-update-global-table
    (equal (idates (update-global-table x st))
           (idates st)))

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

  (defthm user-stobj-alist1-of-update-written-files
    (equal (user-stobj-alist1 (update-written-files x st))
           (user-stobj-alist1 st)))

  (defthm acl2-oracle-of-update-written-files
    (equal (acl2-oracle (update-written-files x st))
           (acl2-oracle st)))

  (defthm open-output-channels-of-update-written-files
    (equal (open-output-channels (update-written-files x st))
           (open-output-channels st)))

  (defthm open-input-channels-of-update-written-files
    (equal (open-input-channels (update-written-files x st))
           (open-input-channels st)))


  )

;; read-over-write rules (same field)

(encapsulate ()
  (local (in-theory (enable state-field-accessors state-field-updaters)))

  (defthm file-clock-of-update-file-clock
    (equal (file-clock (update-file-clock x state))
           x))

  (defthm global-table-of-update-global-table
    (equal (global-table (update-global-table x state))
           x))

  (defthm open-input-channels-of-update-open-input-channels
    (equal (open-input-channels (update-open-input-channels x state))
           x))

  (defthm open-output-channels-of-update-open-output-channels
    (equal (open-output-channels (update-open-output-channels x state))
           x))

  (defthm read-files-of-update-read-files
    (equal (read-files (update-read-files x state))
           x)
    :hints (("Goal" :in-theory (enable read-files update-read-files))))

  (defthm written-files-of-update-written-files
      (equal (written-files (update-written-files x state))
           x)
    :hints (("Goal" :in-theory (enable written-files update-written-files))))
  )

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

;; implied by open-channels-p
(defthm ordered-symbol-alistp-of-open-output-channels
  (implies (state-p1 state)
           (ordered-symbol-alistp (open-output-channels state))))

;; implied by open-channels-p
(defthm open-channel-listp-of-open-output-channels
  (implies (state-p1 state)
           (open-channel-listp (open-output-channels state)))
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

;; todo: flesh out this list:

;move up?
(defthm state-p1-of-update-open-input-channels
  (implies (state-p1 state)
           (equal (state-p1 (update-open-input-channels x state))
                  (open-channels-p x)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defthm state-p-of-update-open-input-channels
  (implies (state-p state)
           (equal (state-p (update-open-input-channels x state))
                  (open-channels-p x)))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm state-p1-of-update-open-output-channels
  (implies (state-p1 state)
           (equal (state-p1 (update-open-output-channels x state))
                  (open-channels-p x)))
  :hints (("Goal" :in-theory (enable state-p1 ;UPDATE-OPEN-OUTPUT-CHANNELS
                                   ))))

(defthm state-p-of-update-open-output-channels
  (implies (state-p state)
           (equal (state-p (update-open-output-channels x state))
                  (open-channels-p x)))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm state-p1-of-update-read-files
  (implies (state-p1 state)
           (equal (state-p1 (update-read-files x state))
                  (read-files-p x)))
  :hints (("Goal" :in-theory (e/d (state-p1)
                                  (true-listp)))))

(defthm state-p1-of-update-written-files
  (implies (state-p1 state)
           (equal (state-p1 (update-written-files x state))
                  (written-files-p x)))
  :hints (("Goal" :in-theory (e/d (state-p1)
                                  (true-listp)))))

(defthm state-p-of-update-written-files
  (implies (state-p state)
           (equal (state-p (update-written-files x state))
                  (written-files-p x)))
  :hints (("Goal" :in-theory (e/d (state-p)
                                  (true-listp)))))

(defthm state-p-of-update-acl2-oracle
  (implies (and (state-p state)
                (true-listp x))
           (state-p (update-acl2-oracle x state)))
  :hints (("Goal" :in-theory (enable state-p))))

;state-p could call this
(defund global-table-p (x)
  (declare (xargs :guard t))
  (and (ordered-symbol-alistp x)
       (all-boundp *initial-global-table* x)
       (plist-worldp (cdr (assoc 'current-acl2-world
                                 x)))
       (symbol-alistp (getpropc 'acl2-defaults-table
                                'table-alist
                                nil
                                (cdr (assoc 'current-acl2-world
                                            x))))
       (timer-alistp (cdr (assoc 'timer-alist x)))
       (print-base-p (cdr (assoc 'print-base x)))
       (known-package-alistp
        (getpropc 'known-package-alist
                  'global-value
                  nil
                  (cdr (assoc 'current-acl2-world
                              x))))))

(defthm state-p1-of-update-global-table
  (implies (state-p1 state)
           (equal (state-p1 (update-global-table x state))
                  (global-table-p x)))
  :hints (("Goal" :in-theory (e/d (state-p1 global-table-p)
                                  (true-listp)))))

(defthm state-p-of-update-global-table
  (implies (state-p state)
           (equal (state-p (update-global-table x state))
                  (global-table-p x)))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm state-p1-of-update-file-clock
  (implies (state-p1 state)
           (equal (state-p1 (update-file-clock x state))
                  (file-clock-p x)))
  :hints (("Goal" :in-theory (e/d (state-p1)
                                  (true-listp)))))

(defthm state-p-of-update-file-clock
  (implies (state-p state)
           (equal (state-p (update-file-clock x state))
                  (file-clock-p x)))
  :hints (("Goal" :in-theory (enable state-p))))

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

(local
 (defthm assoc-equal-when-all-boundp
  (implies (and (all-boundp alist1 alist2) ; alist1 is a free var
                (member-equal key (strip-cars alist1)))
           (assoc-equal key alist2))
  :hints (("Goal" :in-theory (enable assoc-equal all-boundp member-equal)))))

(defconst *initial-globals*
  (strip-cars *initial-global-table*))

;; todo: these are true for anything in *initial-global-table*?:

(defthm boundp-global1-when-state-p1
  (implies (and (member-equal global-name *initial-globals*)
                (state-p1 state))
           (boundp-global1 global-name state))
  :hints (("Goal" :in-theory (e/d (state-p1 boundp-global1)
                                  (member-equal)))))

;; The conclusion matches the guard of get-global
(defthm assoc-equal-of-global-table-when-state-p1
  (implies (and (member-equal global-name *initial-globals*)
                (state-p1 state))
           (assoc-equal global-name (global-table state)))
  :hints (("Goal" :in-theory (e/d (state-p1)
                                  (member-equal)))))

;; (defthm boundp-global-when-state-p1
;;   (implies (and (member-equal global-name *initial-globals*)
;;                 (state-p state))
;;            (boundp-global global-name state))
;;   :hints (("Goal" :in-theory (enable state-p1))))

(defthm boundp-global1-when-state-p
  (implies (and (member-equal global-name *initial-globals*)
                (state-p state))
           (boundp-global1 global-name state))
  :hints (("Goal" :in-theory (e/d (state-p state-p1 boundp-global1)
                                  (member-equal)))))

(defthm boundp-global-when-state-p
  (implies (and (member-equal global-name *initial-globals*)
                (state-p state))
           (boundp-global global-name state))
  :hints (("Goal" :in-theory (enable boundp-global))))

(defthm plist-worldp-of-w-when-state-p1
  (implies (state-p1 state)
           (plist-worldp (w state)))
  :hints (("Goal" :in-theory (enable state-p1 w))))

(defthm state-p1-of-put-global
  (implies (and (state-p1 state)
                (symbolp key)
                (not (member-equal key '(current-acl2-world timer-alist print-base))) ; todo
                )
           (state-p1 (put-global key value state)))
  :hints (("Goal" :in-theory (enable put-global state-p1 global-table-p))))

(defthm state-p-of-put-global
  (implies (and (state-p state)
                (symbolp key)
                (not (member-equal key '(current-acl2-world timer-alist print-base))) ; todo
                )
           (state-p (put-global key value state)))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm boundp-global1-of-put-global
  (implies (not (equal name key))
           (equal (boundp-global1 name (put-global key value state))
                  (boundp-global1 name state)))
  :hints (("Goal" :in-theory (enable put-global boundp-global1))))

; Matt K. addition:
(defthm global-table-p-add-pair
  (implies (and (symbolp sym)
                (not (eq sym 'current-acl2-world))
                (not (eq sym 'timer-alist))
                (not (eq sym 'print-base))
                (global-table-p x))
           (global-table-p (add-pair sym val x)))
  :hints (("Goal" :in-theory (enable global-table-p add-pair))))

; Matt K. addition:
(defthm global-table-p-of-global-table
  (implies (state-p1 state)
           (global-table-p (global-table state)))
  :hints (("Goal" :in-theory (enable global-table-p global-table))))
