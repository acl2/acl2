
; sra-records.lisp                              Vivek & Warren

; Copyright (C) 2020-2022, ForrestHunt, Inc.
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; See file ``README'' for additional information.

; This file defines the VWSIM "record" that stores the simulation
; state for all variables.

(in-package "ACL2")

(include-book "std/util/bstar" :dir :system)
(include-book "num")

(defun symbol-rational-list-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (let ((pair (car x)))
           (and (consp pair)
                (symbolp (car pair))
                (rational-listp (cdr pair))))
         (symbol-rational-list-alistp (cdr x)))))

(defthm symbol-num-list-alistp-is-symbol-rational-list-alistp
  (implies (symbol-num-list-alistp x)
           (symbol-rational-list-alistp x)))

(defthm symbol-rational-listp-alistp-forward-to-alistp
  (implies (symbol-rational-list-alistp x)
           (alistp x))
  :rule-classes :forward-chaining)

(defthm rational-listp-cdr-hons-assoc-symbol-rational-list-alistp
  (implies (symbol-rational-list-alistp r)
           (rational-listp (cdr (hons-assoc-equal x r)))))

(defthm num-listp-cdr-hons-assoc-symbol-rational-list-alistp
  (implies (symbol-num-list-alistp r)
           (num-listp (cdr (hons-assoc-equal x r)))))

(defun alist-entry-consp (x)
  (declare (xargs :guard (alistp x)))
  (if (atom x)
      t
    (let* ((pair (car x))
           (entry (cdr pair)))
      (and (consp entry)
           (alist-entry-consp (cdr x))))))

(defun record-entries-consp (r)
  (declare (xargs :guard t))
  (and (symbol-num-list-alistp r)
       (alist-entry-consp r)))

; Record updating functions

(defun symbol-rational-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (let ((pair (car x)))
           (and (consp pair)
                (symbolp (car pair))
                (rationalp (cdr pair))))
         (symbol-rational-alistp (cdr x)))))

(defun update-r-by-name (r names vals)
  "Update time-value records; expected usage with ~
   (no-duplicatesp (strip-cars names-vals))."
  (declare (xargs :guard (and (symbol-rational-list-alistp r)
                              (alist-entry-consp r)
                              (symbol-listp names)
                              (rational-listp vals)
                              (= (len names) (len vals)))))
  (if (atom names)
      r
    (b* ((r1 (update-r-by-name r (cdr names) (cdr vals)))
         (name (car names))
         (value (car vals))
         (name-record (hons-get name r1))
         (record (cdr name-record))
         (extended-record (cons value record)))
      (hons-acons name extended-record r1))))

(defthm alistp-update-r-by-name
  (implies (alistp r)
           (alistp (update-r-by-name r names vals))))

(defthm alistp-entry-consp--update-r-by-name
  (implies (alist-entry-consp r)
           (alist-entry-consp (update-r-by-name r names vals))))

(defthm symbol-rational-list-1-alistp-update-r-by-name
  (implies (and (symbol-rational-list-alistp r)
                (symbol-listp names)
                (rational-listp vals)
                (= (len names) (len vals)))
           (symbol-rational-list-alistp (update-r-by-name r names vals))))

(defthm record-entries-consp-update-r-by-name
  (implies (and (record-entries-consp r)
                (symbol-listp names)
                (rational-listp vals)
                (= (len names) (len vals)))
           (record-entries-consp (update-r-by-name r names vals))))

(defun all-hons-assoc-equal (names r)
  (declare (xargs :guard (and (symbol-listp names)
                              (alistp r))))
  (if (atom names)
      t
    (and (hons-assoc-equal (car names) r)
         (all-hons-assoc-equal (cdr names) r))))

(defthm hons-get-update-r-by-name
  (implies (hons-assoc-equal name r)
           (hons-assoc-equal name (update-r-by-name r names vals))))

(defthm all-hons-assoc-equal-update-r-by-name
  (implies (all-hons-assoc-equal xs r)
           (all-hons-assoc-equal xs (update-r-by-name r names vals)))
  :hints
  (("Goal"
    :induct (all-hons-assoc-equal xs (update-r-by-name r names vals))
    :in-theory (disable update-r-by-name))))

(defun all-hons-assoc-cddr (names r)
  (declare (xargs :guard (and (symbol-listp names)
                              (symbol-rational-list-alistp r))))
  (if (atom names)
      t
    (and (hons-assoc-equal (car names) r)
         (cddr (hons-assoc-equal (car names) r))
         (all-hons-assoc-cddr (cdr names) r))))

(defthm rationalp-cadr-hons-assoc-name
  (implies (and (or (symbol-rational-list-alistp r)
                    (symbol-num-list-alistp r))
                (cdr (hons-assoc-equal name r)))
           (and (rationalp (cadr (hons-assoc-equal name r)))
                (nump (cadr (hons-assoc-equal name r))))))

(defthm rationalp-caddr-hons-assoc-name
  (implies (and (or (symbol-rational-list-alistp r)
                    (symbol-num-list-alistp r))
                (cddr (hons-assoc-equal name r)))
           (and (rationalp (caddr (hons-assoc-equal name r)))
                (nump (caddr (hons-assoc-equal name r))))))

(in-theory (disable update-r-by-name))

; Some events for fast-alist records

(defthm symbol-rational-list-alistp-of-fast-alist-fork
  (implies (and (symbol-rational-list-alistp ans)
                (symbol-rational-list-alistp r))
           (symbol-rational-list-alistp (fast-alist-fork r ans))))

(defthm symbol-num-list-alistp-of-fast-alist-fork
  (implies (and (symbol-num-list-alistp ans)
                (symbol-num-list-alistp r))
           (symbol-num-list-alistp (fast-alist-fork r ans))))

(encapsulate
  ()
  (local
   (defthm not-symbol-rational-list-alistp-cdr-last
     (implies (symbol-rational-list-alistp x)
              (not (cdr (last x))))))

  (defthm symbol-rational-list-alistp-of-fast-alist-clean
    (implies (symbol-rational-list-alistp r)
             (symbol-rational-list-alistp (fast-alist-clean r)))))

(encapsulate
  ()
  (local
   (defthm not-symbol-num-list-alistp-cdr-last
     (implies (symbol-num-list-alistp x)
              (not (cdr (last x))))))

  (defthm symbol-num-list-alistp-of-fast-alist-clean
    (implies (symbol-num-list-alistp r)
             (symbol-num-list-alistp (fast-alist-clean r)))))

(encapsulate
  ()

  (local
   (defthm first-observation-about-fast-alist-fork
     (implies (atom source)
              (equal (hons-assoc-equal name (fast-alist-fork source target))
                     (hons-assoc-equal name target)))))

  (local
   (defthmd second-observation-about-fast-alist-fork
     ;; Warning -- this lemma hurts us later!
     (implies (atom (car source))
              (equal (hons-assoc-equal name (fast-alist-fork source target))
                     (hons-assoc-equal name (fast-alist-fork (cdr source) target))))))

  (local
   (defthm third-observation-about-fast-alist-fork
     (implies (hons-assoc-equal name target)
              (equal (hons-assoc-equal name (fast-alist-fork source target))
                     (hons-assoc-equal name target)))))

  (local
   (defthm fourth-observation-about-fast-alist-fork
     (implies (not (hons-assoc-equal name target))
              (equal (hons-assoc-equal name (fast-alist-fork source target))
                     (hons-assoc-equal name source)))))

  (local
   (defthm fifth-observation-about-fast-alist-fork
     (implies (atom target)
              (equal (hons-assoc-equal name (fast-alist-fork source target))
                     (hons-assoc-equal name source)))))

  (local
   (defthm atom-cdr-last
     (atom (cdr (last alst)))))

  (defthm observation-about-fast-alist-clean
    (equal (hons-assoc-equal name (fast-alist-clean alst))
           (hons-assoc-equal name alst))
    :hints
    (("Goal"
      :do-not-induct t
      :in-theory (disable fifth-observation-about-fast-alist-fork)
      :use ((:instance fifth-observation-about-fast-alist-fork
                       (name name)
                       (source alst)
                       (target (cdr (last alst)))))))))

(defthm all-hons-assoc-equal-fast-alist-clean
   (equal (all-hons-assoc-equal names (fast-alist-clean alst))
          (all-hons-assoc-equal names alst))
   :hints
   ;; Only the :executable-counterpart of fast-alist-clean is disabled at this
   ;; point, and we want its definition disabled as well.  To see which runes
   ;; are disabled, evaluate (disabledp 'fast-alist-clean).
   (("Goal" :in-theory (disable fast-alist-clean))))

(defthm alist-entry-consp-fast-alist-fork
  (implies (and (alist-entry-consp source)
                (alist-entry-consp target))
           (alist-entry-consp (fast-alist-fork source target))))

(encapsulate
  ()
  (local
   (defthm atom-alist-entry-consp
     (implies (atom x)
              (alist-entry-consp x))))

  (local
   (defthm atom-cdr-last
     (atom (cdr (last alst)))))

  (defthm alist-entry-consp-fast-alist-clean
    (implies (alist-entry-consp source)
             (alist-entry-consp (fast-alist-clean source)))
    :hints
    (("Goal"
      :do-not-induct t
      :in-theory (disable alist-entry-consp fast-alist-fork
                          alist-entry-consp-fast-alist-fork
                          atom-alist-entry-consp)
      :use ((:instance alist-entry-consp-fast-alist-fork
                       (source source)
                       (target (if (consp source)
                                   (cdr (last source))
                                 source)))
            (:instance atom-alist-entry-consp
                       (x (cdr (last source)))))))))

(defthm record-entries-consp-fast-alist-clean
  (implies (record-entries-consp r)
           (record-entries-consp (fast-alist-clean r)))
  :hints
  (("Goal" :in-theory (disable fast-alist-clean))))

(defthm alistp-pairlis$
  ;; This event needs to find a proper home.
  (alistp (pairlis$ x y)))

(defthm alistp-append
  ;; This event needs to find a proper home.
  (implies (and (alistp x)
                (alistp y))
           (alistp (append x y))))

(encapsulate
  ()
  (local
   (defthm hons-assoc-equal-update-r-by-name
     (implies t ;; (alistp alst)
              (iff (hons-assoc-equal name
                                     (update-r-by-name r names vals))
                   (or (hons-assoc-equal name r)
                       (member-equal name names))))
     :hints (("Goal" :in-theory (enable update-r-by-name)))))

  (local
   (defthm open-update-r-by-name-once-1
     (implies (and (symbolp name)
                   (rationalp val))
              (hons-assoc-equal name
                                (update-r-by-name r (cons name names)
                                                  (cons val vals))))
   :hints (("Goal" :in-theory (enable update-r-by-name)))))

  (local
   (defthm open-update-r-by-name-once-2
     (implies (and (symbolp name)
                   (rationalp val)
                   (cddr (hons-assoc-equal
                          name
                          (update-r-by-name r names vals))))
              (cddr (hons-assoc-equal
                     name
                     (update-r-by-name r (cons name names)
                                       (cons val vals)))))
     :hints (("goal" :in-theory (enable update-r-by-name)))))

  (local
   (defthm open-update-r-by-name-once
     (implies (and (symbolp name)
                   (rationalp val)
                   (all-hons-assoc-cddr xs (update-r-by-name r names vals)))
              (all-hons-assoc-cddr
               xs
               (update-r-by-name r (cons name names) (cons val vals))))
     :hints (("Goal" :induct (len xs) :in-theory (enable update-r-by-name)))))

  (defthm hons-assoc-equal-extra-fact
    (implies (and (alist-entry-consp r)
                  (hons-assoc-equal key r))
              (cdr (hons-assoc-equal key r))))

  (local
   (defthm hons-assoc-equal-consp-cddr-update-r-by-single-name
     (implies (and (alist-entry-consp r)
                   (hons-assoc-equal key r))
              (cddr (hons-assoc-equal
                     key
                     (update-r-by-name r
                                       (cons key names) vals))))
     :hints
     (("Goal" :in-theory (enable update-r-by-name)))))

  #||
  (defthm hons-assoc-equal-consp-cddr-update-r-by-name-1
    (implies
     (and (symbol-rational-list-alistp r)
          (alist-entry-consp r)
          (all-hons-assoc-equal x-names r)
          (= (len x-names) (len x-values)))
     (all-hons-assoc-cddr
      x-names
      (update-r-by-name r x-names x-values))))

  (defthm hons-assoc-equal-consp-cddr-update-r-by-name-2
    (implies
     (and (record-entries-consp r)
          (all-hons-assoc-equal x-names r)
          (= (len x-names) (len x-values)))
     (all-hons-assoc-cddr
      x-names
      (update-r-by-name r x-names x-values))))
  ||#
)
