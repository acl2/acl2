; A lightweight book about i/o channels
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also channel-contents.lisp

(include-book "kestrel/bv-lists/unsigned-byte-listp-def" :dir :system)

;; So the rules in this book fire
(in-theory (disable open-channels-p
                    add-pair
                    open-channel-listp
                    open-channel1
                    close-input-channel))

;move?
(local
 (defthm assoc-equal-when-ordered-symbol-alistp-and-symbol<-of-caar
   (implies (and (ordered-symbol-alistp alist)
                 (symbol< key (car (car alist))))
            (equal (assoc-equal key alist)
                   nil))
   :hints (("Goal" :in-theory (enable ordered-symbol-alistp assoc-equal)))))

;; We give this notion a name that we can keep disabled, since it is an unwieldy conjunction.
(defund channel-headerp (header)
  (declare (xargs :guard t))
  (and (true-listp header)
       (equal (length header) 4)
       (eq (car header) :header)
       (member-eq (cadr header) *file-types*)
       (stringp (caddr header))
       (integerp (cadddr header))))

(defthmd stringp-of-caddr-when-channel-headerp
  (implies (channel-headerp header)
           (stringp (caddr header)))
  :hints (("Goal" :in-theory (enable channel-headerp))))

(defthmd integerp-of-cadddr-when-channel-headerp
  (implies (channel-headerp header)
           (integerp (cadddr header)))
  :hints (("Goal" :in-theory (enable channel-headerp))))

;; Avoid name clash with std
(defthm open-channel-listp-of-add-pair-strong
  (implies (open-channel-listp l)
           (equal (open-channel-listp (add-pair key value l))
                  (open-channel1 value)))
  :hints (("Goal" :in-theory (enable open-channel-listp add-pair))))

(defthm ordered-symbol-alistp-of-add-pair
  (implies (ordered-symbol-alistp x)
           (equal (ordered-symbol-alistp (add-pair key val x))
                  (symbolp key)))
  :hints (("Goal" :in-theory (enable add-pair ordered-symbol-alistp))))

;; Avoid name clash with std
(defthm open-channels-p-of-add-pair-strong
  (implies (open-channels-p channels)
           (equal (open-channels-p (add-pair channel value channels))
                  (and (symbolp channel)
                       (open-channel1 value))))
  :hints (("Goal" :in-theory (e/d (open-channels-p)
                                  (add-pair len)))))

(defthm open-channel1-of-cons
  (equal (open-channel1 (cons header rest))
         (and (channel-headerp header)
              (typed-io-listp rest (cadr header))))
  :hints (("Goal" :in-theory (enable open-channel1
                                     channel-headerp))))

(defthm channel-headerp-of-cadr-of-assoc-equal-iff
  (implies (and (symbolp channel)
                (open-channel-listp channels))
           (iff (channel-headerp (cadr (assoc-equal channel channels)))
                (assoc-equal channel channels)))
  :hints (("Goal" :in-theory (enable open-channel-listp channel-headerp))))

;; different hyp
(defthm channel-headerp-of-cadr-of-assoc-equal-iff-2
  (implies (and (symbolp channel)
                (open-channels-p channels))
           (iff (channel-headerp (cadr (assoc-equal channel channels)))
                (assoc-equal channel channels)))
  :hints (("Goal" :in-theory (enable open-channels-p))))

(defthm typed-io-listp-of-cdddr-of-assoc-equal-and-cadr-of-cadr-of-assoc-equal
  (implies (and (symbolp channel)
                (open-channel-listp channels))
           (typed-io-listp (cdddr (assoc-equal channel channels))
                           (cadr (cadr (assoc-equal channel channels)))))
  :hints (("Goal" :in-theory (enable open-channel-listp channel-headerp))))

;; different hyp
(defthm typed-io-listp-of-cdddr-of-assoc-equal-and-cadr-of-cadr-of-assoc-equal-2
  (implies (and (symbolp channel)
                (open-channels-p channels))
           (typed-io-listp (cdddr (assoc-equal channel channels))
                           (cadr (cadr (assoc-equal channel channels)))))
  :hints (("Goal" :in-theory (enable open-channels-p))))

(defthm equal-of-add-pair-same
  (implies (open-channels-p channels)
           (equal (equal (add-pair channel value channels) channels)
                  (and (assoc-eq channel channels)
                       (equal value (cdr (assoc-eq channel channels))))))
  :hints (("Goal" ;:induct (add-pair channel value channel)
           :do-not '(generalize eliminate-destructors)
           :in-theory (enable add-pair
                              open-channel-listp
                              open-channels-p))))

(defthm true-list-of-cddr-of-assoc-equal-when-open-channel-listp
  (implies (open-channel-listp channels)
           (true-listp (cddr (assoc-equal channel channels))))
  :hints (("Goal" :in-theory (enable open-channel-listp open-channel1))))

(defthmd nat-listp-when-typed-io-listp-of-byte
  (implies (typed-io-listp vals :byte)
           (nat-listp vals))
  :hints (("Goal" :in-theory (enable typed-io-listp nat-listp))))

(defthmd unsigned-byte-listp-when-typed-io-listp-of-byte
  (implies (typed-io-listp vals :byte)
           (unsigned-byte-listp 8 vals))
  :hints (("Goal" :in-theory (enable typed-io-listp unsigned-byte-listp))))

(defthm nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
  (implies (and (open-channel-listp channels)
                (equal (cadr (cadr (assoc-equal channel channels))) :byte))
           (nat-listp (cddr (assoc-equal channel channels))))
  :hints (("Goal" :in-theory (enable open-channel-listp
                                     open-channel1
                                     nat-listp-when-typed-io-listp-of-byte))))

(defthm unsigned-byte-listp-of-cddr-of-assoc-equal-when-open-channel-listp
  (implies (and (open-channel-listp channels)
                (equal (cadr (cadr (assoc-equal channel channels))) :byte))
           (unsigned-byte-listp 8 (cddr (assoc-equal channel channels))))
  :hints (("Goal" :in-theory (enable open-channel-listp
                                     open-channel1
                                     unsigned-byte-listp-when-typed-io-listp-of-byte))))

(defthm open-channel-listp-of-cons
  (equal (open-channel-listp (cons ch chs))
         (and (open-channel1 (cdr ch))
              (open-channel-listp chs)))
  :hints (("Goal" :in-theory (enable open-channel-listp))))

(defthm ordered-symbol-alistp-of-remove1-assoc-equal
  (implies (ordered-symbol-alistp channels)
           (ordered-symbol-alistp (remove1-assoc-equal channel channels)))
  :hints (("Goal" :in-theory (enable ordered-symbol-alistp))))

;; Avoid name clash with std
(defthm open-channel-listp-of-remove1-assoc-equal-alt
  (implies (open-channel-listp channels)
           (open-channel-listp (remove1-assoc-equal channel channels)))
  :hints (("Goal" :in-theory (enable open-channel-listp))))

(local (in-theory (disable ordered-symbol-alistp)))

;; Avoid name clash with std
(defthm open-channels-p-of-remove1-assoc-equal-alt
  (implies (open-channels-p channels)
           (open-channels-p (remove1-assoc-equal channel channels)))
  :hints (("Goal" :in-theory (enable open-channels-p))))

(defthm open-input-channel-p1-forward-to-assoc-equal
  (implies (open-input-channel-p1 channel typ state)
           (assoc-equal channel (open-input-channels state)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable open-input-channel-p1))))
