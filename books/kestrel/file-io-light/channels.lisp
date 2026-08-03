; A lightweight book about i/o channels
;
; Copyright (C) 2021-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also ../utilities/channel-contents.lisp

;; TODO: Should this include all the other books about channels?

(include-book "kestrel/bv-lists/unsigned-byte-listp-def" :dir :system)
(include-book "kestrel/utilities/bind-to-bool" :dir :system)
(local (include-book "typed-io-listp"))

;; So the rules in this book fire
(in-theory (disable open-channels-p
                    add-pair
                    open-channel-listp
                    open-channel1))

;move?
(local
 (defthm assoc-equal-when-ordered-symbol-alistp-and-symbol<-of-caar
   (implies (and (ordered-symbol-alistp alist)
                 (symbol< key (car (car alist))))
            (equal (assoc-equal key alist)
                   nil))
   :hints (("Goal" :in-theory (enable ordered-symbol-alistp assoc-equal)))))

;; We keep this disabled, since it is an unwieldy conjunction:
(in-theory (disable channel-headerp))

(defthm channel-headerp-of-list
  (equal (channel-headerp (list a b c d) output-p)
         (and (equal a :header)
              (member-eq b *file-types*)
              (or (stringp c)
                  (and output-p
                       (eq c :string)
                       (eq b :character)))
              (integerp d)))
  :hints (("Goal" :in-theory (enable channel-headerp))))

(defthmd stringp-of-caddr-when-channel-headerp
  (implies (and (bind-to-bool output-p)
                (channel-headerp header output-p)
                (or (not output-p)
                    (not (eq (cadr header) :character))
                    (not (eq (caddr header) :string))))
           (stringp (caddr header)))
  :hints (("Goal" :in-theory (enable channel-headerp))))

(defthmd integerp-of-cadddr-when-channel-headerp
  (implies (and (bind-to-bool output-p)
                (channel-headerp header output-p))
           (integerp (cadddr header)))
  :hints (("Goal" :in-theory (enable channel-headerp))))

(defthm typed-io-listp-of-cdr-and-cadr-of-car
  (implies (and (bind-to-bool output-p)
                (open-channel1 l output-p))
           (typed-io-listp (cdr l) (cadr (car l))))
  :hints (("Goal" :in-theory (enable open-channel1))))

;; matches better
(defthm typed-io-listp-of-cdr-gen
  (implies (and (bind-to-bool output-p)
                (open-channel1 l output-p)
                (equal typ (cadr (car l))) ; the file-type from-the header
                )
           (typed-io-listp (cdr l) typ)))

;; Avoid name clash with std
(defthm open-channel-listp-of-add-pair-strong
  (implies (open-channel-listp l output-p)
           (equal (open-channel-listp (add-pair key value l) output-p)
                  (open-channel1 value output-p)))
  :hints (("Goal" :in-theory (enable open-channel-listp add-pair))))

(defthm open-channel1-of-cdr-of-assoc-equal
  (implies (and (assoc-equal channel channels)
                (open-channel-listp channels output-p))
           (open-channel1 (cdr (assoc-equal channel channels)) output-p))
  :hints (("Goal" :in-theory (enable open-channels-p open-channel-listp))))

(defthm ordered-symbol-alistp-of-add-pair
  (implies (ordered-symbol-alistp x)
           (equal (ordered-symbol-alistp (add-pair key val x))
                  (symbolp key)))
  :hints (("Goal" :in-theory (enable add-pair ordered-symbol-alistp))))

;; Avoid name clash with std
(defthm open-channels-p-of-add-pair-strong
  (implies (open-channels-p channels output-p)
           (equal (open-channels-p (add-pair channel value channels) output-p)
                  (and (symbolp channel)
                       (open-channel1 value output-p))))
  :hints (("Goal" :in-theory (e/d (open-channels-p)
                                  (add-pair len)))))

(defthm open-channel1-of-cons
  (equal (open-channel1 (cons header rest) output-p)
         (and (channel-headerp header output-p)
              (typed-io-listp rest (cadr header))))
  :hints (("Goal" :in-theory (enable open-channel1
                                     channel-headerp))))

(defthm channel-headerp-of-cadr-of-assoc-equal-iff
  (implies (open-channel-listp channels output-p)
           (iff (channel-headerp (cadr (assoc-equal channel channels)) output-p)
                (assoc-equal channel channels)))
  :hints (("Goal" :in-theory (enable open-channel-listp channel-headerp))))

;; different hyp
(defthm channel-headerp-of-cadr-of-assoc-equal-iff-2
  (implies (open-channels-p channels output-p)
           (iff (channel-headerp (cadr (assoc-equal channel channels)) output-p)
                (assoc-equal channel channels)))
  :hints (("Goal" :in-theory (enable open-channels-p))))

(defthm typed-io-listp-of-cdddr-of-assoc-equal-and-cadr-of-cadr-of-assoc-equal
  (implies (and (bind-to-bool output-p)
                (open-channel-listp channels output-p))
           (typed-io-listp (cdddr (assoc-equal channel channels))
                           (cadr (cadr (assoc-equal channel channels)))))
  :hints (("Goal" :in-theory (enable open-channel-listp channel-headerp typed-io-listp))))

;; different hyp
(defthm typed-io-listp-of-cdddr-of-assoc-equal-and-cadr-of-cadr-of-assoc-equal-2
  (implies (and (symbolp channel)
                (bind-to-bool output-p)
                (open-channels-p channels output-p))
           (typed-io-listp (cdddr (assoc-equal channel channels))
                           (cadr (cadr (assoc-equal channel channels)))))
  :hints (("Goal" :in-theory (enable open-channels-p))))

(defthm equal-of-add-pair-same
  (implies (and (bind-to-bool output-p)
                (open-channels-p channels output-p))
           (equal (equal (add-pair channel value channels) channels)
                  (and (assoc-eq channel channels)
                       (equal value (cdr (assoc-eq channel channels))))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable add-pair
                              open-channel-listp
                              open-channels-p))))

(defthm true-listp-of-cddr-of-assoc-equal-when-open-channel-listp
  (implies (and (bind-to-bool output-p)
                (open-channel-listp channels output-p))
           (true-listp (cddr (assoc-equal channel channels))))
  :hints (("Goal" :in-theory (enable open-channel-listp open-channel1))))

(defthm nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
  (implies (and (and (bind-to-bool output-p)
                     (open-channel-listp channels output-p))
                (equal (cadr (cadr (assoc-equal channel channels))) :byte))
           (nat-listp (cddr (assoc-equal channel channels))))
  :hints (("Goal" :in-theory (enable open-channel-listp
                                     open-channel1
                                     nat-listp-when-typed-io-listp-of-byte))))

(defthm unsigned-byte-listp-of-cddr-of-assoc-equal-when-open-channel-listp
  (implies (and (and (bind-to-bool output-p)
                     (open-channel-listp channels output-p))
                (equal (cadr (cadr (assoc-equal channel channels))) :byte))
           (unsigned-byte-listp 8 (cddr (assoc-equal channel channels))))
  :hints (("Goal" :in-theory (enable open-channel-listp
                                     open-channel1
                                     unsigned-byte-listp-when-typed-io-listp-of-byte))))

(defthm character-listp-of-cddr-of-assoc-equal-when-open-channel-listp
  (implies (and (and (bind-to-bool output-p)
                     (open-channel-listp channels output-p))
                (equal (cadr (cadr (assoc-equal channel channels))) :character))
           (character-listp (cddr (assoc-equal channel channels))))
  :hints (("Goal" :in-theory (enable open-channel-listp
                                     open-channel1))))

(defthm open-channel-listp-of-cons
  (equal (open-channel-listp (cons ch chs) output-p)
         (and (open-channel1 (cdr ch) output-p)
              (open-channel-listp chs output-p)))
  :hints (("Goal" :in-theory (enable open-channel-listp))))

(defthm ordered-symbol-alistp-of-remove1-assoc-equal
  (implies (ordered-symbol-alistp channels)
           (ordered-symbol-alistp (remove1-assoc-equal channel channels)))
  :hints (("Goal" :in-theory (enable ordered-symbol-alistp))))

;; Avoid name clash with std
(defthm open-channel-listp-of-remove1-assoc-equal-alt
  (implies (open-channel-listp channels output-p)
           (open-channel-listp (remove1-assoc-equal channel channels) output-p))
  :hints (("Goal" :in-theory (enable open-channel-listp))))

(local (in-theory (disable ordered-symbol-alistp)))

;; Avoid name clash with std
(defthm open-channels-p-of-remove1-assoc-equal-alt
  (implies (open-channels-p channels output-p)
           (open-channels-p (remove1-assoc-equal channel channels) output-p))
  :hints (("Goal" :in-theory (enable open-channels-p))))

(defthm open-input-channel-p1-forward-to-assoc-equal
  (implies (open-input-channel-p1 channel typ state)
           (assoc-equal channel (open-input-channels state)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable open-input-channel-p1))))

(defthmd symbolp-when-assoc-equal-and-open-channels-p
  (implies (and (assoc-equal channel channels)
                (bind-to-bool output-p)
                (open-channels-p channels output-p))
           (symbolp channel))
  :hints (("Goal" :in-theory (enable open-channels-p ordered-symbol-alistp))))

(defthmd symbolp-when-assoc-equal-of-open-input-channels-and-state-p1
  (implies (and (assoc-equal channel (open-input-channels state))
                (state-p1 state))
           (symbolp channel))
  :hints (("Goal" :in-theory (e/d (symbolp-when-assoc-equal-and-open-channels-p state-p1)
                                  (open-input-channels
                                   all-boundp ; for speed
                                   )))))

(defthmd symbolp-when-assoc-equal-of-open-input-channels-and-state-p
  (implies (and (assoc-equal channel (open-input-channels state))
                (state-p state))
           (symbolp channel))
  :hints (("Goal" :in-theory (e/d (state-p
                                   symbolp-when-assoc-equal-of-open-input-channels-and-state-p1)
                                  (open-input-channels)))))

;gen? drop?
(defthm assoc-equal-of-open-input-channels-when-open-input-channel-p
  (implies (open-input-channel-p channel :byte state)
           (assoc-equal channel (open-input-channels state)))
  :hints (("Goal" :in-theory (enable open-input-channel-p open-input-channel-p1))))
