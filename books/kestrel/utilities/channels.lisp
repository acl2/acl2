; A lightweight book about i/o channels
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; So the rules in this book fire
(in-theory (disable open-channels-p
                    add-pair
                    open-channel-listp
                    open-channel1))

;; We give this notion a name that we can keep disabled, since it is an unwieldy conjunction.
(defund channel-headerp (header)
  (declare (xargs :guard t))
  (and (true-listp header)
       (equal (length header) 4)
       (eq (car header) :header)
       (member-eq (cadr header) *file-types*)
       (stringp (caddr header))
       (integerp (cadddr header))))

(defthm open-channel-listp-of-add-pair
  (implies (open-channel-listp l)
           (equal (open-channel-listp (add-pair key value l))
                  (open-channel1 value)))
  :hints (("Goal" :in-theory (enable open-channel-listp add-pair))))

(defthm ordered-symbol-alistp-of-add-pair
  (implies (ordered-symbol-alistp x)
           (equal (ordered-symbol-alistp (add-pair key val x))
                  (symbolp key)))
  :hints (("Goal" :in-theory (enable add-pair ordered-symbol-alistp))))

(defthm open-channels-p-of-add-pair
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
                (open-channel-listp channels)
                (cddr (assoc-equal channel channels)))
           (typed-io-listp (cdddr (assoc-equal channel channels))
                           (cadr (cadr (assoc-equal channel channels)))))
  :hints (("Goal" :in-theory (enable open-channel-listp channel-headerp))))

;; different hyp
(defthm typed-io-listp-of-cdddr-of-assoc-equal-and-cadr-of-cadr-of-assoc-equal-2
  (implies (and (symbolp channel)
                (open-channels-p channels)
                (cddr (assoc-equal channel channels)))
           (typed-io-listp (cdddr (assoc-equal channel channels))
                           (cadr (cadr (assoc-equal channel channels)))))
  :hints (("Goal" :in-theory (enable open-channels-p))))
