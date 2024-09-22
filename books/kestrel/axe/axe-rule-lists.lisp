; Utilities dealing with lists of axe-rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "axe-rules")

;; Recognizes a true-list of axe-rules.
(defund axe-rule-listp (rules)
  (declare (xargs :guard t))
  (if (not (consp rules))
      (null rules)
    (and (axe-rulep (first rules))
         (axe-rule-listp (rest rules)))))

(defthm axe-rule-listp-forward-to-true-listp
  (implies (axe-rule-listp rules)
           (true-listp rules))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable axe-rule-listp))))

(defthm axe-rule-listp-of-reverse-list
  (implies (axe-rule-listp rules)
           (axe-rule-listp (reverse-list rules)))
  :hints (("Goal" :in-theory (enable axe-rule-listp))))

(defthm axe-rule-listp-of-cons
  (equal (axe-rule-listp (cons rule rules))
         (and (axe-rulep rule)
              (axe-rule-listp rules)))
  :hints (("Goal" :in-theory (enable axe-rule-listp))))

(defthm axe-rule-listp-of-append
  (equal (axe-rule-listp (append x y))
         (and (axe-rule-listp (true-list-fix x))
              (axe-rule-listp y)))
  :hints (("Goal" :in-theory (enable axe-rule-listp))))

(defthm axe-rulep-of-car-when-axe-rule-listp
  (implies (and (axe-rule-listp rules)
                (consp rules))
           (axe-rulep (car rules)))
  :hints (("Goal" :in-theory (enable axe-rule-listp))))

;; Extract the rule-symbols from the RULES.
(defund map-rule-symbol (rules)
  (declare (xargs :guard (axe-rule-listp rules)
                  :guard-hints (("Goal" :expand ((axe-rulep (car rules))) ;this is because rule-symbol is a macro?
                                 :in-theory (enable axe-rule-listp)))))
  (if (endp rules)
      nil
    (cons (rule-symbol (first rules))
          (map-rule-symbol (rest rules)))))
