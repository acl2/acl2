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

(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "axe-rules")

;; Recognizes a true-list of axe-rules.
;; todo: avoid using defforall
(defforall axe-rule-listp (rules) (axe-rulep rules) :true-listp t)
(verify-guards axe-rule-listp)

(defthm axe-rule-listp-of-reverse-list
  (implies (axe-rule-listp rules)
           (axe-rule-listp (reverse-list rules)))
  :hints (("Goal" :in-theory (enable axe-rule-listp))))

;todo: defforall should do this (but maybe disable it?)
(defthm axe-rulep-of-car-when-axe-rule-listp
  (implies (and (axe-rule-listp rules)
                (consp rules))
           (axe-rulep (car rules))))

;; Extract the rule-symbols from the RULES.
(defund map-rule-symbol (rules)
  (declare (xargs :guard (axe-rule-listp rules)
                  :guard-hints (("Goal" :expand ((axe-rulep (car rules))) ;this is because rule-symbol is a macro?
                                 :in-theory (enable axe-rule-listp)))))
  (if (endp rules)
      nil
    (cons (rule-symbol (first rules))
          (map-rule-symbol (rest rules)))))
