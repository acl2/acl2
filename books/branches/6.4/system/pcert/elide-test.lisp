(in-package "ACL2")

; The following gets an entry in the :EXPANSION-ALIST-NONLOCAL of the .pcert0
; file.
(make-event
 '(local (defthm test-1
           (equal x x)
           :rule-classes nil)))

; The following gets an :EXPANSION-ALIST-NONLOCAL entry.
(local
 (make-event
  '(defthm test-2
     (equal x x)
     :rule-classes nil)))

; The following gets no :EXPANSION-ALIST-NONLOCAL entry.
(make-event
 '(defthm test-3
    (equal x x)
    :rule-classes nil))

; The following gets an :EXPANSION-ALIST-NONLOCAL entry.
(encapsulate
 ()
 (encapsulate
  ()
  (make-event
   '(local (defthm revappend-revappend
             (equal (revappend (revappend x y) z)
                    (revappend y (append x z))))))
  (defthm reverse-reverse
    (implies (true-listp x)
             (equal (reverse (reverse x)) x)))))
