; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The value of (hol-pprint x) is a human-readable version of x, with types
; omitted.  It is not intended to be fully reliable, but it can be helpful for
; reading large terms.

(in-package "ZF")

(include-book "projects/hol-in-acl2/acl2/portcullis" :dir :system)

(defconst *hol-name-mapping*

; Warning: Keep this in sync with *hol-symbols* in package.lsp and
; *hol-arities* in terms.lisp.  !! And update their warnings.

  '((equal . equal)
    (hp-comma . hol::comma)
    ;; (hp-none . 1)
    (hp-some . hol::some)
    ;; (hp-nil . 1)
    (hp-cons . hol::cons)
    (hp+ . hol::+)
    (hp* . hol::*)
    (hp-implies . hol::implies)
    (hp-and . and)
    (hp-or . or)
    (hp= . hol::=)
    (hp< . hol::<)
    (hp-not . not)
    (hp-forall . hol::forall)
    (hp-exists . hol::exists)
    ;; (hp-true . true)
    ;; (hp-false . false)
    ))

(mutual-recursion

(defun hol-pprint (x)
  (declare (xargs :guard t
                  :measure (1+ (* 2 (acl2-count x)))))
  (cond ((atom x) x)
        ((not (true-listp x))
         (er acl2::hard? 'hol-pprint
             "Not a true list: ~x0"
             x))
        ((eq (car x) 'hap*)
         (hol-pprint-lst (cdr x)))
        ((eq (car x) 'hp-none)
         'hol::none)
        ((eq (car x) 'hp-none)
         'hol::nil)
        ((member-equal x '((hp-true)
                           (hp-false)))
         (car x))
        ((eq (car x) 'hp-num)
         (cadr x))
        (t
         (let ((pair (assoc-eq (car x) *hol-name-mapping*)))
           (cond (pair (cons (cdr pair)
                             (hol-pprint-lst (cdr x))))
                 (t (case-match x
                      ((fn ('typ &))
                       fn)
                      (& (list* :unhandled
                                (hol-pprint-lst x))))))))))

(defun hol-pprint-lst (x)
  (declare (xargs :guard (true-listp x)
                  :measure (* 2 (acl2-count x))))
  (cond ((endp x) nil)
        (t (cons (hol-pprint (car x))
                 (hol-pprint-lst (cdr x))))))
)

(defmacro hol::hol-pprint (x)
  `(hol-pprint ,x))
