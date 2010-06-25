; gentle.lisp                                 Boyer & Hunt

; Jared took these functions out of hons-help.lisp since they (generally) don't
; have anything to do with hons.


(in-package "ACL2")

(defabbrev gentle-car    (x) (if (consp x) (car x) nil))
(defabbrev gentle-cdr    (x) (if (consp x) (cdr x) nil))
(defabbrev gentle-caar   (x) (gentle-car (gentle-car x)))
(defabbrev gentle-cadr   (x) (gentle-car (gentle-cdr x)))
(defabbrev gentle-cdar   (x) (gentle-cdr (gentle-car x)))
(defabbrev gentle-cddr   (x) (gentle-cdr (gentle-cdr x)))
(defabbrev gentle-caaar  (x) (gentle-car (gentle-caar x)))
(defabbrev gentle-cadar  (x) (gentle-car (gentle-cdar x)))
(defabbrev gentle-cdaar  (x) (gentle-cdr (gentle-caar x)))
(defabbrev gentle-cddar  (x) (gentle-cdr (gentle-cdar x)))
(defabbrev gentle-caadr  (x) (gentle-car (gentle-cadr x)))
(defabbrev gentle-caddr  (x) (gentle-car (gentle-cddr x)))
(defabbrev gentle-cdadr  (x) (gentle-cdr (gentle-cadr x)))
(defabbrev gentle-cdddr  (x) (gentle-cdr (gentle-cddr x)))

; [Jared] BOZO I'd kind of prefer not to define any of the following, since at
; four levels of consing you're really getting into unreadable territory.

(defabbrev gentle-caaaar (x) (gentle-car (gentle-caaar x)))
(defabbrev gentle-cadaar (x) (gentle-car (gentle-cdaar x)))
(defabbrev gentle-cdaaar (x) (gentle-cdr (gentle-caaar x)))
(defabbrev gentle-cddaar (x) (gentle-cdr (gentle-cdaar x)))
(defabbrev gentle-caadar (x) (gentle-car (gentle-cadar x)))
(defabbrev gentle-caddar (x) (gentle-car (gentle-cddar x)))
(defabbrev gentle-cdadar (x) (gentle-cdr (gentle-cadar x)))
(defabbrev gentle-cdddar (x) (gentle-cdr (gentle-cddar x)))
(defabbrev gentle-caaadr (x) (gentle-car (gentle-caadr x)))
(defabbrev gentle-cadadr (x) (gentle-car (gentle-cdadr x)))
(defabbrev gentle-cdaadr (x) (gentle-cdr (gentle-caadr x)))
(defabbrev gentle-cddadr (x) (gentle-cdr (gentle-cdadr x)))
(defabbrev gentle-caaddr (x) (gentle-car (gentle-caddr x)))
(defabbrev gentle-cadddr (x) (gentle-car (gentle-cdddr x)))
(defabbrev gentle-cdaddr (x) (gentle-cdr (gentle-caddr x)))
(defabbrev gentle-cddddr (x) (gentle-cdr (gentle-cdddr x)))

(defn gentle-revappend (x y)
  (mbe :logic (revappend x y)
       :exec (if (atom x)
                 y
               (gentle-revappend (cdr x) (cons (car x) y)))))

(defn gentle-reverse (x)
  (mbe :logic (reverse x)
       :exec (if (stringp x)
                 (reverse x)
               (gentle-revappend x nil))))

(defn gentle-strip-cars (l)

; [Jared]: BOZO consider changing this so that it agrees with strip-cars in the
; recursive case.  This would allow us to avoid introducing a new, incompatible
; concept.

  (if (atom l)
      nil
    (cons (if (atom (car l))
              (car l)
            (car (car l)))
          (gentle-strip-cars (cdr l)))))

(defn gentle-strip-cdrs (l)

; [Jared]: BOZO same comment as gentle-strip-cars.

  (if (atom l)
      nil
    (cons (if (atom (car l))
              (car l)
            (cdr (car l)))
          (gentle-strip-cdrs (cdr l)))))


(defn gentle-member-eq (x y)
  (declare (xargs :guard (symbolp x)))
  (mbe :logic (member-equal x y)
       :exec (cond ((atom y) nil)
                   ((eq x (car y)) y)
                   (t (gentle-member-eq x (cdr y))))))

(defn gentle-member-eql (x y)
  (declare (xargs :guard (eqlablep x)))
  (mbe :logic (member-equal x y)
       :exec (cond ((atom y) nil)
                   ((eql x (car y)) y)
                   (t (gentle-member-eql x (cdr y))))))

(defn gentle-member-equal (x y)

; [Jared]: BOZO I find the use of hons-equal kind of odd here.  My objection is
; merely that hons stuff is "spilling over" into these gentle definitions that
; wouldn't appear to have any connection to hons just by their names.

  (mbe :logic (member-equal x y)
       :exec (cond ((atom y) nil)
                   ((hons-equal x (car y)) y)
                   (t (gentle-member-equal x (cdr y))))))

(defn gentle-member (x y)
  (mbe :logic (member-equal x y)
       :exec (cond ((symbolp x) (gentle-member-eq x y))
                   ((or (characterp x) (acl2-numberp x))
                    (gentle-member-eql x y))
                   (t (gentle-member-equal x y)))))

(defn gentle-last (l)
  (mbe :logic (last l)
       :exec (if (or (atom l) (atom (cdr l)))
                 l
               (gentle-last (cdr l)))))



(defn gentle-take (n l)

 "Unlike TAKE, GENTLE-TAKE fills at the end with NILs, if necessary, to
 always return a list n long."

; [Jared]: Note that previously this function had a very strange hons/cons
; behavior; most of the list it created was conses, but if we hit the base
; case, the list of NILs were HONSes because of const-list-acc being used.  I
; changed this to use an ordinary make-list in the base case, so now the list
; it returns is always composed entirely of conses.

 (cond ((not (posp n))
        nil)
       ((atom l)
        (make-list n))
       (t
        (cons (car l)
              (gentle-take (1- n) (cdr l))))))

(defthm true-listp-of-make-list-ac
  (equal (true-listp (make-list-ac n val ac))
         (true-listp ac))
  :rule-classes ((:rewrite)
                 (:type-prescription
                  :corollary
                  (implies (true-listp ac)
                           (true-listp (make-list-ac n val ac))))))

(defthm true-listp-of-gentle-take
  (true-listp (gentle-take n l))
  :rule-classes :type-prescription)



; (mu-defn ...) is like (mutual-recursion ...), but for a list of "defn" rather
; than "defun" calls.

(defn defnp (x)
  (and (consp x)
       (symbolp (car x))
       (eq (car x) 'defn)
       (consp (cdr x))
       (symbolp (cadr x))
       (consp (cddr x))
       (symbol-listp (caddr x))
       (consp (cdddr x))
       (true-listp (cdddr x))))

(defn defn-listp (x)
  (if (atom x)
      (null x)
    (and (defnp (car x))
         (defn-listp (cdr x)))))

(defun mu-defn-fn (l)
  (declare (xargs :guard (defn-listp l)))
  (if (atom l) nil
    (cons `(defun
             ,(cadr (car l))
             ,(caddr (car l))
             (declare (xargs :guard t))
             ,@(cdddr (car l)))
          (mu-defn-fn (cdr l)))))

(defmacro mu-defn (&rest l)
  `(mutual-recursion ,@(mu-defn-fn l)))






; [Jared] Eliminating the following because I think it may be "fluff" we don't
; need.

;; (defn gentle-g (x l)

;; ; [Jared]: BOZO name seems kind of odd -- it's like we're trying to make a
;; ; gentle version of "g" in the records book.  But this definition has nothing
;; ; to do with the records book, so why call it gentle?  I think gentle-cdr-assoc
;; ; might be a better name.

;;   (cdr (gentle-assoc x l)))

;; (defn gentle-s-help (a v l)

;; ; [Jared]: BOZO same naming comment as for gentle-g.

;;   (cond ((atom l)
;;          (cons (cons a v) nil))
;;         ((and (consp (car l))
;;               (equal a (caar l)))
;;          (cons (cons a v) (cdr l)))
;;         (t
;;          (cons (car l)
;;                (gentle-s-help a v (cdr l))))))

;; (defn gentle-s (a v l)

;; ; [Jared]: BOZO same naming comment as for gentle-g.

;;   "The key theorem about GENTLE-S is
;;    (equal (gentle-g a (gentle-s b v l))
;;           (if (equal a b)
;;               v
;;             (gentle-g a l)))."

;;   (let ((pair (gentle-assoc a l)))
;;     (cond ((null pair) (cons (cons a v) l))
;;           ((equal v (cdr pair)) l)
;;           (t (gentle-s-help a v l)))))

;; (defthm hons-assoc-equal-of-gentle-s-help
;;   (equal (hons-assoc-equal a (gentle-s-help b v l))
;;          (if (equal a b)
;;              (cons a v)
;;            (hons-assoc-equal a l))))

;; (defthm gentle-g-of-gentle-s
;;   (equal (gentle-g a (gentle-s b v l))
;;          (if (equal a b)
;;              v
;;            (gentle-g a l))))


;; (defn gentle-binary-+ (x y)
;;   (mbe :logic (+ x y)
;;        :exec (if (acl2-numberp x)
;;                  (if (acl2-numberp y)
;;                      (+ x y)
;;                    x)
;;                (if (acl2-numberp y)
;;                    y
;;                  0))))

;; (defmacro gentle-+ (&rest r)
;;   (cond ((atom r) 0)
;;         ((atom (cdr r)) `(gentle-binary-+ 0 ,(car r)))
;;         ((atom (cddr r)) `(gentle-binary-+ ,(car r) ,(cadr r)))
;;         (t `(gentle-binary-+ ,(car r) (gentle-+ ,@(cdr r))))))



;; (defn gentle-binary-- (x y)

;; ; [Jared]: BOZO consider changing this so that it agrees with the current
;; ; logical definition of minus.  This would allow us to avoid introducing a new,
;; ; incompatible concept.

;;   (if (and (acl2-numberp x)
;;            (acl2-numberp y))
;;       (- x y)
;;     0))

;; (defmacro gentle-- (x &optional y)
;;   (cond ((null y) `(gentle-unary-- ,x))
;;         (t `(gentle-binary-- ,x (gentle-+ ,y)))))


;; (defn gentle-butlast (l n)

;; ; [Jared]: BOZO not equal to butlast, due to the use of gentle-take.  Is there
;; ; a reason to prefer this behavior?  Why not just make a butlast with guard t?

;;   (gentle-take (gentle-- (gentle-length l) n) l))



;; (defn gentle-assoc-eq (x y)

;; ; [Jared]: I don't particularly like using hons-assoc-equal as a normal form,
;; ; but I guess it's fine.

;;   (declare (xargs :guard (symbolp x)))
;;   (mbe :logic
;;        (hons-assoc-equal x y)
;;        :exec
;;        (if (atom y)
;;            nil
;;          (if (and (consp (car y))
;;                   (eq x (caar y)))
;;              (car y)
;;            (gentle-assoc-eq x (cdr y))))))

;; (defn gentle-assoc-eql (x y)
;;   (declare (xargs :guard (eqlablep x)))
;;   (mbe :logic
;;        (hons-assoc-equal x y)
;;        :exec
;;        (if (atom y)
;;            nil
;;          (if (and (consp (car y))
;;                   (eql x (caar y)))
;;              (car y)
;;            (gentle-assoc-eql x (cdr y))))))


;; (defn gentle-assoc-help (x y)

;; ; [Jared]: BOZO as in gentle-member-equal, I find the use of hons-equal kind of
;; ; odd here.  My objection is merely that hons stuff is "spilling over" into
;; ; these gentle definitions that wouldn't appear to have any connection to hons
;; ; just by their names.

;;   (mbe :logic
;;        (hons-assoc-equal x y)
;;        :exec
;;        (if (atom y)
;;            nil
;;          (if (and (consp (car y))
;;                   (hons-equal x (caar y)))
;;              (car y)
;;            (gentle-assoc-help x (cdr y))))))

;; (defn gentle-assoc (x y)
;;   (mbe :logic
;;        (hons-assoc-equal x y)
;;        :exec
;;        (cond ((symbolp x) (gentle-assoc-eq x y))
;;              ((or (acl2-numberp x)
;;                   (characterp x))
;;               (gentle-assoc-eql x y))
;;              (t (gentle-assoc-help x y)))))



;; (defn const-list-acc (n const acc)

;; ; [Jared]: BOZO As above, I find the use of hons kind of odd here.  Why should
;; ; these be honses?  Or why not rename this hons-make-list-acc, etc.

;; redundant with hons-make-list-acc

;; ;; Only used in nil-list and t-list

;;   (mbe :logic (make-list-ac n const acc)
;;        :exec (cond ((not (posp n))
;;                     acc)
;;                    (t
;;                     (const-list-acc (1- n) const (hons const acc))))))


;; (defn gentle-length (l)
;;   (mbe :logic (length l)
;;        :exec (if (stringp l)
;;                  (length l)
;;                (len l))))


;; [Jared]: moved make-same-length to g.lsp (the only place it was used)