; Matt Kaufmann and Rob Sumners

(in-package "ACL2")

#|

We define properties of a generic record accessor function and updater
function.  The basic functions are (g a r) and (s a v r) where a is an
address/key, v is a value, r is a record, and (g a r) returns the value set to
address a in record r, and (s a v r) returns a new record with address a set to
value v in record r.

The following main lemma are "exported" about record (g)et and (s)et:

(defthm g-same-s
  (equal (g a (s a v r))
	 v))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

(defthm s-same-g
  (equal (s a (g a r) r)
	 r))

(defthm s-same-s
  (equal (s a y (s a x r))
	 (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))


we also include some auxiliary lemmas which have proven useful,

(defthm access-of-nil-is-nil
  (not (g a nil)))

(defthm record-set-cannot-be-nil
  (implies v (s a v r)))

(defthm record-get-non-nil-cannot-be-nil
  (implies (g a r) r))

(defthm s-preserves-recordp
  (implies (rcdp r)
           (rcdp (s a v r))))


and we include a theorem formerly from record-equality.lisp

(defthm rcdp-equality-sufficiency
  (implies (and (rcdp r1) (rcdp r2))
           (equal (equal r1 r2)
                  (let ((field (bad-field r1 r2)))
                    (implies (symbolp field)
                             (equal (g field r1)
                                    (g field r2)))))))

Main idea of how this all works:

A lookup structure is the cons of any object onto a non-empty
ordered alist that has only non-nil values, where the cdr is not such a
structure.

Intuitively, the cdr of a lookup structure is the "junk", while the car is the
alist that holds the values.  However, if we have other than a lookup structure
then we view its entirety as "junk."

G returns nil on a non-lookup structure, else looks up in the ordered symbol
alist part.

S would "like" simply to set the value in the ordered symbol alist part.
However, it respects the form of the lookup structure, so for example it has to
delete an existing key if it wants to set a key's value to nil.


|#

(include-book "total-order")

; Ordered alist with no nil cdrs:
(defun rcdp (x)
  (declare (xargs :guard t))
  (if (atom x) (null x)
    (and (consp (car x))
         (cdar x)
         (if (atom (cdr x))
             (null (cdr x))
           (and (rcdp (cdr x))
                (<< (caar x) (caadr x)))))))

; Lookup structure:
(defun lsp (x)
  (declare (xargs :guard t))
  (or (rcdp x)
      (and (consp x)
           (not (lsp (cdr x)))
           (rcdp (car x))
           (car x))))

(defun g (a x)
  (declare (xargs :guard t))
  (cond ((rcdp x)
         (cdr (assoc-equal a x)))
        ((lsp x)
         (cdr (assoc-equal a (car x))))
        (t nil)))

; Ordinary setting, used for non-nil values:
(defun s-aux (a v r)
  (declare (xargs :guard (rcdp r)))
  (cond ((endp r)
         (cons (cons a v) nil))
        ((equal a (caar r))
         (cons (cons a v) (cdr r)))
        ((<< a (caar r))
         (cons (cons a v) r))
        (t (cons (car r) (s-aux a v (cdr r))))))

(defun delete-key (key alist)
  (declare (xargs :guard (rcdp alist)))
  (cond ((endp alist) alist)
        ((equal key (caar alist))
         (cdr alist))
        (t (cons (car alist)
                 (delete-key key (cdr alist))))))

(defun s (a v x)
  (declare (xargs :guard t))
  (cond ((rcdp x)
         (if (null v)
             (delete-key a x)
           (s-aux a v x)))
        ((not (lsp x))
         (if v
             ;; then make x into the cdr of the returned lookup structure
             (cons (list (cons a v)) x)
           ;; else x already is an appropriate result
           x))
        ((null v)
         (if (and (null (cdr (car x)))
                  (equal (caar (car x)) a))
             (cdr x)
           (cons (delete-key a (car x))
                 (cdr x))))
        (t (cons (s-aux a v (car x))
                 (cdr x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interaction properties for s and g;
;;; search for $$$ for main theorems.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
(defthm delete-key-no-op
  (implies (and (rcdp alist)
                (not (assoc-equal key alist)))
           (equal (delete-key key alist) alist))))

(local
(defthm values-not-nil
  (implies (rcdp alist)
           ;; The order below looks dangerous, but apparently the prover's
           ;; heuristics save us.
           (iff (assoc-equal key alist)
                (cdr (assoc-equal key alist))))))

(local
(defthm key-order-lemma
   (implies (and (rcdp alist)
                 (<< a (caar alist)))
            (not (cdr (assoc-equal a alist))))))

(local
(defthm s-aux-to-same
  (implies (and (rcdp alist)
                (cdr (assoc-equal a alist)))
           (equal (s-aux a (cdr (assoc-equal a alist))
                            alist)
                  alist))))

;;;; we can now prove s-same-g
;;;;   (equal (s a (g a r) r)
;;;;          r))

(local
(defthm value-s-aux
  (implies (rcdp alist)
           (equal (cdr (assoc-equal a (s-aux a v alist)))
                  v))))

(local
(defthm s-aux-preserves-rcdp
  (implies (and (rcdp x)
                v)
           (rcdp (s-aux a v x)))))

(local
(defthm cdr-assoc-equal-delete-key
  (implies (rcdp x)
           (not (cdr (assoc-equal a (delete-key a x)))))))

; G-diff-s should go here, but I forgot it on the first pass, so I'll put
; it at the end where more lemmas are available.

(local
(defthm rcdp-delete-key
  (implies (rcdp alist)
           (rcdp (delete-key a alist)))))

;;;; we can now prove g-same-s
;;;;   (equal (g a (s a v r))
;;;;           v))

(local
(defthm s-aux-s-aux-same
  (implies (rcdp alist)
           (equal (s-aux a v (s-aux a w alist))
                  (s-aux a v alist)))))

(local
(defthm delete-key-s-aux-same
  (implies (rcdp alist)
           (equal (delete-key a (s-aux a v alist))
                  (delete-key a alist)))))

(local
(defthm <<-s-aux
  (implies (and (rcdp alist)
                (<< b (caar alist))
                (not (<< a b))
                (not (equal a b)))
           (<< b (caar (s-aux a v alist))))))

(local
(defthm value-nil-sufficiency
  (implies (and (rcdp alist)
                (<< a (caar alist)))
           (equal (cdr (assoc-equal a alist))
                  nil))))

(local
(defthm caar-delete-key
  (implies (rcdp alist)
           (equal (caar (delete-key a alist))
                  (if (eq a (caar alist))
                      (caadr alist)
                    (caar alist))))))

(local
(defthm s-aux-delete-key
  (implies (rcdp alist)
           (equal (s-aux a x (delete-key a alist))
                  (s-aux a x alist)))))

(local
(defthm <<-hack
  (implies (and (<< r6 r9)
                (not (<< r4 r9))
                (not (equal r6 r4)))
           (<< r6 r4))
  :hints (("Goal" :in-theory (disable <<-trichotomy)
           :use ((:instance <<-trichotomy
                            (x r6) (y r4)))))))

;;;; we can now prove s-same-s
;;;;  (equal (s a y (s a x r))
;;;;         (s a y r)))

(local
(defthm s-aux-diff-s-aux
  (implies (and (not (equal a b))
                (rcdp r)
                x
                y)
           (equal (s-aux b y (s-aux a x r))
                  (s-aux a x (s-aux b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s-aux))))))

(local
(defthm rcdp-s-aux
  (implies (and (rcdp x)
                v)
           (rcdp (s-aux a v x)))))

(local
(defthm consp-delete-key
  (implies (rcdp alist)
           (equal (consp (delete-key a alist))
                  (or (consp (cdr alist))
                      (and (consp alist)
                           (not (equal a (caar alist)))))))))

(local
(defthm delete-key-delete-key
  (implies (rcdp r)
           (equal (delete-key b (delete-key a r))
                  (delete-key a (delete-key b r))))
  :rule-classes ((:rewrite :loop-stopper ((b a delete-key))))))

(local
(defthm delete-key-s-aux
  (implies (and (not (equal a b))
                (rcdp r)
                x)
           (equal (delete-key b (s-aux a x r))
                  (s-aux a x (delete-key b r))))))

(local
(defthm delete-key-nil
  (implies (not (delete-key a x))
           (not (delete-key a (delete-key b x))))))

;;;; we can now prove s-diff-s
;;;;  (implies (not (equal a b))
;;;;           (equal (s b y (s a x r))
;;;;                  (s a x (s b y r))))

(local
(defthm assoc-equal-s-aux-different
  (implies (not (equal a b))
           (equal (assoc-equal a (s-aux b v alist))
                  (assoc-equal a alist)))))

(local
(defthm assoc-equal-delete-key-different
  (implies (not (equal a b))
           (equal (assoc-equal a (delete-key b alist))
                  (assoc-equal a alist)))))

(defun bad-field (r1 r2)
  (declare (xargs :guard (and (rcdp r1) (rcdp r2))))
  (cond ((endp r1) (caar r2))
        ((endp r2) (caar r1))
        ((equal (car r1) (car r2))
         (bad-field (cdr r1) (cdr r2)))
        ((<< (caar r1) (caar r2))
         (caar r1))
        (t (caar r2))))

(local
(defthm assoc-eq-symbol<
  (implies (and (rcdp s)
                (<< field (caar s)))
           (equal (assoc-equal field s) nil))))

;;;; we can now prove g-diff-s
;;;;  (implies (not (equal a b))
;;;;           (equal (g a (s b v r))
;;;;                  (g a r))))

;;;;;;;;;;; THE MAIN (exported) THEOREMS ;;;;;;;;;;;;

(defthm access-of-nil-is-nil
  (not (g a nil)))

(defthm record-set-cannot-be-nil
  (implies v (s a v r)))

(defthm record-get-non-nil-cannot-be-nil
  (implies (g a r) r)
  :rule-classes :forward-chaining)

(defthm s-same-g
  (equal (s a (g a r) r)
	 r))

(defthm g-same-s
  (equal (g a (s a v r))
	 v))

(defthm s-same-s
  (equal (s a y (s a x r))
	 (s a y r)))

(defthm s-diff-s
  (implies (not (equal a b))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

(defthm g-diff-s
  (implies (not (equal a b))
           (equal (g a (s b v r))
                  (g a r))))

(defthm s-preserves-recordp
  (implies (rcdp r)
           (rcdp (s a v r)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((s a v r)))
                 :rewrite))

(defthm rcdp-equality-sufficiency
  (implies (and (rcdp r1) (rcdp r2))
           (equal (equal r1 r2)
                  (let ((field (bad-field r1 r2)))
                    (equal (g field r1)
                           (g field r2)))))
  :hints (("Goal" :induct (bad-field r1 r2))))

; We will almost surely never care about the definition of bad-field, other
; than the rule above. We also disable s and g, assuming the rules proven in
; this book are sufficient to manipulate record terms which are encountered.
; Finally, we disable rcdp-equality-sufficiency, since it can be an expensive
; rewrite rule (because it is hung on equal).

(in-theory (disable s g bad-field rcdp-equality-sufficiency))
