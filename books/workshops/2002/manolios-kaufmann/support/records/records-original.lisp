(in-package "ACL2")

(defun fieldp (x)
  (or (symbolp x) (integerp x)))

(defthm fieldp-compound-recognizer
  (iff (fieldp x)
       (or (symbolp x)
           (integerp x)))
  :rule-classes :compound-recognizer)

(defthm integerp-forward-chain-fieldp
  (implies (integerp x) (fieldp x))
  :rule-classes :forward-chaining)

(defthm symbolp-forward-chain-fieldp
  (implies (symbolp x) (fieldp x))
  :rule-classes :forward-chaining)

(in-theory (disable fieldp))

(defun field-< (x y)
  (if (symbolp x)
      (and (symbolp y)
           (symbol< x y))
    (or (symbolp y)
        (< x y))))

(local
(defthm field-<-irreflexive
  (not (field-< x x))))

(local
(defthm field-<-transitive
  (implies (and (field-< x y)
                (field-< y z))
           (field-< x z))))

(local
(defthm field-<-asymmetric
  (implies (field-< x y)
           (not (field-< y x)))))

(local
(defthm field-<-trichotomy
  (implies (and (fieldp x) (fieldp y)
                (not (field-< y x)))
           (iff (field-< x y)
                (not (equal x y))))))

(in-theory (disable field-<))




; Ordered field-alist with no nil cdrs:
(defun sap (x)
  (if (atom x)
      (null x)
    (and (consp (car x))
         (fieldp (caar x))
         (cdar x)
         (if (atom (cdr x))
             (null (cdr x))
           (and (sap (cdr x))
                ;; We unforunately probably ruin tail-recursion here, but at
                ;; least we can verify the guards.
                (field-< (caar x) (caadr x)))))))

; Lookup structure:
(defun lsp (x)
  (or (sap x)
      (and (consp x)
           (not (lsp (cdr x)))
           (sap (car x))
           (car x))))

(defun g (a x)
  (cond
   ((sap x)
    (cdr (assoc-equal a x)))
   ((lsp x)
    (cdr (assoc-equal a (car x))))
   (t
    nil)))

; Ordinary setting, used for non-nil values:
(defun s-aux (a v r)
  (cond ((endp r)
         (cons (cons a v) nil))
        ((equal a (caar r))
         (cons (cons a v) (cdr r)))
        ((field-< a (caar r))
         (cons (cons a v) r))
        (t (cons (car r) (s-aux a v (cdr r))))))

(defun delete-key (key alist)
  (cond
   ((endp alist)
    alist)
   ((equal key (caar alist))
    (cdr alist))
   (t
    (cons (car alist)
          (delete-key key (cdr alist))))))

(defun s (a v x)
  (cond
   ((sap x)
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
   (t
    (cons (s-aux a v (car x))
          (cdr x)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Interaction properties for s and g;
;;; search for $$$ for main theorems.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
(defthm not-field-<-x-x
  (not (field-< x x))
  :hints (("Goal" :in-theory (enable field-<)))))

(local
(defthm delete-key-no-op
  (implies (and (sap alist)
                (not (assoc-equal key alist)))
           (equal (delete-key key alist) alist))))

(local
(defthm values-not-nil
  (implies (sap alist)
           ;; The order below ooks dangerous, but apparently the prover's
           ;; heuristics save us.
           (iff (assoc-equal key alist)
                (cdr (assoc-equal key alist))))))

(local
(defthm key-order-lemma
   (implies (and (fieldp a)
                 (sap alist)
                 (field-< a (caar alist)))
            (not (cdr (assoc-equal a alist))))))

(local
(defthm s-aux-to-same
  (implies (and (fieldp a)
                (sap alist)
                (cdr (assoc-equal a alist)))
           (equal (s-aux a (cdr (assoc-equal a alist))
                            alist)
                  alist))))

; $$$ A main theorem
(defthm s-same-g
  (implies (force (fieldp a))
           (equal (s a (g a r) r)
                  r)))

(local
(defthm value-s-aux
  (implies (and (fieldp a)
                (sap alist))
           (equal (cdr (assoc-equal a (s-aux a v alist)))
                  v))))

(local
(defthm s-aux-preserves-sap
  (implies (and (sap x)
                (fieldp a)
                v)
           (sap (s-aux a v x)))))

(local
(defthm cdr-assoc-equal-delete-key
  (implies (sap x)
           (not (cdr (assoc-equal a (delete-key a x)))))))

; G-diff-s should go here, but I forgot it on the first pass, so I'll put
; it at the end where more lemmas are available.

(local
(defthm sap-delete-key
  (implies (sap alist)
           (sap (delete-key a alist)))))

(local
(defthm sap-forward-to-fieldp-caar
  (implies (sap alist)
           (fieldp (caar alist)))
  :rule-classes :forward-chaining))

; $$$ A main theorem
(defthm g-same-s
  (implies (force (fieldp a))
           (equal (g a (s a v r))
                  v)))

(local
(defthm s-aux-s-aux-same
  (implies (and (fieldp a)
                (sap alist))
           (equal (s-aux a v (s-aux a w alist))
                  (s-aux a v alist)))))

(local
(defthm delete-key-s-aux-same
  (implies (and (fieldp a)
                (sap alist))
           (equal (delete-key a (s-aux a v alist))
                  (delete-key a alist)))))

(local
(defthm field-<-s-aux
  (implies (and (sap alist)
                (fieldp a)
                (fieldp b)
                (field-< b (caar alist))
                (not (field-< a b))
                (not (equal a b)))
           (field-< b (caar (s-aux a v alist))))))

(local
(defthm value-nil-sufficiency
  (implies (and (sap alist)
                (fieldp a)
                (field-< a (caar alist)))
           (equal (cdr (assoc-equal a alist))
                  nil))))

(local
(defthm caar-delete-key
  (implies (sap alist)
           (equal (caar (delete-key a alist))
                  (if (eq a (caar alist))
                      (caadr alist)
                    (caar alist))))))

(local
(defthm s-aux-delete-key
  (implies (sap alist)
           (equal (s-aux a x (delete-key a alist))
                  (s-aux a x alist)))))

(local
(defthm field-<-hack
  (implies (and (field-< r6 r9)
                (not (field-< r4 r9))
                (not (equal r6 r4))
                (fieldp r4)
                (fieldp r6)
                (fieldp r9))
           (field-< r6 r4))
  :hints (("Goal" :in-theory (disable field-<-trichotomy)
           :use ((:instance field-<-trichotomy
                            (x r6) (y r4)))))))

; $$$ A main theorem
(defthm s-same-s
  (implies (force (fieldp a))
           (equal (s a y (s a x r))
                  (s a y r))))

(local
(defthm s-aux-diff-s-aux
  (implies (and (not (equal a b))
                (sap r)
                x
                y
                (fieldp a)
                (fieldp b))
           (equal (s-aux b y (s-aux a x r))
                  (s-aux a x (s-aux b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s-aux))))
  ;; The earlier forward-chaining rule hurts here.
  :hints (("Goal" :in-theory (disable sap-forward-to-fieldp-caar)))))

(local
(defthm sap-s-aux
  (implies (and (sap x)
                (fieldp a)
                v)
           (sap (s-aux a v x)))))

(local
(defthm consp-delete-key
  (implies (sap alist)
           (equal (consp (delete-key a alist))
                  (or (consp (cdr alist))
                      (and (consp alist)
                           (not (equal a (caar alist)))))))))

(local
(defthm delete-key-delete-key
  (implies (sap r)
           (equal (delete-key b (delete-key a r))
                  (delete-key a (delete-key b r))))
  :rule-classes ((:rewrite :loop-stopper ((b a delete-key))))))

(local
(defthm delete-key-s-aux
  (implies (and (not (equal a b))
                (sap r)
                x
                (fieldp a)
                (fieldp b))
           (equal (delete-key b (s-aux a x r))
                  (s-aux a x (delete-key b r))))
  ;; The earlier forward-chaining rule hurts here.
  :hints (("Goal" :in-theory (disable sap-forward-to-fieldp-caar)))))

(local
(defthm delete-key-nil
  (implies (not (delete-key a x))
           (not (delete-key a (delete-key b x))))))

; $$$ A main theorem
(defthm s-diff-s
  (implies (and (force (fieldp a))
                (force (fieldp b))
                (not (equal a b)))
           (equal (s b y (s a x r))
                  (s a x (s b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a s)))))

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

; $$$ A main theorem
(defthm g-diff-s
  (implies (and (force (fieldp a))
                (force (fieldp b))
                (not (equal a b)))
           (equal (g a (s b v r))
                  (g a r))))


;;;; some simple macros for defining sets and gets..

(in-theory (disable s g))

(defmacro <- (x a) `(g ,a ,x))

(defmacro -> (x a v) `(s ,a ,v ,x))

(defun update-macro (upds result)
  (declare (xargs :guard (keyword-value-listp upds)))
  (if (endp upds) result
    (update-macro (cddr upds)
                  (list 's (car upds) (cadr upds) result))))

(defmacro update (old &rest updates)
  (declare (xargs :guard (keyword-value-listp updates)))
  (update-macro updates old))
