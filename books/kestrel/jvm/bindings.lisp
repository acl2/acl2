; Bindings
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "portcullis")

;fixme used typed alists for this?
;; Used in the thread-table
;acons might be sufficient if duplicates are okay, but maybe we do want to get rid of old bindings for a thread, to keep the values from getting huge (but will the binds just stack up when we have symbolic terms)?
(defun bind (x y alist)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) (list (cons x y)))
        ((equal x (car (car alist)))
         (cons (cons x y) (cdr alist)))
        (t (cons (car alist) (bind x y (cdr alist))))))

;ffixme this is just lookup-equal
(defund binding (x alist)
  (declare (xargs :guard (alistp alist)))
  (cdr (assoc-equal x alist)))

(defthm binding-bind
  (equal (binding x (bind x val alist))
         val)
  :hints (("goal" :in-theory (enable bind binding))))

(defund bound-in-alistp (x alist)
  (declare (xargs :guard (alistp alist)))
  (consp (assoc-equal x alist)))

(defthm bound-in-alistp-of-bind
  (bound-in-alistp key (bind key val alist))
  :hints (("Goal" :in-theory (enable bound-in-alistp bind))))

(defthm assoc-equal-bind
  (equal (assoc-equal key1 (bind key2 val alist))
         (if (equal key1 key2)
             (cons key1 val)
           (assoc-equal key1 alist)))
  :hints (("Goal" :in-theory (enable assoc-equal))))

(defthm bind-bind
  (equal (bind x v (bind x w a))
         (bind x v a)))

(defthm move-binding-inside-bind
  (implies (not (equal x y))
           (equal (binding x (bind y val alist))
                  (binding x alist)))
  :hints (("Goal" :in-theory (enable bind binding))))

(defthm bind-bind-diff
  (implies (and (assoc-equal y alist) ;case-split?
                (case-split (not (equal x y)))
                )
           (equal (bind x xval (bind y yval alist))
                  (bind y yval (bind x xval alist))))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :in-theory (enable bind ;bound?
                                     assoc-equal))))

(defthm bind-bind-diff-2
  (implies (and (assoc-equal x alist) ;case-split?
                (case-split (not (equal x y)))
                )
           (equal (bind x xval (bind y yval alist))
                  (bind y yval (bind x xval alist))))
  :rule-classes ((:rewrite :loop-stopper ((x y))))
  :hints (("Goal" :in-theory (enable bind assoc-equal))))

(defthm bind-with-constant-key-move-past-first-binding-with-diff-constant-key
  (implies (and (stringp (caar alist)) ;generalize this but still restrict to constants
                (stringp key1) ;generalize this but still restrict to constants
                (not (equal key1 (caar alist)))
                (case-split (consp alist))
                )
           (equal (bind key1 val1 alist)
                  (cons (car alist) (bind key1 val1 (cdr alist)))))
  :hints (("Goal" :in-theory (enable bind))))

(defthm bind-with-constant-key-move-past-first-binding-with-same-constant-key
  (implies (and (stringp (caar alist)) ;generalize this but still restrict to constants
                (stringp key1) ;generalize this but still restrict to constants
                (equal key1 (caar alist))
                (case-split (consp alist))
                )
           (equal (bind key1 val1 alist)
                  (cons (cons key1 val1) (cdr alist))))
  :hints (("Goal" :in-theory (enable bind))))

; test for the rules above
;; (thm (equal zz (BIND "previous" (LIST 'REF (LEN (HEAP S)))
;;                      '(("element" REF -1)
;;                        ("next" REF -1)
;;                        ("previous" REF -1)))))

(defthm alistp-bind
  (implies (case-split (alistp alist))
           (alistp (bind key val alist)))
  :hints (("Goal" :in-theory (enable alistp bind))))

(defthm alistp-bind-force
  (implies (force (alistp alist))
           (alistp (bind key val alist)))
  :hints (("Goal" :in-theory (enable alistp bind))))

;; (defthm move-bound?-inside-bind
;;   (implies (not (equal x y))
;;         (equal (BOUND?
;;                 x
;;                 (BIND
;;                  y
;;                  val
;;                  alist))
;;                (bound? x alist)))
;;   :hints (("Goal" :in-theory (enable bound?))))

;; (defthm bound?-bind
;;   (BOUND? x (BIND x val alist))
;;    :hints (("Goal" :in-theory (enable bound?))))

;rename
(defthm binding-with-const-1
  (implies (not (equal key1 key2))
           (equal (BINDING
                   key1
                   (cons
                    (CONS key2
                          val)
                    rest))
                  (binding key1 rest)))
  :hints (("Goal" :in-theory (enable binding))))

(defthm binding-with-const-2
  (equal (BINDING
          key1
          (cons
           (CONS key1
                 val)
           rest))
         val)
  :hints (("Goal" :in-theory (enable binding))))

(defthm binding-with-const-both
  (equal (binding key1 (cons (cons key2 val) rest))
         (if (equal key1 key2)
             val
           (binding key1 rest)))
  :hints (("goal" :in-theory (enable binding))))

(defthm binding-bind
  (equal (binding x (bind x val alist))
   val)
  :hints (("goal" :in-theory (enable bind binding))))

;causes a case-split but I think we usually want this rule
(defthm move-binding-inside-bind-both
  (equal (binding x (bind y val alist))
         (if (equal x y)
             val
           (binding x alist)))
  :hints (("goal" :in-theory (enable bind binding))))

;; todo: change packages of these:

;allow alists to differ?
(defthm acl2::bind-equal-bind-reduce
  (equal (equal (jvm::bind x y alist) (jvm::bind x y2 alist))
         (equal y y2))
  :hints (("Goal" :in-theory (enable jvm::bind))))

;move
;newly disabled
(defthmd acl2::bind-what-was-already-there
  (implies (and (assoc-equal key alist)
                (alistp alist)
                (equal v (cdr (assoc-equal key alist))))
           (equal (jvm::bind key v alist)
                  alist))
  :hints (("Goal" :in-theory (enable jvm::bind assoc-equal))))

;move
(defthm acl2::alistp-of-bind
  (implies (alistp alist)
           (equal (alistp (JVM::BIND x y alist))
                  t))
  :hints (("Goal" :in-theory (enable JVM::BIND alistp))))
