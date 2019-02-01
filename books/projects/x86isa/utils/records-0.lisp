; Author:
; Shilpi Goel         <shigoel@cs.utexas.edu>

;; This book is a slightly modified version of the records book by Rob
;; Sumners and Matt Kaufmann (books/misc/records.lisp).

;; Differences between this book and books/misc/records.lisp:
;; - This book uses 0 instead of NIL for absent fields and for the empty record.
;; - This book uses ILL-FORMED-KEY instead of NIL as the "bad key".

(in-package "X86ISA")

(include-book "misc/total-order" :dir :system)

;; ======================================================================

(defun ill-formed-key ()
  (declare (xargs :guard t))
  "unlikely-we-should-ever-encounter-this-particular-string-as-a-key!?!?!?!")

(defun well-formed-alistp-aux (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (not (eql (cdar x) 0))
           (or (atom (cdr x))
               (and (consp (cadr x))
                    (ACL2::<< (caar x) (caadr x))))
           (well-formed-alistp-aux (cdr x)))))

(defun well-formed-alistp (x)
  (declare (xargs :guard t))
  (and (not (equal x nil))
       (or (eql x 0)
           (well-formed-alistp-aux x))))

(defun good-alistp-aux (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (consp (car x))
           (not (equal (caar x) (ill-formed-key)))
           (not (eql (cdar x) 0))
           (or (atom (cdr x))
               (and (consp (cadr x))
                    (ACL2::<< (caar x) (caadr x))))
           (good-alistp-aux (cdr x)))))

(defun good-alistp (x)
  (declare (xargs :guard t))
  (and (not (equal x nil))
       (or (eql x 0)
           (good-alistp-aux x))))

(defthmd good-alistp-aux-implies-well-formed-alistp-aux
  (implies (good-alistp-aux alst)
           (well-formed-alistp-aux alst)))

(defthmd good-alistp-implies-well-formed-alistp
  (implies (good-alistp alst)
           (well-formed-alistp alst)))

(local (in-theory (e/d (good-alistp-aux-implies-well-formed-alistp-aux
                        good-alistp-implies-well-formed-alistp)
                       ())))

(defun ill-formed-alistp (x)
  (declare (xargs :guard t))
  (or (not (well-formed-alistp x))
      (and (consp x)
           (consp (car x))
           (equal (caar x) (ill-formed-key))
           (null (cdr x))
           (ill-formed-alistp (cdar x)))))

(local
 (defthm good-alistp-aux-implies-not-ill-formed-alistp
   (implies (and (good-alistp-aux x)
                 x)
            (not (ill-formed-alistp x)))))

(local
 (defthm good-alistp-implies-not-ill-formed-alistp
   (implies (good-alistp x)
            (not (ill-formed-alistp x)))))

(defun gi (i r)
  (declare (xargs :guard t
                  :measure (acl2-count r)))
  (if (or (eql r 0)
          (atom r)
          (atom (car r)))
      0
    (if (ACL2::<< i (caar r))
        0
      (if (equal (caar r) i)
          (cdar r)
        (if (cdr r)
            (gi i (cdr r))
          0)))))

(defun si-aux (i v r)
  (declare (xargs :guard t))
  (if (or (atom r) (atom (car r)))
      (cons (cons i v) nil)
    (if (equal (caar r) i)
        (cons (cons i v) (cdr r))
      (if (ACL2::<< i (caar r))
          (cons (cons i v) r)
        (cons (car r) (si-aux i v (cdr r)))))))

;; (defthmd len-si-aux-1
;;   (implies (and (well-formed-alistp-aux r)
;;                 (member i (strip-cars r)))
;;            (equal (len (si-aux i v r))
;;                   (len r))))

(defun si-kill (i r)
  (declare (xargs :guard t))
  (if (or (atom r) (atom (car r)))
      nil
    (if (equal (caar r) i)
        (cdr r)
      (cons (car r) (si-kill i (cdr r))))))

(defun si (i v r)
  (declare (xargs :guard t))
  (if (eql r 0)
      (if (eql v 0)
          r
        (cons (cons i v) nil))
    (if (eql v 0)
        (or (si-kill i r) 0)
      (si-aux i v r))))

(local
 (defthm si-kill-preserves-well-formed-alistp-aux
   (implies (well-formed-alistp-aux alst)
            (well-formed-alistp-aux (si-kill i alst)))))

(local
 (defthm si-aux-preserves-well-formed-alistp-aux
   (implies (and (well-formed-alistp-aux alst)
                 (not (equal v 0))
                 (not (equal i (ill-formed-key))))
            (well-formed-alistp-aux (si-aux i v alst)))))

(defthm si-preserves-well-formed-alistp
  (implies (well-formed-alistp alst)
           (well-formed-alistp (si i v alst))))


(local
 (defthm gi-same-si-aux
   (implies (well-formed-alistp-aux alst)
            (equal (gi i (si i v alst))
                   v))))

(local
 (defthm gi-same-si-aux-aux
   (implies (well-formed-alistp-aux alst)
            (equal (gi i (si-aux i v alst))
                   v))))

(defthm gi-same-si
  (implies (well-formed-alistp alst)
           (equal (gi i (si i v alst))
                  v)))

(defthm gi-diff-si
  (implies (and (well-formed-alistp r)
                (not (equal i j)))
           (equal (gi i (si j v r))
                  (gi i r))))

(defthm si-same-gi
  (implies (well-formed-alistp r)
           (equal (si a (gi a r) r)
                  r)))

(local
 (defthm si-aux-same-si-aux
   (implies (and (well-formed-alistp-aux r)
                 (not (equal x 0))
                 (not (equal y 0)))
            (equal (si-aux a y (si-aux a x r))
                   (si-aux a y r)))))

(local
 (defthm si-same-si-helper-1
   (implies (and (well-formed-alistp r)
                 (not (equal r 0)))
            (equal (si-kill a (si-kill a r))
                   (si-kill a r)))))

(local
 (defthm si-same-si-helper-2
   (implies (and (well-formed-alistp r)
                 (not (equal r 0)))
            (equal (si-kill a (si-aux a x r))
                   (si-kill a r)))))

(local
 (defthm si-same-si-helper-3
   (implies (and (well-formed-alistp r)
                 (not (equal r 0)))
            (equal (si-aux a y (si-kill a r))
                   (si-aux a y r)))))

(defthm si-same-si
  (implies (well-formed-alistp r)
           (equal (si a y (si a x r))
                  (si a y r)))
  :otf-flg t)

(defthm si-diff-si
  (implies (and (not (equal i j))
                (well-formed-alistp r))
           (equal (si j y (si i x r))
                  (si i x (si j y r))))
  :rule-classes ((:rewrite :loop-stopper ((j i si))))
  :otf-flg t)

;; ======================================================================

;; Conversion functions:

(defun acl2->map (x) ;; function mapping acl2 objects to well-formed records.
  (declare (xargs :guard t))
  (if (ill-formed-alistp x)
      (list (cons (ill-formed-key) x))
    x))

(defun map->acl2 (x) ;; inverse of acl2->map.
  (declare (xargs :guard t))
  (if (well-formed-alistp x)
      (if (ill-formed-alistp x)
          (cdar x)
        x)
    x))

(local
 (defthm acl2->map-map->acl2-of-well-formed-alistp
   (implies (well-formed-alistp x)
            (equal (acl2->map (map->acl2 x))
                   x))))

(local
 (defthm acl2->map-returns-well-formed-alistp
   (well-formed-alistp (acl2->map x))))

(local
 (defthm acl2->map-preserves-equality
   (iff (equal (acl2->map x) (acl2->map y))
        (equal x y))))

(local
 (defthm map->acl2-acl2->map-inverse
   (equal (map->acl2 (acl2->map x)) x)))

(local
 (defthm map->acl2-of-record-non-zero
   (implies (and (not (equal r 0))
                 (well-formed-alistp r))
            (not (equal (map->acl2 r) 0)))))

;; ======================================================================

;; Definition of gz and sz:

(defun gz (i x) ;; the generic record g(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (gi i (acl2->map x)))

(defun sz (i v x) ;; the generic record s(et) which works on any ACL2 object.
  (declare (xargs :guard t))
  (map->acl2 (si i v (acl2->map x))))

(local
 (defthmd good-alistp-aux-alst-sz-preserves-good-alistp
   (implies (and (good-alistp-aux alst)
                 alst
                 (not (equal i (ill-formed-key))))
            (good-alistp (sz i v alst)))))

(local
 (defthmd sz-preserves-good-alistp-0
   (implies (not (equal i (ill-formed-key)))
            (good-alistp (sz i v 0)))))

(defthm sz-preserves-good-alistp
  (implies (and (good-alistp alst)
                (not (equal i (ill-formed-key))))
           (good-alistp (sz i v alst)))
  :hints (("Goal" :use ((:instance
                         good-alistp-aux-alst-sz-preserves-good-alistp)
                        (:instance
                         sz-preserves-good-alistp-0)))))

(in-theory (disable si gi acl2->map map->acl2))

;; ======================================================================

;; Final exported properties of g and s:

(defthm gz-same-sz
  (equal (gz i (sz i v r)) v))

(defthm gz-diff-sz
  (implies (not (equal a b))
           (equal (gz a (sz b v r))
                  (gz a r))))

;;;; NOTE: The following can be used instead of the above rules to force ACL2
;;;; to do a case-split. We disable this rule by default since it can lead to
;;;; an expensive case explosion, but in many cases, this rule may be more
;;;; effective than two rules above and should be enabled.

(defthm gz-of-sz-redux
  (equal (gz a (sz b v r))
         (if (equal a b)
             v
           (gz a r))))

(in-theory (disable gz-of-sz-redux))

(defthm sz-same-gz
  (equal (sz a (gz a r) r)
         r))

(defthm sz-same-sz
  (equal (sz a y (sz a x r))
         (sz a y r)))

(defthm sz-diff-sz
  (implies (not (equal a b))
           (equal (sz b y (sz a x r))
                  (sz a x (sz b y r))))
  :rule-classes ((:rewrite :loop-stopper ((b a sz)))))

;; The following theorems are less relevant but have been useful in
;; dealing with a default record of 0.

(defthm gz-of-0-is-0
  (equal (gz a 0) 0)
  :hints (("Goal" :in-theory (e/d (gi) ()))))

(defthm non-0-if-gz-non-0
  (implies (not (equal (gz a r) 0)) (not (equal r 0)))
  :hints (("Goal" :in-theory (e/d (gi) ())))
  :rule-classes :forward-chaining)

(defthm sz-non-0-cannot-be-0
  (implies (not (equal v 0))
           (not (equal (sz a v r) 0)))
  :hints (("Goal" :in-theory (e/d (map->acl2 si acl2->map) ()))))

;; Some functions to disable:

(in-theory (disable well-formed-alistp-aux
                    well-formed-alistp
                    good-alistp-aux
                    good-alistp
                    si-aux
                    si-kill))

;; We disable sz and gz, assuming the rules proven in this book are sufficient to
;; manipulate record terms which are encountered.

(in-theory (disable sz gz))

;; ======================================================================
