
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; misc.lisp
;;;
;;; A collection of things that don't easily fit elsewhere.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bytes-and-words")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm eqlable-alistp-alistp
  (implies (eqlable-alistp l)
	   (alistp l)))

(defund nat-to-boolean (x)
  (not (= x 0)))


; Lists and Association Lists of Natural Numbers

(defund n08p-listp (xlst)
  (if (atom xlst)
      (null xlst)
    (and (n08p (car xlst))
         (n08p-listp (cdr xlst)))))

(defund n16p-listp (xlst)
  (if (atom xlst)
      (null xlst)
    (and (n16p (car xlst))
         (n16p-listp (cdr xlst)))))

(defund n32p-listp (xlst)
  (if (atom xlst)
      (null xlst)
    (and (n32p (car xlst))
         (n32p-listp (cdr xlst)))))


(defund n01p-alistp (alst)
  (if (atom alst)
      (symbolp alst)
    (and (consp (car alst))
         (n01p (cdar alst))
         (n01p-alistp (cdr alst)))))

(defund n08p-alistp (alst)
  (if (atom alst)
      (symbolp alst)
    (and (consp (car alst))
         (n08p (cdar alst))
         (n08p-alistp (cdr alst)))))

(defund n16p-alistp (alst)
  (if (atom alst)
      (symbolp alst)
    (and (consp (car alst))
         (n16p (cdar alst))
         (n16p-alistp (cdr alst)))))

(defund n32p-alistp (alst)
  (if (atom alst)
      (symbolp alst)
    (and (consp (car alst))
         (n32p (cdar alst))
         (n32p-alistp (cdr alst)))))

(defund symbolp-n32-alistp (alst)
  (if (atom alst)
      (symbolp alst)
    (and (consp (car alst))
         (symbolp (caar alst))
         (n32p (cdar alst))
         (n32p-alistp (cdr alst)))))

(defthmd natp-+
  (implies (and (natp a)
		(natp b))
	   (natp (+ a b))))

;;; from alist-thms:

(defthm n08p-alistp-put-assoc-equal
  (implies (and (n08p-alistp al)
		(n08p val))
	   (n08p-alistp (put-assoc-equal tag val al)))
  :hints (("Goal" :in-theory (enable n08p-alistp))))

(defthm n32p-alistp-put-assoc-equal
  (implies (and (n32p-alistp al)
		(n32p val))
	   (n32p-alistp (put-assoc-equal tag val al)))
  :hints (("Goal" :in-theory (enable n32p-alistp))))

;; May not be necessary
(defthm assoc-put-assoc-equal
  (implies (alistp al)
	   (equal (assoc tag (put-assoc-equal tag val al))
		  (cons tag val))))
