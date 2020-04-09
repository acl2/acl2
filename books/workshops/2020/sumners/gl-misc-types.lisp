; Copyright (C) 2020, Rob Sumners
; Written by Rob Sumners
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "GL")

(include-book "std/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "misc/random" :dir :system)
;; BOZO -- consider faster alternative in "defexec/other-apps/records/records"?
(include-book "misc/records" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)

(defmacro defprod    (&rest x) `(fty::defprod    ,@x))
(defmacro deflist    (&rest x) `(fty::deflist    ,@x))
(defmacro defalist   (&rest x) `(fty::defalist   ,@x))
(defmacro deffixtype (&rest x) `(fty::deffixtype ,@x))

(define zip! ((x true-listp) (y true-listp))
  :returns (r alistp)
  (cond ((and (endp x) (endp y)) ())
        ((or (endp x) (endp y)) 
         (er hard? 'zip! "should be equal lists:~x0" (list x y)))
        (t (cons (cons (first x) (first y))
                 (zip! (rest x) (rest y))))))

(defabbrev hons= (x y) (hons-equal x y))

(defabbrev lambdap!   (x) (consp x))
(defabbrev quotep!    (x) (and (consp x) (eq (first x) 'quote)))
(defabbrev quote-val! (x) (and (consp x) (consp (cdr x)) (second x)))

(defabbrev ftbl-lkup-fn (op ftbl) (hons-get op ftbl))

(define alist-fix! ((x alistp))
  :returns (r alistp)
  :enabled t
  :inline t
  (mbe :logic (if (alistp x) x nil) :exec x))

(define symbol-list-fix! ((x symbol-listp))
  :returns (r symbol-listp)
  :enabled t
  :inline t
  (mbe :logic (if (symbol-listp x) x nil) :exec x))

(define symbol-alist-fix! ((x symbol-alistp))
  :returns (r symbol-alistp)
  :enabled t
  :inline t
  (mbe :logic (if (symbol-alistp x) x nil) :exec x))

(define pseudo-term-fix ((x pseudo-termp))
  :returns (r pseudo-termp)
  :enabled t
  :inline t
  (mbe :logic (if (pseudo-termp x) x 'x) :exec x))

(deffixtype alist
  :pred alistp
  :fix alist-fix!
  :equiv alist-equiv!
  :define t)

(deffixtype symbol-list
  :pred symbol-listp
  :fix symbol-list-fix!
  :equiv symbol-list-equiv!
  :define t)

(deffixtype symbol-alist
  :pred symbol-alistp
  :fix symbol-alist-fix!
  :equiv symbol-alist-equiv!
  :define t)

(deffixtype pseudo-term
  :pred pseudo-termp
  :fix pseudo-term-fix
  :equiv pseudo-term-equiv
  :define t)

(defalist memo-supp-al
  :key-type alistp
  :val-type true-listp
  :true-listp t)

(defalist memo-supp
  :key-type true-listp
  :val-type memo-supp-al
  :true-listp t)

(defprod ftbl-elem
  ((formals symbol-listp)
   (body pseudo-termp)))

(defalist supp-ftbl
  :key-type symbolp
  :val-type ftbl-elem
  :true-listp t)

(defalist bind-alst
  :key-type symbolp
  :val-type true-listp
  :true-listp t)

(define tlist-fix ((x true-listp))
  :returns (r true-listp)
  :inline t
  (mbe :logic (if (true-listp x) x nil) :exec x))

(defthm memo-supp-al-cdr-assoc-equal
  (implies (memo-supp-al-p al)
           (true-listp (cdr (assoc-equal e al))))
  :hints (("Goal" :in-theory (enable memo-supp-al-p))))

(defthm memo-supp-al-alistp
  (implies (memo-supp-al-p al) (alistp al))
  :hints (("Goal" :in-theory (enable memo-supp-al-p))))

(defthm assoc-equal-consp-nil
  (implies (and (alistp al) (assoc-equal e al))
           (consp (assoc-equal e al))))

(defprod comp-rslt-elem
  ((rslt  acl2::any-p)
   (deps  alistp)
   (time  rationalp)
   (mem   natp)))

(defalist comp-rslt-tbl
  :key-type acl2::any-p
  :val-type comp-rslt-elem-p
  :true-listp t)

(defprod comp-rsrc-descr
  ((timelimit     rationalp :default 3600) ;; default to 1 hour
   (maxmem        natp      :default 20000000000) ;; default to ~20 GB
   (suppress      booleanp  :default nil) ;; do not suppress lisp errors
   (max-time-incr rationalp :default 1/5) ;; default 20% increase..
   (max-mem-incr  rationalp :default 1/5) ;; default 20% increase..
   ))
