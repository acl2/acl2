;; nxtypes.lisp
;;
;; Book defining FTY types and some related constants for the
;; types used in the nxtbl book used to build nxt-tbls and the
;; intermediate forms in the computation of the nxt-tbls.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; BOZOs
;; 1. ???
;;
;; TODOs
;; 1. ??? 
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "std/util/define" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "std/util/defval" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "misc/random" :dir :system)
(include-book "centaur/sv/mods/compile" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "support")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
#|
(set-evisc-tuple (evisc-tuple 10  ; print-level
                              11  ; print-length
                              nil ; alist
                              nil ; hiding-cars
                              )
                 :iprint t
                 :sites :all)
|#

(defconst *prog-tbl-count* 500)

(define var-fix-p (x)
  (or (eq x :reset)
      (eq x :clock)
      (eq x :valid)
      (eq x :out)
      (null x) ;; just self..
      (sv::4vec-p x)))

(define var-fix-fix (x)
  :inline t
  (if (var-fix-p x) x nil))

(defthm var-fix-p-var-fix-fix
  (var-fix-p (var-fix-fix x))
  :hints (("Goal" :in-theory (enable var-fix-p var-fix-fix))))

(defthm var-fix-fix-id
  (equal (var-fix-fix (var-fix-fix x))
         (var-fix-fix x))
  :hints (("Goal" :in-theory (enable var-fix-fix))))

(defthm var-fix-fix-var-fix-p
  (implies (var-fix-p x) (equal (var-fix-fix x) x))
  :hints (("Goal" :in-theory (enable var-fix-p var-fix-fix))))

(fty::deffixtype var-fix
  :pred    var-fix-p
  :fix     var-fix-fix
  :equiv   var-fix-equiv
  :define  t
  :forward t)

(fty::defalist svar-fix-map
               :key-type sv::svar
               :val-type var-fix-p)

(define port-typ-p (x)
  (or (eq x :input)
      (eq x :output)
      (eq x :state)))

(define port-typ-fix (x)
  :inline t
  (if (port-typ-p x) x :state))

(defthm port-typ-p-port-typ-fix
  (port-typ-p (port-typ-fix x))
  :hints (("Goal" :in-theory (enable port-typ-p port-typ-fix))))

(defthm port-typ-fix-id
  (equal (port-typ-fix (port-typ-fix x))
         (port-typ-fix x))
  :hints (("Goal" :in-theory (enable port-typ-fix))))

(defthm port-typ-fix-port-typ-p
  (implies (port-typ-p x) (equal (port-typ-fix x) x))
  :hints (("Goal" :in-theory (enable port-typ-p port-typ-fix))))

(fty::deffixtype port-typ
  :pred    port-typ-p
  :fix     port-typ-fix
  :equiv   port-typ-equiv
  :define  t
  :forward t)

(defthm alistp-alist-fix
  (alistp (alist-fix x))
  :hints (("Goal" :in-theory (enable alistp alist-fix))))

(defthm alist-fix-id
  (equal (alist-fix (alist-fix x))
         (alist-fix x))
  :hints (("Goal" :in-theory (enable alist-fix))))

(defthm alist-fix-alistp
  (implies (alistp x) (equal (alist-fix x) x))
  :hints (("Goal" :in-theory (enable alistp alist-fix))))

(fty::deffixtype alist
   :pred    alistp
   :fix     alist-fix
   :equiv   alist-fix-equiv
   :define  t
   :forward t)

(fty::defprod phase-tbl-elem
              ((wire      sv::wire-p)
               (port      port-typ-p)
               (supp      sv::svarlist-p)
               (neg-step  sv::svex)
               (pos-step  sv::svex)
               (neg-reset sv::svex)
               (pos-reset sv::svex)))

(fty::defalist phase-tbl
               :key-type sv::svar
               :val-type phase-tbl-elem)

(fty::defprod nxt-tbl-elem
              ((step  sv::svex)
               (supp  sv::svarlist-p)
               (wire  sv::wire-p)
               (port  port-typ-p)
               (reset sv::4vec-p)
               (subs  alistp)))

(fty::defalist nxt-tbl
               :key-type sv::svar
               :val-type nxt-tbl-elem)
