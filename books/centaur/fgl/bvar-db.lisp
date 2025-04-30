; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")
(include-book "std/basic/arith-equiv-defs" :dir :system)
(include-book "std/stobjs/absstobjs" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "centaur/misc/prev-stobj-binding" :dir :system)
(include-book "fgl-object")
(include-book "std/stobjs/nicestobj" :dir :system)
(include-book "std/lists/index-of" :dir :system)
;; (include-book "std/lists/index-of" :dir :system)
(local (include-book "std/stobjs/clone" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/lists/final-cdr" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

(local (in-theory (enable* acl2::arith-equiv-forwarding)))

(local (in-theory (disable nth update-nth acl2::nth-when-zp)))

(local (std::add-default-post-define-hook :fix))

(fty::defmap term-bvars :key-type fgl-object :val-type natp :true-listp t)
(fty::defmap term-equivs :key-type fgl-object :val-type nat-listp :true-listp t)
(fty::defmap fn-indices :key-type pseudo-fnsym :val-type nat-listp :true-listp t)

;; ----------- Implementation ----------------
;; The "terms" stored in the bvar-db$c are really g-apply/g-var objects
(stobjs::defnicestobj bvar-db$c
  (base :type (integer 0 *) :initially 0 :pred natp :fix nfix :access base-bvar$c :update update-base-bvar$c)
  (next :type (integer 0 *) :initially 0 :pred natp :fix nfix :access next-bvar1$c :update update-next-bvar1$c)
  (bvar-terms :type (array (satisfies fgl-object-p) (0)) :resizable t
                :pred fgl-object-p :fix fgl-object-fix
                :access bvar-terms$ci :update update-bvar-terms$ci
                :length bvar-terms$c-length :resize resize-bvar-terms$c)
  (term-bvars :type (satisfies term-bvars-p) :pred term-bvars-p :fix term-bvars-fix
                :access term-bvars$c :update update-term-bvars$c)
  (term-equivs :type (satisfies term-equivs-p) :pred term-equivs-p :fix term-equivs-fix
               :access term-equivs$c :update update-term-equivs$c)
  (fn-indices :type (satisfies fn-indices-p)
            :pred fn-indices-p :fix fn-indices-fix
            :access bvar-fn-indices$c :update update-bvar-fn-indices$c))



;; (defthm bvar-terms$cp-is-fgl-objectlist-p
;;   (equal (bvar-terms$cp x)
;;          (fgl-objectlist-p x)))

;; (defthm fgl-object-p-nth-of-fgl-objectlist-p
;;   (implies (fgl-objectlist-p x)

;;   :hints(("Goal" :in-theory (enable nth))))

(local (defthm maybe-natp-lookup-in-term-bvars
         (implies (term-bvars-p x)
                  (acl2::maybe-natp (cdr (hons-assoc-equal k x))))))


(defsection bvar-terms-range-equiv
  (defmacro bvar-terms$ci-non-exec (&rest args)
    `(non-exec (bvar-terms$ci . ,args)))
  
  (stobjs::def-range-equiv bvar-terms-range-equiv
    :nth bvar-terms$ci-non-exec :update update-bvar-terms$ci
    :pkg fgl-pkg)

  (defthm bvar-terms-range-equiv-when-bvar-terms-unchanged
    (implies (equal (bvar-db$c-get :bvar-terms new)
                    (bvar-db$c-get :bvar-terms old))
             (bvar-terms-range-equiv start num new old))
    :hints(("Goal" :in-theory (enable bvar-terms-range-equiv)))))

(define bvar-db-term-bvars-ok ((term-bvars term-bvars-p) bvar-db$c)
  :guard (<= (- (next-bvar1$c bvar-db$c)
                (base-bvar$c bvar-db$c))
             (bvar-terms$c-length bvar-db$c))
  (if (atom term-bvars)
      t
    (and (or (not (mbt (and (consp (car term-bvars))
                            (fgl-object-p (caar term-bvars)))))
             (b* ((idx (lnfix (cdar term-bvars))))
               (and (<= (base-bvar$c bvar-db$c) idx)
                    (< idx (next-bvar1$c bvar-db$c))
                    (equal (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c)) idx) bvar-db$c)
                           (caar term-bvars)))))
         (bvar-db-term-bvars-ok (cdr term-bvars) bvar-db$c)))
  ///
  (defthm lookup-in-bounds-when-bvar-db-term-bvars-ok
    (implies (and (bvar-db-term-bvars-ok term-bvars bvar-db$c)
                  (hons-assoc-equal obj term-bvars)
                  (fgl-object-p obj))
             (let ((idx (cdr (hons-assoc-equal obj term-bvars))))
               (and (<= (base-bvar$c bvar-db$c) (nfix idx))
                    (< (nfix idx) (next-bvar1$c bvar-db$c))
                    (and (equal (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c)) (nfix idx))
                                               bvar-db$c) obj)
                         (equal (bvar-terms$ci (+ (nfix idx) (- (base-bvar$c bvar-db$c)))
                                               bvar-db$c) obj))))))

  (def-updater-independence-thm bvar-db-term-bvars-ok-updater-independence
    (implies (and (equal (base-bvar$c new) (base-bvar$c old))
                  (equal (next-bvar1$c new) (next-bvar1$c old))
                  (bvar-terms-range-equiv 0 (- (next-bvar1$c old) (base-bvar$c old)) new old)
                  ;; (equal (bvar-db$c-get :bvar-terms new) (bvar-db$c-get :bvar-terms old))
                  )
             (equal (bvar-db-term-bvars-ok term-bvars new)
                    (bvar-db-term-bvars-ok term-bvars old)))
    :hints(("Goal" :in-theory (enable BVAR-TERMS$CI-NON-EXEC-WHEN-BVAR-TERMS-RANGE-EQUIV))))

  (defthm bvar-db-term-bvars-ok-of-incr-next-bvar
    (implies (and (bvar-db-term-bvars-ok term-bvars bvar-db$c)
                  (<= (next-bvar1$c bvar-db$c) (nfix next)))
             (bvar-db-term-bvars-ok term-bvars (update-next-bvar1$c next bvar-db$c))))

  (defthm bvar-db-term-bvars-ok-of-update-bvar-terms-out-of-bounds
    (implies (and (bvar-db-term-bvars-ok term-bvars bvar-db$c)
                  (<= (- (next-bvar1$c bvar-db$c) (base-bvar$c bvar-db$c)) (nfix idx)))
             (bvar-db-term-bvars-ok term-bvars (update-bvar-terms$ci idx x bvar-db$c))))
             
  (local (in-theory (enable term-bvars-fix))))


(define bvar-db-bvar-terms-ok ((n natp) bvar-db$c)
  :guard (and (<= (base-bvar$c bvar-db$c) n)
              (<= (- n (base-bvar$c bvar-db$c)) (bvar-terms$c-length bvar-db$c)))
  :measure (nfix (- (nfix n) (base-bvar$c bvar-db$c)))
  (if (mbe :logic (zp (- (nfix n) (base-bvar$c bvar-db$c)))
           :exec (eql n (base-bvar$c bvar-db$c)))
      t
    (b* ((n (1- (lnfix n)))
         (idx (- n (base-bvar$c bvar-db$c)))
         (obj (bvar-terms$ci idx bvar-db$c))
         (look (hons-get obj (term-bvars$c bvar-db$c))))
      (and look
           ;; (equal (cdr look) n)
           (bvar-db-bvar-terms-ok n bvar-db$c))))
  ///
  (defthm lookup-exists-when-bvar-db-bvar-terms-ok
    (implies (and (bvar-db-bvar-terms-ok n bvar-db$c)
                  (integerp m)
                  (< m (nfix n))
                  (<= (base-bvar$c bvar-db$c) m))
             (and (hons-assoc-equal (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c)) m) bvar-db$c)
                                    (term-bvars$c bvar-db$c))
                  (hons-assoc-equal (bvar-terms$ci (+ m (- (base-bvar$c bvar-db$c))) bvar-db$c)
                                    (term-bvars$c bvar-db$c)))))

  ;; (defthm lookup-idx-when-bvar-db-bvar-terms-ok
  ;;   (implies (and (bvar-db-bvar-terms-ok n bvar-db$c)
  ;;                 (integerp m)
  ;;                 (< m (nfix n))
  ;;                 (<= (base-bvar$c bvar-db$c) m))
  ;;            (and (equal (cdr (hons-assoc-equal (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c)) m) bvar-db$c)
  ;;                                               (term-bvars$c bvar-db$c)))
  ;;                        m)
  ;;                 (equal (cdr (hons-assoc-equal (bvar-terms$ci (+ m (- (base-bvar$c bvar-db$c))) bvar-db$c)
  ;;                                               (term-bvars$c bvar-db$c)))
  ;;                        m))))
  

  (def-updater-independence-thm bvar-db-bvar-terms-ok-updater-independence
    (implies (and (equal (base-bvar$c new) (base-bvar$c old))
                  (bvar-terms-range-equiv 0 (- (nfix n) (base-bvar$c old)) new old)
                  (equal (term-bvars$c new) (term-bvars$c old)))
             (equal (bvar-db-bvar-terms-ok n new)
                    (bvar-db-bvar-terms-ok n old)))
    :hints(("Goal" :in-theory (enable BVAR-TERMS$CI-NON-EXEC-WHEN-BVAR-TERMS-RANGE-EQUIV)))))


(define bvar-list-okp$c ((x nat-listp) bvar-db$c)
  (if (atom x)
      t
    (and (<= (base-bvar$c bvar-db$c) (lnfix (car x)))
         (< (lnfix (car x)) (next-bvar1$c bvar-db$c))
         (bvar-list-okp$c (cdr x) bvar-db$c)))
  ///
  (def-updater-independence-thm bvar-list-okp$c-updater-independence
    (implies (and (equal (next-bvar1$c new) (next-bvar1$c old))
                  (equal (base-bvar$c new) (base-bvar$c old)))
             (equal (bvar-list-okp$c x new)
                    (bvar-list-okp$c x old))))

  (defthm bvar-list-okp$-of-update-next-bvar1$c
    (implies (and (bvar-list-okp$c x bvar-db$c)
                  (<= (next-bvar1$c bvar-db$c) (nfix new-next-bvar)))
             (bvar-list-okp$c x (update-next-bvar1$c new-next-bvar bvar-db$c))))

  (defthm bvar-list-okp$c-of-nil
    (bvar-list-okp$c nil bvar-db)))

;; (define bvar-list-cleanup$c ((x nat-listp) bvar-db$c)
;;   :returns (new-x nat-listp)
;;   (if (atom x)
;;       nil
;;     (if (and (<= (base-bvar$c bvar-db$c) (lnfix (car x)))
;;              (< (lnfix (car x)) (next-bvar1$c bvar-db$c)))
;;         (cons (lnfix (car x)) (bvar-list-cleanup$c (cdr x) bvar-db$c))
;;       (bvar-list-cleanup$c (cdr x) bvar-db$c)))
;;   ///
;;   (defthm bvar-list-okp$c-of-<fn>
;;     (bvar-list-okp$c (bvar-list-cleanup$c x bvar-db$c) bvar-db$c)
;;     :hints(("Goal" :in-theory (enable bvar-list-okp$c))))

;;   (defthm bvar-list-cleanup$c-when-bvar-list-okp$c
;;     (implies (bvar-list-okp$c x bvar-db$c)
;;              (equal (bvar-list-cleanup$c x bvar-db$c)
;;                     (acl2::nat-list-fix x)))
;;     :hints(("Goal" :in-theory (enable bvar-list-okp$c))))

;;   (local (in-theory (enable acl2::nat-list-fix))))


(define term-equivs-okp$c ((equivs term-equivs-p) bvar-db$c)
  (declare (xargs :stobjs bvar-db$c))
  (if (atom equivs)
      t
    (and (or (not (mbt (and (consp (car equivs))
                            (fgl-object-p (caar equivs)))))
             (bvar-list-okp$c (cdar equivs) bvar-db$c))
         (term-equivs-okp$c (cdr equivs) bvar-db$c)))
  ///
  (local (in-theory (enable term-equivs-fix)))
  
  (defthm term-equivs-okp$c-nil
    (term-equivs-okp$c nil bvar-db))
  
  (def-updater-independence-thm term-equivs-okp$c-updater-independence
    (implies (and (equal (next-bvar1$c new) (next-bvar1$c old))
                  (equal (base-bvar$c new) (base-bvar$c old)))
             (equal (term-equivs-okp$c x new)
                    (term-equivs-okp$c x old))))

  (defthm term-equivs-okp$-of-update-next-bvar1$c
    (implies (and (term-equivs-okp$c x bvar-db$c)
                  (<= (next-bvar1$c bvar-db$c) (nfix new-next-bvar)))
             (term-equivs-okp$c x (update-next-bvar1$c new-next-bvar bvar-db$c))))

  (defthm lookup-when-term-equivs-okp$c
    (implies (and (term-equivs-okp$c equivs bvar-db$c)
                  (fgl-object-p x))
             (bvar-list-okp$c (cdr (hons-assoc-equal x equivs)) bvar-db$c))))

(define bvar-fn-indices-okp$c ((x fn-indices-p) bvar-db$c)
  (if (atom x)
      t
    (and (or (not (mbt (and (consp (car x))
                            (pseudo-fnsym-p (caar x)))))
             (bvar-list-okp$c (cdar x) bvar-db$c))
         (bvar-fn-indices-okp$c (cdr x) bvar-db$c)))
  ///
  (local (in-theory (enable fn-indices-fix)))

  (def-updater-independence-thm bvar-fn-indices-okp$c-updater-independence
    (implies (and (equal (next-bvar1$c new) (next-bvar1$c old))
                  (equal (base-bvar$c new) (base-bvar$c old)))
             (equal (bvar-fn-indices-okp$c x new)
                    (bvar-fn-indices-okp$c x old))))

  (defthm bvar-fn-indices-okp$-of-update-next-bvar1$c
    (implies (and (bvar-fn-indices-okp$c x bvar-db$c)
                  (<= (next-bvar1$c bvar-db$c) (nfix new-next-bvar)))
             (bvar-fn-indices-okp$c x (update-next-bvar1$c new-next-bvar bvar-db$c))))

  (defthm bvar-list-okp$c-of-lookup-when-bvar-fn-indices-okp$c
    (implies (and (bvar-fn-indices-okp$c x bvar-db)
                  (pseudo-fnsym-p fn))
             (bvar-list-okp$c (cdr (hons-assoc-equal fn x)) bvar-db))
    :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(define bvar-db-wfp$c (bvar-db$c)
  (declare (xargs :stobjs bvar-db$c))
  (and (<= (base-bvar$c bvar-db$c)
           (next-bvar1$c bvar-db$c))
       (<= (- (next-bvar1$c bvar-db$c)
              (base-bvar$c bvar-db$c))
           (bvar-terms$c-length bvar-db$c))
       (bvar-fn-indices-okp$c (bvar-fn-indices$c bvar-db$c) bvar-db$c)
       (term-equivs-okp$c (term-equivs$c bvar-db$c) bvar-db$c)
       (bvar-db-term-bvars-ok (term-bvars$c bvar-db$c) bvar-db$c)
       (bvar-db-bvar-terms-ok (next-bvar1$c bvar-db$c) bvar-db$c))
  ///
  (def-updater-independence-thm bvar-db-wfp$c-updater-independence
    (implies (and (equal (base-bvar$c new) (base-bvar$c old))
                  (equal (next-bvar1$c new) (next-bvar1$c old))
                  (equal (bvar-terms$c-length new)
                         (bvar-terms$c-length old))
                  (equal (bvar-fn-indices$c new) (bvar-fn-indices$c old))
                  (equal (term-bvars$c new) (term-bvars$c old))
                  (equal (term-equivs$c new) (term-equivs$c old))
                  (bvar-terms-range-equiv 0 (- (next-bvar1$c old) (base-bvar$c old)) new old)
                  ;; (equal (bvar-db$c-get :bvar-terms new) (bvar-db$c-get :bvar-terms old))
                  )
             (equal (bvar-db-wfp$c new)
                    (bvar-db-wfp$c old))))

  
  (defthm lookup-in-bounds-when-bvar-db-wfp$c
    (implies (and (bvar-db-wfp$c bvar-db$c)
                  (hons-assoc-equal obj (term-bvars$c bvar-db$c))
                  (fgl-object-p obj))
             (let ((idx (cdr (hons-assoc-equal obj (term-bvars$c bvar-db$c)))))
               (and (<= (base-bvar$c bvar-db$c) idx)
                    (< idx (next-bvar1$c bvar-db$c))
                    (and (equal (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c)) idx)
                                               bvar-db$c)
                                obj)
                         (equal (bvar-terms$ci (+ idx (- (base-bvar$c bvar-db$c)))
                                               bvar-db$c)
                                obj)))))
    :hints (("goal" :use ((:instance lookup-in-bounds-when-bvar-db-term-bvars-ok
                           (term-bvars (term-bvars$c bvar-db$c))))
             :in-theory (disable lookup-in-bounds-when-bvar-db-term-bvars-ok))))

  (defthm lookup-exists-when-bvar-db-wfp$c
    (implies (and (bvar-db-wfp$c bvar-db$c)
                  (integerp m)
                  (< m (next-bvar1$c bvar-db$c))
                  (<= (base-bvar$c bvar-db$c) m))
             (and (hons-assoc-equal (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c)) m) bvar-db$c)
                                    (term-bvars$c bvar-db$c))
                  (hons-assoc-equal (bvar-terms$ci (+ m (- (base-bvar$c bvar-db$c))) bvar-db$c)
                                    (term-bvars$c bvar-db$c)))))

  ;; (defthm lookup-idx-when-bvar-db-bvar-db-wfp$c
  ;;   (implies (and (bvar-db-wfp$c bvar-db$c)
  ;;                 (integerp m)
  ;;                 (< m (next-bvar1$c bvar-db$c))
  ;;                 (<= (base-bvar$c bvar-db$c) m))
  ;;            (and (equal (cdr (hons-assoc-equal (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c)) m) bvar-db$c)
  ;;                                               (term-bvars$c bvar-db$c)))
  ;;                        m)
  ;;                 (equal (cdr (hons-assoc-equal (bvar-terms$ci (+ m (- (base-bvar$c bvar-db$c))) bvar-db$c)
  ;;                                               (term-bvars$c bvar-db$c)))
  ;;                        m))))

  (defthm bvar-db-wfp$c-implies-rw
    (implies (bvar-db-wfp$c bvar-db$c)
             (and (bvar-fn-indices-okp$c (bvar-fn-indices$c bvar-db$c) bvar-db$c)
                  (term-equivs-okp$c (term-equivs$c bvar-db$c) bvar-db$c)
                  (bvar-db-term-bvars-ok (term-bvars$c bvar-db$c) bvar-db$c)
                  (bvar-db-bvar-terms-ok (next-bvar1$c bvar-db$c) bvar-db$c))))

  (defthm bvar-db-wfp$c-implies-linear
    (implies (bvar-db-wfp$c bvar-db$c)
             (and (<= (base-bvar$c bvar-db$c)
                      (next-bvar1$c bvar-db$c))
                  (<= (- (next-bvar1$c bvar-db$c)
                         (base-bvar$c bvar-db$c))
                      (bvar-terms$c-length bvar-db$c))))
    :rule-classes :linear))


;; (define get-term-equivs$c ((x fgl-object-p) bvar-db$c)
;;   :returns (bvars nat-listp)
;;   :guard (bvar-db-wfp$c bvar-db$c)
;;   :guard-hints (("goal" :in-theory (enable bvar-db-wfp$c)))
;;   (mbe :logic (bvar-list-cleanup$c (cdr (hons-get (fgl-object-fix x) (term-equivs$c bvar-db$c))) bvar-db$c)
;;        :exec (cdr (hons-get x (term-equivs$c bvar-db$c))))
;;   ///
;;   (defret bvar-list-okp$c-of-<fn>
;;     (bvar-list-okp$c bvars bvar-db$c)))

(local (defthm integerp-lookup-when-term-bvars-p
         (implies (and (term-bvars-p x)
                       (hons-assoc-equal k x))
                  (and (integerp (cdr (hons-assoc-equal k x)))
                       (natp (cdr (hons-assoc-equal k x)))))
         :rule-classes ((:rewrite))))

(local (defthm integerp-lookup-of-term-bvars$c
         (implies (hons-assoc-equal k (term-bvars$c x))
                  (natp (cdr (hons-assoc-equal k (term-bvars$c x)))))
         :rule-classes :type-prescription))

(define get-term->bvar$c ((x fgl-object-p) bvar-db$c)
  :guard (bvar-db-wfp$c bvar-db$c)
  :returns (bvar acl2::maybe-natp :rule-classes ((:type-prescription :typed-term bvar)))
  (mbe :logic ;; (find-bvar-for-term (next-bvar1$c bvar-db$c) x bvar-db$c)
       
       (let ((look (hons-get (fgl-object-fix x) (term-bvars$c bvar-db$c))))
                (and look
                     (<= (base-bvar$c bvar-db$c) (cdr look))
                     (< (cdr look) (next-bvar1$c bvar-db$c))
                     (equal (bvar-terms$ci (- (cdr look) (base-bvar$c bvar-db$c)) bvar-db$c)
                            (fgl-object-fix x))
                     (cdr look)))
       :exec (cdr (hons-get x (term-bvars$c bvar-db$c)))) ;;
                 ;; (term-bvars-fix (term-bvars$c bvar-db$c))))
  ///
  (def-updater-independence-thm get-term->bvar$c-updater-independence
    (implies (and (equal (base-bvar$c new) (base-bvar$c old))
                  (equal (next-bvar1$c new) (next-bvar1$c old))
                  (equal (term-bvars$c new) (term-bvars$c old))
                  (bvar-terms-range-equiv 0 (- (next-bvar1$c old) (base-bvar$c old))
                                          ;; (bvar-db$c-get :bvar-terms new) (bvar-db$c-get :bvar-terms old)
                                          new old))
             (equal (get-term->bvar$c x new)
                    (get-term->bvar$c x old)))
    :hints(("Goal" :in-theory (enable bvar-terms$ci-non-exec-when-bvar-terms-range-equiv))))

  (defthm get-term->bvar$c-in-bounds
    (implies (get-term->bvar$c x bvar-db$c)
             (and (<= (base-bvar$c bvar-db$c) (get-term->bvar$c x bvar-db$c))
                  (< (get-term->bvar$c x bvar-db$c) (next-bvar1$c bvar-db$c))))
    :rule-classes :linear)

  ;; (defret get-term->bvar$c-correct
  ;;   (implies (and (equal (bvar-terms$ci (- m (base-bvar$c bvar-db$c)) bvar-db$c)
  ;;                        (fgl-object-fix x))
  ;;                 (<= (base-bvar$c bvar-db$c) m)
  ;;                 (< m (next-bvar1$c bvar-db$c))
  ;;                 (natp m))
  ;;            (and bvar
  ;;                 (and (equal (bvar-terms$ci (+ bvar
  ;;                                               (- (base-bvar$c bvar-db$c)))
  ;;                                            bvar-db$c)
  ;;                             (fgl-object-fix x))
  ;;                      (equal (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c))
  ;;                                               bvar)
  ;;                                            bvar-db$c)
  ;;                             (fgl-object-fix x))))))

  ;; (defret get-term->bvar$c-of-inverse-when-bvar-db-wfp$c
  ;;   (implies (and (bvar-db-wfp$c bvar-db$c)
  ;;                 (<= (base-bvar$c bvar-db$c) m)
  ;;                 (< m (next-bvar1$c bvar-db$c))
  ;;                 (natp m))
  ;;            (and (equal (get-term->bvar$c (bvar-terms$ci (- m (base-bvar$c bvar-db$c)) bvar-db$c) bvar-db$c)
  ;;                        m)
  ;;                 (equal (get-term->bvar$c (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c)) m) bvar-db$c) bvar-db$c)
  ;;                        m)))
  ;;   :hints (("goal" :use ((:instance lookup-idx-when-bvar-db-bvar-db-wfp$c))
  ;;            :in-theory (disable lookup-idx-when-bvar-db-bvar-db-wfp$c))))

  (defret bvar-terms$ci-of-get-term->bvar$c
    (implies bvar
             (and (equal (bvar-terms$ci (- bvar (base-bvar$c bvar-db$c)) bvar-db$c)
                         (fgl-object-fix x))
                  (equal (bvar-terms$ci (+ (- (base-bvar$c bvar-db$c)) bvar) bvar-db$c)
                         (fgl-object-fix x))))))



(define next-bvar$c (bvar-db$c)
  :guard (bvar-db-wfp$c bvar-db$c)
  :guard-hints (("goal" :in-theory (enable bvar-db-wfp$c)))
  :returns (next natp :rule-classes :type-prescription)
  :inline t
  (mbe :logic (max (next-bvar1$c bvar-db$c) (base-bvar$c bvar-db$c))
       :exec (next-bvar1$c bvar-db$c))
  ///
  (def-updater-independence-thm next-bvar$c-of-update
    (implies (and (equal (base-bvar$c new)
                         (base-bvar$c old))
                  (equal (next-bvar1$c new)
                         (next-bvar1$c old)))
             (equal (next-bvar$c new)
                    (next-bvar$c old))))

  (defthm next-bvar$c-of-update-next-bvar1$c
    (equal (next-bvar$c (update-next-bvar1$c n bvar-db$c))
           (max (base-bvar$c bvar-db$c) (nfix n))))

  (defthm next-bvar$c-when-wfp
    (implies (bvar-db-wfp$c bvar-db$c)
             (equal (next-bvar$c bvar-db$c)
                    (next-bvar1$c bvar-db$c)))
    :hints(("Goal" :in-theory (enable bvar-db-wfp$c))))

  (defthmd next-bvar$c1-when-wfp
    (implies (bvar-db-wfp$c bvar-db$c)
             (equal (next-bvar$c bvar-db$c)
                    (next-bvar1$c bvar-db$c)))
    :hints(("Goal" :in-theory (enable bvar-db-wfp$c))))

  (defthm next-bvar$c-gte-base
    (<= (base-bvar$c bvar-db$c) (next-bvar$c bvar-db$c))
    :rule-classes :linear)

  (defthm next-bvar$c-gte-next
    (<= (next-bvar1$c bvar-db$c) (next-bvar$c bvar-db$c))
    :rule-classes :linear))


               
           
    

(define get-bvar->term$c ((n natp :type (integer 0 *)) bvar-db$c)
  :guard (and (<= (base-bvar$c bvar-db$c) n)
              (< n (next-bvar1$c bvar-db$c))
              (bvar-db-wfp$c bvar-db$c))
  :split-types t
  :returns (term fgl-object-p)
  :guard-hints (("goal" :in-theory (enable bvar-db-wfp$c)))
  (fgl-object-fix (and (mbt (and (<= (base-bvar$c bvar-db$c) (nfix n))
                                 (< (nfix n) (next-bvar$c bvar-db$c))))
                       (bvar-terms$ci (- (lnfix n) (lnfix (base-bvar$c bvar-db$c))) bvar-db$c)))
  ///
  (def-updater-independence-thm get-bvar->term$c-updater-independence
    (implies (and (equal (base-bvar$c new)
                         (base-bvar$c old))
                  (equal (next-bvar1$c new)
                         (next-bvar1$c old))
                  (equal (bvar-terms$ci (- (nfix n) (base-bvar$c old)) new)
                         (bvar-terms$ci (- (nfix n) (base-bvar$c old)) old)))
             (equal (get-bvar->term$c n new)
                    (get-bvar->term$c n old))))

  (defthm get-bvar->term$c-inverse-of-get-term->bvar$c
    (implies (and ;; (bvar-db-wfp$c bvar-db$c)
                  (get-term->bvar$c obj bvar-db$c))
             (equal (get-bvar->term$c (get-term->bvar$c obj bvar-db$c) bvar-db$c)
                    (fgl-object-fix obj)))
    :hints(("Goal" :in-theory (e/d (next-bvar$c)))))

  ;; (defthm get-term->bvar$c-inverse-of-get-bvar->term$c-when-bvar-db-wfp$c
  ;;   (implies (and (bvar-db-wfp$c bvar-db$c)
  ;;                 (<= (base-bvar$c bvar-db$c) (nfix n))
  ;;                 (< (nfix n) (next-bvar1$c bvar-db$c)))
  ;;            (equal (get-term->bvar$c (get-bvar->term$c n bvar-db$c) bvar-db$c)
  ;;                   (nfix n)))
  ;;   :hints (("goal" :use ((:instance get-term->bvar$c-correct
  ;;                          (x (get-bvar->term$c n bvar-db$c))
  ;;                          (m (nfix n))))
  ;;            :in-theory (disable get-term->bvar$c-correct))))
  )

(local
 (defthm bvar-terms$ci-of-resize
   (implies (or (< (nfix n) (nfix m))
                (<= (bvar-terms$c-length bvar-db$c) (nfix m)))
            (equal (bvar-terms$ci n (resize-bvar-terms$c m bvar-db$c))
                   (bvar-terms$ci n bvar-db$c)))
   :hints(("Goal" :in-theory (enable resize-bvar-terms$c
                                     bvar-db$c->bvar-termsi^
                                     bvar-terms$c-length
                                     bvar-terms$ci)))))


(define add-term-bvar$c ((x fgl-object-p) bvar-db$c)
  :guard (and (bvar-db-wfp$c bvar-db$c)
              ;; (not (get-term->bvar$c x bvar-db$c))
              )
  :guard-hints (("goal" :in-theory (enable bvar-db-wfp$c)))
  :returns new-bvar-db$c
  (b* ((next (the (integer 0 *) (next-bvar$c bvar-db$c)))
       (idx (the (integer 0 *) (- next (base-bvar$c bvar-db$c))))
       (terms-len (the (integer 0 *) (bvar-terms$c-length bvar-db$c)))
       (bvar-db$c (if (mbe :logic (<= terms-len idx)
                           :exec (int= terms-len idx))
                      (resize-bvar-terms$c
                       (max 16 (* 2 idx)) bvar-db$c)
                    bvar-db$c))
       (x (hons-copy (fgl-object-fix x)))
       (bvar-db$c (update-bvar-terms$ci idx x bvar-db$c))
       (bvar-db$c (update-next-bvar1$c (+ 1 next) bvar-db$c))
       (bvar-db$c (update-term-bvars$c
                   (hons-acons x next (term-bvars$c bvar-db$c))
                   bvar-db$c)))
    (fgl-object-case x
      :g-apply (b* ((indices (bvar-fn-indices$c bvar-db$c))
                    (new-indices (hons-acons x.fn (cons next (cdr (hons-get x.fn indices))) indices)))
                 (update-bvar-fn-indices$c new-indices bvar-db$c))
      :otherwise bvar-db$c))
       
  ///

  (defret bvar-db$c-get-of-<fn>
    (implies (not (member (bvar-db$c-field-fix key)
                          '(:next
                            :bvar-terms
                            :term-bvars
                            :fn-indices)))
             (equal (bvar-db$c-get key new-bvar-db$c)
                    (bvar-db$c-get key bvar-db$c))))

  (defthm get-term->bvar$c-of-add-term-bvar$c
    (equal (get-term->bvar$c x (add-term-bvar$c y bvar-db$c))
           (if (fgl-object-equiv x y)
               (next-bvar$c bvar-db$c)
             (get-term->bvar$c x bvar-db$c)))
    :hints(("Goal" :in-theory (enable get-term->bvar$c
                                      ;; find-bvar-for-term
                                    bvar-terms$ci-of-update-bvar-terms$ci-split
                                      next-bvar$c))))

  (local (defthm bvar-terms$ci-when-zp
           (implies (and (syntaxp (not (equal n ''0)))
                         (zp n))
                    (equal (bvar-terms$ci n bvar-db)
                           (bvar-terms$ci 0 bvar-db)))
           :hints (("goal" :use ((:instance bvar-terms$ci$inline-of-nfix-i
                                  (i n)))))))

  (defthm bvar-terms$ci-of-add-term-bvar$c
    (equal (bvar-terms$ci n (add-term-bvar$c x bvar-db$c))
           (if (equal (nfix n) (- (next-bvar$c bvar-db$c)
                                  (base-bvar$c bvar-db$c)))
               (fgl-object-fix x)
             (bvar-terms$ci n bvar-db$c))))
  
  (defthm get-bvar->term$c-of-add-term-bvar$c
    (equal (get-bvar->term$c n (add-term-bvar$c x bvar-db$c))
           (if (equal (nfix n) (next-bvar$c bvar-db$c))
               (fgl-object-fix x)
             (get-bvar->term$c n bvar-db$c)))
    :hints(("Goal" :in-theory (e/d (get-bvar->term$c
                                      next-bvar$c
                                      BVAR-TERMS$CI-OF-UPDATE-BVAR-TERMS$CI-SPLIT)))))

  (defthm next-bvar1$c-of-add-term-bvar$c
    (equal (next-bvar1$c (add-term-bvar$c x bvar-db$c))
           (+ 1 (next-bvar$c bvar-db$c))))

  (defthm next-bvar$c-of-add-term-bvar$c
    (equal (next-bvar$c (add-term-bvar$c x bvar-db$c))
           (+ 1 (next-bvar$c bvar-db$c)))
    :hints(("Goal" :in-theory (enable next-bvar$c))))


  (defthm bvar-list-okp$-of-add-term-bvar$c
    (implies (bvar-list-okp$c lst bvar-db)
             (bvar-list-okp$c lst (add-term-bvar$c x bvar-db)))
    :hints(("Goal" :in-theory (enable add-term-bvar$c
                                      next-bvar$c))))

  (defthm term-equivs-okp$c-of-add-term-bvar
    (implies (term-equivs-okp$c equivs bvar-db)
             (term-equivs-okp$c equivs (add-term-bvar$c x bvar-db))))

  (defthm bvar-fn-indices-okp$c-of-add-term-bvar$c-lemma
    (b* ((new-bvar-db (add-term-bvar$c term bvar-db)))
      (implies (bvar-fn-indices-okp$c x bvar-db)
               (bvar-fn-indices-okp$c x new-bvar-db))))

  (defthm bvar-fn-indices-okp$c-of-add-term-bvar$c
    (b* ((new-bvar-db (add-term-bvar$c x bvar-db)))
      (implies (and (bvar-fn-indices-okp$c (bvar-fn-indices$c bvar-db) bvar-db)
                    (<= (base-bvar$c bvar-db)
                        (next-bvar1$c bvar-db)))
               (bvar-fn-indices-okp$c (bvar-fn-indices$c new-bvar-db) new-bvar-db)))
    :hints(("Goal" :in-theory (enable bvar-list-okp$c
                                      add-term-bvar$c
                                      next-bvar$c)
            :expand ((:free (a b c) (bvar-fn-indices-okp$c (cons a b) c)))
            :use ((:instance bvar-fn-indices-okp$c-of-add-term-bvar$c-lemma
                   (x (bvar-fn-indices$c bvar-db)))))))

  ;; (local (defthm find-bvar-for-term-inverse-special
  ;;          (let ((obj (bvar-terms$ci (+ -1 m (- (base-bvar$c bvar-db$c))) bvar-db$c)))
  ;;            (implies (and (< (base-bvar$c bvar-db$c) m)
  ;;                          (<= m (nfix n))
  ;;                          (posp m))
  ;;                     (and (find-bvar-for-term n obj bvar-db$c)
  ;;                          (implies (and (bvar-db-wfp$c bvar-db$c)
  ;;                                        (<= (nfix n) (next-bvar1$c bvar-db$c)))
  ;;                                   (equal (find-bvar-for-term n obj bvar-db$c)
  ;;                                          (1- m))))))
  ;;          :hints (("goal" :use ((:instance find-bvar-for-term-inverse
  ;;                                 (m (+ -1 m))))
  ;;                   :in-theory (disable find-bvar-for-term-inverse)))))

  ;; (local (defthm find-bvar-for-term-inverse-special2
  ;;          (implies (and (equal (fgl-object-fix obj) (bvar-terms$ci (+ -1 m (- (base-bvar$c bvar-db$c))) bvar-db$c))
  ;;                        (< (base-bvar$c bvar-db$c) m)
  ;;                        (<= m (nfix n))
  ;;                        (posp m))
  ;;                   (and (find-bvar-for-term n obj bvar-db$c)
  ;;                        (implies (and (bvar-db-wfp$c bvar-db$c)
  ;;                                      (<= (nfix n) (next-bvar1$c bvar-db$c)))
  ;;                                 (equal (find-bvar-for-term n obj bvar-db$c)
  ;;                                        (1- m)))))
  ;;          :hints (("goal" :use ((:instance find-bvar-for-term-inverse-special))
  ;;                   :in-theory (disable find-bvar-for-term-inverse-special)))))
  
  (defthm bvar-db-bvar-terms-ok-of-add-term-bvar$c
    (implies (and ;; (bvar-db-wfp$c bvar-db$c)
              (bvar-db-bvar-terms-ok n bvar-db$c)
                  ;; (bvar-db-bvar-terms-ok n bvar-db$c)
                  ;; (not (hons-assoc-equal (fgl-object-fix x) (term-bvars$c bvar-db$c)))
                  ;; (not (get-term->bvar$c x bvar-db$c))
                  (<= (nfix n) (next-bvar1$c bvar-db$c)))
             (bvar-db-bvar-terms-ok n (add-term-bvar$c x bvar-db$c)))
    :hints(("Goal" :in-theory (e/d (bvar-db-bvar-terms-ok)
                                   (add-term-bvar$c))
            :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable add-term-bvar$c
                                     get-term->bvar$c)))
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable add-term-bvar$c
           ;;                           get-term->bvar$c
           ;;                           ;; lookup-in-term-bvars-in-terms-of-find-bvar-for-term-when-bvar-db-wfp
           ;;                           )
           ;;        :do-not-induct t))
           ))

  (defthm term-bvars-of-add-term-bvar$c
    (equal (term-bvars$c (add-term-bvar$c x bvar-db$c))
           (cons (cons (fgl-object-fix x) (next-bvar$c bvar-db$c))
                 (term-bvars$c bvar-db$c))))
  
  (defthm bvar-db-term-bvars-ok-of-add-term-bvar$c
    (implies (bvar-db-term-bvars-ok term-bvars bvar-db$c)
             (bvar-db-term-bvars-ok term-bvars (add-term-bvar$c x bvar-db$c)))
    :hints(("Goal" :in-theory (e/d (bvar-db-term-bvars-ok)
                                   (add-term-bvar$c))
            :induct t)
           (and stable-under-simplificationp
                '(:in-theory (enable add-term-bvar$c)))))
  
  
  (defthm bvar-db-wfp$c-of-add-term-bvar$c
    (implies (and (bvar-db-wfp$c bvar-db$c)
                  ;; (not (get-term->bvar$c x bvar-db$c))
                  )
             (bvar-db-wfp$c (add-term-bvar$c x bvar-db$c)))
    :hints(("Goal" :in-theory (e/d (bvar-db-wfp$c)
                                   (add-term-bvar$c))
            :do-not-induct t)
           (and stable-under-simplificationp
                '(:expand ((:free (a b c) (bvar-db-term-bvars-ok (cons a b) c))
                           (:free (b) (bvar-db-bvar-terms-ok (+ 1 (next-bvar1$c bvar-db$c)) b)))))
           (and stable-under-simplificationp
                '(:in-theory (enable add-term-bvar$c))))
    :otf-flg t))







;; (defthm get-bvar->term$c-of-add-term-equiv$c
;;   (equal (get-bvar->term$c x (add-term-equiv$c y n bvar-db$c))
;;          (get-bvar->term$c x bvar-db$c)))

;; (defthm base-bvar$c-of-add-term-equiv$c
;;   (equal (nth *base-bvar$c* (add-term-equiv$c x n bvar-db$c))
;;          (nth *base-bvar$c* bvar-db$c)))

;; (defthm next-bvar1$c-of-add-term-equiv$c
;;   (equal (nth *next-bvar1$c* (add-term-equiv$c x n bvar-db$c))
;;          (nth *next-bvar1$c* bvar-db$c)))


;; (defthm bvar-db-wfp$c-of-add-term-equiv$c
;;   (implies (bvar-db-wfp$c bvar-db$c)
;;            (bvar-db-wfp$c (add-term-equiv$c x n bvar-db$c))))
(defstobj-clone bvar-db$c1 bvar-db$c :suffix "1")

(define init-bvar-db$c ((base-bvar natp :type (integer 0 *)) bvar-db$c)
  :split-types t
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable bvar-db$cp))))
  :prepwork ((local (defthm take-of-len
                      (implies (equal n (len x))
                               (equal (take n x)
                                      (true-list-fix x))))))
 (b* (((acl2::local-stobjs bvar-db$c1)
        (mv bvar-db$c1 bvar-db$c))
       ((mv bvar-db$c bvar-db$c1)
        ;; avoid ACL2 bug
        (mbe :logic (non-exec (swap-stobjs bvar-db$c bvar-db$c1))
             :exec (swap-stobjs bvar-db$c bvar-db$c1)))
       (bvar-db$c (update-base-bvar$c (lnfix base-bvar) bvar-db$c))
       (bvar-db$c (update-next-bvar1$c (lnfix base-bvar) bvar-db$c))
       ;; (bvar-db$c (resize-bvar-terms$c 0 bvar-db$c))
       ;; (bvar-db$c (update-term-equivs$c nil bvar-db$c))
       ;; (bvar-db$c (update-bvar-fn-indices$c nil bvar-db$c))
       ;; (bvar-db$c (update-term-bvars$c nil bvar-db$c))
       )
    (mv bvar-db$c1 bvar-db$c))
  ///


  (in-theory (disable (init-bvar-db$c)))
  
  (defthm base-bvar$c-of-init-bvar-db$c
    (equal (base-bvar$c (init-bvar-db$c base bvar-db$c))
           (nfix base)))

  (defthm term-equivs$c-of-init-bvar-db$c
    (equal (term-equivs$c (init-bvar-db$c base-bvar bvar-db$c))
           nil))

  (defthm next-bvar1$c-of-init-bvar-db$c
    (equal (next-bvar1$c (init-bvar-db$c base bvar-db$c))
           (nfix base)))

  (defthm get-term->bvar-of-init-bvar-db$c
    (equal (get-term->bvar$c x (init-bvar-db$c base bvar-db$c))
           nil)
    :hints(("Goal" :in-theory (enable get-term->bvar$c))))

  (defthm bvar-db-wfp$c-of-init-bvar-db$c
    (bvar-db-wfp$c (init-bvar-db$c base bvar-db$c))
    :hints(("Goal" :in-theory (enable bvar-db-wfp$c
                                      bvar-fn-indices-okp$c
                                      bvar-db-term-bvars-ok
                                      bvar-db-bvar-terms-ok))))

  
  (defthm init-bvar-db$c-normalize
    (implies (syntaxp (not (equal bvar-db$c ''nil)))
             (equal (init-bvar-db$c base-bvar bvar-db$c)
                    (init-bvar-db$c base-bvar nil))))

  (local (defthm open-update-nth
           (implies (syntaxp (quotep n))
                    (equal (update-nth n val x)
                           (if (zp n)
                               (cons val (cdr x))
                             (cons (car x)
                                   (update-nth (1- n) val (cdr x))))))
           :hints(("Goal" :in-theory (enable update-nth)))))

  (defthmd init-bvar-db$c-as-list
    (implies (syntaxp (not (equal bvar-db$c ''nil)))
             (equal (init-bvar-db$c base-bvar bvar-db$c)
                    (list* (nfix base-bvar) (nfix base-bvar) '(nil nil nil nil))))
    :hints(("Goal" :in-theory (enable update-next-bvar1$c
                                      update-base-bvar$c
                                      update-bvar-db$c->next^
                                      update-bvar-db$c->base^)))))


(defthm create-bvar-db$c-rewrite
  (equal (create-bvar-db$c)
         (init-bvar-db$c 0 nil))
  :hints(("Goal" :in-theory (e/d (init-bvar-db$c)
                                 ((tau-system))))))

(local (in-theory (disable (create-bvar-db$c) create-bvar-db$c)))


(define bvar-fn-term-indices$c ((fn pseudo-fnsym-p) bvar-db$c)
  :returns (indices nat-listp)
  (cdr (hons-get (pseudo-fnsym-fix fn)
                 (bvar-fn-indices$c bvar-db$c)))
  ///
  (def-updater-independence-thm bvar-fn-term-indices$c-updater-independence
    (implies (equal (bvar-fn-indices$c new)
                    (bvar-fn-indices$c old))
             (equal (bvar-fn-term-indices$c fn new)
                    (bvar-fn-term-indices$c fn old))))

  (defthm bvar-fn-term-indices-of-add-term-bvar$c
    (equal (bvar-fn-term-indices$c fn (add-term-bvar$c x bvar-db$c))
           (if (fgl-object-case x :g-apply (equal x.fn (pseudo-fnsym-fix fn))
                 :otherwise nil)
               (cons (next-bvar$c bvar-db$c)
                     (bvar-fn-term-indices$c fn bvar-db$c))
             (bvar-fn-term-indices$c fn bvar-db$c)))
    :hints(("Goal" :in-theory (enable add-term-bvar$c)))))


(define bvar-db$ap (x)
  :non-executable t
  :guard t
  :enabled t
  (ec-call (bvar-db-wfp$c x)))

(local (include-book "tools/easy-simplify" :dir :System))

(local (table def-$a-map 'bvar-db-wfp$c 'bvar-db$ap))

(local
 (defun def-$a-fn (name$a pre-guard guard wrld)
   (declare (xargs :mode :program))
   (b* ((name$c (intern-in-package-of-symbol
                 (str::strsubst "$A" "$C" (symbol-name name$a))
                 name$a))
        (name$c-fn (acl2::deref-macro-name name$c (macro-aliases wrld)))
        (fn-subst (table-alist 'def-$a-map wrld))
        (args (subst 'bvar-db 'bvar-db$c (formals name$c-fn wrld)))
        (fn-guard (sublis fn-subst (subst 'bvar-db 'bvar-db$c (guard name$c-fn t wrld))))
        (guard-terms (append (and (not (eq pre-guard t)) (list pre-guard))
                             (and (not (eq fn-guard t)) (list fn-guard))
                             (and (not (eq guard t)) (list guard))))
        (guard (cond ((atom guard-terms) t)
                     ((atom (cdr guard-terms)) (car guard-terms))
                     (t `(and . ,guard-terms)))))
     `(progn (define ,name$a ,args
               :enabled t
               :guard ,guard
               :non-executable t
               (ec-call (,name$c-fn . ,args)))
             ;; (in-theory (disable (,name$a)))
             (local (table def-$a-map ',name$c-fn ',name$a))
             (local (table def-$a-map ',name$c ',name$a))))))
(local
 (defmacro def-$a (name$a &key (guard 't) (pre-guard 't))
   `(make-event (def-$a-fn ',name$a ',pre-guard ',guard (w state)))))

(def-$a create-bvar-db$a)
(def-$a base-bvar$a)
(def-$a next-bvar$a)
(local (table def-$a-map 'next-bvar1$c 'next-bvar$a))
(local (table def-$a-map 'next-bvar1$c$inline 'next-bvar$a))
(def-$a get-term->bvar$a)
(def-$a get-bvar->term$a :pre-guard (bvar-db$ap bvar-db))
(def-$a term-equivs$a)
(def-$a bvar-list-okp$a)
(def-$a term-equivs-okp$a)
(def-$a add-term-bvar$a)
(def-$a bvar-list-okp$a)
(def-$a term-equivs-okp$a)
(def-$a update-term-equivs$a
  :guard (term-equivs-okp$a term-equivs bvar-db))
(def-$a init-bvar-db$a)
(def-$a bvar-fn-term-indices$a)
;; (def-$a get-term-equivs$a)

;; (defun-sk bvar-dbs-terms-corr (bvar-db$c bvar-db$a)
;;   (forall x
;;           (and (equal (get-term->bvar$c x bvar-db$c)
;;                       (get-term->bvar$a x bvar-db$a))
;;                (equal (term-equivs$c bvar-db$c)
;;                       (term-equivs$a bvar-db$a))))
;;   :rewrite :direct)

;; (defun-sk bvar-dbs-bvars-corr (bvar-db$c bvar-db$a)
;;   (forall n
;;           (implies (and (natp n)
;;                         (<= (base-bvar$a bvar-db$a) n)
;;                         (< n (next-bvar$a bvar-db$a)))
;;                    (equal (get-bvar->term$c n bvar-db$c)
;;                           (get-bvar->term$a n bvar-db$a))))
;;   :rewrite :direct)

;; (local (in-theory (disable bvar-dbs-terms-corr
;;                            bvar-dbs-bvars-corr)))

;; (defun bvar-dbs-corr (bvar-db$c bvar-db$a)
;;   (equal bvar-db$c bvar-db$a))
  ;; (and (equal (base-bvar$c bvar-db$c) (base-bvar$a bvar-db$a))
  ;;      (equal (next-bvar1$c bvar-db$c) (next-bvar$a bvar-db$a))
  ;;      (bvar-dbs-bvars-corr bvar-db$c bvar-db$a)
  ;;      (bvar-dbs-terms-corr bvar-db$c bvar-db$a)))


(encapsulate nil
  (local (in-theory (e/d (bvar-db$ap
                          bvar-fn-indices-okp$c
                          init-bvar-db$c))))

  (local (defthm bvar-db-wfp$c-of-update-term-equivs$c
           (implies (and (bvar-db-wfp$c bvar-db)
                         (term-equivs-okp$c v bvar-db))
                    (bvar-db-wfp$c (update-term-equivs$c v bvar-db)))
           :hints(("Goal" :in-theory (enable bvar-db-wfp$c)))))
  
  (acl2::defabsstobj-events bvar-db
    :creator (create-bvar-db :logic create-bvar-db$a :exec create-bvar-db$c)
    :recognizer (bvar-dbp :logic bvar-db$ap :exec bvar-db$cp)
    :corr-fn equal ;; bvar-dbs-corr
    :exports ((base-bvar :logic base-bvar$a :exec base-bvar$c$inline)
              (next-bvar :logic next-bvar$a :exec next-bvar1$c$inline)
              (get-term->bvar :logic get-term->bvar$a :exec get-term->bvar$c)
              (get-bvar->term :logic get-bvar->term$a :exec get-bvar->term$c)
              (term-equivs :logic term-equivs$a :exec term-equivs$c$inline)
              (bvar-list-okp :logic bvar-list-okp$a :exec bvar-list-okp$c)
              (term-equivs-okp :logic term-equivs-okp$a :exec term-equivs-okp$c)
              (add-term-bvar :logic add-term-bvar$a :exec add-term-bvar$c :protect t)
              (update-term-equivs :logic update-term-equivs$a :exec update-term-equivs$c$inline)
              (init-bvar-db :logic init-bvar-db$a :exec init-bvar-db$c :protect t)
              (bvar-fn-term-indices :logic bvar-fn-term-indices$a :exec bvar-fn-term-indices$c)
              ;; (get-term-equivs :logic get-term-equivs$a :exec get-term-equivs$c)
              )))





(defun-sk bvar-db-bvar->term-extension-p (new old)
  (forall v
          (implies (and (natp v)
                        (or (< v (next-bvar$c old))
                            (<= (next-bvar$c new) v)))
                   (equal (get-bvar->term$c v new)
                          (get-bvar->term$c v old))))
  :rewrite :direct)

(defun-sk bvar-db-term->bvar-extension-p (new old)
  (forall x
          (implies (get-term->bvar$c x old)
                   (equal (get-term->bvar$c x new)
                          (get-term->bvar$c x old))))
  :rewrite :direct)

(in-theory (disable bvar-db-bvar->term-extension-p
                    bvar-db-term->bvar-extension-p))


(defmacro bind-bvar-db-extension (new old-var)
  `(and (bind-free (acl2::prev-stobj-binding ,new ',old-var mfc state))
        (bvar-db-extension-p ,new ,old-var)))



(define bvar-db-extension-p (new old)
  :non-executable t
  :verify-guards nil
  (and (equal (base-bvar$c new) (base-bvar$c old))
       (>= (next-bvar$c new) (next-bvar$c old))
       (bvar-db-bvar->term-extension-p new old)
       (bvar-db-term->bvar-extension-p new old)
       ;; bozo this wouldn't be the right invariant about term-equivs, but it
       ;; seems for now we don't need one.
       ;; (acl2::suffixp (term-equivs$c old) (term-equivs$c new))
       )
  ///
  (defthm bvar-db-extension-preserves-base-bvar
    (implies (bind-bvar-db-extension new old)
             (equal (base-bvar$c new) (base-bvar$c old))))

  (defthm bvar-db-extension-increases
    (implies (bind-bvar-db-extension new old)
             (>= (next-bvar$c new) (next-bvar$c old)))
    :rule-classes ((:linear :trigger-terms ((next-bvar$c new)))))

  (defthm bvar-db-extension-preserves-get-bvar->term
    (implies (and (bind-bvar-db-extension new old)
                  (or (< (nfix v) (next-bvar$c old))
                      (<= (next-bvar$c new) (nfix v))))
             (equal (get-bvar->term$c v new)
                    (get-bvar->term$c v old)))
    :hints (("goal" :use ((:instance bvar-db-bvar->term-extension-p-necc
                           (v (nfix v))))
             :in-theory (disable bvar-db-bvar->term-extension-p-necc))))

  (defthm bvar-db-extension-preserves-get-term->bvar
    (implies (and (bind-bvar-db-extension new old)
                  (get-term->bvar$c x old))
             (equal (get-term->bvar$c x new)
                    (get-term->bvar$c x old))))

  (defthm bvar-db-extension-p-self
    (bvar-db-extension-p x x)
    :hints(("Goal" :in-theory (enable bvar-db-bvar->term-extension-p
                                      bvar-db-term->bvar-extension-p))))

  (local (defthm bvar-db-bvar->term-extension-p-transitive
           (implies (and (bvar-db-bvar->term-extension-p new med)
                         (bvar-db-bvar->term-extension-p med old)
                         (<= (next-bvar$c med) (next-bvar$c new))
                         (<= (next-bvar$c old) (next-bvar$c med)))
                    (bvar-db-bvar->term-extension-p new old))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))

  (local (defthm bvar-db-term->bvar-extension-p-transitive
           (implies (and (bvar-db-term->bvar-extension-p new med)
                         (bvar-db-term->bvar-extension-p med old))
                    (bvar-db-term->bvar-extension-p new old))
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))

  (defthm bvar-db-extension-p-transitive
    (implies (and (bind-bvar-db-extension new med)
                  (bvar-db-extension-p med old))
             (bvar-db-extension-p new old)))

  (defthm bvar-db-extension-p-of-add-term-bvar
    (implies (not (get-term->bvar$c x bvar-db))
             (bvar-db-extension-p (add-term-bvar$c x bvar-db) bvar-db))
    :hints(("Goal" :in-theory (enable bvar-db-bvar->term-extension-p
                                      bvar-db-term->bvar-extension-p))
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable add-term-bvar$c)))
           ;; (and stable-under-simplificationp
           ;;      '(:in-theory (enable add-term-bvar$c
           ;;                           bvar-terms$ci-of-update-bvar-terms$ci-split
           ;;                           nfix)))
           )))



(define add-term-bvar-unique ((x fgl-object-p) bvar-db)
  (let ((look (get-term->bvar x bvar-db)))
    (if look
        (mv look bvar-db)
      (b* ((next (next-bvar bvar-db))
           (bvar-db (add-term-bvar x bvar-db)))
        (mv next bvar-db))))
  ///

  (defthm bvar-db-extension-p-of-add-term-bvar-unique
    (bvar-db-extension-p (mv-nth 1 (add-term-bvar-unique x bvar-db)) bvar-db))

  (defthm natp-bvar-of-add-term-bvar-unique
    (natp (mv-nth 0 (add-term-bvar-unique x bvar-db)))
    :rule-classes :type-prescription)

  (defthm add-term-bvar-unique-bvar-upper-bound
    (b* (((mv bvar new-bvar-db) (add-term-bvar-unique x bvar-db)))
      (< bvar (next-bvar1$c new-bvar-db)))
    :rule-classes (:rewrite :linear))

  (defthm add-term-bvar-unique-bvar-lower-bound
    (b* (((mv bvar ?new-bvar-db) (add-term-bvar-unique x bvar-db)))
      (<= (base-bvar$c bvar-db) bvar))
    :rule-classes (:rewrite :linear))

  (defthm get-bvar->term-of-add-term-bvar-unique
    (b* (((mv bvar new-bvar-db) (add-term-bvar-unique x bvar-db)))
      (equal (get-bvar->term$c v new-bvar-db)
             (if (equal (nfix v) (nfix bvar))
                 (fgl-object-fix x)
               (get-bvar->term$c v bvar-db))))
    :hints(("Goal" :in-theory (e/d ()
                                   (GET-BVAR->TERM$C-INVERSE-OF-GET-TERM->BVAR$C))
            :use ((:instance GET-BVAR->TERM$C-INVERSE-OF-GET-TERM->BVAR$C
                   (bvar-db$c bvar-db) (obj x)))))))

(define bvar-list-cleanup ((x nat-listp) bvar-db)
  :returns (new-x nat-listp)
  (if (atom x)
      nil
    (if (and (<= (base-bvar bvar-db) (lnfix (car x)))
             (< (lnfix (car x)) (next-bvar bvar-db)))
        (cons (lnfix (car x)) (bvar-list-cleanup (cdr x) bvar-db))
      (bvar-list-cleanup (cdr x) bvar-db)))
  ///
  (defthm bvar-list-okp-of-<fn>
    (bvar-list-okp$c (bvar-list-cleanup x bvar-db) bvar-db)
    :hints(("Goal" :in-theory (enable bvar-list-okp$c
                                      next-bvar$c))))

  (defthm bvar-list-cleanup-when-bvar-list-okp$c
    (implies (bvar-list-okp$c x bvar-db)
             (equal (bvar-list-cleanup x bvar-db)
                    (acl2::nat-list-fix x)))
    :hints(("Goal" :in-theory (enable bvar-list-okp$c))))

  (def-updater-independence-thm bvar-list-cleanup-updater-independence
    (implies (and (equal (base-bvar$c new) (base-bvar$c old))
                  (equal (next-bvar1$c new) (next-bvar1$c old)))
             (equal (bvar-list-cleanup x new)
                    (bvar-list-cleanup x old))))

  (local (in-theory (enable acl2::nat-list-fix))))



(define get-term->equivs ((x fgl-object-p) bvar-db)
  :guard-hints ((and stable-under-simplificationp
                     '(:in-theory (enable bvar-db-wfp$c))))
  :returns (equivs nat-listp :rule-classes (:rewrite (:type-prescription :typed-term equivs)))
  (mbe :logic (bvar-list-cleanup (cdr (hons-get (fgl-object-fix x) (term-equivs bvar-db))) bvar-db)
       :exec (cdr (hons-get (fgl-object-fix x) (term-equivs bvar-db))))
  ///
  (local (in-theory (enable get-term->equivs)))

  (defthm bvar-list-okp-get-term->equivs
    (bvar-list-okp$c (get-term->equivs x bvar-db) bvar-db)
    :hints(("Goal" :in-theory (enable get-term->equivs)))))



(define add-term-equiv ((x fgl-object-p)
                        (n natp)
                        bvar-db)
  :guard (and (<= (base-bvar bvar-db) n)
              (< n (next-bvar bvar-db)))
  :guard-hints (("goal" :in-theory (enable term-equivs-okp$c
                                           bvar-list-okp$c)))
  (if (mbt (and (<= (base-bvar bvar-db) (lnfix n))
                (< (lnfix n) (next-bvar bvar-db))))
      (let ((equivs (term-equivs bvar-db)))
        (update-term-equivs (hons-acons (fgl-object-fix x)
                                        (cons (lnfix n) (cdr (hons-get (fgl-object-fix x) equivs)))
                                        equivs)
                            bvar-db))
    bvar-db)
  ///
  (defthm add-term-equiv-preserves
    (implies (not (equal (bvar-db$c-field-fix key) :term-equivs))
             (equal (bvar-db$c-get key (add-term-equiv x n bvar-db))
                    (bvar-db$c-get key bvar-db))))

  (defthm get-term->equivs-of-add-term-equiv
    (equal (get-term->equivs y (add-term-equiv x n bvar-db))
           (if (and (fgl-object-equiv x y)
                    (<= (base-bvar bvar-db) (nfix n))
                    (< (nfix n) (next-bvar bvar-db)))
               (cons (nfix n) (get-term->equivs y bvar-db))
             (get-term->equivs y bvar-db)))
    :hints(("Goal" :in-theory (enable get-term->equivs
                                      bvar-list-cleanup)))))



(define bvar-db-debug-aux ((n natp) bvar-db)
  (declare (xargs :stobjs bvar-db
                  :guard (and (<= (base-bvar bvar-db) n)
                              (<= n (next-bvar bvar-db)))
                  :measure (nfix (- (next-bvar bvar-db) (nfix n)))))
  (if (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
           :exec (eql (next-bvar bvar-db) n))
      nil
    (cons (cons (lnfix n) (summarize-fgl-object (get-bvar->term n bvar-db)))
          (bvar-db-debug-aux (1+ (lnfix n)) bvar-db))))

(defun bvar-db-debug (bvar-db)
  (declare (xargs :stobjs bvar-db))
  (bvar-db-debug-aux (base-bvar bvar-db) bvar-db))


(acl2::set-prev-stobjs-correspondence add-term-bvar$c
                                      :stobjs-out (bvar-db)
                                      :formals (x bvar-db))

(acl2::set-prev-stobjs-correspondence update-term-equivs$c
                                      :stobjs-out (bvar-db)
                                      :formals (x bvar-db))
