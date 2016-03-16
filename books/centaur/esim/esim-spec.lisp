; ESIM Symbolic Hardware Simulator
; Copyright (C) 2008-2015 Centaur Technology
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


; esim-spec.lisp -- simple semantics of esim
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "patterns")
(include-book "esim-sexpr-support")
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "centaur/4v-sexpr/4v-logic" :dir :system)
(include-book "centaur/4v-sexpr/sexpr-equivs" :dir :system)
(local (include-book "esim-sexpr-support-thms"))
(local (include-book "centaur/4v-sexpr/sexpr-advanced" :dir :system))
(local (in-theory (disable* set::double-containment
                            set::sets-are-true-lists)))

(set-well-founded-relation nat-list-<)

(defun 4v-x-res (i alist)
  (declare (xargs :guard t))
  (if (atom i)
      *4vz*
    (4v-res
     (4v-lookup (car i) alist)
     (4v-x-res (cdr i) alist))))

(defun 4v-pat-alist-translate (old-pat new-pat alist acc)
  (declare (Xargs :guard (data-for-patternp old-pat new-pat)))
  (if old-pat
      (if (atom old-pat)
          (hons-acons new-pat (4v-lookup old-pat alist) acc)
        (4v-pat-alist-translate
         (car old-pat) (car new-pat) alist
         (4v-pat-alist-translate
          (cdr old-pat) (cdr new-pat) alist acc)))
    acc))

(defun eapply-spec (al x)
  (declare (xargs :guard t))
  (b* ((nst (gpl :nst x))
       (out (gpl :out x))
       (int (gpl :int x))
       ((with-fast al)))
    (mv (4v-sexpr-eval-alist nst al)
        (4v-sexpr-eval-alist out al)
        (4v-sexpr-eval-alist int al))))

(defun eapply-spec-out (al x)
  (declare (xargs :guard t))
  (mv-let (nst out int)
    (eapply-spec al x)
    (declare (ignore nst int))
    out))

(defun eapply-spec-nst (al x)
  (declare (xargs :guard t))
  (mv-let (nst out int)
    (eapply-spec al x)
    (declare (ignore out int))
    nst))

(defun eapply-spec-int (al x)
  (declare (xargs :guard t))
  (mv-let (nst out int)
    (eapply-spec al x)
    (declare (ignore nst out))
    int))




(defun esim-alist-lattice-height-measure (keys al)
  (declare (xargs :guard t))
  (if (atom keys)
      0
    (+ (if (eq (4v-lookup (car keys) al) *4vx*) 1 0)
       (esim-alist-lattice-height-measure (cdr keys) al))))

(defcong 4v-env-equiv equal (esim-alist-lattice-height-measure keys al) 2
  :hints (("goal" :induct (len keys)
           :in-theory (disable 4v-fix)
           :do-not-induct t)
          (witness :ruleset 4v-env-equiv-hons-assoc-equal-ex)))

(defun 4v-alist-<=-keys (keys al1 al2)
  (declare (xargs :guard t))
  (if (atom keys)
      t
    (and (4v-<= (4v-lookup (car keys) al1)
                (4v-lookup (car keys) al2))
         (4v-alist-<=-keys (cdr keys) al1 al2))))

(defthm esim-alist-lattice-height-measure-nonincreasing
  (implies (4v-alist-<= al1 al2)
           (<= (esim-alist-lattice-height-measure keys al2)
               (esim-alist-lattice-height-measure keys al1)))
  :hints (("goal" :in-theory (disable 4v-fix)
           :induct (len keys)
           :do-not-induct t)
         (witness :ruleset 4v-alist-<=-hons-assoc-equal-example))
  :rule-classes :linear)

(defthm esim-alist-lattice-height-measure-decreasing
  (implies (and (4v-alist-<= al1 al2)
                (not (4v-alist-<=-keys keys al2 al1)))
           (< (esim-alist-lattice-height-measure keys al2)
              (esim-alist-lattice-height-measure keys al1)))
  :hints(("Goal" :in-theory (disable 4v-fix)
          :induct (len keys)
          :do-not-induct t)
         (witness :ruleset 4v-alist-<=-hons-assoc-equal-example))
  :rule-classes :linear)

(defthm esim-alist-lattice-height-measure->=-0
  (<= 0 (esim-alist-lattice-height-measure keys al))
  :rule-classes :linear)


(mutual-recursion
 (defun esim-out (mod ia sa)
   (declare (xargs :measure (list (acl2-count mod) 10 0)
                   :guard (good-esim-modulep mod)
                   :verify-guards nil))
   (b* ((ia (4v-alist-extract (pat-flatten1 (gpl :i mod)) ia))
        (sa (4v-alist-extract (pat-flatten1 (mod-state mod)) sa))
        ((when (gpl :x mod))
         (eapply-spec-out (append ia sa)
                          ;;  (gpl :i mod) (gpl :s mod)
                          ;; (gpl :o mod)
                          (gpl :x mod)))
        (fixpoint (esim-fixpoint mod ia sa)))
     (4v-alist-extract (pat-flatten1 (gpl :o mod)) fixpoint)))

 (defun esim-fixpoint (mod sig-al st-al)
   (declare (xargs :measure (list (acl2-count mod)
                                  9
                                  (esim-alist-lattice-height-measure
                                   (esim-driven-signals mod)
                                   sig-al))
                   :guard (esim-fixpoint-guard mod sig-al st-al)))
   (b* ((occnames (alist-keys (make-fast-alist (occmap mod))))
        (sig-al1 (esim-occs mod occnames sig-al st-al))
        (sig-al (make-fast-alist sig-al))
        (fixed (4v-alist-<=-keys (esim-driven-signals mod) sig-al1 sig-al))
        ((unless (and (not fixed)
                      (mbt (4v-alist-<= sig-al sig-al1))))
         (fast-alist-free sig-al1)
         sig-al))
     (fast-alist-free sig-al)
     (esim-fixpoint mod sig-al1 st-al)))

 (defun esim-occs (mod occs sig-al st-al)
   (declare (xargs :measure
                   (list (acl2-count mod) 7 (len occs))
                   :guard (esim-mod-occs-guard mod occs)))
   (if (or (atom occs)
           (not (mbt (consp (gpl :occs mod)))))
       sig-al
     (b* ((sig-al (esim-occ (esim-get-occ (car occs) mod) sig-al st-al)))
       (esim-occs mod (cdr occs) sig-al st-al))))

 (defun esim-occ (occ sig-al st-al)
   (declare (xargs :measure (list (acl2-count occ) 11 0)
                   :guard (good-esim-occp occ)))
   (b* ((o  (gpl :o occ))
        (i  (gpl :i occ))
        (op (gpl :op occ))
        (iop (gpl :i op))
        (oop (gpl :o op))
        (inal (4v-pat-alist-translate i iop sig-al nil))
        (stal (4v-pat-alist-translate (occ-state occ) (mod-state op) st-al nil))
        (oa (esim-out op inal stal)))
     (4v-pat-alist-translate oop o oa sig-al)))

 (defun esim-fixpoint-guard (mod sig-al st-al)
   (declare (xargs :measure (list (acl2-count mod) 8 0)
                   :guard t))
   (and (good-esim-modulep mod)
        ; (gpl :occs mod)
        (subsetp-equal
         (alist-keys sig-al)
         (append (pat-flatten1 (gpl :i mod))
                 (esim-driven-signals mod)))
        (4v-alist-<=
         sig-al
         (esim-occs mod (alist-keys (occmap mod))
                    sig-al st-al)))))

(mutual-recursion
 (defun esim-nst (mod ia sa)
   (declare (xargs :measure (list (acl2-count mod) 10 0)
                   :guard (good-esim-modulep mod)
                   :verify-guards nil))
   (b* ((ia (4v-alist-extract (pat-flatten1 (gpl :i mod)) ia))
        (sa (4v-alist-extract (pat-flatten1 (mod-state mod)) sa))
        ((when (gpl :x mod))
         (eapply-spec-nst (append ia sa)
                          ;;  (gpl :i mod) (gpl :s mod)
                          ;; (gpl :o mod)
                          (gpl :x mod)))
        (fixpoint (esim-fixpoint mod ia sa)))
     (esim-occs-nst mod (alist-keys (make-fast-alist (occmap mod)))
                    fixpoint sa)))

 (defun esim-occs-nst (mod occs fixpoint st-al)
   (declare (xargs :measure
                   (list (acl2-count mod) 8 (len occs))
                   :guard (esim-mod-occs-guard mod occs)))
   (if (or (atom occs)
           (not (mbt (consp (gpl :occs mod)))))
       nil
     (b* ((nst-al1 (esim-occ-nst (esim-get-occ (car occs) mod)
                                 fixpoint st-al))
          (nst-al2 (esim-occs-nst mod (cdr occs) fixpoint st-al)))
       (append nst-al1 nst-al2))))

 (defun esim-occ-nst (occ fixpoint st-al)
   (declare (xargs :measure (list (acl2-count occ) 11 0)
                   :guard (good-esim-occp occ)))
   (b* ((i (gpl :i occ))
        (op (gpl :op occ))
        (iop (gpl :i op))
        (s (occ-state occ))
        (sop (mod-state op))
        (inal (4v-pat-alist-translate i iop fixpoint nil))
        (stal (4v-pat-alist-translate s sop st-al nil))
        (sa (esim-nst op inal stal)))
     (4v-pat-alist-translate sop s sa nil))))


(mutual-recursion
 (defun esim-int (mod ia sa)
   (declare (xargs :measure (list (acl2-count mod) 10 0)
                   :guard (good-esim-modulep mod)
                   :verify-guards nil))
   (b* ((ia (4v-alist-extract (pat-flatten1 (gpl :i mod)) ia))
        (sa (4v-alist-extract (pat-flatten1 (mod-state mod)) sa))
        ((when (gpl :x mod))
         (eapply-spec-int (append ia sa)
                          ;;  (gpl :i mod) (gpl :s mod)
                          ;; (gpl :o mod)
                          (gpl :x mod)))
        (fixpoint (esim-fixpoint mod ia sa)))
     (append fixpoint
             (esim-occs-int mod (alist-keys (make-fast-alist (occmap mod)))
                              fixpoint sa))))

 (defun esim-occs-int (mod occs fixpoint st-al)
   (declare (xargs :measure
                   (list (acl2-count mod) 8 (len occs))
                   :guard (esim-mod-occs-guard mod occs)))
   (if (or (atom occs)
           (not (mbt (consp (gpl :occs mod)))))
       nil
     (b* ((int-al1 (esim-occ-int (esim-get-occ (car occs) mod)
                                  fixpoint st-al))
          (int-al2 (esim-occs-int mod (cdr occs) fixpoint st-al)))
       (append int-al1 int-al2))))

 (defun esim-occ-int (occ fixpoint st-al)
   (declare (xargs :measure (list (acl2-count occ) 11 0)
                   :guard (good-esim-occp occ)))
   (b* ((i (gpl :i occ))
        (op (gpl :op occ))
        (iop (gpl :i op))
        (s (occ-state occ))
        (sop (mod-state op))
        (int (occ-internals occ))
        (intop (mod-internals op))
        (inal (4v-pat-alist-translate i iop fixpoint nil))
        (stal (4v-pat-alist-translate s sop st-al nil))
        (ia (esim-int op inal stal)))
     (4v-pat-alist-translate intop int ia nil))))








;; (mutual-recursion
;;  (defun esim-int (mod ia sa)
;;    (declare (xargs :measure (list (acl2-count mod) 10 0)
;;                    :guard (good-esim-modulep mod)
;;                    :verify-guards nil))
;;    (let ((occs (gpl :occs mod))
;;          (ia (4v-alist-extract (pat-flatten (gpl :i mod) nil) ia))
;;          (sa (4v-alist-extract (pat-flatten (mod-state mod) nil) sa)))
;;      (if occs
;;          (mv-let (nst fixpoint internal)
;;            (esim-fixpoint-int mod ia sa)
;;            (mv nst (append fixpoint internal)))
;;        (mv-let (nst out)
;;          (eapply-spec ia sa
;;                       (gpl :i mod)
;;                       (gpl :s mod)
;;                       (gpl :o mod)
;;                       (gpl :x mod))
;;          (mv nst (append ia out))))))

;;  (defun esim-fixpoint-int (mod sig-al st-al)
;;    (declare (xargs :measure (list (acl2-count mod)
;;                                   9
;;                                   (esim-alist-lattice-height-measure
;;                                    (esim-driven-signals mod)
;;                                    sig-al))
;;                    :guard (and (good-esim-modulep mod)
;;                                (gpl :occs mod)
;;                                (subsetp-equal
;;                                 (alist-keys sig-al)
;;                                 (append (pat-flatten (gpl :i mod) nil)
;;                                         (esim-driven-signals mod)))
;;                                (b* (((mv & sig-al1 &)
;;                                      (esim-occs-int mod (alist-keys (occmap mod))
;;                                                 sig-al st-al nil nil)))
;;                                  (4v-alist-<= sig-al sig-al1)))))
;;    (b* ((occnames (alist-keys (make-fast-alist (occmap mod))))
;;         ((mv nst-al sig-al1 internal-al)
;;          (esim-occs-int mod occnames sig-al st-al nil nil))
;;         (sig-al (make-fast-alist sig-al))
;;         (driven-signals (esim-driven-signals mod))
;;         (fixed (4v-alist-<=-keys driven-signals sig-al1 sig-al))
;;         ((unless (and (not fixed)
;;                       (mbt (4v-alist-<= sig-al sig-al1))))
;;          (b* ((all-signals (pat-flatten (gpl :i mod) driven-signals))
;;               (sig-al-final (4v-alist-extract all-signals sig-al1)))
;;            (fast-alist-free sig-al)
;;            (fast-alist-free sig-al1)
;;            (mv nst-al sig-al-final internal-al)))
;;      (fast-alist-free sig-al)
;;      (fast-alist-free nst-al)
;;      (fast-alist-free internal-al)
;;      (esim-fixpoint-int mod sig-al1 st-al)))

;;  (defun esim-occs-int (mod occs sig-al st-al nst-al internal-al)
;;    (declare (xargs :measure
;;                    (list (acl2-count mod) 8 (len occs))
;;                    :guard (esim-mod-occs-guard mod occs)))
;;    (if (or (atom occs)
;;            (not (mbt (and (gpl :occs mod) t))))
;;        (mv nst-al sig-al internal-al)
;;      (b* (((mv nst-al sig-al internal-al)
;;            (esim-occ-int (esim-get-occ (car occs) mod)
;;                      sig-al st-al nst-al internal-al)))
;;        (esim-occs-int mod (cdr occs) sig-al st-al nst-al internal-al))))

;;  (defun esim-occ-int (occ sig-al st-al nst-al internal-al)
;;    (declare (xargs :measure (list (acl2-count occ) 11 0)
;;                    :guard (good-esim-occp occ)))
;;    (b* ((o  (gpl :o occ))
;;         (i  (gpl :i occ))
;;         (op (gpl :op occ))
;;         (iop (gpl :i op))
;;         (oop (gpl :o op))
;;         (inal (4v-pat-alist-translate i iop sig-al nil))
;;         (stal (4v-pat-alist-translate (occ-state occ) (mod-state op) st-al nil))
;;         ((mv sa ia) (esim-int op inal stal))
;;         (sa (make-fast-alist sa))
;;         (ia (make-fast-alist ia))
;;         (sig-al (4v-pat-alist-translate oop o ia sig-al))
;;         (internal-al (4v-pat-alist-translate
;;                       (mod-internals op) (occ-internals occ) ia internal-al))
;;         (nst-al (4v-pat-alist-translate
;;                  (mod-state op) (occ-state occ) sa nst-al)))
;;      (fast-alist-free sa)
;;      (fast-alist-free ia)
;;      (mv nst-al sig-al internal-al))))




;; (mutual-recursion
;;  (defun esim (mod ia sa)
;;    (declare (xargs :measure (list (acl2-count mod) 10 0)
;;                    :guard (good-esim-modulep mod)
;;                    :verify-guards nil))
;;    (let ((occs (gpl :occs mod))
;;          (ia (4v-alist-extract (pat-flatten (gpl :i mod) nil) ia))
;;          (sa (4v-alist-extract (pat-flatten (mod-state mod) nil) sa)))
;;      (mv-let (nst fixpoint)
;;        (if occs
;;            (esim-fixpoint mod ia sa)
;;          (eapply-spec ia sa
;;                       (gpl :i mod)
;;                       (gpl :s mod)
;;                       (gpl :o mod)
;;                       (gpl :x mod)))
;;        (mv nst (4v-alist-extract (pat-flatten (gpl :o mod) nil) fixpoint)))))

;;  (defun esim-fixpoint (mod sig-al st-al)
;;    (declare (xargs :measure (list (acl2-count mod)
;;                                   9
;;                                   (esim-alist-lattice-height-measure
;;                                    (esim-driven-signals mod)
;;                                    sig-al))
;;                    :guard (and (good-esim-modulep mod)
;;                                (gpl :occs mod)
;;                                (subsetp-equal
;;                                 (alist-keys sig-al)
;;                                 (append (pat-flatten (gpl :i mod) nil)
;;                                         (esim-driven-signals mod)))
;;                                (b* (((mv & sig-al1)
;;                                      (esim-occs mod (alist-keys (occmap mod))
;;                                                 sig-al st-al nil)))
;;                                  (4v-alist-<= sig-al sig-al1)))))
;;    (b* ((occnames (alist-keys (make-fast-alist (occmap mod))))
;;         ((mv nst-al sig-al1)
;;          (esim-occs mod occnames sig-al st-al nil))
;;         (sig-al (make-fast-alist sig-al))
;;         (fixed (4v-alist-<=-keys (esim-driven-signals mod) sig-al1 sig-al))
;;         ((unless (and (not fixed)
;;                       (mbt (4v-alist-<= sig-al sig-al1))))
;;          (fast-alist-free sig-al)
;;          (mv nst-al sig-al1)))
;;      (fast-alist-free sig-al)
;;      (fast-alist-free nst-al)
;;      (esim-fixpoint mod sig-al1 st-al)))

;;  (defun esim-occs (mod occs sig-al st-al nst-al)
;;    (declare (xargs :measure
;;                    (list (acl2-count mod) 8 (len occs))
;;                    :guard (esim-mod-occs-guard mod occs)))
;;    (if (or (atom occs)
;;            (not (mbt (and (gpl :occs mod) t))))
;;        (mv nst-al sig-al)
;;      (b* (((mv nst-al sig-al)
;;            (esim-occ (esim-get-occ (car occs) mod)
;;                      sig-al st-al nst-al)))
;;        (esim-occs mod (cdr occs) sig-al st-al nst-al))))

;;  (defun esim-occ (occ sig-al st-al nst-al)
;;    (declare (xargs :measure (list (acl2-count occ) 11 0)
;;                    :guard (good-esim-occp occ)))
;;    (b* ((o  (gpl :o occ))
;;         (i  (gpl :i occ))
;;         (op (gpl :op occ))
;;         (iop (gpl :i op))
;;         (oop (gpl :o op))
;;         (inal (4v-pat-alist-translate i iop sig-al nil))
;;         (stal (4v-pat-alist-translate (occ-state occ) (mod-state op) st-al nil))
;;         ((mv sa oa) (esim op inal stal))
;;         (sig-al (4v-pat-alist-translate oop o oa sig-al))
;;         (nst-al (4v-pat-alist-translate (mod-state op) (occ-state occ) sa nst-al)))
;;      (mv nst-al sig-al))))





;; (defthm esim-occ-int-irrel-for-sig-al
;;   (implies (syntaxp (not (and (equal nst-al ''nil)
;;                               (equal internal-al ''nil))))
;;            (equal (mv-nth 1 (esim-occ-int occ sig-al st-al nst-al internal-al))
;;                   (mv-nth 1 (esim-occ-int occ sig-al st-al nil    nil))))
;;   :hints (("goal" :expand ((esim-occ-int occ sig-al st-al nil nil))
;;            :in-theory (disable esim-int))))

;; (defthm esim-occ-int-irrel-for-nst-al
;;   (implies (syntaxp (not (equal internal-al ''nil)))
;;            (equal (mv-nth 0 (esim-occ-int occ sig-al st-al nst-al internal-al))
;;                   (mv-nth 0 (esim-occ-int occ sig-al st-al nst-al nil))))
;;   :hints (("goal" :expand ((esim-occ-int occ sig-al st-al nst-al nil))
;;            :in-theory (disable esim-int))))

;; (defthm esim-occ-int-irrel-for-internal-al
;;   (implies (syntaxp (not (equal nst-al ''nil)))
;;            (equal (mv-nth 2 (esim-occ-int occ sig-al st-al nst-al internal-al))
;;                   (mv-nth 2 (esim-occ-int occ sig-al st-al nil    internal-al))))
;;   :hints (("goal" :expand ((esim-occ-int occ sig-al st-al nil    internal-al))
;;            :in-theory (disable esim-int))))


;; (defun esim-occs-int-nst-irrel-ind (mod occs sig-al st-al nst-al internal-al)
;;   (if (or (atom occs)
;;           (not (mbt (and (gpl :occs mod) t))))
;;       (list nst-al sig-al)
;;     (b* (((mv nst-al1 sig-al1 internal-al1)
;;           (esim-occ-int (cdr (hons-get (car occs) (occmap mod)))
;;                     sig-al st-al nst-al internal-al))
;;          ((mv nst-al2 & internal-al2)
;;           (esim-occ-int (cdr (hons-get (car occs) (occmap mod)))
;;                     sig-al st-al nil nil))
;;          ((mv nst-al3 & internal-al3)
;;           (esim-occ-int (cdr (hons-get (car occs) (occmap mod)))
;;                     sig-al st-al nst-al nil))
;;          ((mv nst-al4 & internal-al4)
;;           (esim-occ-int (cdr (hons-get (car occs) (occmap mod)))
;;                     sig-al st-al nil internal-al)))
;;       (list (esim-occs-int-nst-irrel-ind mod (cdr occs)
;;                                      sig-al1 st-al nst-al1 internal-al1)
;;             (esim-occs-int-nst-irrel-ind mod (cdr occs)
;;                                      sig-al1 st-al nst-al2 internal-al2)
;;             (esim-occs-int-nst-irrel-ind mod (cdr occs)
;;                                      sig-al1 st-al nst-al3 internal-al3)
;;             (esim-occs-int-nst-irrel-ind mod (cdr occs)
;;                                      sig-al1 st-al nst-al4 internal-al4)))))

;; (defthm esim-occs-int-irrelevant-for-sig-al
;;   (implies (syntaxp (not (and (equal nst-al ''nil)
;;                               (equal internal-al ''nil))))
;;            (equal (mv-nth 1 (esim-occs-int mod occs sig-al st-al nst-al internal-al))
;;                   (mv-nth 1 (esim-occs-int mod occs sig-al st-al nil    nil))))
;;   :hints (("goal" :induct (esim-occs-int-nst-irrel-ind mod occs sig-al st-al nst-al
;;                                                    internal-al)
;;            :in-theory (disable esim-occ-int))))

;; (defthm esim-occs-int-irrelevant-for-nst-al
;;   (implies (syntaxp (not (equal internal-al ''nil)))
;;            (equal (mv-nth 0 (esim-occs-int mod occs sig-al st-al nst-al internal-al))
;;                   (mv-nth 0 (esim-occs-int mod occs sig-al st-al nst-al nil))))
;;   :hints (("goal" :induct (esim-occs-int-nst-irrel-ind mod occs sig-al st-al nst-al
;;                                                    internal-al)
;;            :in-theory (disable esim-occ-int))))

;; (defthm esim-occs-int-irrelevant-for-internal-al
;;   (implies (syntaxp (not (equal nst-al ''nil)))
;;            (equal (mv-nth 2 (esim-occs-int mod occs sig-al st-al nst-al internal-al))
;;                   (mv-nth 2 (esim-occs-int mod occs sig-al st-al nil    internal-al))))
;;   :hints (("goal" :induct (esim-occs-int-nst-irrel-ind mod occs sig-al st-al nst-al
;;                                                    internal-al)
;;            :in-theory (disable esim-occ-int))))




(defthm alist-keys-4v-pat-alist-translate
  (implies (similar-patternsp (double-rewrite pat2) (double-rewrite pat1))
           (equal (alist-keys (4v-pat-alist-translate pat1 pat2 al acc))
                  (append (pat-flatten1 pat2)
                          (alist-keys acc)))))

(local (in-theory (disable occmap)))


(defthm alist-keys-esim-occ
  (implies (good-esim-occp occ)
           (equal (alist-keys (esim-occ occ sig-al st-al))
                  (append (pat-flatten1 (gpl :o occ))
                          (alist-keys sig-al))))
  :hints (("goal" :expand ((esim-occ occ sig-al st-al))
           :in-theory (disable esim-out))))

(defthm hons-assoc-equal-4v-pat-alist-translate
  (implies (similar-patternsp (double-rewrite pat1) (double-rewrite pat2))
           (iff (hons-assoc-equal k (4v-pat-alist-translate pat1 pat2 al acc))
                (or (member-equal k (pat-flatten1 pat2))
                    (hons-assoc-equal k acc)))))

(defthm hons-assoc-equal-4v-pat-alist-translate-when-not-bound
  (implies (and (similar-patternsp (double-rewrite pat1) (double-rewrite pat2))
                (not (member-equal k (pat-flatten1 pat2))))
           (equal (hons-assoc-equal k (4v-pat-alist-translate pat1 pat2 al acc))
                  (hons-assoc-equal k acc))))

(defthm hons-assoc-equal-sig-al-of-esim-occ
  (implies (good-esim-occp occ)
           (iff (hons-assoc-equal k (esim-occ occ sig-al st-al))
                (or (member-equal k (pat-flatten1 (gpl :o occ)))
                    (hons-assoc-equal k sig-al))))
  :hints (("goal" :expand ((esim-occ occ sig-al st-al))
           :in-theory (disable esim-out))))






(defthm esim-occ-nil
  (equal (esim-occ nil sig-al st-al)
         sig-al)
  :hints(("Goal" :in-theory (disable esim-out))))



(defun esim-occs-ind (mod occs sig-al st-al)
  (declare (xargs :measure (len occs)))
  (if (or (atom occs)
          (not (mbt (consp (gpl :occs mod)))))
      sig-al
    (b* ((sig-al
          (esim-occ (esim-get-occ (car occs) mod)
                    sig-al st-al)))
      (esim-occs-ind mod (cdr occs) sig-al st-al))))

(defthm member-pat-flatten-gpl-of-lookup1
  (implies (not (member-equal k (collect-signal-list key occs)))
           (not (member-equal k (pat-flatten1 (gpl key (cdr (hons-assoc-equal
                                                             key2 (occmap1 occs))))))))
  :hints(("Goal" :in-theory (enable occmap)
          :induct (len occs))
         (and stable-under-simplificationp
              '(:in-theory (enable gpl)))))

(defthm member-pat-flatten-gpl-of-lookup
  (implies (and (not (member-equal k (collect-signal-list
                                      key (alist-vals (fal-extract names
                                                                   occmap)))))
                (member-equal key2 names))
           (not (member-equal k (pat-flatten1 (gpl key (cdr (hons-assoc-equal
                                                             key2 occmap)))))))
  :hints(("Goal" :in-theory (enable alist-keys gpl fal-extract))))


;; (defthm member-pat-flatten-gpl-of-lookup2
;;   (implies (not (member-equal k (collect-signal-list
;;                                  key (alist-vals (fal-extract names occmap)))))
;;            (not (member-equal k (pat-flatten (gpl key (cdr (hons-assoc-equal
;;                                                             key2 occmap)))
;;                                              nil))))
;;   :hints(("Goal" :in-theory (enable occmap))))



(defthmd fal-extract-from-empty-al
  (implies (not (consp y))
           (equal (fal-extract x y) nil))
  :hints(("Goal" :in-theory (enable fal-extract))))

(defthm alist-keys-esim-occs
  (implies (good-esim-modulep mod)
           (equal (alist-keys (esim-occs mod occs sig-al st-al))
                  (append (collect-signal-list
                           :o (rev (alist-vals
                                    (fal-extract occs (occmap mod)))))
                          (alist-keys sig-al))))
  :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al)
           :in-theory (e/d (fal-extract fal-extract-from-empty-al
                                        occmap-when-no-occs)
                           (esim-occ good-esim-modulep)))
          (and stable-under-simplificationp
               '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))))

;; (defthm hons-assoc-equal-esim-occs
;;   (implies (good-esim-modulep mod)
;;            (iff (hons-assoc-equal k (esim-occs mod occs sig-al st-al))
;;                 (or (member-equal k (collect-signal-list
;;                                      :o (alist-vals
;;                                          (fal-extract occs (occmap mod)))))
;;                     (hons-assoc-equal k sig-al)))))

(defthm not-hons-assoc-equal-esim-occs
  (implies (and (good-esim-modulep mod)
                (not (hons-assoc-equal k sig-al))
                (not (member-equal k (esim-driven-signals mod))))
           (not (hons-assoc-equal k (esim-occs mod occs sig-al st-al))))
  :hints (("goal"
           :in-theory (e/d (subsetp-equal) (esim-occ good-esim-modulep))
           :induct (esim-occs-ind mod occs sig-al st-al))
          (and stable-under-simplificationp
               '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))))

(defthm alist-keys-esim-occs-subset
  (implies (and (good-esim-modulep mod)
                (subsetp-equal (alist-keys sig-al)
                               (append (pat-flatten1 (gpl :i mod))
                                       (esim-driven-signals mod))))
           (subsetp-equal (alist-keys (esim-occs mod occs sig-al st-al))
                          (append (pat-flatten1 (gpl :i mod))
                                  (esim-driven-signals mod))))
  :hints (("goal" :do-not-induct t
           :in-theory (disable good-esim-modulep alist-keys-esim-occs))
          (set-reasoning)))


;; (defthm alist-keys-esim-occs-equal
;;   (implies (good-esim-modulep mod)
;;            (equal (alist-keys (mv-nth 1 (esim-occs mod occs sig-al st-al
;;                                                          nst-al internal-al)))
;;                   (append (collect-signal-list
;;                            :o (reverse (alist-vals (fal-extract occs (occmap mod)))))
;;                           (alist-keys sig-al))))
;;   :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al nst-al
;;                                                internal-al)
;;            :expand ((:free (nst-al internal-al)
;;                            (esim-occs mod occs sig-al st-al nst-al
;;                                             internal-al))
;;                     (fal-extract occs (occmap mod)))
;;            :in-theory (e/d () (esim-occ good-esim-modulep)))
;;           (and stable-under-simplificationp
;;                '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))
;;           (and stable-under-simplificationp
;;                '(:expand ((occmap mod))))))



(defthm esim-occ-non-output-unchanged
  (implies (and (good-esim-occp occ)
                (not (member-equal i (pat-flatten1 (gpl :o occ)))))
           (equal (hons-assoc-equal i (esim-occ occ sig-al st-al))
                  (hons-assoc-equal i sig-al)))
  :hints (("goal" :in-theory (disable esim-out)
           :expand ((esim-occ occ sig-al st-al)))))

(defthm esim-occ-non-output-unchanged-lookup
  (implies (and (good-esim-occp occ)
                (not (member-equal i (pat-flatten1 (gpl :o occ)))))
           (equal (4v-lookup i (esim-occ occ sig-al st-al))
                  (4v-lookup i sig-al)))
  :hints (("goal" :in-theory (disable esim-out))))


(defthm esim-occs-non-output-unchanged
  (implies (and (good-esim-modulep mod)
                (not (member-equal i (collect-signal-list
                                      :o (alist-vals
                                          (fal-extract occs
                                                       (occmap mod)))))))
           (equal (hons-assoc-equal i (esim-occs mod occs sig-al st-al))
                  (hons-assoc-equal i sig-al)))
  :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al)
           :in-theory (e/d (subsetp-equal fal-extract)
                           (good-esim-modulep
                            esim-occ
                            prefix-pattern stringify))
           :do-not-induct t))
  :otf-flg t)


(defthm member-remove-duplicates-equal
  (iff (member-equal x (remove-duplicates-equal y))
       (member-equal x y)))

(defthm remove-duplicates-equal-set-equiv
  (set-equiv (remove-duplicates-equal x)
             (double-rewrite x))
  :hints ((set-reasoning)))

(defthm esim-occs-input-unchanged
  (implies (and (good-esim-modulep mod)
                (member-equal i (pat-flatten1 (gpl :i mod))))
           (equal (hons-assoc-equal i (esim-occs mod (alist-keys
                                                      (occmap mod))
                                                 sig-al st-al))
                  (hons-assoc-equal i sig-al)))
  :hints (("goal" :do-not-induct t
           :use ((:instance esim-occs-non-output-unchanged
                            (occs (alist-keys (occmap mod)))))
           :in-theory (e/d (subsetp-equal)
                           (esim-occ
                            esim-occ-non-output-unchanged
                            esim-occs-non-output-unchanged
                            prefix-pattern stringify))
           :expand ((good-esim-modulep mod)))
          (set-reasoning))
  :otf-flg t)



(defthm esim-occs-input-alist-<=
  (implies (and (good-esim-modulep mod)
                (subsetp-equal (alist-keys sig-al)
                               (pat-flatten1 (gpl :i mod))))
           (4v-alist-<= sig-al
                        (esim-occs mod (alist-keys (occmap mod))
                                   sig-al st-al)))
  :hints (("goal" :do-not-induct t
           :in-theory (disable esim-occs 4v-fix good-esim-modulep))
          (witness :ruleset 4v-alist-<=-witnessing)
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal
                                  4v-fix esim-occs
                                  good-esim-modulep))))
          (witness :ruleset set-reasoning-no-consp)
          (and stable-under-simplificationp
               '(:in-theory (e/d (alist-keys-member-hons-assoc-equal)
                                 (hons-assoc-equal-iff-member-alist-keys
                                  4v-fix esim-occs good-esim-modulep))))))


(defthm 4v-x-res-monotonic
  (implies (4v-alist-<= in1 in2)
           (4v-<= (4v-x-res i in1) (4v-x-res i in2)))
  :hints (("goal" :in-theory (disable* (:ruleset 4v-op-defs)
                                       4v-<=))
          (witness :ruleset 4v-alist-<=-hons-assoc-equal-example)))

(defexample 4v-alist-<=-lookup-ex
  :pattern (4v-lookup k al)
  :templates (k)
  :instance-rulename 4v-alist-<=-instancing)

(defthm 4v-lookup-cons
  (equal (4v-lookup k (cons a b))
         (if (and (consp a) (equal (car a) k))
             (4v-fix (cdr a))
           (4v-lookup k b))))

(defthm 4v-lookup-nil
  (equal (4v-lookup x nil) *4vx*))

(defthm 4v-pat-alist-translate-monotonic
  (implies (and (4v-alist-<= in1 in2)
                (4v-alist-<= acc1 acc2))
           (4v-alist-<= (4v-pat-alist-translate pat1 pat2 in1 acc1)
                        (4v-pat-alist-translate pat1 pat2 in2 acc2)))
  :hints (("goal" :induct t :do-not-induct t
           :in-theory (disable 4v-fix 4v-<= 4v-lookup))
          (witness :ruleset 4v-alist-<=-witnessing)
          (witness :ruleset (4v-alist-<=-lookup-ex))))

(defthm 4v-alist-<=-nil
  (4v-alist-<= nil x)
  :hints ((witness :ruleset 4v-alist-<=-witnessing)))

(defthm 4v-lookup-4v-alist-extract
  (equal (4v-lookup k (4v-alist-extract keys al))
         (if (member-equal k keys)
             (4v-lookup k al)
           *4vx*)))

(defthm 4v-alist-extract-mono
  (implies (4v-alist-<= a b)
           (4v-alist-<= (4v-alist-extract keys a)
                        (4v-alist-extract keys b)))
  :hints(("goal" :in-theory (disable 4v-lookup))
         (witness :ruleset (4v-alist-<=-witnessing
                            4v-alist-<=-lookup-ex))))


(defthm 4v-sexpr-eval-alist-monotonic
  (implies (4v-alist-<= al1 al2)
           (4v-alist-<= (4v-sexpr-eval-alist x al1)
                        (4v-sexpr-eval-alist x al2)))
  :hints (("goal" :induct t :in-theory (disable 4v-sexpr-eval 4v-fix 4v-<=))
          (witness :ruleset (4v-alist-<=-witnessing))))

(defthm eapply-spec-monotonic
  (implies (and (4v-alist-<= al1 al2))
           (b* (((mv nst1 out1) (eapply-spec al1 x))
                ((mv nst2 out2) (eapply-spec al2 x)))
             (and (4v-alist-<= nst1 nst2)
                  (4v-alist-<= out1 out2))))
  :hints (("goal" :in-theory (disable* (:ruleset 4v-op-defs)
                                       (:ruleset 4v-op-execs)
                                       4v-fix 4v-<=
                                       4v-lookup))))

(defthm alist-keys-pat-alist-translate-normalize
  (implies (syntaxp (not (equal al ''nil)))
           (equal (alist-keys (4v-pat-alist-translate a b al acc))
                  (alist-keys (4v-pat-alist-translate a b nil acc)))))

;; (defthm alist-keys-of-eapply-spec
;;   (equal (alist-keys (mv-nth 1 (eapply-spec al x)))
;;          (pat-flatten o nil))
;;   :hints (("goal" :in-theory
;;            '(alist-keys-4v-alist-extract
;;              eapply-spec make-fast-alist
;;              true-listp-pat-flatten
;;              append-right-id))))


(mutual-recursion
 (defun esim-mono (mod sig-al1 sig-al2 st-al1 st-al2)
   (declare (xargs :measure  (list (acl2-count mod) 10 0)
                   :hints (("goal" :in-theory
                            (disable
                             esim-alist-lattice-height-measure
                             good-esim-modulep
                             esim-out esim-fixpoint esim-occs
                             collect-signal-list
                             esim-occ)))))
   (let ((sig-al1 (4v-alist-extract (pat-flatten1 (gpl :i mod)) sig-al1))
         (st-al1 (4v-alist-extract (pat-flatten1 (mod-state mod)) st-al1))
         (sig-al2 (4v-alist-extract (pat-flatten1 (gpl :i mod)) sig-al2))
         (st-al2 (4v-alist-extract (pat-flatten1 (mod-state mod)) st-al2))
         (x (gpl :x mod)))
     (if x
         (list x sig-al1 sig-al2 st-al1 st-al2)
       (esim-fixpoint-mono mod sig-al1 sig-al2 st-al1 st-al2))))
 (defun esim-fixpoint-mono (mod sig-al1 sig-al2 st-al1 st-al2)
   (declare (xargs :measure (list (acl2-count mod)
                                  9
                                  (+ (esim-alist-lattice-height-measure
                                      (esim-driven-signals mod)
                                      sig-al1)
                                     (esim-alist-lattice-height-measure
                                      (esim-driven-signals mod)
                                      sig-al2)))))
   (b* ((occs (alist-keys (occmap mod)))
        ((list &)
         (esim-occs-mono mod occs sig-al1 sig-al2 st-al1 st-al2))
        (sig-al11
         (esim-occs mod occs sig-al1 st-al1))
        (sig-al21
         (esim-occs mod occs sig-al2 st-al2))
        ((list &)
         (esim-occs-mono mod occs sig-al1 sig-al11 st-al1 st-al1))
        ((list &)
         (esim-occs-mono mod occs sig-al2 sig-al21 st-al2 st-al2))
        ;; Note: Termination based on the first (lesser in the lattice) signal
        ;; alist.
        (- (flush-hons-get-hash-table-link sig-al11))
        (sig-al1 (make-fast-alist sig-al1))
        (fixed1 (4v-alist-<=-keys (esim-driven-signals mod)
                                  sig-al11 sig-al1))
        (fixed2 (4v-alist-<=-keys (esim-driven-signals mod)
                                  sig-al21 sig-al2))
        (wrong1 (not (4v-alist-<= sig-al1 sig-al11)))
        (wrong2 (not (4v-alist-<= sig-al2 sig-al21)))
        ((when (and (or fixed1 wrong1)
                    (or fixed2 wrong2)))
         (list sig-al21))
        ((when (or fixed1 wrong1))
         (esim-fixpoint-mono mod sig-al1 sig-al21 st-al1 st-al2))
        ((when (or fixed2 wrong2))
         (esim-fixpoint-mono mod sig-al11 sig-al2 st-al1 st-al2)))
     (esim-fixpoint-mono mod sig-al11 sig-al21 st-al1 st-al2)))

 (defun esim-occs-mono (mod occs sig-al1 sig-al2 st-al1 st-al2)
   (declare (xargs :measure
                   (list (acl2-count mod) 8 (len occs))))
   (if (or (atom occs)
           (not (consp (gpl :occs mod))))
       (list mod sig-al1 sig-al2)
     (b* ((occ (esim-get-occ (car occs) mod))
          (oa1 (esim-occ occ sig-al1 st-al1))
          (oa2 (esim-occ occ sig-al2 st-al2))
          ((list &) (esim-occ-mono occ sig-al1 sig-al2 st-al1
                                   st-al2)))
       (esim-occs-mono mod (cdr occs)
                       oa1 oa2
                       st-al1 st-al2))))

 (defun esim-occ-mono (occ sig-al1 sig-al2 st-al1 st-al2)
   (declare (xargs :measure (list (acl2-count occ) 11 0)))
   (b* ((op (gpl :op occ))
        (i  (gpl :i occ))
        (iop (gpl :i op))
        (inal1 (4v-pat-alist-translate i iop sig-al1 nil))
        (inal2 (4v-pat-alist-translate i iop sig-al2 nil))
        (stal1 (4v-pat-alist-translate (occ-state occ) (mod-state op)
                                       st-al1 nil))
        (stal2 (4v-pat-alist-translate (occ-state occ) (mod-state op)
                                       st-al2 nil)))
     (esim-mono op inal1 inal2 stal1 stal2))))



(flag::make-flag esim-mono-flag esim-mono
                 :hints (("goal" :in-theory
                            (disable
                             esim-alist-lattice-height-measure
                             good-esim-modulep
                             esim-out esim-fixpoint esim-occs
                             collect-signal-list
                             esim-occ))))


;; (defun find-flag-equal-hyp (flagname clause)
;;   (if (atom clause)
;;       nil
;;     (let ((lit (car clause)))
;;       (case-match lit
;;         (('not ('equal a b))
;;          (cond ((and (equal a flagname) (quotep b))
;;                 b)
;;                ((and (equal b flagname) (quotep a))
;;                 a)
;;                (t (find-flag-equal-hyp flagname (cdr clause)))))
;;         (t (find-flag-equal-hyp flagname (cdr clause)))))))



(defthm good-esim-occp-implies
  (implies (good-esim-occp occ)
           (and (good-esim-modulep (gpl :op occ))
                (similar-patternsp (gpl :i (gpl :op occ))
                                   (gpl :i occ))
                (similar-patternsp (gpl :o (gpl :op occ))
                                   (gpl :o occ)))))


(defthm 4v-alist-<=-refl
  (4v-alist-<= x x)
  :hints ((witness :ruleset 4v-alist-<=-witnessing)))


;; (defthm esim-occs-non-output-unchanged
;;   (implies (and (esim-mod-occs-guard mod occs)
;;                 (not (member-equal i (collect-signal-list
;;                                       :o (alist-vals
;;                                           (fal-extract occs
;;                                                        (occmap mod)))))))
;;            (equal (hons-assoc-equal i (mv-nth 1 (esim-occs mod occs sig-al
;;                                                            st-al nst-al)))
;;                   (hons-assoc-equal i sig-al)))
;;   :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al nst-al)
;;            :in-theory (e/d (subsetp-equal)
;;                            (good-esim-modulep
;;                             esim-occ
;;                             prefix-pattern stringify))
;;            :do-not-induct t))
;;   :otf-flg t)

(defthm 4v-<=-refl
  (4v-<= a a))

(defun key-for-not-4v-alist-<=-keys (keys al1 al2)
  (if (atom keys)
      nil
    (if (not (4v-<= (4v-lookup (car keys) al1)
                    (4v-lookup (car keys) al2)))
        (car keys)
      (key-for-not-4v-alist-<=-keys (cdr keys) al1 al2))))

(defthm witness-for-4v-alist-<=-keys
  (implies (not (4v-alist-<=-keys keys a b))
           (and (member-equal (key-for-not-4v-alist-<=-keys keys a b) keys)
                (not (4v-<= (4v-lookup (key-for-not-4v-alist-<=-keys keys a b) a)
                            (4v-lookup (key-for-not-4v-alist-<=-keys keys a b)
                                       b)))))
  :hints(("Goal" :in-theory (e/d () (4v-lookup 4v-<= 4v-fix)))))

(defwitness 4v-alist-<=-keys-witnessing
  :predicate (not (4v-alist-<=-keys keys a b))
  :expr (and (member-equal (key-for-not-4v-alist-<=-keys keys a b) keys)
                (not (4v-<= (4v-lookup (key-for-not-4v-alist-<=-keys keys a b) a)
                            (4v-lookup (key-for-not-4v-alist-<=-keys keys a b)
                                       b))))
  :generalize (((key-for-not-4v-alist-<=-keys keys a b) . key))
  :hints ('(:in-theory nil :use witness-for-4v-alist-<=-keys)))

(encapsulate nil

  (local (defthm esim-occs-non-output-unchanged-lookup
           (implies (and (good-esim-modulep mod)
                         (not (member-equal i (collect-signal-list
                                               :o (alist-vals
                                                   (fal-extract occs
                                                                (occmap mod)))))))
                    (equal (4v-lookup i (esim-occs mod occs sig-al st-al))
                           (4v-lookup i sig-al)))))

  (local (defthm 4v-alist-<=-keys-4v-lookup
           (implies (and (4v-alist-<=-keys keys a b)
                         (case-split (member-equal k keys)))
                    (4v-<= (4v-lookup k a)
                           (4v-lookup k b)))))

  (defthm 4v-alist-<=-keys-iff-4v-alist-<=
    (implies (good-esim-modulep mod)
             (iff (4v-alist-<=-keys (collect-signal-list
                                     :o (alist-vals
                                         (fal-extract occs
                                                      (occmap mod))))
                                    (esim-occs mod occs sig-al st-al)
                                    sig-al)
                  (4v-alist-<= (esim-occs mod occs sig-al st-al)
                               sig-al)))
    :hints (("goal" :do-not-induct t
             :in-theory (disable esim-mod-occs-guard 4v-fix 4v-<= 4v-lookup))
            (witness :ruleset (4v-alist-<=-witnessing
                               4v-alist-<=-keys-witnessing))
            (witness :ruleset 4v-alist-<=-4v-lookup-example))
    :otf-flg t))


(defthmd 4v-alist-<=-trans1
  (implies (and (4v-alist-<= a b)
                (4v-alist-<= b c))
           (4v-alist-<= a c))
  :hints (("goal" :do-not-induct t :in-theory (disable 4v-fix))
          (witness :ruleset 4v-alist-<=-witnessing)
          (witness :ruleset 4v-alist-<=-hons-assoc-equal-example)))

(defthmd 4v-alist-<=-trans2
  (implies (and (4v-alist-<= b c)
                (4v-alist-<= a b))
           (4v-alist-<= a c))
  :hints(("Goal" :in-theory (enable 4v-alist-<=-trans1))))


(defthm 4v-alist-<=-append1
  (implies (and (subsetp-equal (alist-keys b) (alist-keys a))
                (4v-alist-<= a b)
                (4v-alist-<= c d))
           (4v-alist-<= (append a c) (append b d)))
  :hints (("goal" :do-not-induct t :in-theory (disable 4v-fix))
          (witness :ruleset 4v-alist-<=-witnessing)
          (witness :ruleset 4v-alist-<=-hons-assoc-equal-example)
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal 4v-fix))))
          (set-reasoning)))


;; (defthm alist-keys-internals-of-esim-occ
;;   (equal (alist-keys (mv-nth 2 (esim-occ occ sig-al st-al nst-al internal-al)))
;;          (append (pat-flatten (occ-internals occ) nil)
;;                  (alist-keys internal-al)))
;;   :hints (("goal" :expand ((esim-occ occ sig-al st-al nil internal-al))
;;            :in-theory (disable esim))))

;; (defun collect-occ-internals (mod occs)
;;   (if (atom occs)
;;       nil
;;     (append (collect-occ-internals mod (cdr occs))
;;             (pat-flatten (occ-internals (esim-get-occ (car occs) mod)) nil))))

;; (defthmd occmap-when-no-occs
;;   (implies (not (gpl :occs mod))
;;            (equal (occmap mod) nil))
;;   :hints(("Goal" :in-theory (enable occmap))))

;; (defthm collect-occ-internals-when-no-occs
;;   (implies (not (gpl :occs mod))
;;            (equal (collect-occ-internals mod occs) nil))
;;   :hints(("Goal" :in-theory (enable occmap-when-no-occs))))

;; (defthm alist-keys-internals-of-esim-occs
;;   (equal (alist-keys (mv-nth 2 (esim-occs mod occs sig-al st-al nst-al
;;                                           internal-al)))
;;          (append (collect-occ-internals mod occs)
;;                  (alist-keys internal-al)))
;;   :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al nst-al
;;                                          internal-al)
;;            :expand ((esim-occs mod occs sig-al st-al nil internal-al))
;;            :in-theory (enable alist-keys))))


(defun esim-fixpoint-ind (mod sig-al st-al)
  (declare
   (xargs
    :measure (esim-alist-lattice-height-measure
              (esim-driven-signals mod)
              sig-al)))
  (b* ((occnames (alist-keys (make-fast-alist (occmap mod))))
       (sig-al1
        (esim-occs mod occnames sig-al st-al))
       (sig-al (make-fast-alist sig-al))
       (fixed (4v-alist-<=-keys (esim-driven-signals mod)
                                sig-al1 sig-al))
       ((unless (and (not fixed)
                     (mbt (4v-alist-<= sig-al sig-al1))))
        (fast-alist-free sig-al1)
        sig-al))
    (fast-alist-free sig-al)
    (esim-fixpoint-ind mod sig-al1 st-al)))

;; (defthm alist-keys-internals-of-esim-fixpoint
;;   (equal (alist-keys (mv-nth 2 (esim-fixpoint mod sig-al st-al)))
;;          (collect-occ-internals mod (alist-keys (occmap mod))))
;;   :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al)
;;            :in-theory (disable esim-occs good-esim-modulep))))



;; (defthm alist-keys-sigs-of-esim-fixpoint
;;   (implies (and (subsetp-equal (alist-keys sig-al)
;;                                (append (pat-flatten (gpl :i mod) nil)
;;                                        (esim-driven-signals mod)))
;;                 (subsetp-equal (pat-flatten (gpl :i mod) nil)
;;                                (alist-keys sig-al))
;;                 (good-esim-modulep mod))
;;            (set-equiv (alist-keys (mv-nth 1 (esim-fixpoint mod sig-al st-al)))
;;                        (append (pat-flatten (gpl :i mod) nil)
;;                                (esim-driven-signals mod))))
;;   :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al)
;;            :in-theory (disable esim-occs good-esim-modulep))))

(defthm true-listp-4v-pat-alist-translate
  (equal (true-listp (4v-pat-alist-translate pat1 pat2 al acc))
         (true-listp acc)))

;; (defthm true-listp-internals-esim-occ
;;   (equal (true-listp (mv-nth 2 (esim-occ occ sig-al st-al nst-al internal-al)))
;;          (true-listp internal-al))
;;   :hints (("goal" :in-theory (disable esim)
;;            :expand ((esim-occ occ sig-al st-al nil internal-al)))))

;; (defthm true-listp-internals-esim-occs
;;   (equal (true-listp (mv-nth 2 (esim-occs mod occs sig-al st-al nst-al internal-al)))
;;          (true-listp internal-al))
;;   :hints (("goal" :in-theory (disable esim-occ)
;;            :induct (esim-occs-ind mod occs sig-al st-al nst-al internal-al)
;;            :expand ((esim-occs mod occs sig-al st-al nil internal-al)))))

;; (defthm true-listp-internals-esim-fixpoint
;;   (equal (true-listp (mv-nth 2 (esim-fixpoint mod sig-al st-al))) t)
;;   :hints (("goal" :in-theory (disable esim-occs good-esim-modulep)
;;            :induct (esim-fixpoint-ind mod sig-al st-al))))


(defthm true-listp-esim-occ
  (equal (true-listp (esim-occ occ sig-al st-al))
         (true-listp sig-al))
  :hints(("Goal" :in-theory (disable esim-out)
          :expand ((esim-occ occ sig-al st-al)))))

(defthm true-listp-esim-occs
  (equal (true-listp (esim-occs mod occs sig-al st-al))
         (true-listp sig-al))
  :hints(("Goal" :in-theory (disable esim-occ)
          :expand ((:free (nst-al internal-al)
                          (esim-occs mod occs sig-al st-al)))
          :induct (esim-occs-ind mod occs sig-al st-al))))


(defthm true-listp-sigs-esim-fixpoint
  (equal (true-listp (esim-fixpoint mod sig-al st-al))
         (true-listp sig-al))
  :hints (("goal" :in-theory (disable esim-occs good-esim-modulep)
           :induct (esim-fixpoint-ind mod sig-al st-al))))


;; (defthm esim-fixpoint-sig-al-signals
;;   (implies (good-esim-modulep mod)
;;            (set-equiv (alist-keys (esim-fixpoint mod sig-al st-al))
;;                        (append (alist-keys sig-al)
;;                                (esim-driven-signals mod))))
;;   :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al)
;;            :in-theory (disable esim-occs))
;;           (witness :ruleset set-reasoning-no-consp)))



(encapsulate nil
  (local (in-theory (e/d* (4v-alist-<=-trans2)
                          (esim-out
                           esim-fixpoint esim-occs esim-occ
                           good-esim-modulep good-esim-occp eapply-spec
                           mod-state occ-state subsetp-when-atom-left
                           subsetp-trans
                           subsetp-implies-subsetp-cdr
                           subsetp-car-member member-equal
                           alist-keys-when-atom hons-assoc-equal
                           collect-signal-list 4v-pat-alist-translate
                           fal-extract append alist-vals-when-atom
                           4v-lookup default-car default-cdr
                           (:rules-of-class :type-prescription :here))
                          ((:type-prescription alist-keys)
                           (:type-prescription alist-vals)))))

  (defthm-esim-mono-flag
    (defthm esim-is-monotonic
      (implies (and (good-esim-modulep mod)
                    (4v-alist-<= sig-al1 sig-al2)
                    (4v-alist-<= st-al1 st-al2))
               (b* ((out-al1 (esim-out mod sig-al1 st-al1))
                    (out-al2 (esim-out mod sig-al2 st-al2)))
                 (4v-alist-<= out-al1 out-al2)))
      :hints ('(:expand ((esim-out mod sig-al1 st-al1)
                         (esim-out mod sig-al2 st-al2))))
      :flag esim-mono)

    (defthm esim-fixpoint-is-monotonic
      (implies (and (good-esim-modulep mod)
                    (4v-alist-<= sig-al1 sig-al2)
                    (4v-alist-<= st-al1 st-al2)
                    (b* ((sig-al11
                          (esim-occs mod (alist-keys (occmap mod))
                                     sig-al1 st-al1)))
                      (4v-alist-<= sig-al1 sig-al11))
                    (b* ((sig-al21
                          (esim-occs mod (alist-keys (occmap mod))
                                     sig-al2 st-al2)))
                      (4v-alist-<= sig-al2 sig-al21)))
               (b* ((sig-al1
                     (esim-fixpoint mod sig-al1 st-al1))
                    (sig-al2
                     (esim-fixpoint mod sig-al2 st-al2)))
                 (4v-alist-<= sig-al1 sig-al2)))
      :hints ('(:expand ((esim-fixpoint mod sig-al1 st-al1)
                         (esim-fixpoint mod sig-al2 st-al2))))
      :flag esim-fixpoint-mono)

    (defthm esim-occs-is-monotonic
      (implies (and (good-esim-modulep mod)
                    (4v-alist-<= sig-al1 sig-al2)
                    (4v-alist-<= st-al1 st-al2))
               (b* ((sig-al1
                     (esim-occs mod occs sig-al1 st-al1))
                    (sig-al2
                     (esim-occs mod occs sig-al2 st-al2)))
                 (4v-alist-<= sig-al1 sig-al2)))
      :hints ('(:expand ((esim-occs mod occs sig-al1 st-al1)
                         (esim-occs mod occs sig-al2 st-al2)
                         ;; (esim-occs mod nil sig-al1 st-al1 nst-al1)
                         ;; (esim-occs mod nil sig-al2 st-al2 nst-al2)
                         (subsetp-equal occs (alist-keys (occmap mod)))))
              (and stable-under-simplificationp
                   '(:cases ((hons-assoc-equal (car occs) (occmap mod))))))
      :flag esim-occs-mono)

    (defthm esim-occ-is-monotonic
      (implies (and (good-esim-occp occ)
                    (4v-alist-<= sig-al1 sig-al2)
                    (4v-alist-<= st-al1 st-al2))
               (b* ((sig-al1 (esim-occ occ sig-al1 st-al1))
                    (sig-al2 (esim-occ occ sig-al2 st-al2)))
                 (4v-alist-<= sig-al1 sig-al2)))
      :hints ('(:expand ((esim-occ occ sig-al1 st-al1)
                         (esim-occ occ sig-al2 st-al2))))
      :flag esim-occ-mono)

    :hints (("goal" :do-not-induct t
             :do-not '(generalize fertilize eliminate-destructors)))))





(verify-guards esim-out
               :hints(("Goal" :in-theory (e/d (alist-keys
                                               occmap-when-no-occs)
                                              (good-esim-modulep
                                               similar-patternsp
                                               subsetp-when-atom-left
                                               data-for-patternp
                                               eapply-spec
                                               default-car default-cdr
                                               alist-keys))
                       :expand ((subsetp-equal occs (alist-keys (occmap mod))))
                       :do-not-induct t))
               :guard-debug t
               :otf-flg t)


(defun esim-wf-signals (mod occs sig-al st-al)
  (or (atom occs)
      (b* ((sig-al1
            (esim-occ (esim-get-occ (car occs) mod) sig-al st-al)))
        (and (4v-alist-<= sig-al sig-al1)
             (esim-wf-signals mod (cdr occs) sig-al st-al)))))

(defthm esim-wf-signals-member-occ
  (implies (and (esim-wf-signals mod occs sig-al st-al)
                (member-equal occ occs))
           (4v-alist-<=
            sig-al (esim-occ (esim-get-occ occ mod) sig-al st-al))))

(defthm esim-wf-signals-subset
  (implies (and (esim-wf-signals mod occs sig-al st-al)
                (subsetp-equal occs1 occs))
           (esim-wf-signals mod occs1 sig-al st-al))
  :hints (("goal" :induct (len occs1)
           :in-theory (enable subsetp-equal))))

(defcong set-equiv iff (esim-wf-signals mod occs sig-al st-al) 2)

(defthm esim-occ-increases-when-non-outputs-bound
  (implies (and (good-esim-occp occ)
                (not (intersectp-equal (alist-keys sig-al)
                                       (pat-flatten1 (gpl :o occ)))))
           (4v-alist-<= sig-al (esim-occ occ sig-al st-al)))
  :hints (("goal" :do-not-induct t
           :expand ((esim-occ occ sig-al st-al))
           :in-theory (disable esim-out 4v-fix good-esim-modulep))
          (witness :ruleset 4v-alist-<=-witnessing)
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal
                                  esim-out 4v-fix good-esim-modulep))))
          (witness :ruleset set-reasoning-no-consp)))

(defthm esim-occ-increases-when-occ-is-nil
  (4v-alist-<= sig-al (esim-occ nil sig-al st-al))
  :hints (("goal" :do-not-induct t
           :expand ((esim-occ occ sig-al st-al))
           :in-theory (disable esim-out 4v-fix good-esim-modulep))))


(defthm esim-occ-increases-when-input-subset-bound
  (implies (and (good-esim-modulep mod)
                (subsetp-equal (alist-keys sig-al)
                               (pat-flatten1 (gpl :i mod))))
           (4v-alist-<= sig-al (esim-occ (esim-get-occ name mod)
                                                   sig-al st-al)))
  :hints (("goal" :cases ((hons-assoc-equal name (occmap mod))))
          (and stable-under-simplificationp
               '(:use ((:instance esim-occ-increases-when-non-outputs-bound
                                  (occ (esim-get-occ name mod))))
                      :in-theory (e/d (occmap-when-no-occs)
                                      (esim-occ-increases-when-non-outputs-bound))
                      :expand ((good-esim-modulep mod))))
          (set-reasoning)))


(defthm input-subset-bound-impl-esim-wf-signals
  (implies (and (good-esim-modulep mod)
                (subsetp-equal (alist-keys sig-al)
                               (pat-flatten1 (gpl :i mod)))
                (subsetp-equal occs (alist-keys (occmap mod))))
           (esim-wf-signals mod occs sig-al st-al))
  :hints (("goal" :induct (len occs))))






(defthm esim-occ-increases-when-gte
  (implies (and (4v-alist-<= sig-al1 sig-al2)
                (4v-alists-agree (pat-flatten1 (gpl :o occ)) sig-al1 sig-al2)
                (4v-alist-<= sig-al1 (esim-occ occ sig-al1 st-al))
                (good-esim-occp occ))
           (4v-alist-<= sig-al2 (esim-occ occ sig-al2 st-al)))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d* (4v-<=-trans1)
                            (4v-lookup 4v-fix 4v-<= esim-occ
                                       similar-patternsp
                                       good-esim-occp
                                       member-equal
                                       esim-occ-is-monotonic
                                       (:rules-of-class :type-prescription
                                                        :here)))
           :use ((:instance esim-occ-is-monotonic
                            (st-al1 st-al)
                            (st-al2 st-al))))
          (witness :ruleset 4v-alist-<=-witnessing)
          (witness :ruleset (4v-alist-<=-lookup-ex
                             4v-alists-agree-4v-lookup-ex))))





(local
 (progn
   (defthm no-intersect-collect
     (implies (and (not (intersectp-equal (collect-signal-list :o occs) sigs))
                   (member-equal occ occs))
              (and (not (intersectp-equal (pat-flatten1 (gpl :o occ)) sigs))
                   (not (intersectp-equal sigs (pat-flatten1 (gpl :o occ)))))))

   (defthm different-occs-no-overlap
     (implies (and (no-duplicatesp-equal (collect-signal-list :o occs))
                   (member-equal occ1 occs)
                   (member-equal occ2 occs)
                   (not (equal occ1 occ2)))
              (not (intersectp-equal (pat-flatten1 (gpl :o occ1))
                                     (pat-flatten1 (gpl :o occ2)))))
     :hints (("goal" :induct (len occs))))

   (defthm different-occs-no-overlap-rw
     (implies (and (good-esim-modulep mod)
                   (member-equal occ1 (alist-vals (fal-extract (alist-keys
                                                                (occmap mod))
                                                               (occmap mod))))
                   (member-equal occ2 (alist-vals (fal-extract (alist-keys
                                                                (occmap mod))
                                                               (occmap mod))))
                   (not (equal occ1 occ2)))
              (not (intersectp-equal (pat-flatten1 (gpl :o occ1))
                                     (pat-flatten1 (gpl :o occ2)))))
     :hints(("Goal" :in-theory (e/d (occmap-when-no-occs)
                                    (member-equal-of-alist-vals-under-iff))
             :expand ((good-esim-modulep mod)))))


   (defthm 4v-alists-agree-when-outs-not-intersect
     (implies (and (not (intersectp-equal sigs (pat-flatten1 (gpl :o occ))))
                   (good-esim-occp occ))
              (4v-alists-agree sigs sig-al
                               (esim-occ occ sig-al st-al)))
     :hints(("Goal" :in-theory (e/d (intersectp-equal) (4v-fix esim-occ)))))))


(defthm alist-equiv-fal-extract-alist-keys
  (alist-equiv (fal-extract (alist-keys al) al)
               al)
  :hints (("goal" :in-theory (enable alist-equiv-iff-agree-on-bad-guy))))


(defthm good-occsp-nonnil
  (implies (good-esim-occsp x)
           (not (member-equal nil x)))
  :hints(("Goal" :in-theory (enable member-equal))))

(defthm nonnil-vals-occmap
  (implies (good-esim-occsp occs)
           (and (not (member-equal nil (alist-vals (occmap1 occs))))
                (not (hons-rassoc-equal nil (occmap1 occs))))))

(defthm good-esim-modulep-no-null-occs
  (implies (good-esim-modulep x)
           (and (not (member-equal nil (alist-vals (occmap x))))
                (not (hons-rassoc-equal nil (occmap x)))))
  :hints(("Goal" :in-theory (enable occmap good-esim-modulep))))

(defthm hons-rassoc-equal-fal-extract
  (implies (not (hons-rassoc-equal x al))
           (not (hons-rassoc-equal x (fal-extract keys al))))
  :hints(("Goal" :in-theory (enable hons-rassoc-equal
                                    fal-extract))))

(defthm gpl-u-of-occmap1-lookup
  (equal (gpl :u (cdr (hons-assoc-equal x (occmap1 occs))))
         (and (hons-assoc-equal x (occmap1 occs))
              x)))

(defthm not-hons-assoc-equal-nil-of-good-occmap1
  (implies (good-esim-occsp occs)
           (not (hons-assoc-equal nil (occmap1 occs)))))

(defthm not-hons-assoc-equal-nil-of-good-occmap
  (implies (good-esim-modulep mod)
           (not (hons-assoc-equal nil (occmap mod))))
  :hints(("Goal" :in-theory (enable occmap good-esim-modulep))))

(defthm hons-assoc-equal-occmap1
  (implies (not (hons-assoc-equal nil (occmap1 occs)))
           (equal (equal (cdr (hons-assoc-equal x (occmap1 occs)))
                         (cdr (hons-assoc-equal y (occmap1 occs))))
                  (or (and (not (hons-assoc-equal x (occmap1 occs)))
                           (not (hons-assoc-equal y (occmap1 occs))))
                      (equal x y))))
  :hints (("goal" :use ((:instance gpl-u-of-occmap1-lookup)
                        (:instance gpl-u-of-occmap1-lookup
                                   (x y)))
           :in-theory (disable gpl-u-of-occmap1-lookup))))

(defthm hons-assoc-equal-occmap
  (implies (not (hons-assoc-equal nil (occmap mod)))
           (equal (equal (cdr (hons-assoc-equal x (occmap mod)))
                         (cdr (hons-assoc-equal y (occmap mod))))
                  (or (and (not (hons-assoc-equal x (occmap mod)))
                           (not (hons-assoc-equal y (occmap mod))))
                      (equal x y))))
  :hints (("goal" :in-theory (enable occmap))))

(defthm good-esim-modulep-no-null-occs-fal-extract
  (implies (good-esim-modulep x)
           (and (not (member-equal nil (alist-vals (fal-extract (alist-keys
                                                                 (occmap x))
                                                                (occmap x)))))
                (not (hons-rassoc-equal nil (fal-extract (alist-keys
                                                          (occmap x))
                                                         (occmap x))))))
  :hints(("Goal" :in-theory (e/d () (good-esim-modulep)))))



(defthm member-equal-lookup-of-alist-vals
  (implies (and (alist-equiv (double-rewrite al)
                             (double-rewrite al1))
                (not (member-equal nil (alist-vals al1))))
           (and (iff (member-equal (cdr (hons-assoc-equal k al))
                                   (alist-vals al1))
                     (hons-assoc-equal k (double-rewrite al)))
                (iff (hons-rassoc-equal (cdr (hons-assoc-equal k al)) al1)
                     (hons-assoc-equal k (double-rewrite al))))))



(defthm esim-wf-signals-after-esim-occ
  (implies (and (good-esim-modulep mod)
                (4v-alist-<=
                 sig-al (esim-occ (esim-get-occ occ mod) sig-al st-al))
                (esim-wf-signals mod occs sig-al st-al))
              (esim-wf-signals
               mod occs (esim-occ (esim-get-occ occ mod) sig-al st-al)
               st-al))
  :hints (("goal" :induct (len occs)
           :in-theory (e/d (subsetp-equal)
                           (input-subset-bound-impl-esim-wf-signals
                            intersectp-equal-commute
                            esim-wf-signals
                            good-esim-modulep
                            esim-occ-increases-when-non-outputs-bound
                            esim-occ-increases-when-input-subset-bound
                            esim-occ good-esim-occp similar-patternsp
                            member-equal))
           :expand ((:free (sig-al)  (esim-wf-signals mod occs sig-al st-al)))
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))
          (and stable-under-simplificationp
               '(:cases ((hons-assoc-equal occ (occmap mod)))))
          (and stable-under-simplificationp
               '(:cases ((equal occ (car occs))))))
  :otf-flg t)



(defthm esim-wf-signals-after-esim-occs
  (implies (and (good-esim-modulep mod)
                (subsetp-equal occs occs1)
                (esim-wf-signals mod occs1 sig-al st-al))
           (esim-wf-signals
            mod occs1
            (esim-occs mod occs sig-al st-al)
            st-al))
  :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al)
           :in-theory (disable esim-occ good-esim-modulep)
           :expand ((esim-occs mod occs sig-al st-al)))))


(defthm esim-wf-signals-impl-esim-occs-incr
  (implies (and (good-esim-modulep mod)
                (esim-wf-signals mod occs sig-al st-al))
           (4v-alist-<= sig-al
                        (esim-occs mod occs sig-al st-al)))
  :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al)
           :expand ((esim-occs mod occs sig-al st-al))
           :in-theory (e/d (4v-alist-<=-trans1) (esim-occ good-esim-modulep)))
          (and stable-under-simplificationp
               '(:use
                 ((:instance esim-wf-signals-after-esim-occ
                             (occ (car occs))))))))

(defthm esim-wf-signals-impl-esim-occs-incr-more
  (implies (and (good-esim-modulep mod)
                (subsetp-equal occs occs1)
                (esim-wf-signals mod occs1 sig-al st-al))
           (4v-alist-<= sig-al
                        (esim-occs mod occs sig-al st-al))))


(defthmd 4v-env-equiv-when-both-<=
  (implies (and (4v-alist-<= a b)
                (4v-alist-<= b a))
           (equal (4v-env-equiv a b) t))
  :hints (("goal" :in-theory (disable 4v-lookup 4v-fix))
          (witness :ruleset (4v-env-equiv-witnessing
                             4v-alist-<=-lookup-ex))))

(defthmd 4v-env-equiv-iff-both-<=
  (iff (4v-env-equiv a b)
       (and (4v-alist-<= a b)
            (4v-alist-<= b a)))
  :hints (("goal" :in-theory (enable 4v-env-equiv-when-both-<=))))

(defthm occs-fixed-impl-each-occ-fixed
  (implies (and (good-esim-modulep mod)
                (member-equal occ occs)
                (esim-wf-signals mod occs sig-al st-al)
                (4v-alist-<= (esim-occs mod occs sig-al st-al)
                             sig-al))
           (4v-env-equiv (esim-occ (esim-get-occ occ mod) sig-al st-al)
                         sig-al))
  :hints (("goal" :induct (len occs)
           :expand ((esim-occs mod occs sig-al st-al))
           :in-theory (e/d (4v-alist-<=-trans2
                            4v-alist-<=-trans1
                            occmap-when-no-occs
                            4v-env-equiv-iff-both-<=)
                           (esim-occ-increases-when-gte
                            esim-occ-increases-when-non-outputs-bound
                            good-esim-modulep-good-occp-lookup-in-occmap
                            4v-alists-agree
                            4v-lookup
                            good-esim-occp
                            good-esim-modulep esim-occ)))))


(defthm occs-<=-impl-occs-fixed
  (implies (and (good-esim-modulep mod)
                (esim-wf-signals mod occs sig-al st-al)
                (4v-alist-<= (esim-occs mod occs sig-al st-al)
                             sig-al))
           (4v-env-equiv (esim-occs mod occs sig-al st-al)
                         sig-al))
  :hints(("Goal" :in-theory (enable 4v-env-equiv-iff-both-<=))))






;; (def-universal-equiv nth-4v-env-equiv
;;   :qvars n
;;   :equiv-terms ((4v-env-equiv (nth n x)))
;;   :defquant t)

;; (defexample nth-4v-env-equiv-nth-ex
;;   :pattern (nth a b)
;;   :templates (a)
;;   :instance-rulename nth-4v-env-equiv-instancing)

;; (defthmd mv-nth-is-nth
;;   (equal (mv-nth n x) (nth n x))
;;   :hints(("Goal" :in-theory (enable mv-nth))))




;; (defcong nth-4v-env-equiv 4v-env-equiv (mv-nth a b) 2
;;   :hints(("Goal" :in-theory (enable mv-nth-is-nth))
;;          (witness :ruleset nth-4v-env-equiv-nth-ex)))


;; (defcong 4v-env-equiv nth-4v-env-equiv (cons a b) 1
;;   :hints (("goal" :expand ((:free (n) (nth n (cons a b)))))
;;           (witness :ruleset nth-4v-env-equiv-witnessing)))



;; (defcong nth-4v-env-equiv nth-4v-env-equiv (cons a b) 2
;;   :hints (("goal" :expand ((:free (n) (nth n (cons a b)))))
;;           (witness :ruleset nth-4v-env-equiv-witnessing)
;;           (witness :ruleset nth-4v-env-equiv-nth-ex)))


;; (defthm nth-4v-equiv-append-of-conses
;;   (iff (nth-4v-env-equiv (cons a b) (cons c d))
;;        (and (4v-env-equiv a c)
;;             (nth-4v-env-equiv b d)))
;;   :hints (("goal" :use ((:instance nth-4v-env-equiv-necc
;;                                    (x (cons a b)) (y (cons c d))
;;                                    (n 0))))
;;           (witness :ruleset nth-4v-env-equiv-witnessing)
;;           (and stable-under-simplificationp
;;                '(:use ((:instance nth-4v-env-equiv-necc
;;                                   (x (cons a b)) (y (cons a d))
;;                                   (n (+ 1 (nfix n0)))))
;;            :expand ((:free (n a b) (nth n (cons a b))))))))



;; (def-universal-equiv nth-key-and-env-equiv
;;   :qvars n
;;   :equiv-terms ((key-and-env-equiv (nth n x)))
;;   :defquant t)

;; (defexample nth-key-and-env-equiv-nth-ex
;;   :pattern (nth a b)
;;   :templates (a)
;;   :instance-rulename nth-key-and-env-equiv-instancing)

;; (defthmd mv-nth-is-nth
;;   (equal (mv-nth n x) (nth n x))
;;   :hints(("Goal" :in-theory (enable mv-nth))))




;; (defcong nth-key-and-env-equiv key-and-env-equiv (mv-nth a b) 2
;;   :hints(("Goal" :in-theory (enable mv-nth-is-nth))
;;          (witness :ruleset nth-key-and-env-equiv-nth-ex)))


;; (defcong key-and-env-equiv nth-key-and-env-equiv (cons a b) 1
;;   :hints (("goal" :expand ((:free (n) (nth n (cons a b)))))
;;           (witness :ruleset nth-key-and-env-equiv-witnessing)))



;; (defcong nth-key-and-env-equiv nth-key-and-env-equiv (cons a b) 2
;;   :hints (("goal" :expand ((:free (n) (nth n (cons a b)))))
;;           (witness :ruleset nth-key-and-env-equiv-witnessing)
;;           (witness :ruleset nth-key-and-env-equiv-nth-ex)))


;; (defthm nth-key-and-env-equiv-append-of-conses
;;   (iff (nth-key-and-env-equiv (cons a b) (cons c d))
;;        (and (key-and-env-equiv a c)
;;             (nth-key-and-env-equiv b d)))
;;   :hints (("goal" :use ((:instance nth-key-and-env-equiv-necc
;;                                    (x (cons a b)) (y (cons c d))
;;                                    (n 0)))
;;            :in-theory (disable (key-and-env-equiv)))
;;           (witness :ruleset nth-key-and-env-equiv-witnessing)
;;           (and stable-under-simplificationp
;;                '(:use ((:instance nth-key-and-env-equiv-necc
;;                                   (x (cons a b)) (y (cons a d))
;;                                   (n (+ 1 (nfix n0)))))
;;            :expand ((:free (n a b) (nth n (cons a b))))))))


;; (defrefinement nth-key-and-env-equiv nth-4v-env-equiv
;;   :hints ((witness :ruleset (nth-4v-env-equiv-witnessing
;;                              nth-key-and-env-equiv-nth-ex))))


;; (defexample 4v-env-equiv-lookup-ex
;;   :pattern (4v-lookup a b)
;;   :templates (a)
;;   :instance-rulename 4v-env-equiv-instancing)


(defcong 4v-env-equiv 4v-env-equiv (4v-pat-alist-translate pat1 pat2 al acc) 4
  :hints (("goal" :in-theory (disable 4v-lookup 4v-env-equiv-to-key-and-env-equiv)
           :induct t :do-not-induct t))
  :otf-flg t)

(defcong 4v-env-equiv equal (4v-pat-alist-translate pat1 pat2 al acc) 3
  :hints (("goal" :in-theory (disable 4v-lookup 4v-env-equiv-to-key-and-env-equiv)
           :induct t :do-not-induct t))
  :otf-flg t)

;; (defthm keys-equiv-cons
;;   (implies (keys-equiv a b)
;;            (equal (keys-equiv (cons (cons k v1) a)
;;                               (cons (cons k v2) b))
;;                   t))
;;   :hints ((witness :ruleset (keys-equiv-witnessing
;;                              keys-equiv-hons-assoc-equal-ex))))

;; (defcong key-and-env-equiv key-and-env-equiv (4v-pat-alist-translate pat1 pat2 al acc) 4
;;   :hints (("goal" :in-theory (e/d (key-and-env-equiv)
;;                                   (4v-lookup 4v-env-equiv-to-key-and-env-equiv))
;;            :induct t :do-not-induct t))
;;   :otf-flg t)




(defcong 4v-env-equiv 4v-env-equiv (esim-occ occ sig-al st-al) 2
  :hints (("goal" :expand ((esim-occ occ sig-al st-al))
           :in-theory (disable esim-out))))

(defcong 4v-env-equiv equal (esim-occ occ sig-al st-al) 3
  :hints (("goal" :expand ((esim-occ occ sig-al st-al))
           :in-theory (disable esim-out))))

(defcong 4v-env-equiv equal (esim-occ-nst occ sig-al st-al) 2
  :hints (("goal" :expand (esim-occ-nst occ sig-al st-al)
           :in-theory (disable esim-nst))))

(defcong 4v-env-equiv equal (esim-occ-nst occ sig-al st-al) 3
  :hints (("goal" :expand (esim-occ-nst occ sig-al st-al)
           :in-theory (disable esim-nst))))

(defcong 4v-env-equiv equal (esim-occs-nst mod occs sig-al st-al) 3
  :hints (("goal" :expand ((:free (sig-al) (esim-occs-nst mod occs sig-al st-al)))
           :induct (len occs)
           :in-theory (disable esim-occ-nst))))

(defcong 4v-env-equiv equal (esim-occs-nst mod occs sig-al st-al) 4
  :hints (("goal" :expand ((:free (st-al) (esim-occs-nst mod occs sig-al st-al)))
           :induct (len occs)
           :in-theory (disable esim-occ-nst))))

(defcong 4v-env-equiv equal (4v-x-res i al) 2
  :hints(("Goal" :in-theory (disable 4v-lookup))))


(defcong 4v-env-equiv 4v-env-equiv (eapply-spec-out al x) 1
  :hints(("Goal" :in-theory (e/d* (key-and-env-equiv)
                                  (4v-lookup
                                   (:ruleset 4v-op-defs)
                                   4v-env-equiv-to-key-and-env-equiv))
          :do-not-induct t))
  :otf-flg t)

;; (defcong 4v-env-equiv 4v-env-equiv (eapply-spec-out al x) 2
;;   :hints(("Goal" :in-theory (e/d* (key-and-env-equiv)
;;                                   (4v-lookup
;;                                    (:ruleset 4v-op-defs)
;;                                    4v-env-equiv-to-key-and-env-equiv))
;;           :do-not-induct t))
;;   :otf-flg t)

(defcong 4v-env-equiv 4v-env-equiv (eapply-spec-nst al x) 1
  :hints(("Goal" :in-theory (e/d* (key-and-env-equiv)
                                  (4v-lookup
                                   (:ruleset 4v-op-defs)
                                   4v-env-equiv-to-key-and-env-equiv))
          :do-not-induct t))
  :otf-flg t)

;; (defcong 4v-env-equiv equal (eapply-spec-nst sig-al st-al i s o x) 2
;;   :hints(("Goal" :in-theory (e/d* (key-and-env-equiv)
;;                                   (4v-lookup
;;                                    (:ruleset 4v-op-defs)
;;                                    4v-env-equiv-to-key-and-env-equiv))
;;           :do-not-induct t))
;;   :otf-flg t)


(defcong 4v-env-equiv equal (4v-alist-extract keys al) 2)

(defcong 4v-env-equiv equal (esim-nst mod sig-al st-al) 2
  :hints (("goal" :expand (esim-nst mod sig-al st-al)
           :in-theory (disable esim-occs esim-fixpoint eapply-spec-nst))))

(defcong 4v-env-equiv equal (esim-nst mod sig-al st-al) 3
  :hints (("goal" :expand (esim-nst mod sig-al st-al)
           :in-theory (disable esim-occs esim-fixpoint eapply-spec-nst))))


;; (defcong 4v-env-equiv nth-4v-env-equiv (esim-occ occ sig-al st-al nst-al internal-al) 2
;;   :hints (("goal" :expand ((:free (sig-al) (esim-occ occ sig-al st-al nst-al internal-al)))
;;            :in-theory (disable esim))))

;; (defcong key-and-env-equiv nth-key-and-env-equiv (esim-occ occ sig-al st-al nst-al internal-al) 2
;;   :hints (("goal" :expand ((:free (sig-al) (esim-occ occ sig-al st-al nst-al internal-al)))
;;            :in-theory (disable esim))))


;; (defcong 4v-env-equiv equal (esim-occ occ sig-al st-al nst-al internal-al) 3
;;   :hints (("goal" :expand ((:free (sig-al) (esim-occ occ sig-al st-al nst-al internal-al)))
;;            :in-theory (disable esim))))


;; (defcong 4v-env-equiv nth-4v-env-equiv (esim-occ occ sig-al st-al nst-al internal-al) 4
;;   :hints (("goal" :expand ((:free (sig-al) (esim-occ occ sig-al st-al nst-al internal-al)))
;;            :in-theory (disable esim))))

;; (defcong key-and-env-equiv nth-key-and-env-equiv (esim-occ occ sig-al st-al nst-al internal-al) 4
;;   :hints (("goal" :expand ((:free (sig-al) (esim-occ occ sig-al st-al nst-al internal-al)))
;;            :in-theory (disable esim))))

;; (defcong 4v-env-equiv nth-4v-env-equiv (esim-occ occ sig-al st-al nst-al internal-al) 5
;;   :hints (("goal" :expand ((:free (sig-al) (esim-occ occ sig-al st-al nst-al internal-al)))
;;            :in-theory (disable esim))))

;; (defcong key-and-env-equiv nth-key-and-env-equiv (esim-occ occ sig-al st-al nst-al internal-al) 5
;;   :hints (("goal" :expand ((:free (sig-al) (esim-occ occ sig-al st-al nst-al internal-al)))
;;            :in-theory (disable esim))))

;; ;; (defun esim-occs-sig-al-cong-ind (mod occs sig-al sig-al-equiv st-al nst-al internal-al)
;; ;;   (declare (xargs :measure (len occs)))
;; ;;   (if (or (atom occs)
;; ;;           (not (mbt (and (gpl :occs mod) t))))
;; ;;       (list nst-al sig-al sig-al-equiv st-al)
;; ;;     (b* (((mv nst-al sig-al)
;; ;;           (esim-occ (esim-get-occ (car occs) mod)
;; ;;                     sig-al st-al nst-al))
;; ;;          ((mv nst-al sig-al-equiv)
;; ;;           (esim-occ (esim-get-occ (car occs) mod)
;; ;;                     sig-al-equiv st-al nst-al)))
;; ;;       (esim-occs-sig-al-cong-ind mod (cdr occs) sig-al sig-al-equiv st-al
;; ;;                                  nst-al))))

(defun esim-occs-cong-ind (mod occs sig-al sig-al-equiv
                               st-al st-al-equiv)
  (declare (xargs :measure (len occs)))
  (if (or (atom occs)
          (not (mbt (consp (gpl :occs mod)))))
      (mv sig-al sig-al-equiv)
    (b* ((sig-al
          (esim-occ (esim-get-occ (car occs) mod) sig-al st-al))
         (sig-al-equiv
          (esim-occ (esim-get-occ (car occs) mod) sig-al-equiv st-al-equiv)))
      (esim-occs-cong-ind mod (cdr occs) sig-al sig-al-equiv
                          st-al st-al-equiv))))



(defthm 4v-env-equiv-of-esim-occs
  (implies (and (4v-env-equiv sig-al sig-al-equiv)
                (4v-env-equiv st-al st-al-equiv))
           (4v-env-equiv (esim-occs mod occs sig-al st-al)
                         (esim-occs mod occs sig-al-equiv st-al-equiv)))
  :hints (("goal" :induct (esim-occs-cong-ind
                           mod occs sig-al sig-al-equiv
                           st-al st-al-equiv)
           :in-theory (disable esim-occ good-esim-modulep)
           :expand ((:free (sig-al st-al)
                           (esim-occs mod occs sig-al st-al)))))
  :rule-classes nil)

;; (defthm key-and-env-equiv-of-esim-occs
;;   (implies (and (key-and-env-equiv sig-al sig-al-equiv)
;;                 (key-and-env-equiv st-al st-al-equiv)
;;                 (key-and-env-equiv nst-al nst-al-equiv)
;;                 (key-and-env-equiv internal-al internal-al-equiv))
;;            (nth-key-and-env-equiv (esim-occs mod occs sig-al st-al nst-al internal-al)
;;                              (esim-occs mod occs sig-al-equiv st-al-equiv
;;                                         nst-al-equiv internal-al-equiv)))
;;   :hints (("goal" :induct (esim-occs-cong-ind
;;                            mod occs sig-al sig-al-equiv
;;                            st-al st-al-equiv
;;                            nst-al nst-al-equiv
;;                            internal-al internal-al-equiv)
;;            :in-theory (disable esim-occ)))
;;   :rule-classes nil)


(defcong 4v-env-equiv 4v-env-equiv
  (esim-occs mod occs sig-al st-al) 3
  :hints (("goal" :induct (list (esim-occs-ind mod occs sig-al st-al)
                                (esim-occs-ind mod occs sig-al-equiv st-al))
           :in-theory (disable good-esim-modulep))))

(defcong 4v-env-equiv equal
  (esim-occs mod occs sig-al st-al) 4
  :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al)
           :in-theory (disable good-esim-modulep))))

;; (defcong 4v-env-equiv nth-4v-env-equiv
;;   (esim-occs mod occs sig-al st-al nst-al internal-al) 5
;;   :hints (("goal" :use ((:instance 4v-env-equiv-of-esim-occs
;;                                    (sig-al-equiv sig-al)
;;                                    (st-al-equiv st-al)
;;                                    (internal-al-equiv internal-al))))))

;; (defcong 4v-env-equiv nth-4v-env-equiv
;;   (esim-occs mod occs sig-al st-al nst-al internal-al) 6
;;   :hints (("goal" :use ((:instance 4v-env-equiv-of-esim-occs
;;                                    (sig-al-equiv sig-al)
;;                                    (st-al-equiv st-al)
;;                                    (nst-al-equiv nst-al))))))


;; (defcong key-and-env-equiv nth-key-and-env-equiv
;;   (esim-occs mod occs sig-al st-al nst-al internal-al) 3
;;   :hints (("goal" :use ((:instance key-and-env-equiv-of-esim-occs
;;                                    (st-al-equiv st-al)
;;                                    (nst-al-equiv nst-al)
;;                                    (internal-al-equiv internal-al))))))

;; (defcong key-and-env-equiv nth-key-and-env-equiv
;;   (esim-occs mod occs sig-al st-al nst-al internal-al) 4
;;   :hints (("goal" :use ((:instance key-and-env-equiv-of-esim-occs
;;                                    (sig-al-equiv sig-al)
;;                                    (nst-al-equiv nst-al)
;;                                    (internal-al-equiv internal-al))))))

;; (defcong key-and-env-equiv nth-key-and-env-equiv
;;   (esim-occs mod occs sig-al st-al nst-al internal-al) 5
;;   :hints (("goal" :use ((:instance key-and-env-equiv-of-esim-occs
;;                                    (sig-al-equiv sig-al)
;;                                    (st-al-equiv st-al)
;;                                    (internal-al-equiv internal-al))))))

;; (defcong key-and-env-equiv nth-key-and-env-equiv
;;   (esim-occs mod occs sig-al st-al nst-al internal-al) 6
;;   :hints (("goal" :use ((:instance key-and-env-equiv-of-esim-occs
;;                                    (sig-al-equiv sig-al)
;;                                    (st-al-equiv st-al)
;;                                    (nst-al-equiv nst-al))))))



(defun esim-fixpoint-cong-ind (mod sig-al sig-al-equiv
                                   st-al st-al-equiv)
  (declare
   (xargs
    :measure (esim-alist-lattice-height-measure
              (esim-driven-signals mod)
              sig-al)))
  (b* ((occnames (alist-keys (make-fast-alist (occmap mod))))
       (sig-al1
        (esim-occs mod occnames sig-al st-al))
       (sig-al1-equiv
        (esim-occs mod occnames sig-al-equiv st-al-equiv))
       (sig-al (make-fast-alist sig-al))
       (fixed (4v-alist-<=-keys (esim-driven-signals mod)
                                sig-al1 sig-al))
       ((unless (and (not fixed)
                     (mbt (4v-alist-<= sig-al sig-al1))))
        (fast-alist-free sig-al1)
        (list sig-al sig-al-equiv)))
    (fast-alist-free sig-al)
    (esim-fixpoint-cong-ind mod sig-al1 sig-al1-equiv st-al st-al-equiv)))


(defcong 4v-env-equiv iff (4v-alist-<=-keys keys a b) 2
  :hints (("goal" :in-theory (disable 4v-lookup))))

(defcong 4v-env-equiv iff (4v-alist-<=-keys keys a b) 3
  :hints (("goal" :in-theory (disable 4v-lookup))))

(defcong 4v-env-equiv key-and-env-equiv (4v-alist-extract keys al) 2
  :hints(("Goal" :in-theory (e/d (key-and-env-equiv)
                                 (4v-env-equiv-to-key-and-env-equiv)))))

;; (defthm 4v-env-equiv-of-esim-fixpoint
;;   (implies (and (4v-env-equiv sig-al sig-al-equiv)
;;                 (4v-env-equiv st-al st-al-equiv))
;;            (4v-env-equiv (esim-fixpoint mod sig-al st-al)
;;                              (esim-fixpoint mod sig-al-equiv st-al-equiv)))
;;   :hints (("goal" :induct (esim-fixpoint-cong-ind mod sig-al sig-al-equiv
;;                                                   st-al st-al-equiv)
;;            :expand ((esim-fixpoint mod sig-al st-al)
;;                     (esim-fixpoint mod sig-al-equiv st-al-equiv))
;;            :in-theory (disable esim-occs good-esim-modulep 4v-alist-<=-keys
;;                                4v-env-equiv-append
;;                                4v-env-equiv-to-key-and-env-equiv)))
;;   :rule-classes nil)


;; (defthm key-and-env-equiv-of-esim-fixpoint
;;   (implies (and (key-and-env-equiv sig-al sig-al-equiv)
;;                 (key-and-env-equiv st-al st-al-equiv))
;;            (nth-key-and-env-equiv (esim-fixpoint mod sig-al st-al)
;;                              (esim-fixpoint mod sig-al-equiv st-al-equiv)))
;;   :hints (("goal" :induct (esim-fixpoint-cong-ind mod sig-al sig-al-equiv
;;                                                   st-al st-al-equiv)
;;            :expand ((esim-fixpoint mod sig-al st-al)
;;                     (esim-fixpoint mod sig-al-equiv st-al-equiv))
;;            :in-theory (disable esim-occs good-esim-modulep 4v-alist-<=-keys
;;                                4v-env-equiv-append
;;                                4v-env-equiv-to-key-and-env-equiv)))
;;   :rule-classes nil)

(defcong 4v-env-equiv 4v-env-equiv (esim-fixpoint mod sig-al st-al) 2
  :hints (("goal" :induct (esim-fixpoint-cong-ind mod sig-al sig-al-equiv st-al
                                                  st-al)
           :expand ((esim-fixpoint mod sig-al st-al)
                    (esim-fixpoint mod sig-al-equiv st-al))
           :in-theory (disable esim-occs good-esim-modulep))))

(defcong 4v-env-equiv equal (esim-fixpoint mod sig-al st-al) 3
  :hints (("goal" :induct (esim-fixpoint-cong-ind mod sig-al sig-al st-al
                                                  st-al-equiv)
           :expand ((esim-fixpoint mod sig-al st-al-equiv)
                    (esim-fixpoint mod sig-al st-al))
           :in-theory (disable esim-occs good-esim-modulep))))

;; (defcong 4v-env-equiv nth-4v-env-equiv (esim-fixpoint mod sig-al st-al) 3
;;   :hints (("goal" :use ((:instance 4v-env-equiv-of-esim-fixpoint
;;                                    (sig-al-equiv sig-al))))))

;; (defcong key-and-env-equiv nth-key-and-env-equiv (esim-fixpoint mod sig-al st-al) 2
;;   :hints (("goal" :use ((:instance key-and-env-equiv-of-esim-fixpoint
;;                                    (st-al-equiv st-al))))))

;; (defcong key-and-env-equiv nth-key-and-env-equiv (esim-fixpoint mod sig-al st-al) 3
;;   :hints (("goal" :use ((:instance key-and-env-equiv-of-esim-fixpoint
;;                                    (sig-al-equiv sig-al))))))




(defcong 4v-env-equiv equal (esim-out mod sig-al st-al) 2
  :hints (("goal" :expand ((esim-out mod sig-al st-al)
                           (esim-out mod sig-al-equiv st-al))
           :in-theory (disable esim-fixpoint eapply-spec-out))))

(defcong 4v-env-equiv equal (esim-out mod sig-al st-al) 3
  :hints (("goal" :expand ((esim-out mod sig-al st-al)
                           (esim-out mod sig-al st-al-equiv))
           :in-theory (disable esim-fixpoint eapply-spec-out))))






(defun esim-fixpoint-p-occs (mod occs sig-al st-al)
  (or (atom occs)
      (b* ((sig-al1
            (esim-occ (esim-get-occ (car occs) mod)
                      sig-al st-al)))
        (and (4v-env-equiv sig-al sig-al1)
             (esim-fixpoint-p-occs mod (cdr occs) sig-al st-al)))))

(defcong 4v-env-equiv equal (esim-fixpoint-p-occs mod occs sig-al st-al) 3
  :hints (("goal" :in-theory (disable 4v-env-equiv-to-key-and-env-equiv
                                      good-esim-modulep esim-occ))))

(defcong 4v-env-equiv equal (esim-fixpoint-p-occs mod occs sig-al st-al) 4
  :hints (("goal" :in-theory (disable 4v-env-equiv-to-key-and-env-equiv
                                      good-esim-modulep esim-occ))))

(defun esim-fixpoint-p (mod sig-al st-al)
  (esim-fixpoint-p-occs mod (alist-keys (occmap mod)) sig-al st-al))

(defcong 4v-env-equiv equal (esim-fixpoint-p mod sig-al st-al) 2
  :hints(("Goal" :in-theory (disable esim-fixpoint-p-occs))))

(defcong 4v-env-equiv equal (esim-fixpoint-p mod sig-al st-al) 3
  :hints(("Goal" :in-theory (disable esim-fixpoint-p-occs))))


(defthm esim-fixpoint-p-occs-when-<=
  (implies (and (good-esim-modulep mod)
                (esim-wf-signals mod occs sig-al st-al)
                (4v-alist-<=
                 (esim-occs mod occs sig-al st-al)
                 sig-al))
           (esim-fixpoint-p-occs mod occs sig-al st-al))
  :hints(("Goal" :in-theory (e/d (4v-env-equiv-iff-both-<=
                                  4v-alist-<=-trans2
                                  occmap-when-no-occs)
                                 (good-esim-modulep
                                  good-esim-occp
                                  4v-alists-agree
                                  occs-<=-impl-occs-fixed
                                  esim-occ))
          :induct (len occs)
          :expand ((esim-occs mod occs sig-al st-al))
          :do-not-induct t))
  :otf-flg t)

;; (defun esim-fixpoint-ind (mod sig-al st-al)
;;    (declare (xargs :measure (esim-alist-lattice-height-measure
;;                              (esim-driven-signals mod)
;;                              sig-al)))
;;    (b* ((occnames (alist-keys (make-fast-alist (occmap mod))))
;;         ((mv nst-al sig-al1 internal-al)
;;          (esim-occs mod occnames sig-al st-al nil nil))
;;         (sig-al (make-fast-alist sig-al))
;;         (fixed (4v-alist-<=-keys (esim-driven-signals mod) sig-al1 sig-al))
;;         ((unless (and (not fixed)
;;                       (mbt (4v-alist-<= sig-al sig-al1))))
;;          (fast-alist-free sig-al1)
;;          (mv nst-al sig-al internal-al)))
;;      (fast-alist-free sig-al)
;;      (fast-alist-free nst-al)
;;      (esim-fixpoint-ind mod sig-al1 st-al)))

(defthm esim-fixpoint-p-esim-fixpoint-rec
  (implies (and (good-esim-modulep mod)
                (esim-wf-signals mod (alist-keys (occmap mod)) sig-al st-al))
           (esim-fixpoint-p
            mod (esim-fixpoint mod sig-al st-al)
            st-al))
  :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al)
           :in-theory (disable esim-occs))))

(defthm esim-fixpoint-p-esim-fixpoint
  (implies (and (good-esim-modulep mod)
                (subsetp-equal (alist-keys sig-al)
                               (pat-flatten1 (gpl :i mod))))
           (esim-fixpoint-p
            mod
            (esim-fixpoint mod sig-al st-al)
            st-al))
  :hints (("goal" :do-not-induct t
           :in-theory (disable esim-fixpoint-p
                               good-esim-modulep))))

(defthm esim-occ-equiv-when-fixpoint
  (implies (and (esim-fixpoint-p-occs mod occs fixpoint st-al)
                (member-equal occ occs))
           (4v-env-equiv (esim-occ (esim-get-occ occ mod) fixpoint st-al)
                         fixpoint))
  :hints(("Goal" :in-theory (disable esim-occ good-esim-modulep))))

(defthm esim-occ-equiv-when-mod-fixpoint
  (implies (esim-fixpoint-p mod fixpoint st-al)
           (4v-env-equiv (esim-occ (esim-get-occ occ mod) fixpoint st-al)
                         fixpoint))
  :hints(("Goal" :in-theory (disable esim-occ good-esim-modulep)
          :cases ((hons-assoc-equal occ (occmap mod))))))


(defthm esim-occs-equiv-when-fixpoint
  (implies (esim-fixpoint-p-occs mod occs fixpoint st-al)
           (4v-env-equiv (esim-occs mod occs fixpoint st-al)
                         fixpoint))
  :hints(("Goal" :in-theory (e/d (subsetp-equal)
                                 (esim-occ good-esim-modulep))
          :expand (esim-occs mod occs fixpoint st-al)
          :induct (len occs))))

(defthm esim-occs-equiv-when-mod-fixpoint
  (implies (esim-fixpoint-p mod fixpoint st-al)
           (4v-env-equiv (esim-occs mod (alist-keys (occmap mod)) fixpoint
                                    st-al)
                         fixpoint)))

(defthm esim-fixpoint-equiv-when-mod-fixpoint
  (implies (esim-fixpoint-p mod fixpoint st-al)
           (4v-env-equiv (esim-fixpoint mod fixpoint st-al)
                         fixpoint))
  :hints (("goal" :induct (esim-fixpoint-ind mod fixpoint st-al)
           :in-theory (disable esim-occs good-esim-modulep
                               keys-equiv-when-alist-keys
                               esim-fixpoint-p))))


(defthm esim-fixpoint-all-fixpoints-greater1
  (implies (and (good-esim-modulep mod)
                (4v-alist-<= sig-al fixpoint)
                (esim-wf-signals mod (alist-keys (occmap mod)) sig-al st-al)
                (esim-fixpoint-p mod fixpoint st-al))
           (4v-alist-<=
            (esim-fixpoint mod sig-al st-al)
            fixpoint))
  :hints (("goal" :use ((:instance esim-fixpoint-is-monotonic
                                   (sig-al1 sig-al)
                                   (sig-al2 fixpoint)
                                   (st-al1 st-al)
                                   (st-al2 st-al)))
           :in-theory (disable esim-fixpoint-is-monotonic
                               esim-fixpoint esim-occs
                               good-esim-modulep
                               esim-wf-signals esim-occ esim-fixpoint-p)
           :do-not-induct t)
          (and stable-under-simplificationp
               '(:expand ((esim-fixpoint mod sig-al st-al)))))
  :otf-flg t)


(defquant all-fixpoints-greater (mod sig-al st-al)
  (forall fixpoint
          (implies (and (esim-fixpoint-p mod fixpoint st-al)
                        (4v-alists-agree (pat-flatten1 (gpl :i mod))
                                         sig-al fixpoint))
                   (4v-alist-<= sig-al fixpoint))))


(defexample 4v-alists-agree-hons-assoc-equal-ex
  :pattern (hons-assoc-equal x al)
  :templates (x)
  :instance-rulename 4v-alists-agree-instancing)

(defthmd 4v-alist-<=-when-agree-on-only-keys
  (implies (and (subsetp-equal (alist-keys al1) keys)
                (4v-alists-agree keys al1 al2))
           (4v-alist-<= al1 al2))
  :hints (("goal" :do-not-induct t
           :in-theory (disable 4v-fix))
          (witness :ruleset 4v-alist-<=-witnessing)
          (witness :ruleset 4v-alists-agree-hons-assoc-equal-ex)
          (and stable-under-simplificationp
               '(:in-theory (e/d (hons-assoc-equal-iff-member-alist-keys)
                                 (alist-keys-member-hons-assoc-equal
                                  4v-fix 4v-<=))))
          (witness :ruleset (set-reasoning-no-consp))))

(defthmd 4v-alist-<=-when-agree-on-only-keys2
  (implies (and (4v-alists-agree keys al1 al2)
                (subsetp-equal (alist-keys al1) keys))
           (4v-alist-<= al1 al2))
  :hints (("goal" :do-not-induct t
           :in-theory (enable 4v-alist-<=-when-agree-on-only-keys))))

(defthm esim-fixpoint-on-inputs
  (implies (and (good-esim-modulep mod)
                (member-equal x (pat-flatten1 (gpl :i mod))))
           (equal (hons-assoc-equal x (esim-fixpoint mod sig-al st-al))
                  (hons-assoc-equal x sig-al)))
  :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al)
           :in-theory (disable good-esim-modulep esim-occs
                               esim-wf-signals))))

(defthm esim-fixpoint-agree-on-inputs
  (implies (good-esim-modulep mod)
           (4v-alists-agree (pat-flatten1 (gpl :i mod))
                            (esim-fixpoint mod sig-al st-al)
                            sig-al))
  :hints ((witness :ruleset 4v-alists-agree-witnessing)))

(defthm esim-fixpoint-agree-on-inputs2
  (implies (good-esim-modulep mod)
           (4v-alists-agree (pat-flatten1 (gpl :i mod))
                            sig-al
                            (esim-fixpoint mod sig-al st-al)))
  :hints ((witness :ruleset 4v-alists-agree-witnessing)))


(defthmd 4v-alists-agree-commute
  (implies (4v-alists-agree keys b a)
           (4v-alists-agree keys a b))
  :hints(("Goal" :in-theory (disable 4v-lookup))))

(defthmd 4v-alists-agree-trans1
  (implies (and (4v-alists-agree keys a b)
                (4v-alists-agree keys b c))
           (4v-alists-agree keys a c))
  :hints (("goal" :in-theory (disable 4v-lookup))))

(defthmd 4v-alists-agree-trans2
  (implies (and (4v-alists-agree keys b c)
                (4v-alists-agree keys a b))
           (4v-alists-agree keys a c))
  :hints (("goal" :in-theory (enable 4v-alists-agree-trans1))))


(defthm esim-fixpoint-all-fixpoints-greater
  (implies (and (good-esim-modulep mod)
                (subsetp-equal (alist-keys sig-al)
                               (pat-flatten1 (gpl :i mod))))
           (all-fixpoints-greater
            mod (esim-fixpoint mod sig-al st-al)
            st-al))
  :hints (("goal" :in-theory (e/d (4v-alist-<=-when-agree-on-only-keys
                                   4v-alists-agree-trans2)
                                  (4v-alists-agree)))
          (witness :ruleset all-fixpoints-greater-witnessing)))


(defexample all-fixpoints-greater-fixpoint-ex
  :pattern (esim-fixpoint-p mod fixpoint st-al)
  :templates (fixpoint)
  :instance-rulename all-fixpoints-greater-instancing)

(defthm esim-least-fixpoint-unique
  (implies (and (all-fixpoints-greater mod fixpoint1 st-al)
                (all-fixpoints-greater mod fixpoint2 st-al)
                (esim-fixpoint-p mod fixpoint1 st-al)
                (esim-fixpoint-p mod fixpoint2 st-al)
                (4v-alists-agree (pat-flatten1 (gpl :i mod)) fixpoint1 fixpoint2))
           (4v-env-equiv fixpoint1 fixpoint2))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (4v-env-equiv-iff-both-<=
                            4v-alists-agree-commute)
                           (esim-fixpoint-p)))
          (witness :ruleset (all-fixpoints-greater-fixpoint-ex)))
  :rule-classes nil)

(defun 4v-alistp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (4vp (cdar x))
         (4v-alistp (cdr x)))))




(encapsulate nil
  (local (defthm 4v-fix-when-4vp
           (implies (4vp x)
                    (equal (4v-fix x) x))))
  (local (in-theory (e/d* ()
                         (4v-env-equiv-to-key-and-env-equiv
                          4vp default-car default-cdr 4v-fix
                          (:rules-of-class :type-prescription :here)
                          not hons-assoc-equal member-equal
                          subsetp-car-member
                          no-duplicatesp-equal
                          alist-keys-when-atom
                          4v-alistp
                          ))))
  (defthm 4v-alistp-with-same-keys-equal
    (implies (and (4v-alistp a) (4v-alistp b)
                  (equal (alist-keys a) (alist-keys b))
                  (no-duplicatesp-equal (alist-keys a)))
             (equal (4v-env-equiv a b)
                    (equal a b)))
    :hints (("goal"
             :in-theory (enable pairlis$)
             :induct (pairlis$ a b)
             :expand ((:free (k) (hons-assoc-equal k a))
                      (:free (k) (hons-assoc-equal k b))
                      (alist-keys a) (alist-keys b)
                      (4v-alistp a) (4v-alistp b)
                      (:free (a b) (no-duplicatesp-equal (cons a b))))
             :do-not-induct t)
            (and stable-under-simplificationp
                 '(:use ((:instance 4v-env-equiv-necc
                                    (key (caar a)) (x a) (y b)))))
            (witness :ruleset (4v-env-equiv-witnessing
                               4v-env-equiv-4v-lookup-ex
                               4v-env-equiv-hons-assoc-equal-ex))
            (and stable-under-simplificationp
                 '(:in-theory
                   (enable hons-assoc-equal-when-not-member-alist-keys)))
            )
    :rule-classes nil))

(defthm 4v-alistp-4v-alist-extract
  (4v-alistp (4v-alist-extract a b)))


(defthm esim-least-fixpoint-unique-to-equality
  (implies (and (all-fixpoints-greater mod fixpoint1 st-al)
                (all-fixpoints-greater mod fixpoint2 st-al)
                (esim-fixpoint-p mod fixpoint1 st-al)
                (esim-fixpoint-p mod fixpoint2 st-al)
                (4v-alists-agree (pat-flatten1 (gpl :i mod)) fixpoint1 fixpoint2)
                (4v-alistp fixpoint1) (4v-alistp fixpoint2)
                (equal (alist-keys fixpoint1) (alist-keys fixpoint2))
                (no-duplicatesp-equal (alist-keys fixpoint1)))
           (equal fixpoint1 fixpoint2))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable esim-fixpoint-p)
           :use (esim-least-fixpoint-unique
                 (:instance 4v-alistp-with-same-keys-equal
                            (a fixpoint1) (b fixpoint2)))))
  :rule-classes nil)



(defchoose esim-least-fixpoint (lfp) (mod sig-al st-al)
  (and (4v-alists-agree (pat-flatten1 (gpl :i mod)) lfp sig-al)
       (esim-fixpoint-p mod lfp st-al)
       (all-fixpoints-greater mod lfp st-al)
       (4v-alistp lfp)
       (equal (alist-keys lfp)
              (append (pat-flatten1 (gpl :i mod))
                      (esim-driven-signals mod)))))

(defthm 4v-alists-agree-remove-4v-alist-extract
  (implies (subsetp-equal keys keys1)
           (iff (4v-alists-agree keys (4v-alist-extract keys1 al1) al2)
                (4v-alists-agree keys al1 al2)))
  :hints(("Goal" :in-theory (disable 4v-fix))))

(defun hons-assoc-equal-4v-pat-alist-translate-ind (op np al acc)
  (if op
      (if (atom op)
          (list np acc)
        (list (hons-assoc-equal-4v-pat-alist-translate-ind
               (cdr op) (cdr np) al acc)
              (hons-assoc-equal-4v-pat-alist-translate-ind
               (car op) (car np) al
               (4v-pat-alist-translate
                (cdr op) (cdr np) al nil))
              (hons-assoc-equal-4v-pat-alist-translate-ind
               (car op) (car np) al
               (4v-pat-alist-translate
                (cdr op) (cdr np) al acc))))
    acc))

(defthm 4v-pat-alist-translate-to-append
  (implies (syntaxp (not (equal acc ''nil)))
           (equal (4v-pat-alist-translate op np al acc)
                  (append (4v-pat-alist-translate
                           op np al nil)
                          acc)))
  :hints (("goal" :induct (hons-assoc-equal-4v-pat-alist-translate-ind
                           op np al acc))))

(defthmd 4v-pat-alist-translate-when-4v-alists-agree
  (implies (and (similar-patternsp (double-rewrite a)
                                   (double-rewrite b))
                (4v-alists-agree (pat-flatten1 a) al1 al2))
           (equal (4v-pat-alist-translate a b al1 nil)
                  (4v-pat-alist-translate a b al2 nil)))
  :hints (("goal"
           :induct (4v-pat-alist-translate a b al1 nil)
           :in-theory (disable* 4v-fix similar-patternsp-commutes
                                4v-alists-agree-commute
                                4v-alists-agree default-car default-cdr
                                consp-of-hons-assoc-equal
                                hons-assoc-equal
                                member-equal not
                                (:definition 4v-pat-alist-translate)
                                (:rules-of-class :type-prescription :here))
          :expand ((4v-alists-agree (list a) al1 al2)
                   (:free (al acc) (4v-pat-alist-translate a b al acc))
                   (:free (al acc) (4v-pat-alist-translate nil nil al acc)))
          :do-not-induct t)))

(defthmd 4v-pat-alist-translate-when-4v-alists-agree-rw
  (implies (and (similar-patternsp (double-rewrite a)
                                   (double-rewrite b))
                (4v-alists-agree (pat-flatten1 a) al1 al2))
           (equal (equal (4v-pat-alist-translate a b al1 nil)
                         (4v-pat-alist-translate a b al2 nil))
                  t))
  :hints(("Goal" :in-theory (enable 4v-pat-alist-translate-when-4v-alists-agree))))

(defthmd esim-occ-when-4v-alists-agree
  (implies (and (good-esim-occp occ)
                (4v-alists-agree (pat-flatten1 (gpl :i occ))
                                 sig-al1 sig-al2)
                (4v-alists-agree (pat-flatten1 (gpl :o occ))
                                 sig-al1 sig-al2))
           (iff (4v-env-equiv sig-al1
                              (esim-occ occ sig-al1 st-al))
                (4v-env-equiv sig-al2
                              (esim-occ occ sig-al2 st-al))))
  :hints(("Goal" :in-theory (disable* esim-out 4v-fix good-esim-occp
                                     4v-pat-alist-translate
                                     member-equal default-car default-cdr
                                     (:rules-of-class :type-prescription :here))
          :expand ((:free (sig-al)
                          (esim-occ occ sig-al st-al)))
          :use ((:instance 4v-pat-alist-translate-when-4v-alists-agree-rw
                           (a (gpl :i occ))
                           (b (gpl :i (gpl :op occ)))
                           (al1 sig-al1)
                           (al2 sig-al2))))
         (witness :ruleset (4v-env-equiv-witnessing
                            4v-env-equiv-4v-lookup-ex
                            4v-alists-agree-4v-lookup-ex))))


(defthmd 4v-alists-agree-lookups-equal
  (implies (and (4v-alists-agree keys a b)
                (member-equal k keys))
           (equal (equal (4v-lookup k a)
                         (4v-lookup k b))
                  t)))

(defthmd 4v-alists-agree-subset
  (implies (and (4v-alists-agree keys1 a b)
                (subsetp-equal keys keys1))
           (4v-alists-agree keys a b))
  :hints (("goal" :induct (len keys)
           :in-theory (e/d (subsetp-equal 4v-alists-agree-lookups-equal)
                           (4v-fix 4v-lookup)))))

(defthm occ-inputs-subset-of-all-signals1
  (implies (and (subsetp-equal (collect-signal-list
                                :i (alist-vals (fal-extract occs (occmap mod))))
                               sigs)
                (member-equal occ occs))
           (subsetp-equal (pat-flatten1 (gpl :i (esim-get-occ occ mod)))
                          sigs))
  :hints(("Goal" :in-theory (enable fal-extract))))

(defthm occ-outputs-subset-of-driven-signals1
  (implies (member-equal occ occs)
           (subsetp-equal (pat-flatten1 (gpl :o (esim-get-occ occ mod)))
                          (collect-signal-list
                                :o (alist-vals (fal-extract occs (occmap mod))))))
  :hints(("Goal" :in-theory (enable fal-extract))))


(defthm occ-inputs-subset-of-all-signals
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod)))
           (subsetp-equal (pat-flatten1 (gpl :i (esim-get-occ occ mod)))
                          (append (pat-flatten1 (gpl :i mod))
                                  (esim-driven-signals mod))))
  :hints(("Goal" :in-theory (enable good-esim-modulep)
          :expand ((good-esim-modulep mod)))
         (and stable-under-simplificationp
              '(:cases ((member-equal occ (alist-keys (occmap mod))))))
         (and stable-under-simplificationp
              '(:in-theory (enable occmap)))))

(defthm occ-outputs-subset-of-driven-signals
  (subsetp-equal (pat-flatten1 (gpl :o (esim-get-occ occ mod)))
                 (esim-driven-signals mod))
  :hints(("Goal" :in-theory (enable good-esim-modulep)
          :expand ((good-esim-modulep mod)))
         (and stable-under-simplificationp
              '(:cases ((member-equal occ (alist-keys (occmap mod))))))))

(defthmd esim-fixpoint-p-occs-when-4v-alists-agree
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod))
                (4v-alists-agree (append (pat-flatten1 (gpl :i mod))
                                         (esim-driven-signals mod))
                                 sig-al1 sig-al2))
           (equal (equal (esim-fixpoint-p-occs mod occs sig-al1 st-al)
                         (esim-fixpoint-p-occs mod occs sig-al2 st-al))
                  t))
  :hints(("Goal" :in-theory (e/d (4v-alists-agree-subset)
                                 (esim-occ
                                  good-esim-occp
                                  good-esim-modulep
                                  esim-fixpoint-p
                                  esim-wf-signals
                                  4v-alists-agree
                                  esim-fixpoint-p-occs
                                  4v-env-equiv-to-key-and-env-equiv
                                  4v-alists-agree-append))
          :expand ((:free (sig-al) (esim-fixpoint-p-occs mod occs sig-al st-al)))
          :induct (len occs))
         (and stable-under-simplificationp
              '(:cases ((hons-assoc-equal (car occs) (occmap mod)))))
         (and stable-under-simplificationp
              '(:use ((:instance esim-occ-when-4v-alists-agree
                                 (occ (esim-get-occ (car occs) mod))))))))

(defthmd esim-fixpoint-p-when-4v-alists-agree
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod))
                (4v-alists-agree (append (pat-flatten1 (gpl :i mod))
                                         (esim-driven-signals mod))
                                 sig-al1 sig-al2))
           (equal (equal (esim-fixpoint-p mod sig-al1 st-al)
                         (esim-fixpoint-p mod sig-al2 st-al))
                  t))
  :hints(("Goal" :in-theory
          (enable esim-fixpoint-p-occs-when-4v-alists-agree))))

(defthm 4v-alist-<=-4v-alist-extract
  (4v-alist-<= (4v-alist-extract keys al) al)
  :hints ((witness :ruleset 4v-alist-<=-witnessing)))

(defthm all-fixpoints-greater-4v-alist-extract
  (implies (and (all-fixpoints-greater mod sig-al st-al)
                (subsetp-equal (pat-flatten1 (gpl :i mod))
                               keys))
           (all-fixpoints-greater
            mod (4v-alist-extract keys sig-al) st-al))
  :hints (("goal" :do-not-induct t
           :in-theory (e/d (4v-alist-<=-trans2)
                           (good-esim-modulep
                            esim-fixpoint-p)))
          (witness :ruleset (all-fixpoints-greater-witnessing
                             all-fixpoints-greater-fixpoint-ex))))


(defthm esim-fixpoint-p-4v-alist-extract
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod)))
           (equal (esim-fixpoint-p
                   mod (4v-alist-extract
                        (append (pat-flatten1 (gpl :i mod))
                                (esim-driven-signals mod))
                        sig-al) st-al)
                  (esim-fixpoint-p
                   mod sig-al st-al)))
  :hints(("Goal" :in-theory (e/d (esim-fixpoint-p-when-4v-alists-agree)
                                 (esim-fixpoint-p)))))

(defthm least-fixpointp-esim-least-fixpoint
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod))
                (subsetp-equal (alist-keys sig-al)
                               (pat-flatten1 (gpl :i mod))))
           (let ((lfp (esim-least-fixpoint mod sig-al st-al)))
             (and (4v-alists-agree (pat-flatten1 (gpl :i mod))
                                   lfp sig-al)
                  (esim-fixpoint-p mod lfp st-al)
                  (all-fixpoints-greater mod lfp st-al)
                  (4v-alistp lfp)
                  (equal (alist-keys lfp)
                         (append (pat-flatten1 (gpl :i mod))
                                 (esim-driven-signals mod))))))
  :hints (("goal" :use ((:instance esim-least-fixpoint
                                   (lfp (4v-alist-extract
                                         (append (pat-flatten1 (gpl :i mod))
                                                 (esim-driven-signals mod))
                                         (esim-fixpoint mod sig-al st-al)))))
           :in-theory (disable esim-fixpoint esim-fixpoint-p
                               4v-alists-agree))))



(defthm extract-of-esim-fixpoint-equiv-esim-least-fixpoint
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod))
                (subsetp-equal (alist-keys sig-al)
                               (pat-flatten1 (gpl :i mod))))
           (equal (esim-least-fixpoint mod sig-al st-al)
                  (4v-alist-extract (append (pat-flatten1 (gpl :i mod))
                                            (esim-driven-signals mod))
                                    (esim-fixpoint mod sig-al st-al))))
  :hints (("goal" :use
           ((:instance
             esim-least-fixpoint-unique-to-equality
             (fixpoint1
              (4v-alist-extract (append (pat-flatten1 (gpl :i mod))
                                        (esim-driven-signals mod))
                                (esim-fixpoint mod sig-al
                                               st-al)))
             (fixpoint2 (esim-least-fixpoint mod sig-al st-al)))
            (:instance least-fixpointp-esim-least-fixpoint))

           :in-theory (e/d (4v-alists-agree-trans1
                            4v-alists-agree-commute
                            good-esim-modulep)
                           (esim-fixpoint
                            esim-fixpoint-p
                            no-duplicatesp-equal-non-cons
                            no-duplicatesp-equal
                            4v-alist-extract
                            member-equal
                            collect-signal-list
                            append
                            least-fixpointp-esim-least-fixpoint
                            4v-alists-agree)))))

;; (defthm esim-fixpoint-and-esim-least-fixpoint-keys-equiv
;;   (implies (and (good-esim-modulep mod)
;;                 (set-equiv (alist-keys sig-al)
;;                             (pat-flatten (gpl :i mod) nil)))
;;            (set-equiv (alist-keys (mv-nth 1 (esim-fixpoint mod sig-al st-al)))
;;                        (alist-keys (esim-least-fixpoint mod sig-al st-al)))))

;; (defthm esim-fixpoint-equiv-esim-least-fixpoint
;;   (implies (and (good-esim-modulep mod)
;;                 (set-equiv (alist-keys sig-al)
;;                             (pat-flatten (gpl :i mod) nil)))
;;            (key-and-env-equiv (mv-nth 1 (esim-fixpoint mod sig-al st-al))
;;                               (esim-least-fixpoint mod sig-al st-al)))
;;   :hints (("goal" :use ((:instance esim-least-fixpoint-unique
;;                                    (fixpoint1 (mv-nth 1 (esim-fixpoint mod
;;                                                                        sig-al
;;                                                                        st-al)))
;;                                    (fixpoint2 (esim-least-fixpoint mod sig-al
;;                                                                    st-al)))
;;                         (:instance least-fixpointp-esim-least-fixpoint))
;;            :in-theory (e/d (4v-alists-agree-trans1
;;                             4v-alists-agree-commute
;;                             key-and-env-equiv)
;;                            (least-fixpointp-esim-least-fixpoint
;;                             esim-fixpoint-p
;;                             4v-alists-agree
;;                             esim-fixpoint-sig-al-signals
;;                             4v-env-equiv-to-key-and-env-equiv)))))



;; (defun esim-fixpoint-nst-occ (occ sig-al st-al nst-al)
;;   (b* ((i  (gpl :i occ))
;;        (op (gpl :op occ))
;;        (iop (gpl :i op))
;;        (inal (4v-pat-alist-translate i iop sig-al nil))
;;        (stal (4v-pat-alist-translate (occ-state occ) (mod-state op) st-al nil))
;;        ((mv sa &) (esim op inal stal))
;;        (nst-al (4v-pat-alist-translate (mod-state op) (occ-state occ) sa nst-al)))
;;     nst-al))

;; (defthm esim-fixpoint-nst-occ-is-esim-occ
;;   (equal (esim-fixpoint-nst-occ occ sig-al st-al nst-al)
;;          (mv-nth 0 (esim-occ occ sig-al st-al nst-al nil)))
;;   :hints (("goal" :expand ((esim-occ occ sig-al st-al nst-al nil))
;;            :in-theory (disable esim))))

;; (defun esim-fixpoint-nst-occs (mod occs sig-al st-al nst-al)
;;   (if (or (atom occs)
;;           (not (mbt (and (gpl :occs mod) t))))
;;       nst-al
;;     (b* ((nst-al
;;           (esim-fixpoint-nst-occ (esim-get-occ (car occs) mod)
;;                                  sig-al st-al nst-al)))
;;       (esim-fixpoint-nst-occs mod (cdr occs) sig-al st-al nst-al))))

;; (defthm esim-fixpoint-nst-occs-is-esim-occs-when-fixpoint
;;   (implies (esim-fixpoint-p mod sig-al st-al)
;;            (4v-env-equiv (mv-nth 0 (esim-occs mod occs sig-al st-al nst-al internal-al))
;;                          (esim-fixpoint-nst-occs mod occs sig-al st-al
;;                                                  nst-al)))
;;   :hints (("goal" :induct t
;;            :in-theory (disable good-esim-modulep esim-occ)
;;            :expand (esim-occs mod occs sig-al st-al nst-al nil))))

;; (defun esim-fixpoint-internal-occ (occ sig-al st-al internal-al)
;;   (b* ((i  (gpl :i occ))
;;        (op (gpl :op occ))
;;        (iop (gpl :i op))
;;        (inal (4v-pat-alist-translate i iop sig-al nil))
;;        (stal (4v-pat-alist-translate (occ-state occ) (mod-state op) st-al nil))
;;        ((mv & ia) (esim op inal stal))
;;        (internal-al (4v-pat-alist-translate (mod-internals op)
;;                                             (occ-internals occ) ia internal-al)))
;;     internal-al))

;; (defthm esim-fixpoint-internal-occ-is-esim-occ
;;   (equal (esim-fixpoint-internal-occ occ sig-al st-al internal-al)
;;          (mv-nth 2 (esim-occ occ sig-al st-al nil internal-al)))
;;   :hints (("goal" :expand ((esim-occ occ sig-al st-al nil internal-al))
;;            :in-theory (disable esim))))

;; (defthm alist-keys-esim-fixpoint-internal-occ
;;   (equal (alist-keys (esim-fixpoint-internal-occ occ sig-al st-al internal-al))
;;          (append (pat-flatten (occ-internals occ) nil)
;;                  (alist-keys internal-al))))

;; (defun esim-fixpoint-internal-occs (mod occs sig-al st-al internal-al)
;;   (if (or (atom occs)
;;           (not (mbt (and (gpl :occs mod) t))))
;;       internal-al
;;     (b* ((internal-al
;;           (esim-fixpoint-internal-occ (esim-get-occ (car occs) mod)
;;                                  sig-al st-al internal-al)))
;;       (esim-fixpoint-internal-occs mod (cdr occs) sig-al st-al internal-al))))

;; (defthm esim-fixpoint-internal-occs-is-esim-occs-when-fixpoint
;;   (implies (esim-fixpoint-p mod sig-al st-al)
;;            (4v-env-equiv (mv-nth 2 (esim-occs mod occs sig-al st-al nst-al internal-al))
;;                          (esim-fixpoint-internal-occs mod occs sig-al st-al
;;                                                  internal-al)))
;;   :hints (("goal" :induct t
;;            :in-theory (disable good-esim-modulep esim-occ)
;;            :expand (esim-occs mod occs sig-al st-al nil internal-al))))

;; (defthm alist-keys-esim-fixpoint-internal-occs
;;   (equal (alist-keys (esim-fixpoint-internal-occs mod occs sig-al st-al
;;                                                   internal-al))
;;          (append (collect-occ-internals mod occs)
;;                  (alist-keys internal-al)))
;;   :hints(("Goal" :in-theory (enable occmap-when-no-occs))))


;; (defthm esim-fixpoint-mv-thm
;;   (equal (esim-fixpoint mod sig-al st-al)
;;          (list (mv-nth 0 (esim-fixpoint mod sig-al st-al))
;;                (mv-nth 1 (esim-fixpoint mod sig-al st-al))
;;                (mv-nth 2 (esim-fixpoint mod sig-al st-al))))
;;   :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al)
;;            :in-theory (disable good-esim-modulep
;;                                esim-fixpoint)
;;            :expand ((esim-fixpoint mod sig-al st-al))))
;;   :rule-classes nil)

;; (defthm esim-fixpoint-of-self
;;   (implies (and (good-esim-modulep mod)
;;                 (subsetp-equal (alist-keys sig-al)
;;                                (pat-flatten (gpl :i mod) nil)))
;;            (4v-env-equiv
;;             (mv-nth 1 (esim-fixpoint
;;                        mod (mv-nth 1 (esim-fixpoint mod sig-al st-al))
;;                        st-al))
;;             (mv-nth 1 (esim-fixpoint mod sig-al st-al)))))


;; (defthm esim-fixpoint-nst-of-self
;;   (implies (and (good-esim-modulep mod)
;;                 (esim-wf-signals mod (alist-keys (occmap mod))
;;                                  sig-al st-al))
;;            (4v-env-equiv
;;             (mv-nth 0 (esim-fixpoint
;;                        mod (mv-nth 1 (esim-fixpoint mod sig-al st-al)) st-al))
;;             (mv-nth 0 (esim-fixpoint mod sig-al st-al))))
;;   :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al)
;;            :in-theory (disable esim-fixpoint-p
;;                                esim-wf-signals
;;                                esim-occs
;;                                good-esim-modulep
;;                                esim-fixpoint-p-occs))))


;; (defthm esim-fixpoint-internal-of-self
;;   (implies (and (good-esim-modulep mod)
;;                 (esim-wf-signals mod (alist-keys (occmap mod))
;;                                  sig-al st-al))
;;            (4v-env-equiv
;;             (mv-nth 2 (esim-fixpoint
;;                        mod (mv-nth 1 (esim-fixpoint mod sig-al st-al)) st-al))
;;             (mv-nth 2 (esim-fixpoint mod sig-al st-al))))
;;   :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al)
;;            :in-theory (disable esim-fixpoint-p
;;                                esim-wf-signals
;;                                esim-occs
;;                                good-esim-modulep
;;                                esim-fixpoint-p-occs))))


(defthm 4v-alist-extract-subset
  (implies (subsetp-equal keys keys1)
           (equal (4v-alist-extract keys (4v-alist-extract keys1 al))
                  (4v-alist-extract keys al))))

(defthm good-esim-modulep-outs-subset-of-driven
  (implies (and (good-esim-modulep mod)
                (not (gpl :x mod)))
           (subsetp-equal (pat-flatten1 (gpl :o mod))
                          (esim-driven-signals mod)))
  :hints(("Goal" :in-theory (enable good-esim-modulep))))


(defthm esim-out-in-terms-of-least-fixpoint
  (implies
   (good-esim-modulep mod)
   (equal
    (esim-out mod sig-al st-al)
    (b* ((sig-al (4v-alist-extract (pat-flatten1 (gpl :i mod)) sig-al))
         (st-al (4v-alist-extract (pat-flatten1 (mod-state mod)) st-al))
         ((when (gpl :x mod))
          (eapply-spec-out (append sig-al st-al)
                           (gpl :x mod)))
         (lfp (esim-least-fixpoint mod sig-al st-al)))
      (4v-alist-extract (pat-flatten1 (gpl :o mod)) lfp))))

  :hints(("Goal" :in-theory (disable eapply-spec good-esim-modulep
                                     ;; esim-fixpoint-nst-of-self
                                     ;; esim-fixpoint-internal-of-self
                                     esim-fixpoint-equiv-when-mod-fixpoint
                                     4v-env-equiv-append
                                     4v-alist-extract
                                     esim-occs esim-occs-input-alist-<=
                                     alist-keys-when-atom
                                     fal-extract
                                     collect-signal-list
                                     subsetp-when-atom-left
                                     hons-assoc-equal
                                     esim-wf-signals-impl-esim-occs-incr
                                     default-car default-cdr mod-internals
                                     4v-lookup
                                     4v-env-equiv-to-key-and-env-equiv))))


;; (defthm esim-in-terms-of-least-fixpoint
;;   (implies
;;    (good-esim-modulep mod)
;;    (nth-4v-env-equiv
;;     (esim mod sig-al st-al)
;;     (b* ((sig-al (4v-alist-extract (pat-flatten (gpl :i mod) nil) sig-al))
;;          (st-al (4v-alist-extract (pat-flatten (mod-state mod) nil) st-al)))
;;       (if (gpl :occs mod)
;;           (let* ((lfp (esim-least-fixpoint mod sig-al st-al))
;;                  (nst (esim-fixpoint-nst-occs
;;                        mod (alist-keys (occmap mod)) lfp st-al nil))
;;                  (int (esim-fixpoint-internal-occs
;;                        mod (alist-keys (occmap mod)) lfp st-al nil)))
;;             (mv nst (append lfp int)))
;;         (mv-let (nst out)
;;           (eapply-spec sig-al st-al
;;                        (gpl :i mod)
;;                        (gpl :s mod)
;;                        (gpl :o mod)
;;                        (gpl :x mod))
;;           (mv nst (append sig-al out)))))))
;;   :hints(("Goal" :in-theory (disable eapply-spec good-esim-modulep
;;                                      esim-fixpoint-nst-of-self
;;                                      esim-fixpoint-internal-of-self
;;                                      esim-fixpoint-equiv-when-mod-fixpoint
;;                                      4v-env-equiv-append
;;                                      4v-alist-extract
;;                                      esim-occs esim-occs-input-alist-<=
;;                                      pat-flatten-is-append
;;                                      alist-keys-when-atom
;;                                      fal-extract
;;                                      collect-signal-list
;;                                      subsetp-when-atom-left
;;                                      hons-assoc-equal
;;                                      esim-wf-signals-impl-esim-occs-incr
;;                                      default-car default-cdr pat-flatten mod-internals
;;                                      4v-lookup
;;                                      4v-env-equiv-to-key-and-env-equiv))
;;          (let ((sig-al '(4v-alist-extract
;;                          (pat-flatten (gpl :i mod) nil)
;;                          sig-al))
;;                (st-al '(4v-alist-extract
;;                         (pat-flatten (mod-state mod) nil)
;;                         st-al)))
;;            `(:use ((:instance esim-fixpoint-mv-thm
;;                               (sig-al ,sig-al)
;;                               (st-al ,st-al))
;;                    (:instance esim-fixpoint-nst-of-self
;;                               (sig-al ,sig-al)
;;                               (st-al ,st-al))
;;                    (:instance esim-fixpoint-internal-of-self
;;                               (sig-al ,sig-al)
;;                               (st-al ,st-al))
;;                    (:instance 4v-env-equiv-append
;;                               (a (MV-NTH 2 (ESIM-FIXPOINT MOD ,sig-al ,st-al)))
;;                               (c (ESIM-LEAST-FIXPOINT
;;                                   MOD ,sig-al ,st-al))
;;                               (b (ESIM-FIXPOINT-INTERNAL-OCCS
;;                                   MOD (ALIST-KEYS (OCCMAP MOD))
;;                                   (ESIM-LEAST-FIXPOINT
;;                                    MOD ,sig-al ,st-al)
;;                                   ,st-al NIL))
;;                               (d (ESIM-LEAST-FIXPOINT MOD ,sig-al ,st-al))))
;;              :expand
;;              ((esim mod sig-al st-al)
;;               (esim-fixpoint
;;                mod (esim-least-fixpoint
;;                     mod ,sig-al ,st-al)
;;                ,st-al)))))
;;   :rule-classes ((:definition :install-body nil))
;;   :otf-flg t)

;; (defthm 4v-alist-extract-append
;;   (equal (4v-alist-extract (append a b) al)
;;          (append (4v-alist-extract a al)
;;                  (4v-alist-extract b al))))






;; (defthm 4v-alists-agree-4v-alist-extract
;;   (implies (subsetp-equal keys keys1)
;;            (4v-alists-agree keys (4v-alist-extract keys1 al) al))
;;   :hints (("goal" :induct (len keys))))

;; (defthm 4v-pat-alist-translate-of-4v-alist-extract
;;   (implies (similar-patternsp (double-rewrite old-pat)
;;                               (double-rewrite new-pat))
;;            (equal (4v-pat-alist-translate
;;                    old-pat new-pat
;;                    (4v-alist-extract (pat-flatten old-pat nil) al)
;;                    acc)
;;                   (4v-pat-alist-translate old-pat new-pat al acc)))
;;   :hints(("Goal" :in-theory (enable 4v-pat-alist-translate-when-4v-alists-agree-rw))))


;; (defthm esim-occ-internals-agree-on-outs
;;   (implies (and (good-esim-occp occ)
;;                 (member-equal k (pat-flatten (gpl :o occ) nil)))
;;            (mv-let (nst sig-al1 int1)
;;              (esim-occ occ sig-al st-al nst-al int-al)
;;              (declare (ignore nst))
;;              (equal (hons-assoc-equal k (append sig-al1 int1))
;;                     (hons-assoc-equal k sig-al1))))
;;   :hints(("Goal" :in-theory (disable esim
;;                                      esim-in-terms-of-least-fixpoint)
;;           :expand ((:free (nst-al int-al)
;;                           (esim-occ occ sig-al st-al nst-al int-al))))))


;; (flag::make-flag esim-flag esim)

;; (mutual-recursion
;;  (defun good-esim-modulep (x)
;;    (declare (xargs :guard t
;;                    :well-founded-relation nat-list-<
;;                    :measure (list (acl2-count x) 1)))
;;    (or (not (gpl :occs x))
;;        (and (not (hons-intersect-p (pat-flatten (gpl :o x) nil)
;;                                    (pat-flatten (mod-internals x) nil)))
;;             (good-esim-occsp (gpl :occs x)))))

;;  (defun good-esim-occsp (x)
;;    (declare (xargs :guard t
;;                    :measure (list (acl2-count x) 2)))
;;    (or (atom x)
;;        (and (good-esim-occp (car x))
;;             (good-esim-occsp (cdr x)))))

;;  (defun good-esim-occp (x)
;;    (declare (xargs :guard t
;;                    :measure (list (acl2-count x) 2)))
;;    (good-esim-modulep (gpl :op x))))

;; (defun nonnil-atom-listp (x)
;;   (if (atom x)
;;       (eq x nil)
;;     (and (atom (car x))
;;          (car x)
;;          (nonnil-atom-listp (cdr x)))))

;; (defthm pat-flatten-of-nonnil-atom-listp
;;   (implies (nonnil-atom-listp x)
;;            (equal (pat-flatten x nil) x)))

;; (defthm nonnil-atom-listp-pat-flatten
;;   (nonnil-atom-listp (pat-flatten x nil)))

;; (defthm nonnil-atom-listp-append
;;   (implies (and (nonnil-atom-listp x)
;;                 (nonnil-atom-listp y))
;;            (nonnil-atom-listp (append x y))))

;; (defthm nonnil-atom-listp-collect-signal-list
;;   (nonnil-atom-listp (collect-signal-list k occs)))

;; (defthm nonnil-atom-listp-set-difference-equal
;;   (implies (nonnil-atom-listp x)
;;            (nonnil-atom-listp (set-difference-equal x y)))
;;   :hints(("Goal" :in-theory (enable set-difference-equal))))

;; (defthm hons-set-diff2-is-set-difference-equal
;;   (equal (hons-set-diff2 x y)
;;          (set-difference-equal x y))
;;   :hints(("Goal" :in-theory (enable set-difference-equal))))

;; (defthm hons-sd1-is-set-difference-equal
;;   (equal (hons-sd1 x y)
;;          (set-difference-equal x (alist-keys y)))
;;   :hints(("Goal" :in-theory (enable set-difference-equal))))


;; (defcong set-equiv equal (set-difference-equal x y) 2
;;   :hints(("Goal" :in-theory (enable set-difference-equal))))

;; (defthm hons-set-diff-is-set-difference-equal
;;   (equal (hons-set-diff x y)
;;          (set-difference-equal x y)))


;; (defun esim-occs-ind (mod occs sig-al st-al nst-al)
;;   (if (or (atom occs)
;;           (not (mbt (and (gpl :occs mod) t))))
;;       (mv nst-al sig-al)
;;     (b* (((mv nst-al sig-al)
;;           (esim-occ (esim-get-occ (car occs) mod)
;;                     sig-al st-al nst-al)))
;;       (esim-occs-ind mod (cdr occs) sig-al st-al nst-al))))

;; (defthmd esim-occs-mv-thm
;;   (equal (equal (esim-occs mod occs sig-al st-al nst-al)
;;                 (list (mv-nth 0 (esim-occs mod occs sig-al st-al nst-al))
;;                       (mv-nth 1 (esim-occs mod occs sig-al st-al nst-al))))
;;          t)
;;   :hints (("goal" :induct (esim-occs-ind mod occs sig-al st-al nst-al))))

;; (defun esim-fixpoint-ind (mod sig-al st-al)
;;   (declare (xargs :measure (esim-alist-lattice-height-measure
;;                             (esim-driven-signals mod)
;;                             sig-al)))
;;   (b* ((occnames (alist-keys (make-fast-alist (occmap mod))))
;;        ((mv nst-al sig-al1)
;;         (esim-occs mod occnames sig-al st-al nil))
;;        (sig-al (make-fast-alist sig-al))
;;        (fixed (4v-alist-<=-keys (esim-driven-signals mod)
;;                                 sig-al1 sig-al))
;;        ((unless (and (not fixed)
;;                      (mbt (4v-alist-<= sig-al sig-al1))))
;;         (fast-alist-free sig-al)
;;         (mv nst-al sig-al1)))
;;     (fast-alist-free sig-al)
;;     (fast-alist-free nst-al)
;;     (esim-fixpoint-ind mod sig-al1 st-al)))

;; (defthmd esim-fixpoint-mv-thm
;;   (equal (equal (esim-fixpoint mod sig-al st-al)
;;                 (list (mv-nth 0 (esim-fixpoint mod sig-al st-al))
;;                       (mv-nth 1 (esim-fixpoint mod sig-al st-al))))
;;          t)
;;   :hints (("goal" :induct (esim-fixpoint-ind mod sig-al st-al))))


;; (defthmd 4v-alist-extract-when-agree
;;   (implies (4v-alists-agree keys a b)
;;            (equal (equal (4v-alist-extract keys a)
;;                          (4v-alist-extract keys b))
;;                   t)))

;; (defthm 4v-alists-agree-cons-when-first-not-member
;;   (implies (not (member-equal k keys))
;;            (4v-alists-agree keys (cons (cons k v) a) a)))

;; (defthm 4v-alists-agree-append-when-first-not-intersecting
;;   (implies (not (intersectp-equal (double-rewrite (alist-keys a))
;;                                   (double-rewrite keys)))
;;            (4v-alists-agree keys (append a b) b))
;;   :hints(("Goal" :in-theory (enable intersectp-equal))))

;; (defthm 4v-alist-extract-append-when-first-not-intersecting
;;   (implies (not (intersectp-equal (double-rewrite (alist-keys a))
;;                                   (double-rewrite keys)))
;;            (equal (4v-alist-extract keys (append a b))
;;                   (4v-alist-extract keys b)))
;;   :hints(("Goal" :in-theory (enable 4v-alist-extract-when-agree))))

;; (defthm 4v-alists-agree-append-when-first-covers
;;   (implies (subsetp-equal (double-rewrite keys)
;;                           (double-rewrite (alist-keys a)))
;;            (4v-alists-agree keys (append a b) a))
;;   :hints(("Goal" :in-theory (enable subsetp-equal))))

;; (defthm 4v-alist-extract-append-when-first-covers
;;   (implies (subsetp-equal (double-rewrite keys)
;;                           (double-rewrite (alist-keys a)))
;;            (equal (4v-alist-extract keys (append a b))
;;                   (4v-alist-extract keys a)))
;;   :hints(("Goal" :in-theory (enable 4v-alist-extract-when-agree))))



;; (defthm good-esim-modulep-outputs-subset-of-driven
;;   (implies (and (good-esim-modulep mod)
;;                 (gpl :occs mod))
;;            (subsetp-equal (pat-flatten (gpl :o mod) nil)
;;                           (esim-driven-signals mod)))
;;   :hints(("Goal" :expand ((good-esim-modulep mod)))))



;; (defthm alist-keys-esim-occ
;;   (implies (good-esim-occp occ)
;;            (equal (alist-keys (mv-nth 1 (esim-occ occ sig-al st-al nst-al)))
;;                   (append (pat-flatten (gpl :o occ) nil)
;;                           (alist-keys sig-al))))
;;   :hints(("Goal" :in-theory (e/d () (esim good-esim-occp))
;;           :expand ((esim-occ occ sig-al st-al nst-al)))))

;; (defthm alist-keys-esim-occs
;;   (implies (good-esim-modulep mod)
;;            (equal (alist-keys (mv-nth 1 (esim-occs mod occs sig-al st-al
;;                                                    nst-al)))
;;                   (append (collect-signal-list
;;                            :o (rev (alist-vals (fal-extract occs (occmap mod)))))
;;                           (alist-keys sig-al))))
;;   :hints(("Goal" :in-theory (e/d (occmap1 fal-extract) (esim-occ good-esim-modulep))
;;           :induct (esim-occs-ind mod occs sig-al st-al nst-al))
;;          (and stable-under-simplificationp
;;               '(:expand ((occmap mod)
;;                          (esim-occ nil sig-al st-al nst-al))))))

;; (defthm alist-keys-esim-fixpoint
;;   (implies (good-esim-modulep mod)
;;            (set-equiv (alist-keys (mv-nth 1 (esim-fixpoint mod sig-al st-al)))
;;                        (append (alist-keys sig-al)
;;                                (esim-driven-signals mod))))
;;   :hints(("Goal" :in-theory (disable esim-occs good-esim-modulep)
;;           :induct (esim-fixpoint-ind mod sig-al st-al))
;;          (witness :ruleset set-reasoning-no-consp)))


;; (encapsulate nil
;;   (local (in-theory (disable esim esim-fixpoint esim-occs esim-occ
;;                              esim esim-fixpoint
;;                              esim-occs esim-occ
;;                              esim-in-terms-of-least-fixpoint
;;                              eapply-spec
;;                              hons-set-diff
;;                              good-esim-modulep
;;                              good-esim-occp)))

;;   (local (defthm equal-mv-list-2
;;            (implies (equal x (list (mv-nth 0 x) (mv-nth 1 x)))
;;                     (equal (equal x (list (mv-nth 0 y) (mv-nth 1 y)))
;;                            (and (equal (mv-nth 0 x) (mv-nth 0 y))
;;                                 (equal (mv-nth 1 x) (mv-nth 1 y)))))))

;;   (local (defthm equal-mv-list-3
;;            (implies (equal x (list (mv-nth 0 x) (mv-nth 1 x) (mv-nth 2 x)))
;;                     (equal (equal x (list (mv-nth 0 y) (mv-nth 1 y) (mv-nth 2 y)))
;;                            (and (equal (mv-nth 0 x) (mv-nth 0 y))
;;                                 (equal (mv-nth 1 x) (mv-nth 1 y))
;;                                 (equal (mv-nth 2 x) (mv-nth 2 y)))))))

;;   (local (defthm good-esim-modulep-in-and-out-not-intersecting
;;            (implies (good-esim-modulep mod)
;;                     (not (intersectp-equal (pat-flatten (gpl :i mod) nil)
;;                                            (pat-flatten (gpl :o mod) nil))))
;;            :hints(("Goal" :in-theory (enable good-esim-modulep)))))

;;   (defthm-esim-flag
;;     (defthm esim-in-terms-of-esim
;;       (implies (good-esim-modulep mod)
;;                (equal (esim mod ia sa)
;;                       (mv-let (nst int)
;;                         (esim mod ia sa)
;;                         (mv nst (4v-alist-extract (pat-flatten (gpl :o mod) nil)
;;                                                   int)))))
;;       :hints ('(:expand ((esim mod ia sa)
;;                          (esim mod ia sa))
;;                         :in-theory (enable esim-fixpoint-mv-thm)))
;;       :flag esim)

;;     (defthm esim-fixpoint-in-terms-of-esim-fixpoint
;;       (implies (good-esim-modulep mod)
;;                (equal (esim-fixpoint mod sig-al st-al)
;;                       (mv-let (nst sig-al1 int-al)
;;                         (esim-fixpoint mod sig-al st-al)
;;                         (declare (ignore int-al))
;;                         (mv nst sig-al1))))
;;       :hints ('(:expand ((esim-fixpoint mod sig-al st-al)
;;                          (esim-fixpoint mod sig-al st-al))
;;                         :in-theory (enable esim-occs-mv-thm)))
;;       :flag esim-fixpoint)

;;     (defthm esim-occs-in-terms-of-esim-occs
;;       (implies (and (good-esim-modulep mod))
;;                (equal (esim-occs mod occs sig-al st-al nst-al)
;;                       (mv-let (nst-al sig-al1 int-al)
;;                         (esim-occs mod occs sig-al st-al nst-al nil)
;;                         (declare (ignore int-al))
;;                         (mv nst-al sig-al1))))
;;       :hints ('(:expand ((esim-occs mod occs sig-al st-al nst-al)
;;                          (esim-occs mod occs sig-al st-al nst-al nil)
;;                          (esim-occ nil sig-al st-al nst-al)))
;;               (and stable-under-simplificationp
;;                    '(:cases ((hons-assoc-equal (car occs) (occmap mod))))))
;;       :flag esim-occs)

;;     (defthm esim-occ-in-terms-of-esim-occ
;;       (implies (and (good-esim-occp occ))
;;                (equal (esim-occ occ sig-al st-al nst-al)
;;                       (mv-let (nst-al sig-al1 int-al)
;;                         (esim-occ occ sig-al st-al nst-al nil)
;;                         (declare (ignore int-al))
;;                         (mv nst-al sig-al1))))
;;       :hints ('(:expand ((esim-occ occ sig-al st-al nst-al)
;;                          (esim-occ occ sig-al st-al nst-al nil))))
;;       :flag esim-occ)))

