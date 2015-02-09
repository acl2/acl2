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


; esim-sexpr-support-thms.lisp -- Mostly guard-related theorems about esim-faig
; supporting functions.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "esim-sexpr-support")
(include-book "local-theory")


(defthm true-listp-collect-signal-list
   (true-listp (collect-signal-list k occs)))





;; Theorems about occmap, occmap1

(defthm acl2-count-lookup-in-occmap1
  (<= (acl2-count (cdr (hons-assoc-equal x (occmap1 y))))
      (acl2-count y))
  :rule-classes :linear)

(defthm acl2-count-lookup-in-occmap-weak
  (<= (acl2-count (cdr (hons-assoc-equal x (occmap y))))
      (acl2-count y))
  :rule-classes :linear)

(defthm acl2-count-lookup-in-occmap-strong
  (implies (gpl :occs y)
           (< (acl2-count (cdr (hons-assoc-equal x (occmap y))))
              (acl2-count y)))
  :rule-classes :linear)


(defthm good-esim-occsp-good-occp-lookup-in-occmap1
  (implies (and (good-esim-occsp occs)
                (hons-assoc-equal u (occmap1 occs)))
           (good-esim-occp (cdr (hons-assoc-equal u (occmap1 occs))))))

(defthm good-esim-modulep-good-occp-lookup-in-occmap
  (implies (and (good-esim-modulep mod)
                (hons-assoc-equal u (occmap mod)))
           (good-esim-occp (cdr (hons-assoc-equal u (occmap mod)))))
  :hints(("Goal" :in-theory (enable good-esim-modulep))))




(defthm good-esim-probe-occsp-good-occp-lookup-in-occmap1
  (implies (and (good-esim-probe-occsp occs)
                (hons-assoc-equal u (occmap1 occs)))
           (good-esim-probe-occp (cdr (hons-assoc-equal u (occmap1 occs))))))

(defthm good-esim-probe-modulep-good-occp-lookup-in-occmap
  (implies (and (good-esim-probe-modulep mod)
                (hons-assoc-equal u (occmap mod)))
           (good-esim-probe-occp (cdr (hons-assoc-equal u (occmap mod))))))


(defthmd occmap-when-no-occs
  (implies (not (consp (gpl :occs mod)))
           (not (occmap mod)))
  :hints(("Goal" :in-theory (enable occmap occmap1)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)))

(defthm good-esim-probe-modulep-op
  (implies (good-esim-probe-occp occ)
           (good-esim-probe-modulep (gpl :op occ))))





(defthm prefix-pattern-similar-patternsp
  (similar-patternsp (prefix-pattern str sep s)
                     (double-rewrite s))
  :hints(("Goal" :in-theory (enable prefix-pattern))))

;; (defthm data-for-patternp-prefix-pattern
;;   (and (data-for-patternp s (prefix-pattern str sep s))
;;        (data-for-patternp (prefix-pattern str sep s) s))
;;   :hints(("Goal" :in-theory (enable prefix-pattern))))

;; (defthm similar-patternsp-prefix-pattern
;;   (and (similar-patternsp s (prefix-pattern str sep s))
;;        (similar-patternsp (prefix-pattern str sep s) s))
;;   :hints(("Goal" :in-theory (enable prefix-pattern))))


(defthm alist-keys-append
  (equal (alist-keys (append a b))
         (append (alist-keys a) (alist-keys b)))
  :hints(("Goal" :in-theory (enable alist-keys))))



(defthm nat-listp-append
  (implies (and (nat-listp a)
                (nat-listp b))
           (nat-listp (append a b))))



;; bozo put these where they belong

(defthm true-listp-prefix-pattern
  (implies (true-listp pat)
           (true-listp (prefix-pattern pre sep pat)))
  :rule-classes ((:rewrite) (:type-prescription))
  :hints(("Goal" :in-theory (enable prefix-atom prefix-pattern))))

(defthm len-of-prefix-pattern
  (equal (len (prefix-pattern pre sep x))
         (len x))
  :hints(("Goal" :in-theory (enable prefix-pattern))))




(defthm data-for-patternp-id
  (data-for-patternp x x))







(defthm collect-signal-list-append
  (equal (collect-signal-list k (append a b))
         (append (collect-signal-list k a)
                 (collect-signal-list k b))))


(defthm member-equal-rev
  (iff (member-equal k (rev x))
       (member-equal k x))
  :hints(("Goal" :in-theory (enable rev))))

(defthm set-equiv-rev
  (set-equiv (rev x) x)
  :hints ((witness)))


(defun collect-signal-list-member-witness (x key vals)
  (if (atom vals)
      nil
    (if (member-equal x (pat-flatten1 (gpl key (car vals))))
        (car vals)
      (collect-signal-list-member-witness x key (cdr vals)))))

(defthmd collect-signal-list-witness-correct
  (iff (member-equal x (collect-signal-list key vals))
       (let ((val (collect-signal-list-member-witness x key vals)))
         (and (member-equal val vals)
              (member-equal x (pat-flatten1 (gpl key val)))))))

(defthm collect-signal-list-member
  (implies (and (member-equal x (pat-flatten1 (gpl key val)))
                (member-equal val vals))
           (member-equal x (collect-signal-list key vals))))

(defwitness collect-signal-list-member-witnessing
  :predicate (member-equal x (collect-signal-list key vals))
  :expr (let ((val (collect-signal-list-member-witness x key vals)))
          (and (member-equal val vals)
               (member-equal x (pat-flatten1 (gpl key val)))))
  :generalize (((collect-signal-list-member-witness x key vals) . val))
  :hints ('(:in-theory (e/d (collect-signal-list-witness-correct)
                            (collect-signal-list-member-witness
                             collect-signal-list member-equal pat-flatten gpl)))))

(defcong set-equiv set-equiv (collect-signal-list key vals) 2
  :hints (("goal" :do-not-induct t)
          (witness :ruleset set-equiv-witnessing)
          (witness :ruleset collect-signal-list-member-witnessing)))


(defthm no-duplicatesp-equal-collect-signal-list-rev
  (iff (no-duplicatesp-equal (collect-signal-list k (rev lst)))
       (no-duplicatesp-equal (collect-signal-list k lst)))
  :hints(("Goal" :in-theory (enable rev)
          :induct t :do-not-induct t)
         (witness :ruleset set-reasoning-no-consp)))

;; (defthm set-difference-equal-acl2-count
;;   (<= (acl2-count (set-difference-equal a b))
;;       (acl2-count a))
;;   :hints(("Goal" :in-theory (enable set-difference-equal acl2-count)))
;;   :rule-classes :linear)

;; (defun set-diff-ind (x)
;;   (if (atom x)
;;       x
;;     (set-diff-ind (set-difference-equal (cdr x) (list (car x))))))



;; (defthm rev-set-difference
;;   (equal (rev (set-difference-equal a b))
;;          (set-difference-equal (rev a) b))
;;   :hints(("Goal" :in-theory (enable rev set-difference-equal))))

;; (defthm remove-duplicates-set-difference
;;   (equal (remove-duplicates-equal (set-difference-equal a b))
;;          (set-difference-equal (remove-duplicates-equal a) b))
;;   :hints(("Goal" :in-theory (enable set-difference-equal))))

;; (defthm intersectp-equal-collect-signals-set-diff
;;   (implies (not (intersectp-equal b (collect-signal-list k lst)))
;;            (not (intersectp-equal b (collect-signal-list k (set-difference-equal
;;                                                          lst a)))))
;;   :hints(("Goal" :in-theory (enable intersectp-equal
;;                                     set-difference-equal)
;;           :induct t :do-not-induct t))
;;   :otf-flg t)

;; (defthm no-duplicatesp-equal-collect-signals-set-diff
;;   (implies (no-duplicatesp-equal (collect-signal-list k lst))
;;            (no-duplicatesp-equal (collect-signal-list k (set-difference-equal
;;                                                          lst a))))
;;   :hints(("Goal" :in-theory (enable set-difference-equal)
;;           :induct t :do-not-induct t))
;;   :otf-flg t)

;; (defthm no-duplicatesp-equal-collect-signal-list-remove-duplicates-rev
;;   (iff (no-duplicatesp-equal (collect-signal-list k (remove-duplicates-equal
;;                                                      (rev lst))))
;;        (no-duplicatesp-equal (collect-signal-list k (remove-duplicates-equal
;;                                                      lst))))
;;   :hints(("Goal" :in-theory (enable rev)
;;           :induct (set-diff-ind lst) :do-not-induct t)))

(defthm hons-intersect-p1-intersectp
  (iff (hons-intersect-p1 a b)
       (intersectp-equal a (alist-keys b))))

(defthm hons-intersect-p2-intersectp
  (iff (hons-intersect-p2 a b)
       (intersectp-equal a b)))

(defthm hons-intersect-p-intersectp
  (iff (hons-intersect-p a b)
       (intersectp-equal a b))
  :hints(("Goal" :in-theory (disable append-of-nil))))


;; no longer necessary, never reason about pat-flatten
;; (defthm pat-flatten-nonnil
;;   (not (member-equal nil (pat-flatten x nil))))

(defthm collect-signal-list-nonnil
  (not (member-equal nil (collect-signal-list k x))))

(defthm hons-subset2-subsetp-equal
  (iff (hons-subset2 x y)
       (subsetp-equal x y))
  :hints(("Goal" :in-theory (enable subsetp-equal))))

(defthm hons-subset1-subsetp-equal
  (iff (hons-subset1 x y)
       (subsetp-equal x (alist-keys y)))
  :hints(("Goal" :in-theory (enable subsetp-equal alist-keys))))

(defthm hons-subset-subsetp-equal
  (iff (hons-subset x y)
       (subsetp-equal x y))
  :hints(("Goal" :in-theory (disable append-of-nil))))

(in-theory (disable hons-subset))


(defthm true-listp-pat->al
  (equal (true-listp (pat->al a b c))
         (true-listp c)))



(defthm occs-state-of-list-fix
  (equal (occs-state (list-fix occs))
         (occs-state occs))
  :hints(("Goal"
          :induct (len occs)
          :in-theory (enable occs-state))))

(defcong list-equiv equal (occs-state occs) 1
  :hints(("Goal"
          :in-theory (e/d (list-equiv)
                          (occs-state-of-list-fix))
          :use ((:instance occs-state-of-list-fix (occs occs))
                (:instance occs-state-of-list-fix (occs occs-equiv))))))

(defthm collect-signal-list-of-list-fix
  (equal (collect-signal-list key (list-fix occs))
         (collect-signal-list key occs))
  :hints(("Goal" :in-theory (enable collect-signal-list))))

(defcong list-equiv equal (collect-signal-list key occs) 2
  :hints(("Goal"
          :in-theory (e/d (list-equiv)
                          (collect-signal-list-of-list-fix))
          :use ((:instance collect-signal-list-of-list-fix (occs occs))
                (:instance collect-signal-list-of-list-fix (occs occs-equiv))))))
