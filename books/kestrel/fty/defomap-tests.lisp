; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defomap")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (fty::defomap nat-string-map
   :key-type nat
   :val-type string
   :elementp-of-nil nil))

(must-fail
 (fty::defomap nat-string-map
   :key-type nat
   :val-type string
   :cheap t))

(must-fail
 (fty::defomap nat-set 
   :elt-type nat))

(must-fail
 (fty::defomap nat string-map
   :key-type nat
   :val-type string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string)
 (assert! (function-symbolp 'nat-string-map-p (w state)))
 (assert! (function-symbolp 'nat-string-map-fix (w state)))
 (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :pred nat-string-mapp)
 (assert! (function-symbolp 'nat-string-mapp (w state)))
 (assert! (function-symbolp 'nat-string-map-fix (w state)))
 (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :fix nat-string-mfix)
 (assert! (function-symbolp 'nat-string-map-p (w state)))
 (assert! (function-symbolp 'nat-string-mfix (w state)))
 (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :equiv nat-string-mequiv)
 (assert! (function-symbolp 'nat-string-map-p (w state)))
 (assert! (function-symbolp 'nat-string-map-fix (w state)))
 (assert! (function-symbolp 'nat-string-mequiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :parents (fty::defomap omap::omaps)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :short "short"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :short (concatenate 'string "sh" "ort")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :long "long"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defomap nat-string-map
               :key-type nat
               :val-type string
               :long (concatenate 'string "lo" "ng")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Recursive tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::deftypes int-term-m
                (fty::deftagsum int-term-m
                                (:num ((val integerp)))
                                (:plus ((args int-term-m-map))))
                (fty::defomap int-term-m-map
                              :key-type natp
                              :val-type int-term-m))

 (defines eval-int-term-m/s
   (define eval-int-term-m ((tm int-term-m-p))
     :measure (int-term-m-count tm)
     :returns (i integerp)
     (case (int-term-m-kind tm)
       (:num (int-term-m-num->val tm))
       (:plus (eval-int-term-m-map (int-term-m-plus->args tm)))))
   (define eval-int-term-m-map ((map int-term-m-map-p))
     :measure (int-term-m-map-count map)
     :returns (i integerp)
     (if (or (omap::empty map)
             (not (int-term-m-map-p map)))
         0
       (+ (eval-int-term-m (omap::head-val map))
          (eval-int-term-m-map (omap::tail map)))))
   :verify-guards nil
   ///
   (verify-guards eval-int-term-m)
   )

 (defines sum-i-values-m/s
   (define sum-i-values-m ((i natp) (tm int-term-m-p))
     :measure (int-term-m-count tm)
     :returns (j integerp)
     (case (int-term-m-kind tm)
       (:num (int-term-m-num->val tm))
       (:plus (sum-i-values-m-map i (int-term-m-plus->args tm)))))
   (define sum-i-values-m-map ((i natp) (map int-term-m-map-p))
     :measure (int-term-m-map-count map)
     :hints (("Goal" :in-theory (e/d () (int-term-m-map-count-when-not-empty))))
     :returns (j integerp)
     (if (or (omap::empty map)
             (not (int-term-m-map-p map)))
         0
       (let ((i-pr (omap::in i map)))
         (if i-pr
             (sum-i-values-m i (omap::lookup i map))
           0))))
   :verify-guards nil
   ///
   (verify-guards sum-i-values-m :guard-debug t)
   ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::deftypes function-description
   (fty::deftagsum arg-decl
     (:next ((next arg-check)))
     (:done ((r booleanp))))
   (fty::defomap arg-check
     :key-type symbolp
     :val-type arg-decl)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::deftypes bunch-of-stuff
   (fty::deftagsum foosum
     (:prod1  ((a integerp)
               (b natp)
               (c natp)))
     (:prod2 ((lst foosumlist)
              (lst2 unusedlist)))
     (:empty ())
     (:prod3 ((alst1 foosum-omap)
              (alst2 foosum-omap2)
              (alst3 foosum-omap3)
              (alst4 unused-omap)))
     :measure (two-nats-measure (acl2-count x) 0))
   (fty::deftagsum unused-sum
     (:proda ((sum1 foosum-p)))
     (:prodb ((sum2 foosum-p)))
     :base-case-override :proda
     :measure (two-nats-measure (acl2-count x) 1))
   (fty::deflist foosumlist :elt-type foosum :measure (two-nats-measure (acl2-count x) 1))
   (fty::deflist unusedlist :elt-type unused-sum :measure (two-nats-measure (acl2-count x) 1))
   (fty::defomap foosum-omap :key-type natp :val-type foosumlist :measure (two-nats-measure (acl2-count x) 1))
   (fty::defomap foosum-omap2 :key-type foosum-p :val-type stringp :measure (two-nats-measure (acl2-count x) 1))
   (fty::defomap foosum-omap3 :key-type integerp :val-type foosum-p :measure (two-nats-measure (acl2-count x) 1))
   (fty::defomap unused-omap  :key-type stringp :val-type unused-sum :measure (two-nats-measure (acl2-count x) 1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::deftypes recomap
   (fty::deftagsum alterm
     (:v ((val natp)))
     (:t ((fn symbolp)
          (al recomap)))
     :layout :list)
   (fty::defomap recomap :key-type integerp :val-type alterm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::deftypes vl-type-error
   (fty::deftagsum vl-type-error
     (:incompat ((actual-type symbolp)
                 (detail stringp)))
     (:trunc/extend ((lhs-size natp :rule-classes :type-prescription)
                     (rhs-selfsize natp :rule-classes :type-prescription)))
     (:qmark-subexpr ((map vl-type-error-map))))
   (fty::defomap vl-type-error-map :key-type symbolp :val-type vl-type-error))
 (defines vl-type-error-basic-warn
   (define vl-type-error-basic-warn ((x symbolp "outer expression")
                                     (err vl-type-error-p)
                                     (type symbolp))
     :measure (vl-type-error-count err)
     (vl-type-error-case err
                         :incompat (list err.actual-type err.detail)
                         :trunc/extend (list err.lhs-size err.rhs-selfsize)
                         :qmark-subexpr (vl-type-error-map-basic-warn err.map x type)))
   (define vl-type-error-map-basic-warn ((map vl-type-error-map-p)
                                         (x symbolp)
                                         (type symbolp))
     :measure (vl-type-error-map-count map)
     (b* ((map (vl-type-error-map-fix map))
          ((unless (consp map)) nil)
          (warnings (vl-type-error-map-basic-warn (omap::tail map) x type)))
       (append warnings (vl-type-error-basic-warn (omap::head-key map) (omap::head-val map) type))))
   ///
   (fty::deffixequiv-mutual vl-type-error-basic-warn))
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

