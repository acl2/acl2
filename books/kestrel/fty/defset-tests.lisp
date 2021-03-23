; FTY Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Authors: Alessandro Coglio (coglio@kestrel.edu) and Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil)
 (assert! (function-symbolp 'nat-set-p (w state)))
 (assert! (function-symbolp 'nat-set-fix (w state)))
 (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
 (fty::defset nat set 
   :elt-type nat
   :elementp-of-nil nil))

(must-fail
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :cheap t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :pred nat-setp)
 (assert! (function-symbolp 'nat-setp (w state)))
 (assert! (function-symbolp 'nat-set-fix (w state)))
 (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :fix nat-sfix)
 (assert! (function-symbolp 'nat-set-p (w state)))
 (assert! (function-symbolp 'nat-sfix (w state)))
 (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :equiv nat-sequiv)
 (assert! (function-symbolp 'nat-set-p (w state)))
 (assert! (function-symbolp 'nat-set-fix (w state)))
 (assert! (function-symbolp 'nat-sequiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :pred nat-setp
   :fix nat-sfix
   :equiv nat-sequiv)
 (assert! (function-symbolp 'nat-setp (w state)))
 (assert! (function-symbolp 'nat-sfix (w state)))
 (assert! (function-symbolp 'nat-sequiv$inline (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :parents (fty::defset set::std/osets)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :short "short"))

(must-succeed
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :short (concatenate 'string "sh" "ort")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :long "long"))

(must-succeed
 (fty::defset nat-set
   :elt-type nat
   :elementp-of-nil nil
   :long (concatenate 'string "lo" "ng")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
 (fty::defset sym-set
   :elt-type symbol
   :elementp-of-nil t))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Recursive structures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#| list model
(deftypes int-term
  (deftagsum int-term
    (:num ((val integerp)))
    (:plus ((args int-termlist))))
  (deflist int-termlist
    :elt-type int-term))

(defines eval-int-term/s
  (define eval-int-term ((tm int-term-p))
    :measure (int-term-count tm)
    :returns (i integerp)
    (case (int-term-kind tm)
      (:num (int-term-num->val tm))
      (:plus (eval-int-termlist (int-term-plus->args tm)))))
  (define eval-int-termlist ((tms int-termlist-p))
    :measure (int-termlist-count tms)
    :returns (i integerp)
    (if (atom tms)
        0
      (+ (eval-int-term (car tms))
         (eval-int-termlist (cdr tms)))))
      ;:guard-debug t
  :verify-guards nil
  ///
  (verify-guards eval-int-term)
) ; eval-int-term/s
|#

(must-succeed*
 (fty::deftypes int-term-s
   (fty::deftagsum int-term-s
     (:num ((val integerp)))
     (:plus ((args int-term-s-set))))
   (fty::defset int-term-s-set
     :elt-type int-term-s
     :elementp-of-nil nil))

 (defines eval-int-term-s/s
   (define eval-int-term-s ((tm int-term-s-p))
     :measure (int-term-s-count tm)
     :returns (i integerp)
     (case (int-term-s-kind tm)
       (:num (int-term-s-num->val tm))
       (:plus (eval-int-term-s-set (int-term-s-plus->args tm)))))
   (define eval-int-term-s-set ((tms int-term-s-set-p))
     :measure (int-term-s-set-count tms)
     :returns (i integerp)
     (if (or (set::empty tms)
             (not (int-term-s-set-p tms)))
         0
       (+ (eval-int-term-s (set::head tms))
          (eval-int-term-s-set (set::tail tms)))))
   :verify-guards nil
   ///
   (verify-guards eval-int-term-s)
   )) ; eval-int-term-s/s

(must-succeed*
 (fty::deftypes int-term-s
   (fty::deftagsum int-term-s
     (:num ((val integerp)))
     (:plus ((args int-term-s-set))))
   (fty::defset int-term-s-set
     :elt-type int-term-s)))

(include-book "std/basic/two-nats-measure" :dir :system)

#|
(deftypes rec-list
  (deftagsum rec-list
    (:slist ((args rec-list-list)))
    :base-case-override :slist
    :measure (two-nats-measure (acl2-count x) 1))
  (deflist rec-list-list
    :elt-type rec-list
    :measure (two-nats-measure (acl2-count x) 0)))
|#

(must-succeed*
 (fty::deftypes rec-set
   (fty::deftagsum rec-set
     (:sset ((args rec-set-set)))
     :base-case-override :sset
     :measure (two-nats-measure (acl2-count x) 1))
   (fty::defset rec-set-set
     :elt-type rec-set
     :measure (two-nats-measure (acl2-count x) 0))))

