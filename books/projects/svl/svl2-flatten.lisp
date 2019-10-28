; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

(include-book "centaur/sv/svex/vars" :dir :system)

(include-book "centaur/sv/mods/lhs" :dir :system)
(include-book "centaur/sv/mods/svmods" :dir :system)

(include-book "std/strings/decimal" :dir :system)
(include-book "std/strings/substrp" :dir :system)
(include-book "tools")
(include-book "macros")
(include-book "centaur/fty/top" :dir :system)

(include-book "sv-to-svl")

(include-book "svex-simplify")

(include-book "svl2-flatten-simplify-lemmas")

(include-book "projects/rp-rewriter/top" :dir :system)

(in-theory (disable acl2::natp-when-gte-0
                    acl2::natp-when-integerp))

(define alistp$ (x)
  :enabled t
  (if (atom x)
      t
    (and (consp (car x))
         (alistp$ (cdr x)))))

(encapsulate
  nil
  (local
   (in-theory (enable rp::measure-lemmas)))

  (local
   (defthm m-lemma1
     (implies (and (< a x)
                   (natp z)
                   (natp y))
              (< a
                 (+ x y z)))))

  (local
   (defthm m-lemma2
     (implies (and t)
              (equal (< a
                        (+ x y a))
                     (< 0 (+ x y))))))

  (local
   (defthm lemma1
     (implies
      (and (consp x) (consp (car x)))
      (< (cons-countw (cdr (car x)) 2)
         (cons-countw x 2)))
     :hints (("goal"
	      :in-theory (e/d (cons-countw)
                              (ACL2::FOLD-CONSTS-IN-+))))))

  (local
   (defthm lemma2-lemma
     (implies (and (natp a)
                   (natp b)
                   (natp x))
              (< x
                 (+ 1 a x b)))))

  (local
   (defthm lemma2-lemma2
     (implies (and (natp a))
              (< 2
                 (+ 3 a)))))

  (local
   (defthm lemma2
     (< (cons-countw (cadr x) 2)
        (+ 1 (cons-countw x 2)))
     :otf-flg t
     :hints (("goal"
              :expand ((cons-countw x 2)
                       (cons-countw (cdr x) 2))
              :in-theory (e/d () ())))))

  (local
   (defthm lemma3-lemma1
     (implies (natp w)
              (<= w (cons-countw x w)))
     :hints (("Goal"
              :induct (cons-countw x w)
              :in-theory (e/d (cons-countw) ())))))

  (local
   (defthm lemma3-lemma2
     (implies
      (and (<= 2 a)
           (<= 2 b))
      (< (1+ x)
         (+ a b x)))))

  (local
   (defthm lemma3
     (implies (and (consp x) (consp (car x)))
              (< (+ 1 (cons-countw (cdr (car x)) 2))
                 (cons-countw x 2)))
     :hints (("Goal"
              :expand ((cons-countw x 2)
                       (CONS-COUNTW (CAR X) 2))
              :in-theory (e/d () ())))))

  (fty::defprod
   alias
   ((name sv::svar-p :default "")
    (val sv::svex-p :default 0)))

  (fty::deflist
   alias-lst
   :elt-type alias-p)

  (fty::defalist
   alias-alist
   :true-listp t
   :key-type sv::svar-p
   :val-type sv::svex-p)

  (fty::deftypes
   aliasdb
   (fty::defprod aliasdb
                 ((this alias-alist)
                  (sub aliasdb-alist-p))
                 :tag nil
                 :count nil
                 :measure (+ 1 (cons-countw x 2))
                 :layout :list)

   (fty::defalist aliasdb-alist
                  :count nil
                  :measure (cons-countw x 2)
                  :val-type aliasdb)))

;; (local
;;  (defthm TRUE-LISTP-ALIASDB->THIS
;;    (implies (aliasdb-p aliasdb)
;;             (true-listp (ALIASDB->THIS aliasdb)))
;;    :otf-flg t
;;    :hints (("Goal"
;;             :in-theory (e/d (ALIASDB->THIS
;;                              ALIAS-ALIST-FIX
;;                              aliasdb-p) ())))))

(acl2::defines
 free-aliasdb
 :hints (("Goal"
          :in-theory (e/d (rp::measure-lemmas
                           aliasdb->sub
                           ALIASDB-FIX
                           ALIASDB-p
                           aliasdb-alist-p
                           aliasdb-alist-fix) ())))
 :prepwork
 ((local
   (defthm lemma1
     (implies (consp x)
              (o< (cons-count (cdr (car x)))
                  (cons-count x)))
     :hints (("goal"
              :in-theory (e/d (cons-count) ()))))))

 (define free-aliasdb ((aliasdb aliasdb-p))
   :measure (cons-count (aliasdb-fix aliasdb))
   (b* ((aliasdb (mbe :logic (aliasdb-fix aliasdb)
                      :exec aliasdb))
        (- (fast-alist-free (aliasdb->this aliasdb)))
        (- (fast-alist-free (aliasdb->sub aliasdb)))
        (- (free-aliasdb-alist (aliasdb->sub aliasdb))))
     nil))
 (define free-aliasdb-alist ((subs aliasdb-alist-P))
   :measure (cons-count (aliasdb-alist-fix subs))
   (b* ((subs (mbe :logic (aliasdb-alist-fix subs)
                   :exec subs)))
     (if (atom subs)
         nil
       (b* ((- (free-aliasdb (cdar subs))))
         (free-aliasdb-alist (cdr subs)))))))

(define trace-p (trace)
  (declare (ignorable trace))
  (true-listp trace))

(define update-var-with-trace ((var1 sv::svar-p)
                               (trace trace-p))
  :verify-guards nil
  :guard-hints (("Goal"
                 :in-theory (e/d (trace-p
                                  SV::SVAR-P
                                  SV::SVAR->NAME) ())))
  (b* (((sv::svar var) var1)
       (var.name
        (case-match var.name
          ((':address n & depth)
           (let ((prefix (nth depth trace)))
             (if prefix (cons prefix n) n)))
          (& (let ((prefix (car trace)))
               (if prefix (cons prefix var.name) var.name))))))
    (sv::change-svar var1 :name var.name)))

#|
(update-var-with-trace '(:VAR (:ADDRESS "padded_multiplier" NIL 3)
                              . 0)
                       '(("m1" "m2" . "m3")
                         ("m1" . "m2")
                         "m1"))
||#

(acl2::defines
 update-svex-vars-with-trace
 (define update-svex-vars-with-trace ((svex sv::svex-p)
                                      (trace trace-p))
   :verify-guards nil
   :hints (("Goal"
            :in-theory (e/d (svex-kind) ())))
   (b* ((kind (sv::svex-kind svex)))
     (case-match kind
       (':var
        (update-var-with-trace svex trace))
       (':quote
        svex)
       (& (cons (car svex)
                (update-svex-vars-with-trace-lst (cdr svex)
                                                 trace))))))
 (define update-svex-vars-with-trace-lst ((svex-lst svexlist-p)
                                          (trace trace-p))
   :verify-guards nil
   (if (atom svex-lst)
       nil
     (cons (update-svex-vars-with-trace (car svex-lst) trace)
           (update-svex-vars-with-trace-lst (cdr svex-lst) trace)))))

;; (update-svex-vars-with-trace '(CONCAT 65
;;                                  (RSH 1040
;;                                       (:VAR (:ADDRESS "padded_multiplier" NIL 2)
;;                                             . 0))
;;                                  '(0 . -1))
;;                         '(("m1" "m2" . "m3")
;;                           ("m1" . "m2")
;;                           "m1"))

(defun cons-to-end (acl2::x acl2::y)
  (declare (xargs :guard t))
  (cond ((atom acl2::x) (cons acl2::x acl2::y))
        (t (cons (car acl2::x)
                 (cons-to-end (cdr acl2::x)
                              acl2::y)))))

(define aliaspair->alias ((alias-1 sv::lhs-p)
                          (alias-2 sv::lhs-p)
                          (trace trace-p)
                          (aliases aliasdb-p))
  :verify-guards nil
  (b* (((mv alias-1 alias-2)
        (if (and (equal (len alias-2) 1)
                 (equal (sv::lhatom-kind (sv::lhrange->atom (car alias-2))) ':var)
                 (equal (sv::lhatom-var->name (sv::lhrange->atom (car alias-2)))
                        ':self))
            (mv alias-2 alias-1)
          (mv alias-1 alias-2)))
       (- (if (or (> (len alias-1) 1)
                  (equal (sv::lhatom-kind (sv::lhrange->atom (car alias-1)))
                         :z))
              (hard-error 'aliaspair->alias
                          "This alias pairs (~p0) is unexpected Fix ~
                          aliaspair->alias"
                          (list (cons #\0 alias-1)
                                ))
            nil))
       (lhrange1 (car alias-1))
       (w1 (sv::lhrange->w lhrange1))
       ((sv::lhatom-var atom1) (sv::lhrange->atom lhrange1))

       (varname (sv::svar->name atom1.name))
       (newname (if (consp varname)
                    (sv::change-svar atom1.name :name (cdr varname))
                  atom1.name))
       (place (if (consp varname) (car varname) nil))
       (- (if (and (consp varname)
                   (consp (cdr varname)))
              (hard-error 'aliaspair->alias
                          "Unexpected varname for aliaspairs (~p0 ~p1). ~%"
                          (list (cons #\0 alias-1)
                                (cons #\1 alias-2)))
            nil))
       (svex2-old-val (if (equal place nil)
                          aliases
                        (cdr (hons-get place (aliasdb->sub aliases)))))
       (svex2-old-val (if svex2-old-val
                          (hons-get newname (aliasdb->this
                                             svex2-old-val))
                        nil))
       (svex2-old-val (cond (svex2-old-val (cdr svex2-old-val))
                            ((consp trace)
                             (sv::change-svar
                              atom1.name
                              :name
                              (if (consp varname)
                                  (cons (cons-to-end (car trace) (car varname))
                                        (cdr varname))
                                (cons (car trace) varname))))
                            (t atom1.name)))
       (svex2 (sv::lhs->svex alias-2))
       (svex2 (update-svex-vars-with-trace svex2 trace))
       (svex2 `(sv::partinst ,atom1.rsh ,w1 ,svex2-old-val ,svex2)))
    (mv place newname svex2)))

#|

(aliaspair->alias '((3 :VAR
                       ("partial_product_mux" . "multiplier_bits")
                       . 0))
                  '((2 (:VAR (:ADDRESS "padded_multiplier" NIL 3)
                             . 0)
                       . 25)
                    ((:VAR (:ADDRESS "padded_multiplier" NIL 3)
                             . 0)
                       . 27))
                  '(("m1" "m2" . "m3")
                    ("m1" . "m2")
                    "m1")
                    (make-aliasdb))

(aliaspair->alias '((65 :VAR 16 . 0))
                  '((65 :SELF . 1040))
                  '(("m1" "m2" . "m3")
                    ("m1" . "m2")
                    "m1")
                  (make-aliasdb))
||#

(define insert-into-aliasdb (place key val aliasdb)
  :verify-guards nil
  ;; place can be nil or consed module names.
  (cond ((not place)
         (change-aliasdb aliasdb
                         :this
; (fast-alist-clean
                         (hons-acons key val
                                     (aliasdb->this aliasdb))
; )
                         ))
        ((atom place)
         (b* ((sub-aliasdb (hons-get place (aliasdb->sub aliasdb)))
              (sub-aliasdb (if sub-aliasdb (cdr sub-aliasdb) (make-aliasdb)))
              (sub-aliasdb
               (change-aliasdb
                sub-aliasdb
                :this
;(fast-alist-clean
                (hons-acons key val
                            (aliasdb->this sub-aliasdb))
; )
                )))
           (change-aliasdb
            aliasdb
            :sub
;(fast-alist-clean
            (hons-acons place
                        sub-aliasdb
                        (aliasdb->sub aliasdb))
; )
            )))
        (t (b* ((curplace (car place))
                (cur-sub (hons-get curplace (aliasdb->sub aliasdb)))
                (cur-sub (if cur-sub (cdr cur-sub) (make-aliasdb)))
                (cur-sub (insert-into-aliasdb (cdr place) key val cur-sub)))
             (change-aliasdb aliasdb
                             :sub
; (fast-alist-clean
                             (hons-acons curplace
                                         cur-sub
                                         (aliasdb->sub aliasdb))
; )
                             )))))

(define aliaspair-lst->aliasdb ((aliaspairs sv::lhspairs-p)
                                (trace trace-p))
  :verify-guards nil
  (if (atom aliaspairs)
      (make-aliasdb)
    (b* ((rest (aliaspair-lst->aliasdb (cdr aliaspairs) trace))
         ((mv cur-place cur-name cur-svex)
          (aliaspair->alias (caar aliaspairs)
                            (cdar aliaspairs)
                            trace
                            rest)))
      (insert-into-aliasdb cur-place cur-name cur-svex rest))))

#|
(wet
 (aliaspair-lst->aliasdb '((((65 :var 16 . 0)) (65 :self . 1040))
                       (((65 :var 15 . 0)) (65 :self . 975))
                       (((65 :var 14 . 0)) (65 :self . 910))
                       (((65 :var 13 . 0)) (65 :self . 845))
                       (((65 :var 12 . 0)) (65 :self . 780))
                       (((65 :var 11 . 0)) (65 :self . 715))
                       (((65 :var 10 . 0)) (65 :self . 650))
                       (((65 :var 9 . 0)) (65 :self . 585))
                       (((65 :var 8 . 0)) (65 :self . 520))
                       (((65 :var 7 . 0)) (65 :self . 455))
                       (((65 :var 6 . 0)) (65 :self . 390))
                       (((65 :var 5 . 0)) (65 :self . 325))
                       (((65 :var 4 . 0)) (65 :self . 260))
                       (((65 :var 3 . 0)) (65 :self . 195))
                       (((65 :var 2 . 0)) (65 :self . 130))
                       (((65 :var 1 . 0)) (65 :self . 65))
                       (((65 :var 0 . 0)) (65 . :self)))
                     '(("m1" "m2" . "m3")
                       ("m1" . "m2")
                       "m1")))

(aliaspair-lst->aliasdb '((((3 :VAR
                           ("partial_product_mux" . "multiplier_bits")
                           . 0))
                       (3 (:VAR (:ADDRESS "padded_multiplier" NIL 3)
                                . 0)
                          . 25))
                      (((64 :VAR
                            ("partial_product_mux" . "multiplicand")
                            . 0))
                       (64 :VAR (:ADDRESS "multiplicand" NIL 3)
                           . 0))
                      (((:VAR ("partial_product_mux" . "multiplicand_sign")
                              . 0))
                       (:VAR (:ADDRESS "multiplicand_sign" NIL 3)
                             . 0))
                      (((:VAR ("partial_product_mux" . "partial_product_sign")
                              . 0))
                       ((:VAR (:ADDRESS "partial_product_signs" NIL 3)
                              . 0)
                        . 13))
                      (((:VAR ("partial_product_mux" . "partial_product_inverted")
                              . 0))
                       ((:VAR (:ADDRESS "partial_product_increments" NIL 3)
                              . 0)
                        . 13))
                      (((65 :VAR
                            ("partial_product_mux" . "partial_product")
                            . 0))
                       (65 (:VAR (:ADDRESS "partial_products" NIL 1)
                                 . 0)
                           . 845)))
                    '(
                      ("m1" "m2" . "m3")
                      ("m1" . "m2")
                      "m1"))

||#

(define merge-this-insts-aliasdb ((sub-aliasdb aliasdb-alist-p)
                                  (insts-aliasdb-alist aliasdb-alist-p))
  :verify-guards nil
  :guard-hints (("Goal"
                 :in-theory (e/d () (fast-alist-clean))))
  (if (atom insts-aliasdb-alist)
      (fast-alist-clean sub-aliasdb)
    (b* ((cur (car insts-aliasdb-alist))
         (name (car cur))
         (cur-aliasdb (cdr cur))
         (cursub (hons-get name sub-aliasdb))
         (cursub (if cursub (cdr cursub) (make-aliasdb)))
         (- (if (aliasdb->sub cursub)
                (hard-error 'merge-this-insts-aliasdb
                            "Unexpected sub entry while merge ~p0~%"
                            (list (cons #\0 cursub)))
              nil))
         (- (fast-alist-free (aliasdb->this cursub)))
         (- (fast-alist-free (aliasdb->this cur-aliasdb)))
         (cursub-this (append (aliasdb->this cursub)
                              (aliasdb->this cur-aliasdb)))
         (cursub-this (fast-alist-clean (make-fast-alist cursub-this)))
         (cursub (change-aliasdb cursub
                                 :this cursub-this
                                 :sub (aliasdb->sub cur-aliasdb)))
         (sub-aliasdb (hons-acons name cursub sub-aliasdb)))
      (merge-this-insts-aliasdb sub-aliasdb
                                (cdr insts-aliasdb-alist)))))



(acl2::defines
 add-delay-to-vars-in-svex
 :hints (("Goal"
          :in-theory (e/d (sv::svex-kind) ())))
 :guard-hints (("Goal"
                :in-theory (e/d (sv::svex-kind sv::svar-p sv::svex-p) ())))
 (define add-delay-to-vars-in-svex ((svex sv::svex-p))
   (cond ((equal (sv::svex-kind svex) ':quote)
          svex)
         ((equal (sv::svex-kind svex) ':var)
          (sv::change-svar svex :delay 1))
         (t
          (cons (car svex)
                (add-delay-to-vars-in-svex-lst (cdr svex))))))

 (define add-delay-to-vars-in-svex-lst ((lst sv::svexlist-p))
   (if (atom lst)
       nil
     (cons (add-delay-to-vars-in-svex (car lst))
           (add-delay-to-vars-in-svex-lst (cdr lst))))))
   
   
(define get-svex-from-aliasdb ((name)
                               (trace-name)
                               (delay natp)
                               (aliasdb aliasdb-p))
  :measure (acl2-count trace-name)
  (cond ((not trace-name)
         (b* ((var (sv::make-svar :name name
                                  :delay 0))
              (res (hons-get var (aliasdb->this aliasdb))))
           (cond ((and res (equal delay 0))
                  (cdr res))
                 ((and res (equal delay 1))
                  (add-delay-to-vars-in-svex (cdr res)))
                 (t
                  nil))))
        ((atom trace-name)
         (b* ((instname trace-name)
              (subaliases (aliasdb->sub aliasdb))
              (subaliasdb (hons-get instname subaliases)))
           (if subaliasdb
               (b* ((var (sv::make-svar :name  name :delay 0))
                    (res (hons-get var (aliasdb->this (cdr subaliasdb)))))
                 (cond ((and res (equal delay 0))
                        (cdr res))
                       ((and res (equal delay 1))
                        (add-delay-to-vars-in-svex (cdr res)))
                       (t
                        nil)))
             nil)))
        (t (b* ((instname (car trace-name))
                (subaliases (aliasdb->sub aliasdb))
                (subaliasdb (hons-get instname subaliases)))
             (if subaliasdb
                 (get-svex-from-aliasdb name
                                        (cdr trace-name)
                                        delay
                                        (cdr subaliasdb))
               nil)))))

(defun nthcdr2 (acl2::n acl2::l)
  (declare (xargs :guard (and (integerp acl2::n)
                              (<= 0 acl2::n))))
  (if (zp acl2::n)
      acl2::l
    (if (atom acl2::l)
        nil
      (nthcdr2 (+ acl2::n -1) (cdr acl2::l)))))

(acl2::defines
 update-svex-with-aliasdb
 :guard-hints (("Goal"
                :in-theory (e/d (svex-kind
                                 sv::svar-p
                                 svex-p) ())))
 :hints (("Goal"
          :in-theory (e/d (svex-kind) ())))

 (define update-svex-with-aliasdb ((svex sv::svex-p)
                                   (aliasdb aliasdb-p)
                                   (skip-var-name)
                                   (trace-size natp))
   (let ((kind (sv::svex-kind svex)))
     (cond ((eq kind ':quote)
            svex)
           ((eq kind ':var)
            (b* ((var-name (sv::svar->name svex))
                 (var-delay (sv::svar->delay svex))
                 (place (if (consp var-name) (car var-name) nil))
                 (name (if (consp var-name) (cdr var-name) var-name))
                 (place (nthcdr2 trace-size place))
                 ((when (equal var-name skip-var-name)) svex)
                 #|((mv var-name trace-name) (if (consp var-name)
                 (mv (cdr var-name) (car
                 var-name))
                 (mv var-name nil)))||#
                 (res (get-svex-from-aliasdb name place var-delay aliasdb)))
              (if res
                  res
                svex)))
           (t
            (cons-with-hint (car svex)
                            (update-svex-with-aliasdb-lst (cdr svex)
                                                          aliasdb
                                                          skip-var-name
                                                          trace-size)
                            svex)))))

 (define update-svex-with-aliasdb-lst ((lst sv::svexlist-p)
                                       (aliasdb aliasdb-p)
                                       (skip-var-name)
                                       (trace-size natp))
   (if (atom lst)
       nil
     (cons-with-hint
      (update-svex-with-aliasdb (car lst)
                                aliasdb skip-var-name trace-size)
      (update-svex-with-aliasdb-lst (cdr lst)
                                    aliasdb skip-var-name trace-size)
      lst))))

(define fix-this-aliases ((this-aliases alias-alist-p)
                          (trace-size natp)
                          (aliasdb aliasdb-p))
  (if (atom this-aliases)
      nil
    (b* ((cur (car this-aliases))
         (cur-name (car cur))
         (cur-svex (cdr cur))
         (cur-svex (update-svex-with-aliasdb cur-svex
                                             aliasdb
                                             cur-name
                                             trace-size)))
      (hons-acons cur-name
                  cur-svex
                  (fix-this-aliases (cdr this-aliases)
                                    trace-size
                                    aliasdb)))))

(acl2::defines
 mod-aliaspairs->aliasdb-pt1
 (define mod-aliaspairs->aliasdb-pt1 ((modname sv::modname-p)
                                      (modalist sv::modalist-p)
                                      ;;  (proc-history )
                                      (trace trace-p)
                                      (mods-to-skip sv::modnamelist-p)
                                      (limit natp "To prove termination"))
   :verify-guards nil
   (declare (xargs :mode :program)) ;; to profile
   :measure (nfix limit)
   (cond ((zp limit)
          (progn$ (hard-error 'mod-aliaspairs->aliasdb-pt1
                              "Limit Reached! ~%"
                              nil)
                  (make-aliasdb)))
         ;; ((hons-get modname proc-history)
         ;;  (cdr (hons-get modname proc-history)))
         (t
          (b* ((module (hons-get modname modalist))
               (module (if module
                           (cdr module)
                         (progn$
                          (hard-error 'mod-aliaspairs->aliasdb-pt1
                                      "Module not found in modalist ~p0 ~%"
                                      (list (cons #\0 modname)))
                          nil)))
               ((sv::module module) module)
               (aliasdb (aliaspair-lst->aliasdb module.aliaspairs
                                                trace))
               (insts-aliasdb-alist
                (mod-aliaspairs->aliasdb-pt1-lst module.insts
                                                 modalist
                                                 ;;proc-history
                                                 trace
                                                 mods-to-skip
                                                 (1- limit)))
               (merged-sub (merge-this-insts-aliasdb (aliasdb->sub aliasdb)
                                                     insts-aliasdb-alist))
               (aliasdb (change-aliasdb aliasdb :sub merged-sub))
               (this-aliases (aliasdb->this aliasdb))
               (this-aliases (fix-this-aliases this-aliases
                                               (len (car trace))
                                               aliasdb))
               (- (fast-alist-free (aliasdb->this aliasdb))))
            (change-aliasdb aliasdb :this this-aliases)))))

 (define mod-aliaspairs->aliasdb-pt1-lst ((insts sv::modinstlist-p)
                                          (modalist sv::modalist-p)
                                          (trace trace-p)
                                          (mods-to-skip sv::modnamelist-p)
                                          (limit natp "To prove termination"))
   :measure (nfix limit)
   (cond ((zp limit)
          (progn$ (hard-error 'mod-aliaspairs->aliasdb-pt1
                              "Limit Reached! ~%"
                              nil)
                  nil))
         ((atom insts)
          nil)
         (t (b* (((sv::modinst inst) (car insts))
                 (rest (mod-aliaspairs->aliasdb-pt1-lst (cdr insts)
                                                        modalist
                                                        trace
                                                        mods-to-skip
                                                        (1- limit)))
                 ((when (member-equal inst.modname mods-to-skip))
                  rest)
                 (trace- (cons (if trace
                                   (cons-to-end (car trace) inst.instname)
                                 inst.instname)
                               trace)))
              (acons inst.instname
                     (mod-aliaspairs->aliasdb-pt1 inst.modname
                                                  modalist
                                                  trace-
                                                  mods-to-skip
                                                  (1- limit))
                     rest))))))

#|

(mod-aliaspairs->aliasdb-pt1 "mul_test1"
                             (make-fast-alist (sv::design->modalist *booth-sv-design*))
                             nil
                             (expt 2 30))

(mod-aliaspairs->aliasdb-pt1 "booth2_multiplier_signed_64x32_97"
                             (make-fast-alist (sv::design->modalist *big-sv-design*))
                             nil
                             '("booth2_reduction_dadda_17x65_97")
                             (expt 2 30))
||#

(acl2::defines
 update-svex-with-aliases-alist
 :guard-hints (("Goal"
                :in-theory (e/d (svex-kind
                                 sv::svar-p
                                 svex-p) ())))
 :hints (("Goal"
          :in-theory (e/d (svex-kind) ())))
 :prepwork ((local
             (in-theory (enable svex-p
                                svex-kind
                                sv::svexlist-p
                                SV::SVAR-P))))

 (define update-svex-with-aliases-alist ((svex sv::svex-p)
                                         (aliases-alist alias-alist-p))
   :returns (res svex-p :hyp (and (sv::svex-p svex)
                                  (alias-alist-p aliases-alist)))
   (let ((kind (sv::svex-kind svex)))
     (cond ((eq kind ':quote)
            svex)
           ((eq kind ':var)
            (b* ((res (hons-get svex aliases-alist)))
              (if res (cdr res) svex)))
           (t
            (cons-with-hint (car svex)
                            (update-svex-with-aliases-alist-lst (cdr svex)
                                                                aliases-alist)
                            svex)))))

 (define update-svex-with-aliases-alist-lst ((lst sv::svexlist-p)
                                             (aliases-alist alias-alist-p))
   :returns (res-lst sv::svexlist-p
                     :hyp (and (sv::svexlist-p lst)
                               (alias-alist-p aliases-alist)) )
   (if (atom lst)
       nil
     (cons-with-hint
      (update-svex-with-aliases-alist (car lst) aliases-alist)
      (update-svex-with-aliases-alist-lst (cdr lst) aliases-alist)
      lst))))

(define add-to-aliases-alist ((this-alias-alist alias-alist-p)
                              (aliases-alist alias-alist-p)
                              (trace trace-p))
  :guard-hints (("Goal"
                 :in-theory (e/d () ())))
  (if (atom this-alias-alist)
      (mv aliases-alist nil)
    (b* ((cur (car this-alias-alist))
         (cur-svar (car cur))
         (cur-svex (cdr cur))
         (cur-svex (update-svex-with-aliases-alist cur-svex aliases-alist))
         (new-svar (if (consp trace)
                       (cons (car trace) cur-svar)
                     cur-svar))
         (aliases-alist
          (hons-acons (sv::change-svar cur-svar :name new-svar)
                      cur-svex
                      aliases-alist))
         ((mv aliases-alist rest)
          (add-to-aliases-alist (cdr this-alias-alist)
                                aliases-alist
                                trace)))
      (mv aliases-alist
          (hons-acons cur-svar cur-svex
                      rest)))))
(acl2::defines
 mod-aliaspairs->aliasdb-pt2
 :prepwork
 ((local
   (defthm lemma1
     (O< (CONS-COUNT (ALIASDB-ALIST-FIX (CADR ALIASDB)))
         (CONS-COUNT (ALIASDB-FIX ALIASDB)))
     :hints (("Goal"
              :in-theory (e/d (cons-count
                               ALIASDB-FIX
                               ALIASDB-ALIST-FIX) ())))))
  (local
   (defthm lemma2
     (implies (consp x)
              (o< (cons-count (cdr (car x)))
                  (cons-count x)))
     :hints (("Goal"
              :in-theory (e/d (cons-count) ()))))))

 (define mod-aliaspairs->aliasdb-pt2 ((aliasdb aliasdb-p)
                                      (aliases-alist alias-alist-p)
                                      (trace trace-p))
   :hints (("Goal"
            :in-theory (e/d (ALIASDB->SUB
                             ALIASDB-ALIST-FIX
                             rp::measure-lemmas) ())))
   :measure (cons-count (aliasdb-fix aliasdb))
   :verify-guards nil
   (declare (xargs :mode :program)) ;; to profile
   (b* (((aliasdb aliasdb) aliasdb)
        ((mv aliases-alist new-this)
         (add-to-aliases-alist aliasdb.this aliases-alist trace))
        (- (fast-alist-free aliasdb.this))
        (- (fast-alist-free aliasdb.sub))
        ((mv new-sub aliases-alist)
         (mod-aliaspairs->aliasdb-pt2-lst aliasdb.sub aliases-alist trace)))
     (mv (change-aliasdb aliasdb
                         :this new-this
                         :sub new-sub)
         aliases-alist)))

 (define mod-aliaspairs->aliasdb-pt2-lst ((aliasdb.sub aliasdb-alist-p)
                                          (aliases-alist alias-alist-p)
                                          (trace trace-p))
   :measure (cons-count (aliasdb-alist-fix aliasdb.sub))
   (b* ((aliasdb.sub (mbe :logic (aliasdb-alist-fix aliasdb.sub)
                          :exec aliasdb.sub)))
     (if (atom aliasdb.sub)
         (mv nil aliases-alist)
       (b* ((trace-tmp (cons (if (consp trace)
                                 (cons-to-end (car trace) (caar aliasdb.sub))
                               (caar aliasdb.sub))
                             trace))
            ((mv new-sub-entry aliases-alist)
             (mod-aliaspairs->aliasdb-pt2 (cdar aliasdb.sub)
                                          aliases-alist
                                          trace-tmp))
            ((mv rest-subs aliases-alist)
             (mod-aliaspairs->aliasdb-pt2-lst (cdr aliasdb.sub)
                                              aliases-alist
                                              trace)))
         (mv (hons-acons (caar aliasdb.sub) new-sub-entry rest-subs)
             aliases-alist))))))

(define mod-aliaspairs->aliasdb ((modname sv::modname-p)
                                 (modalist sv::modalist-p)
                                 (mods-to-skip sv::modnamelist-p))
  :verify-guards nil
  (declare (xargs :mode :program)) ;; to profile
  (b* ((aliasdb (mod-aliaspairs->aliasdb-pt1 modname modalist nil
                                             mods-to-skip
                                             (expt 2 59)))
       ((mv aliasdb aliases-alist)
        (mod-aliaspairs->aliasdb-pt2 aliasdb
                                     nil
                                     nil))
       (- (fast-alist-free aliases-alist)))
    aliasdb))

#|

(mod-aliaspairs->aliasdb "mul_test1"
                         (make-fast-alist (sv::design->modalist *booth-sv-design*))
                         nil)

;; not unfree fast-alist
(b* ((modalist (make-fast-alist (sv::design->modalist *signed64-sv-design*))))
  (progn$ (free-aliasdb (mod-aliaspairs->aliasdb "S_SP_64_64"
                                                modalist
                                                nil))
         (fast-alist-free modalist)
          nil))

(mod-aliaspairs->aliasdb "booth2_multiplier_signed_64x32_97"
                         (make-fast-alist (sv::design->modalist *big-sv-design*))
                         '("booth2_reduction_dadda_17x65_97"))
||#

;; (vl-design-to-insouts *big-vl-design2* *big-sv-design*)

(acl2::defines
 update-svex-with-aliasdb-and-trace
 :guard-hints (("Goal"
                :in-theory (e/d (svex-kind
                                 sv::svar-p
                                 trace-p
                                 svex-p) ())))
 :hints (("Goal"
          :in-theory (e/d (svex-kind) ())))

 (define update-svex-with-aliasdb-and-trace ((svex sv::svex-p)
                                             (aliasdb aliasdb-p)
                                             (trace trace-p))
   (declare (xargs :mode :program))
   (let ((kind (sv::svex-kind svex)))
     (cond ((equal aliasdb `(,(make-aliasdb)))
            svex)
           ((eq kind ':quote)
            svex)
           ((eq kind ':var)
            (b* ((var-name (sv::svar->name svex))
                 (var-delay (sv::svar->delay svex))
                 ((mv var-name address)
                  (case-match var-name
                    ((':address n & depth) (mv n depth))
                    (& (mv var-name 0))))

                 (cur-trace (nth (nfix address) trace))

                 (place (if (consp var-name) (car var-name) nil))
                 (place (if place
                            (if cur-trace
                                (cons-to-end cur-trace place)
                              place)
                          cur-trace))

                 (name (if (consp var-name) (cdr var-name) var-name))
                 (res (get-svex-from-aliasdb name place var-delay aliasdb))
                 ((when res) res)

                 (svar (sv::change-svar svex :name (if place (cons place name) name))))
              svar))
           (t
            (cons-with-hint (car svex)
                            (update-svex-with-aliasdb-and-trace-lst (cdr svex)
                                                                    aliasdb
                                                                    trace)
                            svex)))))

 (define update-svex-with-aliasdb-and-trace-lst ((lst sv::svexlist-p)
                                                 (aliasdb aliasdb-p)
                                                 (trace trace-p))
   (if (atom lst)
       nil
     (cons-with-hint
      (update-svex-with-aliasdb-and-trace (car lst)
                                          aliasdb trace)
      (update-svex-with-aliasdb-and-trace-lst (cdr lst)
                                              aliasdb trace)
      lst))))

(define get-lhs-w ((lhs sv::lhs-p))
  (if (atom lhs)
      0
    (+ (sv::lhrange->w (car lhs))
       (get-lhs-w (cdr lhs)))))

(define svex->lhs (svex)
  ;; example input :
  ;; (CONCAT
  ;;  65
  ;;  (PARTSEL 0 65 (:VAR ("partial_products" . 2) . 0))
  ;;  (CONCAT
  ;;   61
  ;;   (PARTSEL 4 61 (:VAR ("partial_products" . 2) . 0))
  ;;   (PARTSEL 65 5 (:VAR ("x" . "out") . 0))))

  (case-match svex
    (('sv::partsel start size var)
     (b* (((unless (sv::svar-p var))
           (progn$ (hard-error 'svex->lhs
                               "something is wrong with the svex ~p0~%"
                               (list (cons #\0 svex)))
                   nil))
          (start (nfix start))
          (size (if (posp size) size 1))
          (lhatom (sv::make-lhatom-var :name var
                                       :rsh start))
          (lhrange (sv::make-lhrange :w size
                                     :atom lhatom)))
       (list lhrange)))
    (('sv::concat concat-size ('sv::partsel & size &) term2)
     (b* ((concat-size (nfix concat-size))
          (size (nfix size)))
       (cond ((eql concat-size size)
              (append (svex->lhs (caddr svex))
                      (svex->lhs term2)))
             ((< concat-size size)
              (hard-error 'svex->lhs
                          "Unexpected size combination ~p0 ~%."
                          (list (cons #\0 svex))))
             (t (append (svex->lhs (caddr svex))
                        (list (sv::make-lhrange :w (- concat-size size)
                                                :atom (sv::make-lhatom-z)))
                        (svex->lhs term2))))))
    (&
     (hard-error 'svex->lhs
                 "Unexpected Expression~ ~p0 ~%"
                 (list (cons #\0 svex))))))

#|
(svex->lhs
 '(CONCAT
   68
   (PARTSEL 0 65 (:VAR ("partial_products" . 2) . 0))
   (CONCAT
    61
    (PARTSEL 4 61 (:VAR ("partial_products" . 2) . 0))
    (PARTSEL 65 5 (:VAR ("x" . "out") . 0)))))
||#

(define lhs-to-svl-wirelist ((lhs sv::lhs-p))
  :returns (wires wire-list-p :hyp (sv::lhs-p lhs))
  (if (atom lhs)
      nil
    (b* (((sv::lhrange lhrange) (car lhs))
         (wire-name (if (equal (sv::lhatom-kind lhrange.atom) :z)
                        :z
                      (sv::lhatom-var->name lhrange.atom)))
         (wire-start (if (equal (sv::lhatom-kind lhrange.atom) :z)
                         0
                       (sv::lhatom-var->rsh lhrange.atom)))
         (wire-size lhrange.w)
         (wire `(,wire-name ,wire-size . ,wire-start)))
      (cons wire
            (lhs-to-svl-wirelist (cdr lhs))))))

#|

(lhs-to-svl-wirelist '((65 :VAR ("partial_products" . 2) . 0)
                       (3 . :Z)
                       (61 (:VAR ("partial_products" . 2) . 0)
                           . 4)
                       (5 (:VAR ("x" . "out") . 0) . 65)))
||#

(acl2::defines
 get-inputs-for-svex
 :prepwork
 ((local
   (in-theory (enable SV::SVARLIST-P
                      SVEX-P

                      svex-kind)))
  (local
   (defthm wire-list-p-implies-true-listp
     (implies (wire-list-p wires)
              (true-listp wires))))
  (local
   (defthm SVarLIST-P-implies-true-listp
     (implies (sv::SVarLIST-P wires)
              (true-listp wires)))))

 (define get-inputs-for-svex ((svex sv::svex-p)
                              (modname sv::modname-p)
                              (modalist sv::modalist-p))
   :verify-guards nil
   :returns (mv (wires wire-list-p
                       :hyp (sv::svex-p svex))
                (delayed sv::svarlist-p
                         :hyp (sv::svex-p svex))
                (success booleanp))
   (declare (ignorable modname modalist)) ;; will use these when var is not in
   ;; partsel. If so, will see if the wire is of size 1. Then it's all good..
   (b* ((kind (sv::svex-kind svex)))
     (cond ((eq kind ':quote)
            (mv nil nil t))
           ((eq kind ':var)
            (b* ((delayed (eql (sv::svar->delay svex) 1)))
              (mv (if delayed nil (list `(,svex)))
                  (if delayed (list svex) nil)
                  (if delayed t
                    (cw "~% Reached a var that was not in a partsel ~p0 ~%" svex)))))
           ((case-match svex (('sv::partsel start size sub-svex)
                              (and (sv::svar-p sub-svex)
                                   (natp start)
                                   (natp size)))
              (& nil))
            (b* ((start (cadr svex))
                 (size (caddr svex))
                 (svar (cadddr svex))
                 (delayed (eql (sv::svar->delay svar) 1)))
              (mv (if delayed nil (list `(,svar ,size . ,start)))
                  (if delayed (list svar) nil)
                  t)))
           (t
            (get-inputs-for-svex-lst (cdr svex) modname modalist)))))

 (define get-inputs-for-svex-lst ((lst sv::svexlist-p)
                                  (modname sv::modname-p)
                                  (modalist sv::modalist-p))
   :returns (mv (wires wire-list-p
                       :hyp (sv::svexlist-p lst))
                (delayed sv::svarlist-p
                         :hyp (sv::svexlist-p lst))
                (success booleanp))
   (if (atom lst)
       (mv nil nil t)
     (b* (((mv rest rest-delayed success1)
           (get-inputs-for-svex (car lst) modname modalist))
          ((mv rest2 rest-delayed2 success2)
           (get-inputs-for-svex-lst (cdr lst) modname modalist)))
       (mv (append rest rest2)
           (append rest-delayed
                   rest-delayed2)
           (and success1 success2)))))

 ///

 (verify-guards get-inputs-for-svex))

(define assign-occ-merge-ins ((ins wire-list-p))
  :verify-guards nil
  :returns (res wire-list-p :hyp (wire-list-p ins))
  :prepwork
  ((local
    (defthm wire-p-implies-fc-1
      (implies (and (wire-p wire)
                    (and (consp wire) (consp (cdr wire))))
               (and (sv::svar-p (car wire))
                    (and (natp (cadr wire))
                         (integerp (cadr wire))
                         (acl2-numberp (cadr wire))
                         (rationalp (cadr wire)))
                    (natp (cddr wire))
                    (integerp (cddr wire))
                    (acl2-numberp (cddr wire))
                    (rationalp (cddr wire))))))

   (local
    (defthm wire-p-implies-fc-2
      (implies (and (wire-p wire)
                    (and (consp wire) (eq (cdr wire) nil)))

               (sv::svar-p (car wire)))))
   (local
    (defthm lemma1
      (implies (and (natp a)
                    (natp b)
                    (integerp c)
                    (or (< c a)
                        (<= c a)))
               (natp (+ b a (- c))))
      :hints (("goal"
               :in-theory (e/d (natp) ())))))

   (local
    (defthm lemma1-2
      (implies (and (natp a)
                    (natp b)
                    (integerp c)
                    (<= c a))
               (natp (+ (- c) b a)))
      :hints (("goal"
               :in-theory (e/d (natp) ())))))
   (local
    (defthm lemma2
      (implies (and (consp (assoc-equal name lst))
                    (wire-list-p lst))
               (wire-p (assoc-equal name lst)))
      ))

   (local
    (defthm lemma3
      (implies (and (assoc-equal name lst)
                    (wire-list-p lst))
               (wire-p (assoc-equal name lst)))
      )))

  (if (atom ins)
      nil
    (b* ((rest (assign-occ-merge-ins (cdr ins)))
         (cur (car ins))
         ((mv wire-name size start)
          (case-match cur
            ((wire-name size . start) (mv wire-name size start))
            ((wire-name) (mv wire-name -1 -1))
            (& (mv "" 0 0))))
         (other (assoc-equal wire-name rest))
         ((unless other)
          (cons-with-hint cur rest ins))
         ((mv o-size o-start)
          (case-match other
            ((& size . start) (mv size start))
            ((&) (mv -1 -1))
            (& (mv 0 0))))
         ((when (or (eql start -1) (eql o-start -1)))
          (cons `(,wire-name) rest))
         (end (+ start size))
         (o-end (+ o-start o-size))
         (new-start (min o-start start))
         (new-end (max o-end end))
         (new-size (- new-end new-start)))
      (cons `(,wire-name ,new-size . ,new-start)
            rest)))

  ///

  (defthm alistp-assign-occ-merge-ins
    (implies (wire-list-p ins)
             (alistp (assign-occ-merge-ins ins))))

  (verify-guards assign-occ-merge-ins
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (min max) ())))))

(define assign-occ-unify-ins ((ins wire-list-p))
  :prepwork
  ((local
    (defthm WIRE-LIST-P-FAST-ALIST-FORK
      (implies (and (wire-list-p ins)
                    (wire-list-p x))
               (wire-list-p (FAST-ALIST-FORk ins x)))
      :hints (("Goal"
               :in-theory (e/d (FAST-ALIST-FORK) ())))))
   (local
    (defthm lemma2
      (implies (and (wire-list-p ins))
               (wire-list-p (cdr (last ins))))
      :hints (("Goal"
               :in-theory (e/d (last) ()))))))

  :returns (res wire-list-p :hyp (wire-list-p ins))

  (fast-alist-clean (assign-occ-merge-ins ins)))

(define assign-to-occ ((lhs sv::lhs-p)
                       (rhs-svex sv::svex-p)
                       (modname sv::modname-p)
                       (modalist sv::modalist-p))
  (b* ((outs (lhs-to-svl-wirelist lhs))
       ((mv ins prev-ins success)
        (get-inputs-for-svex rhs-svex modname modalist))
       (- (or success
              (cw "Warning issued (assign-to-occ) for this svex: ~p0 ~
it may help to add a rewrite rule for this. ~%" rhs-svex)))

       (ins (assign-occ-unify-ins ins))
       (- (fast-alist-free ins)))
    (make-occ-assign
     :inputs ins
     :delayed-inputs prev-ins
     :outputs outs
     :svex rhs-svex)))

(define create-assign-occ-names ((trace trace-p)
                                 (prefix)
                                 (cnt natp))
  :guard-hints (("Goal"
                 :in-theory (e/d (trace-p) ())))
  :inline t
  (if (car trace)
      (cons (car trace) (sa prefix cnt))
    (sa prefix cnt)))

(define sv-mod->svl2-occs-assigns ((assigns sv::assigns-p)
                                   (trace trace-p)
                                   (aliasdb aliasdb-p)
                                   (cnt natp)
                                   (svex-simplify-preloaded)
                                   (modname sv::modname-p)
                                   (modalist sv::modalist-p)
                                   &key
                                   (rp::rp-state 'rp::rp-state)
                                   (state 'state))
  ;; Goal: convert all the assignsments into svl-type occs by replacing all the
  ;; aliases and adding the trace for flattening.
  ;; Also call svex-simplify for both lhs and rhs of assignments.
  (declare (xargs :stobjs (state rp::rp-state)
                  :mode :program
                  :guard (svex-simplify-preloaded-guard svex-simplify-preloaded state)
                  :verify-guards nil))
  (cond
   ((atom assigns)
    (mv nil cnt rp::rp-state))
   (t
    (b* (;;(- (cw "Starting sv-mod->svl2-occs-assigns ~%"))
         (cur (car assigns))
         ((sv::driver driver) (cdr cur))
         #|(- (if (not (equal driver.strength 6))
                (cw "Driver strength is not 6. For this assignment ~p0 ~%" cur)
              nil))||#
         (lhs-w (get-lhs-w (car cur)))

         ;; Prepare lhs-svex
         (lhs-svex (sv::lhs->svex (car cur)))

         ;;(- (cw "Calling update-svex-with-aliasdb-and-trace ~%"))
         (lhs-svex (update-svex-with-aliasdb-and-trace lhs-svex
                                                       aliasdb
                                                       trace))

         ;;(- (cw "Calling svex-simplify ~%"))
         (lhs-svex `(sv::partsel 0 ,lhs-w ,lhs-svex))
         ((mv lhs-svex rp::rp-state) (svex-simplify lhs-svex
                                                    :svex-simplify-preloaded svex-simplify-preloaded
                                                    :runes nil))

         ;; lhs svex to lhs
         (lhs (svex->lhs lhs-svex))

         ;; prepare rhs svex
         (rhs-svex driver.value)

         ;;(- (cw "hons-copy of rhs-svex... ~%"))
         (rhs-svex (hons-copy rhs-svex))
         ;;(- (cw "calculating the size of rhs-svex... ~%"))
         ;;(- (cw "rhs-svex size: ~p0 ~%" (rp::cons-count rhs-svex)))
         
         ;;(- (cw "Calling update-svex-with-aliasdb-and-trace ~%"))
         (rhs-svex (update-svex-with-aliasdb-and-trace rhs-svex
                                                       aliasdb
                                                       trace))

         ;;(- (cw "Calling svex-simplify ~%"))
         (rhs-svex `(sv::partsel 0 ,lhs-w ,rhs-svex))
         ((mv rhs-svex rp::rp-state) (svex-simplify rhs-svex
                                                    :svex-simplify-preloaded svex-simplify-preloaded
                                                    :runes nil))

         ;;(- (cw "Calling svex->lhs ~%"))
      

         ;;(- (cw "Calling assign-to-occ ~%"))
         ;; convert lhs and rhs-svex to svl style occ object
         (occ (assign-to-occ lhs rhs-svex modname modalist))

         ;;(- (cw "Done: sv-mod->svl2-occs-assigns ~%"))
         ((mv rest cnt-new rp::rp-state) (sv-mod->svl2-occs-assigns (cdr assigns)
                                                                    trace
                                                                    aliasdb
                                                                    (1+ cnt)
                                                                    svex-simplify-preloaded
                                                                    modname
                                                                    modalist))
         #|(- (cw "Even more done: sv-mod->svl2-occs-assigns ~%"))||#)
      ;; save and return the object.
      (mv (acons (create-assign-occ-names trace 'assign cnt) occ rest)
          cnt-new rp::rp-state)))))

(define sv-mod->svl2-occs-module-aux ((sigs wire-list-p)
                                      (aliasdb aliasdb-p)
                                      (place)
                                      (svex-simplify-preloaded)
                                      &key
                                      (rp::rp-state 'rp::rp-state)
                                      (state 'state))
  :guard (svex-simplify-preloaded-guard svex-simplify-preloaded state)
  :verify-guards nil
  (if (atom sigs)
      (mv nil rp::rp-state)
    (b* (((mv rest rp::rp-state)
          (sv-mod->svl2-occs-module-aux (cdr sigs)
                                        aliasdb
                                        place
                                        svex-simplify-preloaded))
         (cur (car sigs))
         (cur-name (car cur))
         (cur-w (cadr cur))

         (alias-svex (get-svex-from-aliasdb cur-name place 0 aliasdb))
         #|(- (cw "alias-svex ~p0 for cur-sig ~p1 in place ~p2 ~%"
         alias-svex cur place))||#
         ((unless alias-svex)
          (mv (acons cur-name `(,(sv::make-lhrange
                                  :atom (sv::make-lhatom-var :name (sv::make-svar :name (if place
                                                                                            (cons place cur-name)
                                                                                          cur-name)
                                                                                  :delay 0)
                                                             :rsh 0)
                                  :w cur-w))
                     rest)
              rp::rp-state))
         (alias-svex `(sv::partsel 0 ,cur-w ,alias-svex))
         ((mv alias-svex rp::rp-state)
          (svex-simplify alias-svex
                         :svex-simplify-preloaded svex-simplify-preloaded
                         :runes nil))
         (alias-lhs (svex->lhs alias-svex))
         ;; ((unless (equal (len alias-lhs) 1))
         ;;  (progn$ (hard-error 'sv-mod->svl2-occs-module-aux
         ;;                      "This module has an input or output port that
         ;;                             gets more than one wire. ~p0. this is a
         ;;                             temporary error and will be fixed later. ~%"
         ;;                      (list (cons #\0 alias-svex)))
         ;;          (mv nil rp::rp-state)))
         ;; (cur-wire (car alias-lhs))
         ;; (cur-wire `(,(sv::lhatom-var->name (sv::lhrange->atom cur-wire))
         ;;             ,(sv::lhrange->w cur-wire)
         ;;             .
         ;;             ,(sv::lhatom-var->rsh (sv::lhrange->atom cur-wire))))
         )
      (mv (acons cur-name alias-lhs rest)
          rp::rp-state))))

(define sv-mod->svl2-occs-module ((modname sv::modname-p)
                                  (aliasdb aliasdb-p)
                                  (trace trace-p)
                                  (vl-insouts vl-insouts-sized-p)
                                  (svex-simplify-preloaded)
                                  &key
                                  (rp::rp-state 'rp::rp-state)
                                  (state 'state))
  :guard (svex-simplify-preloaded-guard svex-simplify-preloaded state)
  :verify-guards nil
  (declare (ignorable modname
                      trace
                      aliasdb
                      vl-insouts
                      svex-simplify-preloaded state
                      rp::rp-state))
  (b* ((this-vl-insouts (assoc-equal modname vl-insouts))
       (in-names (cadr this-vl-insouts))
       (out-names (cddr this-vl-insouts))
       (place (car trace))
       ((mv ins rp::rp-state) (sv-mod->svl2-occs-module-aux in-names
                                                            aliasdb
                                                            place
                                                            svex-simplify-preloaded))
       ((mv outs rp::rp-state) (sv-mod->svl2-occs-module-aux out-names
                                                             aliasdb
                                                             place
                                                             svex-simplify-preloaded))
       (occ (make-occ-module :inputs ins
                             :outputs outs
                             :name modname)))

    (mv occ rp::rp-state)))

(set-state-ok t)

(acl2::defines
 sv-mod->svl2-occs

 (define sv-mod->svl2-occs ((modname sv::modname-p)
                            (modalist sv::modalist-p)
                            (aliasdb aliasdb-p)
                            (trace trace-p)
                            (mods-to-skip sv::modnamelist-p)
                            (vl-insouts vl-insouts-sized-p)
                            (svex-simplify-preloaded)
                            (limit natp "To prove termination")
                            &key
                            (rp::rp-state 'rp::rp-state)
                            (state 'state))
   (declare (xargs :stobjs (state rp::rp-state)))

   (declare (xargs :mode :program)) ;; to profile

   :verify-guards nil
   :measure (nfix limit)
   :guard (svex-simplify-preloaded-guard svex-simplify-preloaded state)

   ;; Goal: by flattening, create all the occs including assigns and modules.
   (cond ((zp limit)
          (progn$ (hard-error 'mod-assigns->occs
                              "Limit Reached! ~%"
                              nil)
                  (mv nil rp::rp-state)))
         (t
          (b* ((module (hons-get modname modalist))
               (module (if module (cdr module)
                         (progn$
                          (hard-error 'mod-aliaspairlis$->aliasdb-pt1
                                      "Module not found in modalist ~p0 ~%"
                                      (list (cons #\0 modname)))
                          nil)))
               ((sv::module module) module)
               ((mv assign-occs ?cnt rp::rp-state)
                (sv-mod->svl2-occs-assigns module.assigns trace aliasdb
                                           0
                                           svex-simplify-preloaded
                                           modname modalist))
               ((mv insts-occs  rp::rp-state)
                (sv-mod->svl2-occs-insts module.insts
                                         modalist
                                         aliasdb
                                         trace
                                         mods-to-skip
                                         vl-insouts
                                         svex-simplify-preloaded
                                         (1- limit))))
            (mv (append assign-occs insts-occs)  rp::rp-state)))))

 (define sv-mod->svl2-occs-insts ((insts sv::modinstlist-p)
                                  (modalist sv::modalist-p)
                                  (aliasdb aliasdb-p)
                                  (trace trace-p)
                                  (mods-to-skip sv::modnamelist-p)
                                  (vl-insouts vl-insouts-sized-p)
                                  (svex-simplify-preloaded)
                                  (limit natp "To prove termination")
                                  &key
                                  (rp::rp-state 'rp::rp-state)
                                  (state 'state))
   (declare (xargs :stobjs (state rp::rp-state)))
   :guard (svex-simplify-preloaded-guard svex-simplify-preloaded state)
   :measure (nfix limit)

   (cond ((zp limit)
          (progn$ (hard-error 'mod-assigns->occs
                              "Limit Reached! ~%"
                              nil)
                  (mv nil  rp::rp-state)))
         ((atom insts)
          (mv nil  rp::rp-state))
         (t
          (b* (((sv::modinst inst) (car insts))
               ((mv rest  rp::rp-state)
                (sv-mod->svl2-occs-insts (cdr insts)
                                         modalist
                                         aliasdb
                                         trace
                                         mods-to-skip
                                         vl-insouts
                                         svex-simplify-preloaded
                                         (1- limit)))
               (trace-tmp (cons (if (consp trace)
                                    (cons-to-end (car trace) inst.instname)
                                  inst.instname)
                                trace))
               ((when (member-equal inst.modname mods-to-skip))
                (b* (((mv this-occ rp::rp-state)
                      (sv-mod->svl2-occs-module inst.modname aliasdb trace-tmp
                                                vl-insouts svex-simplify-preloaded)))
                  (mv (acons (car trace-tmp)
                             this-occ
                             rest)
                      rp::rp-state)))
               ((aliasdb aliasdb) aliasdb)
               #|(aliasdb-tmp (hons-get inst.instname aliasdb.sub))
               (aliasdb-tmp (if aliasdb (cdr aliasdb) (make-aliasdb)))||#

               ((mv cur-inst-occs  rp::rp-state)
                (sv-mod->svl2-occs inst.modname
                                   modalist
                                   aliasdb
                                   trace-tmp
                                   mods-to-skip
                                   vl-insouts
                                   svex-simplify-preloaded
                                   (1- limit))))
            (mv (append cur-inst-occs rest)
                rp::rp-state))))))

(progn

  ;; Input or output signals might be aliased to some other signals.
  ;; If it is the case, then we'd have to create assignments for input and
  ;; output signals to assign those aliases for the main module.

  (define svl2-flatten-mod-insert-assigns-for-inputs-aux ((input-wire wire-p)
                                                          (lhs sv::lhs-p)
                                                          (rsh natp)
                                                          (cnt natp)
                                                          (acc occ-alist-p))
    :prepwork
    ((local
      (in-theory (enable occ-name-p
                         sym-app-fnc
                         intern-in-package-of-symbol
                         svex-p
                         sv::svar-p)))
     (local
      (defthm occ-alist-p-is-alistp
        (implies (occ-alist-p alist)
                 (alistp$ alist)))))
    :returns (mv (res occ-alist-p :hyp (occ-alist-p acc))
                 (cnt-res natp :hyp (natp cnt)))
    :verify-guards nil
    (if (atom lhs)
        (mv acc cnt)
      (b* (((sv::lhrange cur-range) (car lhs))
           ((mv acc cnt)
            (svl2-flatten-mod-insert-assigns-for-inputs-aux input-wire
                                                            (cdr lhs)
                                                            (+ rsh cur-range.w)
                                                            cnt
                                                            acc))
           ((when (eq (sv::lhatom-kind cur-range.atom) ':z))
            (mv acc cnt))
           (assign-rsh `(sv::partsel ,rsh
                                     ,cur-range.w
                                     ,(wire-name input-wire)))
           (assign-ins `((,(wire-name input-wire) ,cur-range.w . ,rsh)))
           (assign-outs `((,(sv::lhatom-var->name cur-range.atom)
                           ,cur-range.w
                           .
                           ,(sv::lhatom-var->rsh cur-range.atom))))
           (occ (make-occ-assign :inputs assign-ins
                                 :delayed-inputs nil
                                 :outputs assign-outs
                                 :svex assign-rsh)))
        (mv (acons (sa 'init_assign cnt)
                   occ
                   acc)
            (1+ cnt))))
    ///
    (verify-guards svl2-flatten-mod-insert-assigns-for-inputs-aux))

  (define svl2-flatten-mod-insert-assigns-for-inputs ((this-aliases alias-alist-p)
                                                      (inputs wire-list-p)
                                                      (cnt natp)
                                                      (svex-simplify-preloaded)
                                                      &key
                                                      (rp::rp-state 'rp::rp-state)
                                                      (state 'state))
    :guard (svex-simplify-preloaded-guard svex-simplify-preloaded state)
    :verify-guards nil
    (if (atom inputs)
        (mv nil cnt rp::rp-state)
      (b* (((mv rest cnt rp::rp-state)
            (svl2-flatten-mod-insert-assigns-for-inputs this-aliases
                                                        (cdr inputs)
                                                        cnt
                                                        svex-simplify-preloaded))
           (cur (car inputs))
           (alias (hons-get (wire-name cur) this-aliases))
           ((unless alias)
            (mv rest cnt rp::rp-state))

           (alias-svex (cdr alias))
           (alias-svex `(sv::partsel 0 ,(wire-size cur) ,alias-svex))
           ((mv alias-svex rp::rp-state)
            (svex-simplify alias-svex
                           :svex-simplify-preloaded svex-simplify-preloaded
                           :runes nil))
           (alias-lhs (svex->lhs alias-svex))
           ((mv assigns cnt)
            (svl2-flatten-mod-insert-assigns-for-inputs-aux cur
                                                            alias-lhs
                                                            0
                                                            cnt
                                                            rest)))
        (mv assigns cnt rp::rp-state))))

  (define svl2-flatten-mod-insert-assigns-for-outputs ((this-aliases alias-alist-p)
                                                       (outputs wire-list-p)
                                                       (cnt natp)
                                                       (svex-simplify-preloaded)
                                                       (modname sv::modname-p)
                                                       (modalist sv::modalist-p)
                                                       &key
                                                       (rp::rp-state 'rp::rp-state)
                                                       (state 'state))
    :guard (svex-simplify-preloaded-guard svex-simplify-preloaded state)
    :verify-guards nil
    (if (atom outputs)
        (mv nil cnt rp::rp-state)
      (b* (((mv rest cnt rp::rp-state)
            (svl2-flatten-mod-insert-assigns-for-outputs this-aliases
                                                         (cdr outputs)
                                                         cnt
                                                         svex-simplify-preloaded
                                                         modname
                                                         modalist))
           (cur (car outputs))

           (alias (hons-get (wire-name cur) this-aliases))
           ((unless alias)
            (mv rest cnt rp::rp-state))

           (alias-svex (cdr alias))
           (alias-svex `(sv::partsel 0 ,(wire-size cur) ,alias-svex))
           ((mv alias-svex rp::rp-state)
            (svex-simplify alias-svex
                           :svex-simplify-preloaded svex-simplify-preloaded
                           :runes nil))
           ((mv ins prev-ins success)
            (get-inputs-for-svex alias-svex modname modalist))
           (- (or success
              (cw "Warning issued (in alias-pairs) for this svex  ~p0 ~
it may help to add a rewrite rule for this. ~%" alias-svex)))
           (occ (make-occ-assign :inputs ins
                                 :delayed-inputs prev-ins
                                 :outputs `(,cur)
                                 :svex alias-svex)))
        (mv (acons (sa 'out_assign cnt) occ rest)
            (1+ cnt)
            rp::rp-state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Create listeners...
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; signals to occ listeners.
(progn
  (define create-signals-to-occ-listeners-module-aux ((lhs sv::lhs-p)
                                                      (occ-name occ-name-p)
                                                      (alist alistp$))
    :returns (res alistp$ :hyp (alistp$ alist))
    (if (atom lhs)
        alist
      (b* ((atom (sv::lhrange->atom (car lhs)))
           ((when (equal (sv::lhatom-kind atom) ':z))
            (create-signals-to-occ-listeners-module-aux (cdr lhs)
                                                        occ-name
                                                        alist))
           (name (sv::lhatom-var->name atom))
           (entry (hons-get name alist))
           (alist (hons-acons name (cons occ-name (cdr entry)) alist)))
        (create-signals-to-occ-listeners-module-aux (cdr lhs)
                                                    occ-name
                                                    alist))))

  (define create-signals-to-occ-listeners-module ((module-ins
                                                   module-occ-wire-list-p)
                                                  (occ-name occ-name-p)
                                                  (alist alistp$))
    :returns (res alistp$ :hyp (alistp$ alist))
    (if (atom module-ins)
        alist
      (b* ((cur-lhs (if (sv::lhs-p (cdar module-ins)) (cdar module-ins) nil))
           (alist (create-signals-to-occ-listeners-module-aux cur-lhs occ-name alist)))
        (create-signals-to-occ-listeners-module (cdr module-ins)
                                                occ-name
                                                alist))))

  (define create-signals-to-occ-listeners-assign ((wires wire-list-p)
                                                  (occ-name occ-name-p)
                                                  (alist alistp$))
    :returns (res alistp$ :hyp (alistp$ alist))
    (if (atom wires)
        alist
      (b* ((wire (car wires))
           ((when (equal (wire-name wire) ':z))
            (create-signals-to-occ-listeners-assign (cdr wires)
                                                    occ-name
                                                    alist))
           (entry (hons-get (wire-name wire) alist))
           (alist (hons-acons (wire-name wire) (cons occ-name (cdr entry)) alist)))
        (create-signals-to-occ-listeners-assign (cdr wires)
                                                occ-name
                                                alist))))

  (define create-signal-to-occ-listeners ((occs occ-alist-p)
                                          (alist alistp$))
    :returns (res alistp$ :hyp (alistp$ alist))
    (if (atom occs)
        alist
      (b* ((occ-name (caar occs))
           (occ (cdar occs))
           (alist
            (if (eq (occ-kind occ) ':module)
                (create-signals-to-occ-listeners-module (occ-module->inputs occ)
                                                        occ-name
                                                        alist)
              (create-signals-to-occ-listeners-assign (occ-assign->inputs occ)
                                                      occ-name
                                                      alist))))
        (create-signal-to-occ-listeners (cdr occs) alist)))))

;;;;

(progn
  (define check-intersection-for-lhs ((wire-name sv::svar-p)
                                      (start natp)
                                      (w natp)
                                      (lhs sv::lhs-p))
    :guard-hints (("Goal"
                   :in-theory (e/d ()
                                   ((:e tau-system)))))
    (if (atom lhs)
        nil
      (b* (((sv::lhrange lhrange) (car lhs))
           ((when (eq (sv::lhatom-kind lhrange.atom) :z))
            (check-intersection-for-lhs wire-name
                                        start
                                        w
                                        (cdr lhs)))
           ((sv::lhatom-var var) lhrange.atom)

           (end (+ w start))
           (start2 var.rsh)
           (end2 (+ start2 lhrange.w)))
        (or (and (equal var.name wire-name)
                 (or (and (<= end2 end)
                          (< start end2))
                     (and (< start2 end)
                          (<= start start2))
                     (and (<= end end2)
                          (< start2 end))
                     (and (< start end2)
                          (<= start2 start))))
            (check-intersection-for-lhs wire-name
                                        start
                                        w
                                        (cdr lhs))))))

  (define check-intersection-for-wire-list ((wire-name sv::svar-p)
                                            (start natp)
                                            (w natp)
                                            (wires wire-list-p))
    :guard-hints (("Goal"
                   :in-theory (e/d ()
                                   ((:e tau-system)))))
    (if (atom wires)
        nil
      (b* ((end (+ w start))
           (start2 (wire-start (car wires)))
           ((unless start2)
            (or (equal (wire-name (car wires)) wire-name)
                (check-intersection-for-wire-list wire-name
                                                  start
                                                  w
                                                  (cdr wires))))
           (end2 (+ start2 (wire-size (car wires))))
           #|(- (cw "start ~p0, end ~p1, start2 ~p2, end2 ~p3 ~%" start end
           start2 end2))||#)
        (or (and (equal (wire-name (car wires)) wire-name)
                 (or (and (<= end2 end)
                          (< start end2))
                     (and (< start2 end)
                          (<= start start2))
                     (and (<= end end2)
                          (< start2 end))
                     (and (< start end2)
                          (<= start2 start))
                     ))
            (check-intersection-for-wire-list wire-name
                                              start
                                              w
                                              (cdr wires))))))

  #|(check-intersection-for-wire-list '(:VAR ("product_terms" . 0) . 0)
  91 1
  '(((:VAR ("product_terms" . 0) . 0)
  97 . 0)
  ((:VAR ("product_terms" . 1) . 0)
  97 . 0)))||#

  (defun binary-append2 (acl2::x acl2::y)
    (declare (xargs :guard t))
    (cond ((atom acl2::x) acl2::y)
          (t (cons (car acl2::x)
                   (binary-append2 (cdr acl2::x)
                                   acl2::y)))))

  (define module-occ-wires->lhs ((inputs module-occ-wire-list-P))
    (if (atom inputs)
        nil
      (binary-append2
       (cdar inputs)
       (module-occ-wires->lhs (cdr inputs)))))

  (define does-intersect-occ-to-occ-listener ((wire-name sv::svar-p)
                                              (start natp)
                                              (w natp)
                                              (occ occ-p))
    (cond ((eq (occ-kind occ) ':module)
           (let ((lhs (module-occ-wires->lhs (occ-module->inputs occ))))
             (check-intersection-for-lhs wire-name
                                         start
                                         w
                                         (if (sv::lhs-p lhs)
                                             lhs
                                           nil))))
          (t
           (check-intersection-for-wire-list wire-name
                                             start
                                             w
                                             (occ-assign->inputs occ)))))

  #|(does-intersect-occ-to-occ-listener '(:VAR ("product_terms" . 0) . 0)
  91 1
  '(:ASSIGN
  (((:VAR ("product_terms" . 0) . 0)
  97 . 0)
  ((:VAR ("product_terms" . 1) . 0)
  97 . 0))
  NIL (("product_terms" 194 . 0))
  (CONCAT 97
  (PARTSEL 0 97 (:VAR ("product_terms" . 0) . 0))
  (PARTSEL 0 97 (:VAR
  ("product_terms" . 1) . 0)))))||#

  #| (define does-wires-intesect-with-occ ((wires wire-list-p)
  (occ occ-p)) ; ;
  (if (atom wires) ; ;
  nil ; ;
  (or (b* ((wire (car wire)) ; ;
  ((mv name start size) ; ;
  (mv (wire-name wire) (wire-start wire) (wire-size wire))) ; ;
  ((unless start) ; ;
  (hard-error 'does-wires-intesect-with-occ ; ;
  "Unexpected wire type ~p0 ~%" ; ;
  (list (cons #\0 wire))))) ; ;
  (does-intersect-occ-to-occ-listener name ; ;
  start ; ;
  size ; ;
  occ)) ; ;
  (does-wires-intesect-with-occ (cdr wires) ; ;
  occ)))) ; ;
; ; ; ; ; ; ; ; ; ; ; ; ;
  (define does-lhs-intersect-with-occ ((lhs sv::lhs-p) ; ;
  (occ occ-p)) ; ;
  (if (atom lhs) ; ;
  nil ; ;
  (or (b* (((sv::lhrange lhrange) (car lhs)) ; ;
  ((unless (eq (sv::lhatom-kind lhrange.atom) ':z)) ; ;
  (does-lhs-intersect-with-occ (cdr lhs) occ))) ; ;
  (does-intersect-occ-to-occ-listener (sv::lhatom-var->name lhrange.atom) ; ;
  (sv::lhatom-var->rsh lhrange.atom) ; ;
  lhrange.rsh ; ;
  occ)) ; ;
  (does-lhs-intersect-with-occ (cdr lhs) ; ;
  occ))))||#

  (define member-equal-wrapper ((x)
                                (lst true-listp))
    :enabled t
    (member-equal x lst))

  (define get-intersecting-occs ((wire-name sv::svar-p)
                                 (start natp)
                                 (w natp)
                                 (occ-names occ-name-list-p)
                                 (all-occs occ-alist-p)
                                 (acc true-listp)
                                 &key
                                 (duplicate 'nil))
    :returns (res true-listp
                  :hyp (true-listp acc))
    (if (atom occ-names)
        acc
      (b* ((occ (hons-get (car occ-names) all-occs))
           (acc (get-intersecting-occs wire-name
                                       start
                                       w
                                       (cdr occ-names)
                                       all-occs
                                       acc
                                       :duplicate duplicate)))
        (if (and occ
                 (does-intersect-occ-to-occ-listener wire-name
                                                     start
                                                     w
                                                     (cdr occ))
                 (or duplicate
                     (not (member-equal (car occ-names) acc))))
            (cons (car occ-names) acc)
          acc))))

  #|(get-intersecting-occs '(:VAR ("product_terms" . 0) . 0)
  91
  1
  '(OUT_ASSIGN_0)
  '((OUT_ASSIGN_0 :ASSIGN
  (((:VAR ("product_terms" . 0) . 0)
  97 . 0)
  ((:VAR ("product_terms" . 1) . 0)
  97 . 0))
  NIL (("product_terms" 194 . 0))
  (CONCAT 97
  (PARTSEL 0 97 (:VAR ("product_terms" . 0) . 0))
  (PARTSEL 0 97 (:VAR
  ("product_terms" . 1) . 0)))))
  nil)||#

  (define get-intersecting-occ-for-lhs ((lhs sv::lhs-p)
                                        (sig-to-occ-listeners)
                                        (all-occs occ-alist-p))
    (if (atom lhs)
        nil
      (b* ((rest (get-intersecting-occ-for-lhs (cdr lhs)
                                               sig-to-occ-listeners
                                               all-occs))
           ((sv::lhrange range) (car lhs))
           ((when (eq (sv::lhatom-kind range.atom) ':z))
            rest)
           ((sv::lhatom-var atom) range.atom))
        (get-intersecting-occs atom.name
                               atom.rsh
                               range.w
                               (cdr (hons-get atom.name sig-to-occ-listeners))
                               all-occs
                               rest))))

  (define get-intersecting-occ-for-wires ((wires wire-list-p)
                                          (sig-to-occ-listeners)
                                          (all-occs occ-alist-p)
                                          &key
                                          (duplicate 'nil))
    (if (atom wires)
        nil
      (b* ((rest (get-intersecting-occ-for-wires (cdr wires)
                                                 sig-to-occ-listeners
                                                 all-occs
                                                 :duplicate duplicate))
           (wire (car wires))
           ((mv name start size)
            (mv (wire-name wire) (wire-start wire) (wire-size wire)))
           ((unless start)
            (hard-error 'get-intersecting-occ-for-wires
                        "Unexpected wire type ~p0 ~%"
                        (list (cons #\0 wire)))))
        (get-intersecting-occs name
                               start
                               size
                               (cdr (hons-get name sig-to-occ-listeners))
                               all-occs
                               rest
                               :duplicate duplicate))))

  (define create-occ-to-occ-listeners ((occs occ-alist-p)
                                       (all-occs occ-alist-p)
                                       (sig-to-occ-listeners))
    (if (atom occs)
        nil
      (b* ((occ-name (caar occs))
           (occ (cdar occs))
           (value (if (equal (occ-kind occ) ':assign)
                      (get-intersecting-occ-for-wires (occ-assign->outputs occ)
                                                      sig-to-occ-listeners
                                                      all-occs)
                    (b* ((lhs (module-occ-wires->lhs (occ-module->outputs occ))))
                      (get-intersecting-occ-for-lhs
                       (if (sv::lhs-p lhs) lhs
                         (hard-error
                          'create-occ-to-occ-listeners
                          "This should not have happened ~%"
                          nil))
                       sig-to-occ-listeners
                       all-occs))))
           #|(- (if (and (equal (occ-kind occ) ':assign)
           (equal occ-name 'ASSIGN_26))
           (cw "value ~p0, outputs ~p1, listeners ~p2, intersecting ~p3 ~%"
           value
           (occ-assign->outputs occ)
           (cdr (hons-get '(:VAR
           ("product_terms" . 0) . 0)
           sig-to-occ-listeners))
           (get-intersecting-occs '(:VAR ("product_terms" . 0) . 0)
           91
           1
           (cdr (hons-get '(:VAR
           ("product_terms" . 0) . 0)
           sig-to-occ-listeners))
           all-occs
           nil))
           nil))||#
           (rest (create-occ-to-occ-listeners (cdr occs)
                                              all-occs
                                              sig-to-occ-listeners)))
        (if value
            (acons occ-name value rest)
          rest))))

  (define fast-unify-list ((vals true-listp))
    :verify-guards nil
    (declare (xargs :mode :program)) ;; for guards
    (b* ((vals (pairlis$ vals nil))
         (vals (make-fast-alist vals))
         (vals (fast-alist-clean vals))
         (vals (fast-alist-free vals)))
      (strip-cars vals)))

  (define add-initial-to-occ-listeners ((input-wires wire-list-p)
                                        (all-occs occ-alist-p)
                                        (sig-to-occ-listeners)
                                        (occ-to-occ-listeners))
    (declare (xargs :mode :program))
    (b* ((val1 (get-intersecting-occ-for-wires input-wires
                                               sig-to-occ-listeners
                                               all-occs
                                               :duplicate t))
         (val1 (fast-unify-list val1))
         (occ-to-occ-listeners (hons-acons ':initial val1
                                           occ-to-occ-listeners))
         (val2 (sv->svl-listeners-uncovered-occs occ-to-occ-listeners
                                                 all-occs))
         (val (append val1 val2)))
      (fast-alist-clean (hons-acons ':initial val
                                    occ-to-occ-listeners)))))

(progn
  (define create-occ-in-nodes-count-aux ((occ-names)
                                         (acc))
    :verify-guards nil
    (if (atom occ-names)
        acc
      (b* ((this (car occ-names))
           (entry (hons-get this acc))
           (val (if entry (1+ (cdr entry)) 1))
           (acc (hons-acons this val acc)))
        (create-occ-in-nodes-count-aux (cdr occ-names)
                                       acc))))

  (define create-occ-in-nodes-count ((listeners)
                                     (acc))
    ;; create an alist
    ;; keys are occ-names
    ;; and values are total number of other occs that need to be evaluated before.
    :verify-guards nil
    (if (atom listeners)
        (fast-alist-clean acc)
      (create-occ-in-nodes-count (cdr listeners)
                                 (create-occ-in-nodes-count-aux (cdar listeners)
                                                                acc))))

  (acl2::defines
   svl2-sort-occs
   (define svl2-sort-occs ((occ-name occ-name-p)
                           (all-occs occ-alist-p)
                           (occ-to-occ-listeners)
                           (occ-in-nodes-count))
     :verify-guards nil
     (declare (xargs :mode :program))
     (b* ((occ (hons-get occ-name all-occs))
          (candidates (cdr (hons-get occ-name occ-to-occ-listeners)))
          ((mv rest occ-in-nodes-count)
           (svl2-sort-occs-lst candidates all-occs occ-to-occ-listeners
                               occ-in-nodes-count)))
       (mv (cons occ rest)
           occ-in-nodes-count)))

   (define svl2-sort-occs-lst ((candidates occ-name-list-p
                                           "Occs that might be ready to add")
                               (all-occs occ-alist-p)
                               (occ-to-occ-listeners)
                               (occ-in-nodes-count))
     (cond
      ((atom candidates)
       (mv nil occ-in-nodes-count))
      (t
       (b* ((cur (car candidates))
            (in-node-cnt (1- (nfix (cdr (hons-get cur occ-in-nodes-count)))))
            (occ-in-nodes-count (hons-acons cur in-node-cnt occ-in-nodes-count))
            ((mv added-occs occ-in-nodes-count)
             (if (equal in-node-cnt 0)
                 (svl2-sort-occs cur all-occs occ-to-occ-listeners
                                 occ-in-nodes-count)
               (mv nil occ-in-nodes-count)))
            ((mv rest occ-in-nodes-count)
             (svl2-sort-occs-lst (cdr candidates)
                                 all-occs
                                 occ-to-occ-listeners
                                 occ-in-nodes-count)))
         (mv (append added-occs rest)
             occ-in-nodes-count))))))

  ;; to check and make sure that all the occ are added.
  (define count-not-added-occs (occ-in-nodes-count)
    :verify-guards  nil
    (if (atom occ-in-nodes-count)
        0
      (+ (if (not (equal (cdar occ-in-nodes-count) 0))
             1
           0)
         (count-not-added-occs (cdr occ-in-nodes-count)))))


  (define get-not-added-module-occs ((all-occs occ-alist-p)
                                     (occ-in-nodes-count))
    (declare (xargs :mode :program))
    (if (atom occ-in-nodes-count)
        nil
      (b* ((rest (get-not-added-module-occs all-occs (cdr occ-in-nodes-count)))
           (not-added (not (equal (cdar occ-in-nodes-count) 0)))
           (is-module (equal (svl::occ-kind (cdr (hons-get (caar occ-in-nodes-count)
                                                           all-occs)))
                             ':module))
           (module-name (if is-module (svl::occ-module->name (cdr (hons-get (caar occ-in-nodes-count)
                                                                            all-occs)))
                          nil)))
        (if (and not-added
                 is-module
                 (not (member-equal module-name rest)))
            (cons module-name rest)
          rest)))) 
  
  (define svl2-sort-occs-main ((all-occs occ-alist-p)
                               (occ-to-occ-listeners))
    (declare (xargs :mode :program))
    (b* ((occ-in-nodes-count (create-occ-in-nodes-count occ-to-occ-listeners
                                                        'occ-in-nodes-count))
         ((mv sorted-occs occ-in-nodes-count)
          (svl2-sort-occs-lst (cdr (hons-get ':initial occ-to-occ-listeners))
                              all-occs
                              occ-to-occ-listeners
                              occ-in-nodes-count))
         (occ-in-nodes-count (fast-alist-clean occ-in-nodes-count))
         (not-added-occs-count (count-not-added-occs occ-in-nodes-count))
         (- (and (not (equal not-added-occs-count 0))
                 (progn$
                  (cw "~% ~% Not added modules: ~p0 ~%"
                      (get-not-added-module-occs all-occs occ-in-nodes-count))
                  (hard-error 'svl2-sort-occs-main
                              "~p0 occs are not added! Possibly a combinational
                               loop~% ~%"
                              (list (cons #\0 not-added-occs-count))))))
         (- (fast-alist-free occ-in-nodes-count)))
      sorted-occs)))

;;;;;;;;;;;;;;

(define wire-list-listp (list)
  :enabled t
  (if (atom list)
      (equal list nil)
    (and (wire-list-p (car list))
         (wire-list-listp (cdr list)))))

(define wire-list-list-fix (list)
  :returns (res wire-list-listp)
  :enabled t
  (if (wire-list-listp list)
      list
    nil))

(fty::deffixtype wire-list-list
                 :pred  wire-list-listp
                 :fix   wire-list-list-fix
                 :equiv equal)

(fty::deftagsum
 svl2-occ
 (:assign ((output sv::svar-p)
           (svex sv::svex-p)))
 (:module ((inputs sv::svexlist-p)
           (outputs wire-list-list)
           (name sv::modname-p))))

(fty::defalist svl2-occ-alist
               :true-listp t
               :val-type svl2-occ)

(define lhs->svex ((acl2::x sv::lhs-p))
  :returns (sv::xx svex-p)
  (if (atom acl2::x)
      0
    (b* (((sv::lhrange sv::xf) (car acl2::x)))
      (sv::svex-concat sv::xf.w (sv::lhatom->svex sv::xf.atom)
                       (lhs->svex (cdr acl2::x))))))

(define lhslist->svex ((lhslist sv::lhslist-p))
  :returns (res sv::svexlist-p)
  (if (atom lhslist)
      nil
    (cons (lhs->svex (car lhslist))
          (lhslist->svex (cdr lhslist)))))

(define occs->svl2-occs-assign ((occ-name occ-name-p)
                                (outputs wire-list-p)
                                (svex sv::svex-p)
                                (wires sv::wirelist-p)
                                (rsh natp))
  :verify-guards nil
  :returns (res svl2-occ-alist-p)
  :guard-hints (("Goal"
                 :in-theory (e/d (svex-p sv::svar-p) ())))
  (if (atom outputs)
      nil
    (b* ((cur-output (car outputs))
         (only-1-output (and (equal (len outputs) 1)
                             (equal rsh 0)))
         (wire  (vl-insouts-assocwire (wire-name cur-output) wires))
         (whole-wire-covered (and (equal (- (nfix (sv::wire->width wire))
                                            (nfix (sv::wire->low-idx wire)))
                                         (wire-size cur-output))
                                  (equal (wire-start cur-output)
                                         0))))
      (if only-1-output
          (acons occ-name
                 (make-svl2-occ-assign
                  :output (wire-name cur-output)
                  :svex (if whole-wire-covered
                            svex
                          `(sv::partinst ,(wire-start cur-output)
                                         ,(wire-size cur-output)
                                         ,(wire-name cur-output)
                                         ,svex)))
                 nil)
        (acons (cons occ-name rsh)
               (make-svl2-occ-assign
                :output (wire-name cur-output)
                :svex (if whole-wire-covered
                          `(partsel ,rsh ,(wire-size cur-output) ,svex)
                        `(sv::partinst ,(wire-start cur-output)
                                       ,(wire-size cur-output)
                                       ,(wire-name cur-output)
                                       (partsel ,rsh ,(wire-size cur-output)
                                                ,svex))))
               (occs->svl2-occs-assign occ-name
                                       (cdr outputs)
                                       svex
                                       wires
                                       (+ rsh (nfix (wire-size cur-output)))))))))

(progn
  (define lhrange->wire ((range sv::lhrange-p))
    :Returns (res wire-p)
    (b* (((sv::lhrange range) range))
      (if (equal (sv::lhatom-kind range.atom) :z)
          `(:z ,range.w . 0)
        `(,(sv::lhatom-var->name range.atom)
          ,range.w
          .
          ,(sv::lhatom-var->rsh range.atom)))))

  (define lhs->wire-list ((lhs sv::lhs-p))
    :returns (res wire-list-p)
    (if (atom lhs)
        nil
      (cons (lhrange->wire (car lhs))
            (lhs->wire-list (cdr lhs)))))

  (define lhslist->wire-list ((lhslist sv::lhslist-p))
    :returns (res wire-list-listp)
    (if (atom lhslist)
        nil
      (cons (lhs->wire-list (car lhslist))
            (lhslist->wire-list (cdr lhslist))))))

(define occs->svl2-occs ((occs occ-alist-p)
                         (wires sv::wirelist-p))
;:returns (res svl2-occ-alist :hyp (occ-alist-p occs))
  :verify-guards nil
  :returns (res svl2-occ-alist-p)
  (cond
   ((atom occs) nil)
   ((equal (occ-kind (cdar occs)) ':assign)
    (b* (((occ-assign occ) (cdar occs))
         (new-svl2-occs (occs->svl2-occs-assign (caar occs) occ.outputs occ.svex wires 0)))
      (append new-svl2-occs
              (occs->svl2-occs (cdr occs) wires))))
   (t (b* (((occ-module occ) (cdar occs)))
        (acons (caar occs)
               (make-svl2-occ-module
                :inputs (lhslist->svex (strip-cdrs occ.inputs))
                :outputs (lhslist->wire-list (strip-cdrs occ.outputs))
                :name occ.name)
               (occs->svl2-occs (cdr occs)
                                wires))))))

(fty::defprod
 svl2-module
 ((rank natp :default '0)
  (inputs wire-list-p)
  (delayed-inputs sv::svarlist-p)
  (outputs wire-list-p)
  (occs svl2-occ-alist))
 :layout :alist)

(fty::defalist svl2-module-alist
               :val-type svl2-module
               :true-listp t
               :key-type sv::modname-p)

(define union-equal2 ((lst1)
                      (lst2 true-listp))
  :prepwork
  ((local
    (in-theory (disable (:DEFINITION ALWAYS$)))))

  (if (atom lst1)
      lst2
    (b* ((rest (union-equal2 (cdr lst1) lst2)))
      (if (member-equal (car lst1) rest)
          rest
        (cons (car lst1) rest))))
  ///
  (defthm svarlist-p-of-union-equal2
    (implies (and (sv::svarlist-p lst1)
                  (sv::svarlist-p lst2))
             (sv::svarlist-p (union-equal2 lst1 lst2)))
    :hints (("Goal"
             :in-theory (e/d (sv::svarlist-p union-equal2) ())))))

(define svl2-collect-delayed-inputs ((occs occ-alist-p))
  :verify-guards nil
  :returns (res sv::svarlist-p)
  (if (atom occs)
      nil
    (b* ((rest (svl2-collect-delayed-inputs (cdr occs)))
         (occ (cdar occs)))
      (if (equal (occ-kind occ) ':module)
          rest
        (union-equal2 (occ-assign->delayed-inputs occ)
                      rest))))
  ///
  (verify-guards svl2-collect-delayed-inputs))

(define svl2-flatten-mod ((modname sv::modname-p)
                          (modalist sv::modalist-p)
                          (mods-to-skip sv::modnamelist-p)
                          (vl-insouts vl-insouts-sized-p)
                          (svex-simplify-preloaded)
                          &key
                          (rp::rp-state 'rp::rp-state)
                          (state 'state))
  (declare (xargs :mode :program))
  :guard (svex-simplify-preloaded-guard svex-simplify-preloaded state)
  (b* ((- (cw "Now working on mod: ~p0 ~%" modname))
       ((mv input-wires output-wires)
        (mv (cadr (assoc-equal modname vl-insouts))
            (cddr (assoc-equal modname vl-insouts))))

       (- (cw "Processing alias-pairs... "))
       ;; Create aliasdb
       (aliasdb (mod-aliaspairs->aliasdb modname modalist mods-to-skip))

       (- (cw "Creating occs... "))
       ;; Create occs
       ((mv occs rp::rp-state) (sv-mod->svl2-occs modname
                                                  modalist
                                                  aliasdb
                                                  nil
                                                  mods-to-skip
                                                  vl-insouts
                                                  svex-simplify-preloaded
                                                  (expt 2 30)))

       ;; Expand occs for cases where input and output signals are aliased to
       ;; other signals
       ((mv init-occs-for-aliased-inputs & rp::rp-state)
        (svl2-flatten-mod-insert-assigns-for-inputs (aliasdb->this aliasdb)
                                                    input-wires
                                                    0
                                                    svex-simplify-preloaded))
       ((mv occs-for-outputs & rp::rp-state)
        (svl2-flatten-mod-insert-assigns-for-outputs (aliasdb->this aliasdb)
                                                     output-wires
                                                     0
                                                     svex-simplify-preloaded
                                                     modname
                                                     modalist))
       (occs (append init-occs-for-aliased-inputs occs-for-outputs occs))

       (- (cw "Sorting occs... "))
       ;; Create Listeners.
       (occs (make-fast-alist occs)) ;; necessary for occ-to-occ listeners.
       (sig-to-occ-listeners (fast-alist-clean (create-signal-to-occ-listeners occs 'sig-to-occ-listeners)))
       (occ-to-occ-listeners (create-occ-to-occ-listeners occs occs sig-to-occ-listeners))
       (occ-to-occ-listeners (make-fast-alist occ-to-occ-listeners))
       (occ-to-occ-listeners (add-initial-to-occ-listeners input-wires occs
                                                           sig-to-occ-listeners
                                                           occ-to-occ-listeners))
       ;; Sort occs
       (sorted-occs (svl2-sort-occs-main occs occ-to-occ-listeners))

       ;; Convert occs to to svl2-occs
       (wires (sv::module->wires (cdr (assoc-equal modname modalist))))
       (new-svl2-occs (occs->svl2-occs sorted-occs wires))

       (- (free-aliasdb aliasdb))
       (- (fast-alist-free occs))
       (- (fast-alist-free sig-to-occ-listeners))
       (- (fast-alist-free occ-to-occ-listeners))
       (- (cw "Done! ~% ~%"))
       (?module (cons modname
                      (make-svl2-module :inputs input-wires
                                        :delayed-inputs
                                        (svl2-collect-delayed-inputs occs)
                                        :outputs output-wires
                                        :occs new-svl2-occs))))
    (mv module rp::rp-state)))

#|(b* ((vl-insouts (vl-design-to-insouts *big-vl-design2* *big-sv-design*))
     (vl-insouts2 (vl-insouts-insert-wire-sizes vl-insouts *big-sv-design*
                                                '("full_adder_1$WIDTH=1"
                                                  "full_adder$WIDTH=1"
                                                  "booth2_reduction_dadda_17x65_97")
                                                ))
     (svex-simplify-preloaded (svex-simplify-preload)))
  (svl2-flatten-mod "booth2_reduction_dadda_17x65_97"
                    (make-fast-alist (sv::design->modalist *big-sv-design*))
                    '("full_adder_1$WIDTH=1" "full_adder$WIDTH=1")
                    vl-insouts2
                    svex-simplify-preloaded))||#

(define svl2-flatten-mods ((modnames sv::modnamelist-p)
                           (modalist sv::modalist-p)
                           (mods-to-skip sv::modnamelist-p)
                           (vl-insouts vl-insouts-sized-p)
                           (svex-simplify-preloaded)
                           &key
                           (rp::rp-state 'rp::rp-state)
                           (state 'state))
  :guard (svex-simplify-preloaded-guard svex-simplify-preloaded state)
  (declare (xargs :mode :program))
  (if (atom modnames)
      (mv nil rp::rp-state)
    (b* (((mv this rp::rp-state)
          (svl2-flatten-mod (car modnames)
                            modalist
                            mods-to-skip
                            vl-insouts
                            svex-simplify-preloaded))
         ((mv rest rp::rp-state)
          (svl2-flatten-mods (cdr modnames)
                             modalist
                             mods-to-skip
                             vl-insouts
                             svex-simplify-preloaded)))
      (mv (cons this rest)
          rp::rp-state))))

(acl2::defines
 svl2-mod-calculate-ranks
 (define svl2-mod-calculate-ranks ((modname sv::modname-p)
                                   (modules svl2-module-alist-p)
                                   (ranks alistp$)
                                   (trace) ;; to check for module instantiation loops
                                   (limit natp) ;; to easily prove termination
                                   )
   :verify-guards nil
   (declare (xargs :mode :program)) ;; to profile...
   :measure (nfix limit)
   (cond
    ((zp limit)
     ranks)
    ((member-equal modname trace)
     (hard-error 'svl2-mod-calculate-ranks
                 "It seems there's a loop in module instances. Trace = ~p0,
                                  module = ~p1 ~%"
                 (list (cons #\0 trace)
                       (cons #\1 modname))))
    (t  (b* ((module (assoc-equal modname modules))
             ((unless module) ranks)
             (module (cdr module))
             (occs (svl2-module->occs module))
             ((mv max-occ-rank ranks)
              (svl2-mod-calculate-ranks-occs occs
                                             modules
                                             ranks
                                             (cons modname trace)
                                             (1- limit))))
          (acons modname (1+ max-occ-rank) ranks)))))
 (define svl2-mod-calculate-ranks-occs ((occs svl2-occ-alist-p)
                                        (modules svl2-module-alist-p)
                                        (ranks alistp$)
                                        (trace)
                                        (limit natp))
   :measure (nfix limit)
   (cond
    ((zp limit)
     (mv 0 ranks))
    ((atom occs)
     (mv 0 ranks))
    (t
     (b* (((mv rest-max ranks)
           (svl2-mod-calculate-ranks-occs (cdr occs) modules ranks trace (1- limit)))
          ((when (equal (svl2-occ-kind (cdar occs)) :assign))
           (mv rest-max ranks))
          (modname (svl2-occ-module->name (cdar occs)))
          (module-rank (assoc-equal modname ranks))
          ((when module-rank)
           (mv (max (cdr module-rank) rest-max) ranks))
          (ranks (svl2-mod-calculate-ranks modname modules ranks trace (1- limit)))
          (module-rank (assoc-equal modname ranks))
          ((when module-rank)
           (mv (max (cdr module-rank) rest-max) ranks)))
       (mv 0
           (hard-error 'svl2-mod-calculate-ranks
                       "Something is wrong. Cannot calculate rank for module ~p0~%"
                       (list (cons #\0 modname)))))))))

(define update-modules-with-ranks ((ranks alistp)
                                   (modules svl2-module-alist-p))
  (if (atom modules)
      nil
    (acons (caar modules)
           (change-svl2-module (cdar modules)
                               :rank (nfix (cdr (assoc-equal (caar modules)
                                                             ranks))))
           (update-modules-with-ranks ranks
                                      (cdr modules)))))

(define get-string-modnames ((modnames sv::modnamelist-p))
  :returns (res string-listp)
  (if (atom modnames)
      nil
    (if (stringp (car modnames))
        (cons (car modnames)
              (get-string-modnames (cdr modnames)))
      (get-string-modnames (cdr modnames)))))

;; (str::strprefixp (concatenate 'string name "$") sv-module-name)

(progn
  (define fix-dont-aflatten-aux ((base stringp)
                                 (sv-module-names string-listp))
    :returns (res string-listp
                  :hyp (string-listp sv-module-names))
    (if (atom sv-module-names)
        nil
      (b* ((sv-module-name (car sv-module-names))
           (rest (fix-dont-aflatten-aux base
                                        (cdr sv-module-names))))
        (if (str::strprefixp (concatenate 'string base "$") sv-module-name)
            (cons sv-module-name
                  rest)
          rest))))

  (local
   (defthm string-listp-of-append
     (implies (and (string-listp x)
                   (string-listp y))
              (string-listp (append x y)))))

  (define fix-dont-flatten ((dont-flatten string-listp)
                            (sv-module-names string-listp))
    :returns (res string-listp :hyp (and (string-listp dont-flatten)
                                         (string-listp sv-module-names)))
    (if (atom dont-flatten)
        nil
      (b* ((extra-mod-names (fix-dont-aflatten-aux (car dont-flatten)
                                                   sv-module-names)))
        (append
         extra-mod-names
         (cons (car dont-flatten)
               (fix-dont-flatten (cdr dont-flatten)
                                 sv-module-names)))))))

(define clean-dont-flatten ((dont-flatten string-listp)
                            (all-modnames string-listp))
  :returns (res string-listp
                :hyp (string-listp dont-flatten))
  (if (atom dont-flatten)
      nil
    (b* ((rest (clean-dont-flatten (cdr dont-flatten) all-modnames)))
      (if (member-equal (car dont-flatten) all-modnames)
          (cons (car dont-flatten)
                rest)
        rest))))

(define svl2-flatten-design ((sv-design sv::design-p)
                             (vl-design)
                             &key
                             (rp::rp-state 'rp::rp-state)
                             (dont-flatten 'nil) ;; names of modules that
                             ;; should not be flattened. It should be the
                             ;; original name of the module from Verilog
                             ;; designs. (but not from SV designs)
                             (top 'nil) ;; can override the top module.
                             (state 'state))
  (declare (xargs :mode :program))
  (b* (((sv::design sv-design) sv-design)
       (sv-design.modalist (make-fast-alist sv-design.modalist))

       (all-modnames (get-string-modnames (strip-cars sv-design.modalist)))
       (dont-flatten-all (equal dont-flatten ':all))
       (top (if top top sv-design.top))
       (dont-flatten (if dont-flatten-all
                         all-modnames
                       (fix-dont-flatten
                        (union-equal dont-flatten
                                     (list top))
                        all-modnames)))

       (vl-insouts (vl-design-to-insouts vl-design
                                         sv-design
                                         (if dont-flatten-all nil dont-flatten)))

       (dont-flatten
        (if dont-flatten-all
            all-modnames
          (clean-dont-flatten dont-flatten all-modnames)))

       (vl-insouts (vl-insouts-insert-wire-sizes vl-insouts sv-design
                                                 dont-flatten))

       (svex-simplify-preloaded (svex-simplify-preload
                                 :runes *svl2-flatten-simplify-lemmas*
                                 ))
       (- (cw "Starting to flatten modules and create SVL2 design... ~%"))
       ((mv modules rp::rp-state)
        (svl2-flatten-mods dont-flatten sv-design.modalist
                           dont-flatten vl-insouts
                           svex-simplify-preloaded))
       (- (cw "Inserting ranks to unflattened modules... ~%"))
       (ranks (svl2-mod-calculate-ranks top
                                        modules
                                        nil
                                        nil
                                        (expt 2 30)))
       (modules (update-modules-with-ranks ranks
                                           modules))
       (- (cw "All done! ~%"))
       (- (fast-alist-free sv-design.modalist))
       (- (svex-rw-free-preload svex-simplify-preloaded state)))
    (mv modules rp::rp-state)))

(define svl2-modules-port-info ((modules svl2-module-alist-p))
  (if (atom modules)
      nil
    (acons (caar modules)
           `((:inputs . ,(svl2-module->inputs (cdar modules)))
             (:outputs . ,(svl2-module->outputs (cdar modules))))
           (svl2-modules-port-info (cdr modules)))))

;;;

;;

;;;;

#|
:i-am-here

(b* ((modnames '("fa" "mul_test1" "partial")))
  (svl2-flatten-design modnames
                       *booth-sv-design*
                       *booth-vl-design2*))

(b* ((modnames '("full_adder_1$WIDTH=1"
                 "full_adder$WIDTH=1"
                 "booth2_reduction_dadda_17x65_97"
                 "booth2_multiplier_signed_64x32_97")))
  (svl2-flatten-design modnames
                       *big-sv-design*
                       *big-vl-design2*))

#|(svl2-flatten-mod "booth_encoder"
                 (make-fast-alist (sv::design->modalist *booth-sv-design*))
nil)||#

(b* ((vl-insouts (vl-design-to-insouts *big-vl-design2* *big-sv-design*))
(vl-insouts2 (vl-insouts-insert-wire-sizes vl-insouts *big-sv-design*
'("full_adder_1$WIDTH=1"
"full_adder$WIDTH=1"
"booth2_reduction_dadda_17x65_97"
"booth2_multiplier_signed_64x32_97")
)))
(svl2-flatten-mod "booth2_multiplier_signed_64x32_97"
(make-fast-alist (sv::design->modalist *big-sv-design*))
'("full_adder_1$WIDTH=1" "full_adder$WIDTH=1" "booth2_reduction_dadda_17x65_97")
vl-insouts2))

(b* ((vl-insouts (vl-design-to-insouts *big-vl-design2* *big-sv-design*))
(vl-insouts2 (vl-insouts-insert-wire-sizes vl-insouts *big-sv-design*
'("full_adder_1$WIDTH=1"
"full_adder$WIDTH=1"
"booth2_reduction_dadda_17x65_97")
))
(svex-simplify-preloaded (svex-simplify-preload)))
(svl2-flatten-mod "booth2_reduction_dadda_17x65_97"
(make-fast-alist (sv::design->modalist *big-sv-design*))
'("full_adder_1$WIDTH=1" "full_adder$WIDTH=1")
vl-insouts2
svex-simplify-preloaded))
||#
