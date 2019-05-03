; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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

; g-sexpr-eval.lisp
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "svarmap")
(include-book "sexpr-to-faig")
(include-book "sexpr-equivs")
(include-book "centaur/gl/gl-util" :dir :system)
(include-book "centaur/misc/numlist" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
(local (include-book "centaur/misc/hons-sets" :dir :system))
(local (include-book "centaur/aig/eval-restrict" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (in-theory (disable nth-when-zp)))


(defun num-varmap (keys n)
  (declare (xargs :guard (acl2-numberp n)))
  (let* ((keys     (hons-remove-duplicates keys))
         (nkeys    (len keys))
         (onsets   (numlist n 2 nkeys))
         (offsets  (numlist (+ 1 n) 2 nkeys))
         (onoff    (pairlis$ onsets offsets))
         (onoff-al (pairlis$ keys onoff)))

; Honsing the onoff-alist is useful for def-gl-param-thms.  See the comments in
; 4v-sexpr-eval-by-faig for more details.

    (hons-copy onoff-al)))



(local
 (defun vvnv-ind (n keys)
   (if (atom keys)
       n
     (vvnv-ind (+ 2 n) (cdr keys)))))


(local
 (progn

   (defthm hons-assoc-equal-in-num-varmap1
     (implies (acl2-numberp n)
              (equal (HONS-ASSOC-EQUAL
                      KEY0
                      (PAIRLIS$ keys
                                (PAIRLIS$ (NUMLIST n 2 (len keys))
                                          (NUMLIST (+ 1 n) 2 (len keys)))))
                     (and (member-equal key0 keys)
                          (cons key0
                                (cons (+ n (* 2 (- (len keys)
                                                   (len (member-equal key0 keys)))))
                                      (+ 1 n (* 2 (- (len keys)
                                                     (len (member-equal key0 keys))))))))))
     :hints(("Goal" :in-theory (enable member-equal
                                       hons-assoc-equal
                                       pairlis$)
             :induct (vvnv-ind n keys))))

   (defun num-varmap-key-idx (key keys n)
     (let ((keys (hons-remove-duplicates keys)))
       (+ n (* 2 (- (len keys) (len (member-equal key keys)))))))

   (defthm hons-assoc-equal-in-num-varmap
     (implies (acl2-numberp n)
              (equal (hons-assoc-equal key0 (num-varmap keys n))
                     (and (member-equal key0 keys)
                          (cons key0
                                (cons (num-varmap-key-idx key0 keys n)
                                      (+ 1 (num-varmap-key-idx key0 keys n))))))))

   (in-theory (disable num-varmap-key-idx))

   (defthm len-pairlis$
     (equal (len (pairlis$ a b))
            (len a)))

   (defthm hons-assoc-equal-pairlis$
     (implies (equal (len a) (len b))
              (iff (hons-assoc-equal k (pairlis$ a b))
                   (member-equal k a)))
     :hints(("Goal" :in-theory (enable hons-assoc-equal
                                       pairlis$))))


   (defthm svarmap-vals-num-varmap
     (equal (svarmap-vals (pairlis$
                           keys
                           (pairlis$ (numlist n 2 (len keys))
                                     (numlist (+ 1 n) 2 (len keys)))))
            (numlist n 1 (* 2 (len keys))))
     :hints (("goal" :induct (vvnv-ind n keys)
              :expand ((:free (k) (numlist n 1 k))
                       (:free (k) (numlist (+ 1 n) 1 k))))))

   (defthm alist-keys-pairlis$
     (implies (equal (len a) (len b))
              (equal (alist-keys (pairlis$ a b))
                     (append a nil))))

   (defthm aig-svar-cons-val-alistp-num-varmap
     (implies (acl2-numberp n)
              (aig-svar-cons-val-alistp
               (pairlis$
                keys
                (pairlis$ (numlist n 2 (len keys))
                          (numlist (+ 1 n) 2 (len keys))))))
     :hints (("goal" :induct (vvnv-ind n keys))))

   (defthm not-member-numlist-when-less-than-start
     (implies (and (acl2-numberp n)
                   (< x n)
                   (< 0 diff))
              (not (member-equal x (numlist n diff k)))))

   (defthm no-duplicatesp-numlist
     (no-duplicatesp-equal (numlist n 1 k)))

   (defthm not-member-numlist-when-not-number
     (implies (and (acl2-numberp n)
                   (not (acl2-numberp x)))
              (not (member-equal x (numlist n d k)))))


   (defthm good-svarmap-num-varmap1
     (implies (and (no-duplicatesp-equal keys)
                   (acl2-numberp n))
              (good-svarmap (pairlis$
                             keys
                             (pairlis$ (numlist n 2 (len keys))
                                       (numlist (+ 1 n) 2 (len keys))))))
     :hints(("Goal" :in-theory (e/d (good-svarmap))
             :do-not-induct t))
     :otf-flg t)

   (defthm good-svarmap-num-varmap
     (implies (acl2-numberp idx)
              (good-svarmap (num-varmap keys idx))))

   (in-theory (disable num-varmap))))

(defthm good-svarmap-num-varmap
  ;; [Jared]: Adding this non-locally so that I can use it in simple
  ;; sexpr->faig conversion.
  (implies (acl2-numberp idx)
           (good-svarmap (num-varmap keys idx))))



(defun 4v-sexpr-eval-by-faig (x al opt)
  (let* ((vars (alist-keys al))
         ;; hons-copy the varmap so that sexpr-to-faig-3v-opt memoization can happen
         (onoff-al (make-fast-alist (num-varmap vars 0)))
         (faig-eval-al (sig-al-to-svar-al
                        (4v-alist->faig-const-alist al) onoff-al)))
  (faig-const->4v
   (faig-eval
    (4v-sexpr-to-faig x onoff-al :optimize opt)
    faig-eval-al))))

(defun 4v-sexpr-eval-by-faig-list (x al opt)
  (b* ((vars (alist-keys al))
       ;; hons-copy the varmap so that 4v-sexpr-to-faig-opt memoization can happen
       (onoff-al (make-fast-alist (cwtime (num-varmap vars 0) :mintime 1)))
       (faig-eval-al (sig-al-to-svar-al
                      (cwtime (4v-alist->faig-const-alist al) :mintime 1)
                      onoff-al))
       (faig-list (cwtime (4v-sexpr-to-faig-list x onoff-al :optimize opt)
                          :mintime 1))
       (evals (cwtime (faig-eval-list faig-list faig-eval-al) :mintime 1)))
    (cwtime (faig-const-list->4v-list evals) :mintime 1)))

(defthmd 4v-sexpr-eval-by-faig-list-alt-def
  (equal (4v-sexpr-eval-by-faig-list x al opt)
         (if (atom x)
             nil
           (cons (4v-sexpr-eval-by-faig (car x) al opt)
                 (4v-sexpr-eval-by-faig-list (cdr x) al opt))))
  :hints(("Goal" :in-theory (e/d (4v-list->faig-const-list
                                  faig-const-list->4v-list)
                                 (faig-eval 4v-sexpr-to-faig-opt
                                            faig-const->4v
                                            4v->faig-const
                                            4v-sexpr-to-faig-plain
                                            4v-sexpr-eval))))
  :rule-classes ((:definition :install-body nil)))





(local
 (progn
   (defthm iff-cons-t
     (iff (cons a b) t))

   (defun my-evenp (x)
     (if (zp x)
         t
       (and (not (eql x 1))
            (my-evenp (- x 2)))))

   (encapsulate
     nil
     (local
      (progn

        (defthm my-evenp-integer-half
          (implies (and (natp x)
                        (my-evenp x))
                   (integerp (* 1/2 x))))

        (defthm not-my-evenp-integerp-minus-half
          (implies (and (natp x)
                        (not (my-evenp x)))
                   (integerp (+ -1/2 (* 1/2 x)))))

        (defthm my-evenp-integerp-half-diff
          (implies (and (natp (- k n))
                        (my-evenp (- k n)))
                   (integerp (+ (* 1/2 k) (- (* 1/2 n)))))
          :hints (("goal" :use ((:instance my-evenp-integer-half
                                           (x (- k n)))))))

        (defthm not-my-evenp-integerp-half-diff
          (implies (and (natp (- k n))
                        (not (my-evenp (- k n))))
                   (integerp (+ -1/2 (* 1/2 k) (- (* 1/2 n)))))
          :hints (("goal" :use ((:instance not-my-evenp-integerp-minus-half
                                           (x (- k n)))))))

        (defthm within-2-lemma
          (implies (and (integerp m)
                        (<= 0 m)
                        (< m 2)
                        (not (equal m 0)))
                   (equal m 1))
          :rule-classes nil)

        (defthm k-minus-n-within-2
          (implies (and (integerp (- k n))
                        (acl2-numberp n)
                        (acl2-numberp k)
                        (<= n k)
                        (not (equal k n))
                        (not (equal k (+ 1 n))))
                   (not (< (+ k (- n)) 2)))
          :hints (("goal" :use ((:instance within-2-lemma
                                           (m (- k n)))))))

        (defthm half-diff-lt-half
          (implies (natp (- k n))
                   (iff (< 1/2 (+ (* 1/2 k) (- (* 1/2 n))))
                        (< 1 (- k n))))
          :hints (("goal" :use ((:instance <-*-left-cancel
                                           (z 1/2)
                                           (y (- k n))
                                           (x 1))))))
        ))


     (defthm svar-assoc-num-varmap1
       (implies (and (no-duplicatesp-equal keys)
                     (acl2-numberp k) (acl2-numberp n)
                     )
                (equal (svar-assoc k (pairlis$
                                      keys
                                      (pairlis$ (numlist n 2 (len keys))
                                                (numlist (+ 1 n) 2 (len keys)))))
                       (and (natp (- k n))
                            (< (- k n) (* 2 (len keys)))
                            (if (my-evenp (- k n))
                                (cons (nth (/ (- k n) 2) keys) t)
                              (cons (nth (/ (1- (- k n)) 2) keys) nil)))))
       :hints (("goal" :induct (vvnv-ind n keys)
                :do-not-induct t
                :in-theory (enable natp)))))


   (defthm svar-assoc-num-varmap
     (implies (and (acl2-numberp n)
                   (acl2-numberp k))
              (equal (svar-assoc k (num-varmap keys n))
                     (let ((keys (hons-remove-duplicates keys)))
                       (and (natp (- k n))
                            (< (- k n) (* 2 (len keys)))
                            (if (my-evenp (- k n))
                                (cons (nth (/ (- k n) 2) keys) t)
                              (cons (nth (/ (1- (- k n)) 2) keys) nil))))))
     :hints(("Goal" :in-theory (enable num-varmap))))

   (defthm len-member-equal
     (<= (len (member-equal k x)) (len x))
     :rule-classes :linear)

   (defthm len-member-equal-is-zero
     (equal (equal (len (member-equal k x)) 0)
            (not (member-equal k x))))

   (defthm member-nth-diff-of-member-len
     (equal (nth (+ (len x) (- (len (member-equal k x)))) x)
            (and (member-equal k x)
                 k)))

   (defun natp-ind (x)
     (if (zp x)
         x
       (natp-ind (1- x))))

   (defthm my-evenp-*-2
     (implies (natp n)
              (my-evenp (* 2 n)))
     :hints(("Goal" :induct (natp-ind n))))

   (defthm my-evenp-diff-times-2
     (implies (natp (- k n))
              (my-evenp (+ (* 2 k) (- (* 2 n)))))
     :hints (("goal" :use ((:instance my-evenp-*-2
                                      (n (- k n)))))))

   (defthm not-my-evenp-*-2-+-1
     (implies (natp n)
              (not (my-evenp (+ 1 (* 2 n)))))
     :hints(("Goal" :induct (natp-ind n))))

   (defthm not-my-evenp-diff-times-2-+-1
     (implies (natp (- k n))
              (not (my-evenp (+ 1 (* 2 k) (- (* 2 n))))))
     :hints (("goal" :use ((:instance not-my-evenp-*-2-+-1
                                      (n (- k n)))))))

   (defthm nat-*-2-lte-1
     (implies (natp n)
              (iff (< 1 (* 2 n))
                   (not (equal n 0)))))


   (local (defthm l0
            (equal (consp (member a x))
                   (if (member a x)
                       t
                     nil))))

   (defthm svar-assoc-numvarmap-key-idx
     (implies (acl2-numberp n)
              (equal (svar-assoc (num-varmap-key-idx key keys n)
                                 (num-varmap keys n))
                     (and (member-equal key keys)
                          (cons key t))))
     :hints(("Goal" :in-theory (e/d (num-varmap-key-idx
                                     natp)
                                    ())
             :do-not-induct t)))

   (defthm svar-assoc-numvarmap-key-idx-1
     (implies (acl2-numberp n)
              (equal (svar-assoc (+ 1 (num-varmap-key-idx key keys n))
                                 (num-varmap keys n))
                     (and (member-equal key keys)
                          (cons key nil))))
     :hints(("Goal" :in-theory (enable num-varmap-key-idx natp)
             :do-not-induct t)))


   (defthm 4v-alist-equiv-faig-const-alist->4v-alist-lemma
     (4v-env-equiv
      (FAIG-CONST-ALIST->4V-ALIST
       (FAIG-EVAL-ALIST
        (num-varmap (alist-keys al) 0)
        (SIG-AL-TO-sVAR-AL
         (4V-ALIST->FAIG-CONST-ALIST AL)
         (num-varmap (alist-keys al) 0))))
      al)
     :hints (("goal" :do-not-induct t
              :in-theory (e/d (faig-eval aig-env-lookup 4v->faig-const)
                              (4v-fix faig-const->4v faig-fix)))
             (witness :ruleset 4v-env-equiv-witnessing)
             (and stable-under-simplificationp
                  '(:in-theory (enable 4v-fix))))
     :otf-flg t)))

(defthm 4v-alist-equiv-faig-const-alist->4v-alist-lemma
  ;; [Jared]: Adding this non-locally so that I can use it in simple
  ;; sexpr->faig conversion.
  (4v-env-equiv
   (FAIG-CONST-ALIST->4V-ALIST
    (FAIG-EVAL-ALIST
     (num-varmap (alist-keys al) 0)
     (SIG-AL-TO-sVAR-AL
      (4V-ALIST->FAIG-CONST-ALIST AL)
      (num-varmap (alist-keys al) 0))))
   al))

(defthm 4v-sexpr-eval-by-faig-is-4v-sexpr-eval
  (equal (4v-sexpr-eval-by-faig x al opt)
         (4v-sexpr-eval x al))
  :hints(("Goal" :in-theory (disable 4v-sexpr-eval
                                     4v-sexpr-to-faig-opt
                                     4v-sexpr-to-faig-plain
                                     faig-const-fix
                                     faig-const->4v
                                     4v->faig-const)
          :do-not-induct t))
  :otf-flg t)



(defthm 4v-sexpr-eval-by-faig-list-is-4v-sexpr-eval-list
  (equal (4v-sexpr-eval-by-faig-list x al opt)
         (4v-sexpr-eval-list x al))
  :hints (("goal" :induct (len x)
           :in-theory (e/d (4v-sexpr-eval-by-faig-list-alt-def)
                           (4v-sexpr-eval-by-faig
                            4v-sexpr-eval-by-faig-list
                            4v-sexpr-eval)))))

(in-theory (disable 4v-sexpr-eval-by-faig
                    4v-sexpr-eval-by-faig-list))


(defthmd 4v-sexpr-eval-gl-def
  (equal (4v-sexpr-eval x env)
         (4v-sexpr-eval-by-faig x env t))
  :rule-classes ((:definition :install-body nil)))

(defthmd 4v-sexpr-eval-gl-def-no-opt
  (equal (4v-sexpr-eval x env)
         (4v-sexpr-eval-by-faig x env nil))
  :rule-classes ((:definition :install-body nil)))

(defthmd 4v-sexpr-eval-list-gl-def
  (equal (4v-sexpr-eval-list x env)
         (4v-sexpr-eval-by-faig-list x env t))
  :rule-classes ((:definition :install-body nil)))

(defthmd 4v-sexpr-eval-list-gl-def-no-opt
  (equal (4v-sexpr-eval-list x env)
         (4v-sexpr-eval-by-faig-list x env nil))
  :rule-classes ((:definition :install-body nil)))

(defthmd 4v-sexpr-eval-alist-gl-def
  (equal (4v-sexpr-eval-alist x env)
         (pairlis$ (alist-keys x)
                   (4v-sexpr-eval-list (alist-vals x) env)))
  :hints(("Goal" :in-theory (disable 4v-sexpr-eval)))
  :rule-classes ((:definition :install-body nil)))

(gl::set-preferred-def 4v-sexpr-eval 4v-sexpr-eval-gl-def)
;; To avoid sexpr-to-faig optimizations:
;; (gl::set-preferred-def 4v-sexpr-eval 4v-sexpr-eval-gl-def-no-opt)
(table gl::override-props '4v-sexpr-eval '((recursivep . nil)))

(gl::set-preferred-def 4v-sexpr-eval-list 4v-sexpr-eval-list-gl-def)
;; To avoid sexpr-to-faig optimizations:
;; (gl::set-preferred-def 4v-sexpr-eval-list 4v-sexpr-eval-list-gl-def-no-opt)
(table gl::override-props '4v-sexpr-eval-list '((recursivep . nil)))

(gl::set-preferred-def 4v-sexpr-eval-alist 4v-sexpr-eval-alist-gl-def)
(table gl::override-props '4v-sexpr-eval-alist '((recursivep . nil)))



(defun len-of-each (x)
  (declare (Xargs :guard t))
  (if (atom x)
      nil
    (cons (len (car x))
          (len-of-each (cdr x)))))

(defun append-lists (x)
  (declare (xargs :guard (true-list-listp x)))
  (if (atom x)
      nil
    (append (car x) (append-lists (cdr x)))))

(defun take-lists (lens x)
  (Declare (xargs :guard (true-listp x)))
  (if (atom lens)
      nil
    (let ((len (nfix (car lens))))
      (cons (take len x)
            (take-lists (cdr lens) (nthcdr len x))))))

(local
 (progn
   (include-book "std/lists/take" :dir :system)

   (defthm nthcdr-len-x-of-append-x
     (Equal (nthcdr (len x) (append x y)) y))

   (defthm take-lists-and-append-lists-inverses
     (implies (true-list-listp x)
              (equal (take-lists (len-of-each x) (append-lists x))
                     x))
     :hints(("Goal" :in-theory (enable take))))

   (defthm 4v-sexpr-eval-list-of-append
     (equal (4v-sexpr-eval-list (append a b) env)
            (append (4v-sexpr-eval-list a env)
                    (4v-sexpr-eval-list b env)))
     :hints(("Goal" :in-theory (enable append))))

   (defthm 4v-sexpr-eval-list-of-append-lists
     (equal (4v-sexpr-eval-list (append-lists x) env)
            (append-lists (4v-sexpr-eval-list-list x env))))

   (defthm true-list-listp-4v-sexpr-eval-list-list
     (true-list-listp (4v-sexpr-eval-list-list x env)))

   (defthm len-4v-sexpr-eval-list
     (equal (len (4v-sexpr-eval-list x env))
            (len x)))

   (defthm len-of-each-4v-sexpr-eval-list-list
     (equal (len-of-each (4v-sexpr-eval-list-list x env))
            (len-of-each x)))))


(defthmd 4v-sexpr-eval-list-list-gl-def
  (equal (4v-sexpr-eval-list-list x env)
         (take-lists (len-of-each x)
                     (4v-sexpr-eval-list (append-lists x) env)))
  :hints(("Goal" :in-theory (disable 4v-sexpr-eval-list
                                     take-lists append-lists
                                     len-of-each)
          :use ((:instance take-lists-and-append-lists-inverses
                 (x (4v-sexpr-eval-list-list x env))))))
  :rule-classes ((:definition :install-body nil)))

(gl::set-preferred-def 4v-sexpr-eval-list-list 4v-sexpr-eval-list-list-gl-def)
(table gl::override-props '4v-sexpr-eval-list-list '((recursivep . nil)))




(gl::add-clause-proc-exec-fns '(sig-al-to-svar-al
                                hons-remove-duplicates
                                num-varmap
                                alist-keys
                                good-svarmap
                                4v-sexpr-to-faig-opt))


(include-book "centaur/gl/def-gl-rewrite" :dir :system)

(gl::gl-set-uninterpreted bool-to-4v)
(gl::gl-set-uninterpreted faig-const->4v)
(gl::def-gl-rewrite 4v->faig-const-of-bool-to-4v-gl
  (equal (4v->faig-const (bool-to-4v x))
         (cons (not (not x)) (not x))))

(gl::def-gl-rewrite faig-const->4v-equal-x-gl
  (equal (equal (faig-const->4v a) 'x)
         (not (or (equal a (faig-t))
                  (equal a (faig-f))
                  (equal a (faig-z)))))
  :hints(("Goal" :in-theory (enable faig-const->4v))))

(gl::def-gl-rewrite faig-const->4v-equal-t-gl
  (equal (equal (faig-const->4v a) 't)
         (equal a (faig-t)))
  :hints(("Goal" :in-theory (enable faig-const->4v))))

(gl::def-gl-rewrite faig-const->4v-equal-f-gl
  (equal (equal (faig-const->4v a) 'f)
         (equal a (faig-f)))
  :hints(("Goal" :in-theory (enable faig-const->4v))))

(gl::def-gl-rewrite 4v->faig-const-of-faig-const->4v-gl
  (equal (4v->faig-const (faig-const->4v x))
         (if (and (consp x)
                  (booleanp (car x))
                  (booleanp (cdr x)))
             x
           '(t . t)))
  :hints(("Goal" :in-theory (enable faig-const-fix
                                    faig-const-p))))

(gl::def-gl-rewrite 4vp-of-faig-const->4v-rewrite
  (equal (4vp (faig-const->4v x)) t))

;; the following 4 theorems are not needed in STV proofs but end up being
;; useful in non-STV ones
(gl::def-gl-rewrite equal-of-bool-to-4v-1
  (equal (equal (bool-to-4v x) y)
         (or (and x (equal y (4vt)))
             (and (equal x nil) (equal y (4vf))))))

(gl::def-gl-rewrite equal-of-bool-to-4v-2
  (equal (equal y (bool-to-4v x))
         (or (and x (equal y (4vt)))
             (and (equal x nil) (equal y (4vf))))))

(gl::def-gl-rewrite equal-of-faig-const->4v-1
  (equal (equal (faig-const->4v x) y)
         (or (and (equal x (faig-t)) (equal y (4vt)))
             (and (equal x (faig-f)) (equal y (4vf)))
             (and (equal x (faig-z)) (equal y (4vz)))
             (and (not (equal x (faig-t)))
                  (not (equal x (faig-f)))
                  (not (equal x (faig-z)))
                  (equal y (4vx)))))
  :hints(("Goal" :in-theory (enable faig-const->4v))))

(gl::def-gl-rewrite equal-of-faig-const->4v-2
  (equal (equal y (faig-const->4v x))
         (or (and (equal x (faig-t)) (equal y (4vt)))
             (and (equal x (faig-f)) (equal y (4vf)))
             (and (equal x (faig-z)) (equal y (4vz)))
             (and (not (equal x (faig-t)))
                  (not (equal x (faig-f)))
                  (not (equal x (faig-z)))
                  (equal y (4vx)))))
  :hints(("Goal" :in-theory (enable faig-const->4v))))


;; this is used in STVs
(defun 4v-to-nat-cons (car rest)
  (b* (((unless (integerp rest)) rest)
       (a (4v->faig-const car))
       ((unless (or (equal a (faig-t))
                    (equal a (faig-f))))
        'x))
    (+ (if (equal a (faig-t)) 1 0) (* 2 rest))))

(defthmd 4v-to-nat-redef
  (equal (4v-to-nat x)
         (b* (((when (atom x)) 0)
              (rest (4v-to-nat (cdr x))))
           (4v-to-nat-cons (car x) rest)))
  :hints(("Goal" :in-theory (enable 4v->faig-const)))
  :rule-classes ((:definition :install-body nil)))

(gl::set-preferred-def 4v-to-nat 4v-to-nat-redef)
