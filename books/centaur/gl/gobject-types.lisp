
(in-package "GL")

(include-book "defagg")
(include-book "tools/pattern-match" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)

(defagg g-concrete (obj))
(defagg g-boolean (bool))
(defagg g-number (num))
(defagg g-ite (test then else))
(defagg g-apply (fn args) :notinline t)
(defagg g-var (name))

(defconst *g-keywords*
  '(:g-boolean :g-number :g-concrete :g-ite :g-apply :g-var))



(defun g-keyword-symbolp (x)

;; Performance considerations: We'll be calling this function a lot on various
;; atoms.  We check symbolp first so that we skip the more expensive member
;; check on non-symbols.  Oddly, it doesn't seem to help to also check keywordp
;; -- it seems that's more expensive than member.  Also, in CCL benchmarks, in
;; general (member-eq x lst) is faster than (member x lst), but for some reason
;; (and (symbolp x) (member x lst)) is faster than
;; (and (symbolp x) (member-eq x lst)).

;; [Jared]: I put in an MBE equivalence here that seems to speed this up by about
;; 3x on some arguments.  It is slighly slower on conses but I don't think we care
;; too much about that.  I don't use member, so this now returns a boolean, which is
;; probably nice.  Here is some performance testing data.

;;   v1 -- symbolp, but member (no boolean fixing) instead of eq checks
;;   v2 -- symbolp, mbe with explicit eq checks

#||
 (in-package "GL")
 (let ((x (cons 1 1)))

  ;; v1 4.689 sec    v2 5.022 sec ;
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 24.760 sec   v2 9.201 sec ;
   (setq x 'foo)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 4.682 sec    v2 5.018 sec ;
   (setq x 17)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 15.388 sec   v2 5.367 sec ;
   (setq x :g-boolean)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 17.395 sec   v2 6.375 sec ;
   (setq x :g-number)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 18.732 sec   v2 7.277 sec ;
   (setq x :g-concrete)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x)))

  ;; v1 24.086 sec   v2 9.199 sec ;
   (setq x :g-var)
   (time (loop for i fixnum from 1 to 1000000000 do (g-keyword-symbolp x))))
||#

  (declare (xargs :guard t))
  (and (symbolp x)
       (mbe :logic (if (member x *g-keywords*)
                       t
                     nil)
            :exec
            (or (eq x :g-boolean)
                (eq x :g-number)
                (eq x :g-concrete)
                (eq x :g-ite)
                (eq x :g-apply)
                (eq x :g-var)))))

(in-theory (disable g-keyword-symbolp))



(defthmd g-keyword-symbolp-def
  (equal (g-keyword-symbolp x)
         (if (member-equal x *g-keywords*)
             t
           nil))
  :hints(("Goal" :in-theory (enable g-keyword-symbolp))))

(defthm not-g-keyword-symbol-when-not-symbol
  (implies (not (symbolp x))
           (not (g-keyword-symbolp x)))
  :hints(("Goal" :in-theory (enable g-keyword-symbolp)))
  :rule-classes ((:rewrite :backchain-limit-lst 0)
                 :type-prescription))

