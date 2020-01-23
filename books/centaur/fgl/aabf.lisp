; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2018 Centaur Technology
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

(include-book "centaur/misc/starlogic" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "centaur/misc/prev-stobj-binding" :dir :system)

;; Advanced Abstract Boolean Function representation.
;; This 

(defun aabf-op-formalsubsts (formals)
  (declare (xargs :mode :program))
  (if (atom formals)
      nil
    (cons (acl2::make-tmplsubst :atoms `((<x> . ,(car formals))))
          (aabf-op-formalsubsts (cdr formals)))))


(defun def-aabf-op-fn (name formals fnsymb fn man-mode)
  (declare (xargs :mode :program))
  (acl2::template-subst '(progn
                           (local (defun <name> (<formals> (:@ :man man))
                                    (:@ (and :man (not :return-man))
                                     (declare (ignore man)))
                                    (:@ :return-man (mv (list '<fnsymb> <formals>) man))
                                    (:@ (not :return-man) (list '<fnsymb> <formals>))))

                           (defthm aabf-eval-of-<name>
                             (b* (((:@ :return-man (mv res new-man))
                                   (:@ (not :return-man) res)
                                   (<name> <formals> (:@ :man man))))
                               (equal (aabf-eval res env (:@ :return-man new-man) (:@ (not :return-man) man))
                                      (<fn> (:@proj <formal-substs>
                                             (aabf-eval <x> env man))))))
                           ;; (defthm abf-syntactically-depends-on-of-<name>
                           ;;   (implies (and . (:@proj <formal-substs>
                           ;;                    (not (abf-syntactically-depends-on <x> var))))
                           ;;            (not (abf-syntactically-depends-on (<name> . <formals>) var))))

                           (:@ :return-man
                            (defthm aabf-extension-p-of-<name>
                              (b* (((mv ?res new-man) (<name> <formals> man)))
                                (aabf-extension-p new-man man))))

                           (defthm aabf-p-of-<name>
                             (b* (((:@ :return-man (mv res new-man))
                                   (:@ (not :return-man) res)
                                   (<name> <formals> (:@ :man man))))
                             (implies (and (:@proj <formal-substs>
                                            (aabf-p <x> man)))
                                      (aabf-p res (:@ :return-man new-man) (:@ (not :return-man) man)))))

                           (defthm aabf-pred-of-<name>
                             (b* (((:@ :return-man (mv res new-man))
                                   (:@ (not :return-man) res)
                                   (<name> <formals> (:@ :man man))))
                             (implies (and (:@proj <formal-substs>
                                            (aabf-pred <x> man)))
                                      (aabf-pred res (:@ :return-man new-man) (:@ (not :return-man) man)))))

                           ;; (:@ (and :man (not :return-man))
                           ;;  ;; this is actually just for AABF-NOT and ensures
                           ;;  ;; that extensions to the manager don't change the
                           ;;  ;; object returned.
                           ;;  (defthmd aabf-extension-preserves-<name>
                           ;;    (implies (and (bind-aabf-extension new old)
                           ;;                  (:@proj <formal-substs>
                           ;;                   (aabf-p <x> old))
                           ;;                  )
                           ;;             (equal (<name> <formals> new)
                           ;;                    (<name> <formals> old))))

                           ;;  (add-to-ruleset! aabf-extension-preserves-rules
                           ;;                   aabf-extension-preserves-<name>))

                           (:@ :return-man
                            (acl2::set-prev-stobjs-correspondence <name> :stobjs-out (nil man) :formals (<formals> man))))
                           :atom-alist `((<name> . ,name)
                                      (<fnsymb> . ,fnsymb)
                                      (<fn> . ,(or fn fnsymb)))
                        :splice-alist `((<formals> . ,formals))
                        :str-alist `(("<NAME>" . ,(symbol-name name)))
                        :subsubsts `((<formal-substs>
                                      . ,(aabf-op-formalsubsts formals)))
                        :features (case man-mode
                                    (:take '(:man))
                                    (:none '())
                                    (t '(:man :return-man)))
                        :pkg-sym 'fgl::fgl-packge))

(defmacro def-aabf-op (name formals fnsymb &key fn man-mode)
  (def-aabf-op-fn name formals fnsymb fn man-mode))

(defmacro bind-aabf-extension (new old-var)
  `(and (bind-free (acl2::prev-stobj-binding ,new ',old-var mfc state))
        (aabf-extension-p ,new ,old-var)))

(encapsulate
  (((aabf-p * *) => *
    :formals (x man)
    :guard t)

   ((aabf-eval * * *) => *
    :formals (x env man)
    :guard (aabf-p x man))

   ((aabf-pred * *) => *
    :formals (x man)
    :guard (aabf-p x man))

   ((aabf-true) => *)
   ((aabf-false) => *)

   ((aabf-not * *) => *
    :formals (x man)
    :guard (aabf-p x man))

   ((aabf-and * * *) => (mv * *)
    :formals (x y man)
    :guard (and (aabf-p x man)
                (aabf-p y man)))

   ((aabf-or * * *) => (mv * *)
    :formals (x y man)
    :guard (and (aabf-p x man)
                (aabf-p y man)))

   ((aabf-xor * * *) => (mv * *)
    :formals (x y man)
    :guard (and (aabf-p x man)
                (aabf-p y man)))

   ((aabf-iff * * *) => (mv * *)
    :formals (x y man)
    :guard (and (aabf-p x man)
                (aabf-p y man)))

   ((aabf-ite * * * *) => (mv * *)
    :formals (x y z man)
    :guard (and (aabf-p x man)
                (aabf-p y man)
                (aabf-p z man)))

   ((aabf-syntactically-equal * *) => *)

   ((aabf-extension-p * *) => *))

  (local (defun aabf-extension-p (new old)
           (>= (nfix new) (nfix old))))

  (defthm aabf-extension-p-self
    (aabf-extension-p x x))

  (defthm aabf-extension-p-transtive
    (implies (and (bind-aabf-extension x y)
                  (aabf-extension-p y z))
             (aabf-extension-p x z)))

  (local (defun aabf-p (x man)
           (if (atom x)
               (and (natp x) (<= x (nfix man)))
             (case (car x)
               ((true false) t)
               (not (aabf-p (second x) man))
               ((and or xor iff)
                (and (aabf-p (second x) man)
                     (aabf-p (third x) man)))
               (ite
                (and (aabf-p (second x) man)
                     (aabf-p (third x) man)
                     (aabf-p (fourth x) man)))))))

  (defthm booleanp-of-aabf-p
    (booleanp (aabf-p x man))
    :rule-classes :type-prescription)

  (defthm aabf-p-of-extension
    (implies (and (bind-aabf-extension new old)
                  (aabf-p x old))
             (aabf-p x new)))

  (local (defun aabf-pred (x man)
           (if (atom x)
               (and (natp x)
                    (<= x (nfix man))
                    (<= x 5))
             (case (car x)
               ((true false) t)
               (not (aabf-pred (second x) man))
               ((and or xor iff)
                (and (aabf-pred (second x) man)
                     (aabf-pred (third x) man)))
               (ite
                (and (aabf-pred (second x) man)
                     (aabf-pred (third x) man)
                     (aabf-pred (fourth x) man)))))))

  (defthm aabf-pred-of-extension
    (implies (and (bind-aabf-extension new old)
                  (aabf-p x old))
             (equal (aabf-pred x new)
                    (aabf-pred x old))))

  (defthm booleanp-of-aabf-pred
    (booleanp (aabf-pred x man))
    :rule-classes :type-prescription)

  (local (defun aabf-eval (x env man)
           (if (atom x)
               (and (natp x) (<= x (nfix man)) (nth x env) t)
             (case (car x)
               (true t)
               (false nil)
               (not  (not (aabf-eval (second x) env man)))
               (and (and (aabf-eval (second x) env man)
                         (aabf-eval (third x) env man)))
               (or  (or  (aabf-eval (second x) env man)
                         (aabf-eval (third x) env man)))
               (xor (xor (aabf-eval (second x) env man)
                         (aabf-eval (third x) env man)))
               (iff (iff (aabf-eval (second x) env man)
                         (aabf-eval (third x) env man)))
               (ite (if  (aabf-eval (second x) env man)
                         (aabf-eval (third x) env man)
                         (aabf-eval (fourth x) env man)))))))

  (defthm aabf-eval-of-extension
    (implies (and (bind-aabf-extension new old)
                  (aabf-p x old))
             (equal (aabf-eval x env new)
                    (aabf-eval x env old))))

  (defthm booleanp-of-aabf-eval
    (booleanp (aabf-eval x env man))
    :rule-classes :type-prescription)

  (local (defun aabf-syntactically-equal (x y) (equal x y)))

  (defequiv aabf-syntactically-equal)

  (defcong aabf-syntactically-equal equal (aabf-p x man) 1)
  (defcong aabf-syntactically-equal equal (aabf-eval x env man) 1)

  (def-aabf-op aabf-true () true :fn (lambda () t) :man-mode :none)
  (def-aabf-op aabf-false () false :fn (lambda () nil) :man-mode :none)

  (def-aabf-op aabf-not (x) not :man-mode :take)

  (def-aabf-op aabf-and (x y) and :fn and*)
  (def-aabf-op aabf-or (x y) or :fn or*)
  (def-aabf-op aabf-xor (x y) xor)
  (def-aabf-op aabf-iff (x y) iff)
  (def-aabf-op aabf-ite (x y z) ite :fn if*))



(defun aabflist-p (x man)
  (declare (xargs :guard t))
  (if (atom x)
      t
    (and (aabf-p (car x) man)
         (aabflist-p (cdr x) man))))

(defun aabflist-eval (x env man)
  (declare (xargs :guard (aabflist-p x man)))
  (if (atom x)
      nil
    (cons (aabf-eval (car x) env man)
          (aabflist-eval (cdr x) env man))))

(defun aabflist-pred (x man)
  (declare (xargs :guard (aabflist-p x man)))
  (if (atom x)
      t
    (and (aabf-pred (car x) man)
         (aabflist-pred (cdr x) man))))


(defthm aabflist-p-of-extension
  (implies (and (bind-aabf-extension new old)
                (aabflist-p x old))
           (aabflist-p x new)))

(defthm aabflist-pred-of-extension
  (implies (and (bind-aabf-extension new old)
                (aabflist-p x old))
           (equal (aabflist-pred x new)
                  (aabflist-pred x old))))

(defthm aabflist-eval-of-extension
  (implies (and (bind-aabf-extension new old)
                (aabflist-p x old))
           (equal (aabflist-eval x env new)
                  (aabflist-eval x env old))))

(defthm aabf-true-not-equal-false
  (not (aabf-syntactically-equal (aabf-true) (aabf-false)))
  :hints (("goal" :use ((:instance aabf-eval-of-aabf-true)
                        (:instance aabf-eval-of-aabf-false))
           :in-theory (disable aabf-eval-of-aabf-true aabf-eval-of-aabf-false))))

