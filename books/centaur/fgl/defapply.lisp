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
(include-book "tools/rulesets" :dir :system)
(include-book "std/util/bstar" :dir :system)
(local (in-theory (disable mv-nth)))

(defun defeval-fns-to-calls (fns world)
  (declare (xargs :guard (and (symbol-listp fns)
                              (plist-worldp world))))
  (b* (((when (atom fns))
        nil)
       (formals (getprop (car fns) 'formals :missing
                         'current-acl2-world world))
       ((when (eq formals :missing))
        (er hard? 'defeval-fns-to-calls
            "Missing formals for function: ~x0~%" (car fns))
        (defeval-fns-to-calls (cdr fns) world)))
    (cons (cons (car fns) formals)
          (defeval-fns-to-calls (cdr fns) world))))

(defmacro defeval-wrap (ev evlst fns)
  `(make-event
    `(acl2::defevaluator
      ,',ev ,',evlst
      ,(defeval-fns-to-calls ',fns (w state))
      :namedp t)))


(defthmd len-open-for-defapply
  (equal (len (cons a b))
         (+ 1 (len b))))

(defthmd nth-open-for-defapply
  (implies (syntaxp (quotep n))
           (equal (nth n (cons a b))
                  (if (zp n)
                      a
                    (nth (1- n) b)))))

(defun my-return-last (x y z)
  (declare (xargs :guard t))
  (mbe :logic (return-last x y z)
       :exec (if (or (not (eq x 'acl2::mbe1-raw))
                     (equal y z))
                 (return-last x y z)
               z)))


(program)

(defun make-list-of-nths (sym start n)
  (declare (xargs :guard (and (natp start)
                              (natp n))))
  (if (zp n)
      nil
    (cons `(nth ,start ,sym)
          (make-list-of-nths sym (1+ start) (1- n)))))

(defmacro ecc (call)
  (declare (xargs :guard (consp call)))
  (cond ((eq (car call) 'return-last)
         (cons 'my-return-last (cdr call)))
        ((member-eq (car call) acl2::*ec-call-bad-ops*)
         call)
        (t `(ec-call ,call))))

(defun make-mv-call (f args world)
  (let* ((stobjs-out (getprop f 'stobjs-out nil 'current-acl2-world world)))
    (if (and stobjs-out (< 1 (length stobjs-out)))
        `(mv-list ,(length stobjs-out)
                  (ecc (,f . ,args)))
      `(ecc (,f . ,args)))))

(defun make-apply-entry (f world)
  (let* ((formals (getprop f 'formals nil 'current-acl2-world world)))
    `((and (eq f ',f)
           (true-listp args)
           (eql (len args) ,(length formals)))
      ,(make-mv-call f (make-list-of-nths 'args 0 (length formals)) world))))

(defun make-apply-clique-entries (clique world)
  (if (atom clique)
      nil
    (cons (make-apply-entry (car clique) world)
          (make-apply-clique-entries (cdr clique) world))))

(defun make-apply-entries (fns world acc)
  (if (atom fns)
      (prog2$ (flush-hons-get-hash-table-link acc)
              nil)
    (if (hons-get (car fns) acc)
        (make-apply-entries (cdr fns) world acc)
      (let* ((clique (or (getpropc (car fns) 'recursivep nil world)
                         (list (car fns))))
             (acc (fast-alist-fork (pairlis$ clique (make-list (len clique) :initial-element t))
                                   acc)))
        (append (make-apply-clique-entries clique world)
                (make-apply-entries (cdr fns) world acc))))))

;; (defun double-rewrite-formals (formals)
;;   (if (atom formals)
;;       nil
;;     (cons `(double-rewrite ,(car formals))
;;           (double-rewrite-formals (cdr formals)))))

;; (defun apply-rw-name (apply fn)
;;   (intern-in-package-of-symbol
;;    (concatenate 'string (symbol-name apply) "-" (symbol-name fn))
;;    apply))

;; (defun apply-rw-thms (clique name world)
;;   (if (atom clique)
;;       nil
;;     (let* ((fn (car clique))
;;            (formals (wgetprop fn 'formals)))
;;       (cons `(defthm ,(apply-rw-name name fn)
;;                (equal (,name ',fn (list . ,formals))
;;                       (,fn . ,(double-rewrite-formals formals)))
;;                :hints (("goal" :in-theory
;;                         (e/d** (minimal-theory
;;                                 ;; (:executable-counterpart-theory :here)
;;                                 (equal) (len) (nth) (binary-+) (not)
;;                                 (zp)
;;                                 (:definition ,name)
;;                                 len-open-for-defapply
;;                                 nth-open-for-defapply))
;;                         :do-not '(preprocess))
;;                        (and stable-under-simplificationp
;;                             ;; Special case for HIDE and functions that
;;                             ;; normalize to a constant.
;;                             '(:expand ((:free ,formals (,fn . ,formals)))))))
;;             (apply-rw-thms (cdr clique) name world)))))




;; (defun make-apply-rewrites (name fns world)
;;   (if (atom fns)
;;       nil
;;     (append (b* ((recursivep (getprop (car fns) 'recursivep nil
;;                                       'current-acl2-world world)))
;;               (apply-rw-thms (or recursivep (list (car fns))) name world))
;;             (make-apply-rewrites name (cdr fns) world))))

(def-ruleset! defapply-guards '((:executable-counterpart eqlablep)
                                (:executable-counterpart equal)
                                my-return-last))

(defun mk-arity-table (lst w)
  (if (atom lst)
      nil
    (cons (cons (car lst)
                (len (getprop (car lst) 'formals nil 'current-acl2-world w)))
          (mk-arity-table (cdr lst) w))))


;; Test case:
(local (DEFUN MYAPP-ARITIES
         NIL (DECLARE (XARGS :GUARD T))
         '((MVFN . 2)
           (IF . 3)
           (EQUAL . 2)
           (NOT . 1)
           (LEN . 1)
           (CONS . 2))))
(local (DEFEVAL-WRAP MYAPP-EV MYAPP-EV-LST
                           (IF EQUAL NOT LEN CONS)))




(defun make-apply (name evname fns world)
  (declare (xargs :mode :program))
  (b* ((ev evname)
       (ev-lst (intern-in-package-of-symbol
                (concatenate 'string (symbol-name evname) "-LIST")
                evname)))
  `(progn
     (defun ,(intern-in-package-of-symbol
              (concatenate 'string (symbol-name name) "-ARITIES")
              name)
       ()
       (declare (xargs :guard t))
       ',(mk-arity-table fns world))
     (encapsulate nil
       (local (in-theory (e/d** ((:ruleset defapply-guards)
                                 eq eql car-cons cdr-cons
                                 cadr-kwote-lst-meta-correct
                                 (nfix)
                                 ;; make-apply-open-nth
                                 ;; (zp) (unary--) (binary-+)
                                 (:rules-of-class :type-prescription :here)))))
       (defeval-wrap ,ev ,ev-lst ,fns)

       (defund ,name (f args)
         (declare (xargs :guard t
                         :normalize nil))
         (mbe :logic (,ev (cons f (kwote-lst args)) nil)
              :exec
              (cond
               ,@(make-apply-entries fns world nil)
               (t (,ev (cons f (ec-call (kwote-lst args))) nil)))))
       (table g-apply-table ',name ',fns)))))




(defmacro defapply (name evname fns)
  `(make-event (make-apply ',name ',evname ',fns (w state))))

(logic)

(defthmd make-apply-open-nth
  (equal (nth n args)
         (if (zp n)
             (car args)
           (nth (1- n) (cdr args)))))

(defund mvfn (x y) (mv x y))


(defevaluator cadkw-ev cadkw-ev-lst
  ((car x) (cdr x) (len x) (kwote-lst x) (< x y) (nth n x) (cons x y) (nfix x)))

(defun cadr-kwote-lst-count-cdrs (x)
  (declare (xargs :guard (pseudo-termp x)))
  (b* (((when (or (atom x) (not (eq (car x) 'cdr))))
        (mv 0 x))
       ((mv count final) (cadr-kwote-lst-count-cdrs (cadr x))))
    (mv (+ 1 count) final)))

(Defthm natp-cadr-kwote-lst-count-cdrs
  (natp (mv-nth 0 (cadr-kwote-lst-count-cdrs x)))
  :rule-classes :type-prescription)

(local (include-book "arithmetic/top-with-meta" :dir :system))

(local (defthm cdr-of-nthcdr
         (equal (cdr (nthcdr n x))
                (nthcdr n (cdr x)))))

(defthm cadr-kwote-lst-count-cdrs-correct
  (mv-let (n y)
    (cadr-kwote-lst-count-cdrs x)
    (equal (nthcdr n (cadkw-ev y a))
           (cadkw-ev x a)))
  :hints (("goal" :induct (cadr-kwote-lst-count-cdrs x))))

(defthm car-of-nthcdr
  (equal (car (nthcdr n x))
         (nth n x)))

(defthm cadr-kwote-lst-count-cdrs-correct-nth
  (mv-let (n y)
    (cadr-kwote-lst-count-cdrs x)
    (equal (nth n (cadkw-ev y a))
           (car (cadkw-ev x a))))
  :hints (("goal" :use ((:instance car-of-nthcdr
                         (n (mv-nth 0 (cadr-kwote-lst-count-cdrs x)))
                         (x (cadkw-ev (mv-nth 1 (cadr-kwote-lst-count-cdrs x))
                                      a))))
           :in-theory (disable car-of-nthcdr))))

(defun cadr-kwote-lst-meta-res (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x) (eq (car x) 'car))
      (b* (((mv n kwote-lst-term) (cadr-kwote-lst-count-cdrs (cadr x)))
           ((unless (and (consp kwote-lst-term)
                         (eq (car kwote-lst-term) 'kwote-lst)))
            x))
        `(cons 'quote (cons (nth ',n ,(cadr kwote-lst-term)) 'nil)))
    x))

(defun cadr-kwote-lst-meta-hyp (x)
  (declare (xargs :guard (pseudo-termp x)))
  (if (and (consp x) (eq (car x) 'car))
      (b* (((mv n kwote-lst-term) (cadr-kwote-lst-count-cdrs (cadr x)))
           ((unless (and (consp kwote-lst-term)
                         (eq (car kwote-lst-term) 'kwote-lst)))
            't))
        `(< (nfix ',n) (len ,(cadr kwote-lst-term))))
    't))

(in-theory (disable cadr-kwote-lst-count-cdrs
                    car-of-nthcdr))

(defthm nth-of-kwote-lst-when-len
  (implies (< (nfix n) (len x))
           (equal (nth n (kwote-lst x))
                  (list 'quote (nth n x)))))

(defthmd cadr-kwote-lst-meta-correct
  (implies (cadkw-ev (cadr-kwote-lst-meta-hyp x) a)
           (equal (cadkw-ev x a)
                  (cadkw-ev (cadr-kwote-lst-meta-res x) a)))
  :hints (("goal" :use ((:instance cadr-kwote-lst-count-cdrs-correct-nth
                         (x (cadr x))))
           :in-theory (disable cadr-kwote-lst-count-cdrs-correct-nth)))
  :rule-classes ((:meta :trigger-fns (car))))




;; (defapply myapp (BINARY-*
;;    BINARY-+
;;    PKG-WITNESS
;; ;   UNARY-/
;;    UNARY--
;;    COMPLEX-RATIONALP
;; ;   BAD-ATOM<=
;;    ACL2-NUMBERP
;;    SYMBOL-PACKAGE-NAME
;;    INTERN-IN-PACKAGE-OF-SYMBOL
;;    CODE-CHAR
;; ;   DENOMINATOR
;;    CDR
;; ;   COMPLEX
;;    CAR
;;    CONSP
;;    SYMBOL-NAME
;;    CHAR-CODE
;;    IMAGPART
;;    SYMBOLP
;;    REALPART
;; ;   NUMERATOR
;;    EQUAL
;;    STRINGP
;;    RATIONALP
;;    CONS
;;    INTEGERP
;;    CHARACTERP
;;    <
;;    COERCE
;;    booleanp
;;    logbitp
;;    binary-logand
;;    binary-logior
;;    lognot
;;    ash
;;    integer-length
;;    floor
;;    mod
;;    truncate
;;    rem
;; ;   acl2::boolfix

;;    ;; these are from the constant *expandable-boot-strap-non-rec-fns*.
;;    NOT IMPLIES
;;    EQ ATOM EQL = /= NULL ENDP ZEROP ;; SYNP
;;    PLUSP MINUSP LISTP ;; RETURN-LAST causes guard violation
;;    ;; FORCE CASE-SPLIT
;;    ;; DOUBLE-REWRITE
;;    mvfn))
