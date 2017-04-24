; Centaur Miscellaneous Books
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

(in-package "ACL2")

(include-book "std/basic/arith-equivs" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/base" :dir :system)
(include-book "centaur/fty/fixtype" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)

(encapsulate nil
  (local (in-theory (enable* arith-equiv-forwarding)))
  (local (include-book "arithmetic/top-with-meta" :dir :System))

  (encapsulate
    (((iter-step * * *) => *)  ;; one step of the iteration
     ((iter-first * *) => *)   ;; lowest index
     ((iter-last * *) => *)    ;; highest index
     ((iter-fix-val *) => *))  ;; normalize the val -- for multiple values

    (set-ignore-ok t)
    (set-irrelevant-formals-ok t)

    ;; val is the thing that's transformed each step; aux is the data used to
    ;; determine how to modify it; n is the counter
    (local (defun iter-step (n aux val)
             (list (update-nth n (car aux) (car val)))))
    (local (defun iter-first (aux val)
             (cadr aux)))
    (local (defun iter-last (aux val)
             (caddr aux)))
    (local (defun iter-fix-val (val)
             (list (car val))))

    ;; probably first and last shouldn't depend on val, but we'll allow it as
    ;; long as step doesn't alter them
    (defthm iter-first-of-iter-step
      (equal (iter-first aux (iter-step n aux val))
             (iter-first aux val)))

    (defthm iter-last-of-iter-step
      (equal (iter-last aux (iter-step n aux val))
             (iter-last aux val)))

    (defthm iter-first-of-iter-fix
      (equal (iter-first aux (iter-fix-val val))
             (iter-first aux val)))

    ;; fix will be something like:
    ;;  (lambda (val)
    ;;    (b* (((mv a b) val))
    ;;       (mv a b)))
    ;; this will be transparent to the step function since it will be
    ;; instantiated as something like:
    ;; (lambda (n aux val)
    ;;    (b* (((mv a b) val)
    ;;         ((list c d e) aux)
    ;;         (idx n))
    ;;     (real-step-function n c a d e b)))
    (defthm iter-last-of-iter-fix
      (equal (iter-last aux (iter-fix-val val))
             (iter-last aux val)))

    (defthm iter-fix-of-iter-fix
      (equal (iter-fix-val (iter-fix-val val))
             (iter-fix-val val)))

    (defthm iter-step-of-iter-fix
      (equal (iter-step n aux (iter-fix-val val))
             (iter-step n aux val)))

    (defthm iter-fix-of-iter-step
      (equal (iter-fix-val (iter-step n aux val))
             (iter-step n aux val))))

  ;; tail-recursive version counting up
  (defun iter-up (n aux val)
    (declare (xargs :measure (nfix (- (ifix (iter-last aux val))
                                      (ifix n)))))
    (if (zp (- (ifix (iter-last aux val))
               (ifix n)))
        (iter-fix-val val)
      (iter-up (1+ (ifix n)) aux (iter-step (ifix n) aux val))))

  ;; non-tail-recursive version counting down
  (defun iter-down (n aux val)
    (declare (xargs :measure (nfix (- (ifix n)
                                      (ifix (iter-first aux val))))))
    (if (zp (- (ifix n)
               (ifix (iter-first aux val))))
        (iter-fix-val val)
      (iter-step (1- (ifix n)) aux (iter-down (1- (ifix n)) aux val))))

  (defthm iter-last-of-iter-up
    (equal (iter-last aux (iter-up n aux val))
           (iter-last aux val)))

  (defthm iter-last-of-iter-down
    (equal (iter-last aux (iter-down n aux val))
           (iter-last aux val)))

  (defthm iter-fix-val-of-iter-up
    (equal (iter-fix-val (iter-up n aux val))
           (iter-up n aux val)))

  (defthm iter-fix-val-of-iter-down
    (equal (iter-fix-val (iter-down n aux val))
           (iter-down n aux val))
    :hints (("goal" :induct (iter-down n aux val))))

  (defthm iter-up-of-iter-fix-val
    (equal (iter-up n aux (iter-fix-val val))
           (iter-up n aux val)))

  (defthm iter-down-of-iter-fix-val
    (equal (iter-down n aux (iter-fix-val val))
           (iter-down n aux val)))

  (defthm iter-up-of-iter-down
    (implies (and (<= (ifix n) (ifix (iter-last aux val)))
                  (<= (ifix (iter-first aux val)) (ifix n)))
             (equal (iter-up n aux (iter-down n aux val))
                    (iter-up (iter-first aux val) aux val)))
    :hints (("goal" :induct (iter-down n aux val)
             :expand ((:free (val) (iter-up n aux val))))))

  (defthm iter-up-is-iter-down
    (equal (iter-up (iter-first aux val) aux val)
           (iter-down (iter-last aux val) aux val))
    :hints (("goal" :use ((:instance iter-up-of-iter-down
                           (n (iter-last aux val))))
             :in-theory (disable iter-up-of-iter-down))
            (and stable-under-simplificationp
                 '(:expand ((iter-down (iter-last aux val) aux val)))))))


;; returns declarations, doc string, body, keyword-list
(defun defiteration-sort-args (args)
  (cond ((atom args)
         (prog2$ (er hard? 'defiteration "not enough args")
                 (mv nil nil nil nil)))
        ((and (consp (car args)) (eq (caar args) 'declare))
         (b* (((mv decls doc body kwlist)
               (defiteration-sort-args (cdr args))))
           (mv (cons (car args) decls) doc body kwlist)))
        ((stringp (car args))
         ;; if rest is a keyword list, this is body, else doc.
         (b* (((when (keyword-value-listp (cdr args)))
               (mv nil nil (car args) (cdr args)))
              ((mv decls doc body kwlist)
               (defiteration-sort-args (cdr args)))
              ((when doc)
               (er hard? 'defiteration "multiple doc strings")
               (mv nil nil nil nil)))
           (mv decls (car args) body kwlist)))
        ;; now car has to be body, which means rest has to be keyword list
        ((keyword-value-listp (cdr args))
         (mv nil nil (car args) (cdr args)))
        (t (prog2$ (er hard? 'defiteration "args after body not keyword-value-listp")
                   (mv nil nil nil nil)))))

(defun get-kw (key default kwlist)
  (declare (xargs :guard (keyword-value-listp kwlist)))
  (let ((look (assoc-keyword key kwlist)))
    (if look (cadr look) default)))

(defun var/const-listp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (eq x nil)
    (and (or (atom (car x))
             (eq (caar x) 'quote))
         (var/const-listp (cdr x)))))

(defun defiteration-fn (name formals args)
  (b* (((mv decls doc body kwlist) (defiteration-sort-args args))
       (first (get-kw :first 0 kwlist))
       (last (get-kw :last nil kwlist))
       ((unless last) (er hard? 'defiteration "Need :last argument"))
       (index (get-kw :index (intern-in-package-of-symbol
                              "N" name)
                      kwlist))
       ((when (member index formals))
        (er hard? 'defiteration "Index variable (~x0) must not be in formals" index))
       (init-vals (get-kw :init-vals nil kwlist))
       (init-val-vars (strip-cars init-vals))
       ((unless (and (symbol-listp init-val-vars)
                     (not (member-eq index init-val-vars))
                     (not (intersectp-eq init-val-vars formals))))
        (er hard? 'defiteration "May not assign initial values to formals or index var"))
       (returns (get-kw :returns nil kwlist))
       ((unless returns)
        (er hard? 'defiteration "Must specify :returns"))
       ((unless (if (symbolp returns)
                    (or (member returns formals)
                        (member returns init-val-vars))
                  (and (symbol-listp returns)
                       (eq (car returns) 'mv)
                       (consp (cdr returns))
                       (subsetp-eq (set-difference-eq (cdr returns) formals)
                                   init-val-vars))))
        (er hard? 'defiteration "Returns must be either a variable symbol or ~
                                 MV of variable symbols, with each symbol ~
                                 either a formal or given an initial value in ~
                                 :init-vals"))
       (hints (get-kw :hints nil kwlist))
       (iter-guard (get-kw :iter-guard t kwlist))
       (iter-decls (get-kw :iter-decls nil kwlist))
       (top-guard (get-kw :top-guard t kwlist))
       (top-returns (get-kw :top-returns nil kwlist))
       (guard-hints (get-kw :guard-hints nil kwlist))
       (package (get-kw :package name kwlist))
       (val-vars (if (symbolp returns)
                     (list returns)
                   (cdr returns)))
       (aux-vars (set-difference-eq (append formals init-val-vars) val-vars))
       (body-is-simple (or (atom body)
                           (and (symbolp (car body))
                                (var/const-listp (cdr body)))))
       (iter-formals (cons index (append init-val-vars formals)))
       (step-call (if body-is-simple
                      body
                    (cons (intern-in-package-of-symbol
                           (concatenate 'string (symbol-name name) "-STEP")
                           package)
                          iter-formals)))
       (step (car step-call))
       (tailrec (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-TAILREC")
                 package))
       (iter (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-ITER")
                 package))
       (iter-meas (if (equal first 0)
                      index
                    `(- (ifix ,index) (ifix ,first))))
       (thmname (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name tailrec) "-IS-"
                              (symbol-name iter))
                 package)))
    `(encapsulate nil
       ,@(and (not body-is-simple)
              `((defun-inline ,step ,iter-formals
                  (declare (type (integer ,(if (integerp first) first '*)
                                          ,(if (integerp last) last '*))
                                 ,index)
                           (ignorable ,index ,@init-val-vars . ,formals)
                           (xargs :guard-hints ,guard-hints)
                           . ,iter-decls)
                  ,@decls
                  (declare (xargs :guard (and (<= ,first ,index)
                                              (< ,index ,last)
                                              ,iter-guard)))
                  ,body)))
       (defund ,tailrec ,iter-formals
         (declare (type (integer ,(if (integerp first) first '*)
                                 ,(if (integerp last) last '*))
                        ,index)
                  (xargs :measure (nfix (- (ifix ,last)
                                           (ifix ,index))))
                  . ,iter-decls)
         ,@decls
         (declare (xargs :guard (and (<= ,first ,index)
                                     (<= ,index ,last)
                                     ,iter-guard)))
         (b* (((when (mbe :logic (zp (- (ifix ,last)
                                        (ifix ,index)))
                          :exec (int= ,last ,index)))
               ,returns)
              (,index (lifix ,index))
              (,returns ,step-call))
           (,tailrec (1+ ,index) . ,(cdr iter-formals))))
       (defund ,iter ,iter-formals
         (declare (type (integer ,(if (integerp first) first '*)
                                 ,(if (integerp last) last '*))
                        ,index)
                  (xargs :measure (nfix ,iter-meas)
                         :verify-guards nil)
                  . ,iter-decls)
         ,@decls
         (declare (xargs :guard (and (<= ,first ,index)
                                     (<= ,index ,last)
                                     ,iter-guard)))
         (b* (((when (mbe :logic (zp ,iter-meas)
                          :exec (int= ,first ,index)))
               ,returns)
              (,index (1- (lifix ,index)))
              (,returns (,iter . ,iter-formals)))
           ,step-call))
       (fty::deffixcong int-equiv equal (,iter . ,iter-formals) ,index
         :hints (("goal" :in-theory (enable ,iter))))
       (encapsulate nil
         (set-ignore-ok t)
         (defthm ,thmname
           (equal (,tailrec ,first . ,(cdr iter-formals))
                  (,iter ,last . ,(cdr iter-formals)))
           :hints (("goal" :use
                    ((:instance
                      (:functional-instance
                       iter-up-is-iter-down
                       (iter-fix-val
                        (lambda (val)
                          (b* ((,returns val))
                            ,returns)))
                       (iter-first
                        (lambda (aux val)
                          (b* (((list . ,aux-vars) aux)
                               (,returns val))
                            ,first)))
                       (iter-last
                        (lambda (aux val)
                          (b* (((list . ,aux-vars) aux)
                               (,returns val))
                            ,last)))
                       (iter-step
                        (lambda (n aux val)
                          (b* (((list . ,aux-vars) aux)
                               (,returns val)
                               (,index n))
                            ,step-call)))
                       (iter-up
                        (lambda (n aux val)
                          (b* (((list . ,aux-vars) aux)
                               (,returns val))
                            (,tailrec n . ,(cdr iter-formals)))))
                       (iter-down
                        (lambda (n aux val)
                          (b* (((list . ,aux-vars) aux)
                               (,returns val))
                            (,iter n . ,(cdr iter-formals))))))
                      (aux (list . ,aux-vars))
                      (val ,returns)))
                    :in-theory '(,iter
                                 ,tailrec
                                 car-cons
                                 cdr-cons
                                 zp-when-integerp
                                 commutativity-of-+
                                 (equal) (ifix) (unary--) (zp)
                                 ifix-positive-to-non-zp
                                 unicity-of-0
                                 fix
                                 lnfix lifix
                                 (:type-prescription ifix))
                    ;; (,step))
                    ;; (<-0-+-negative-1
                    ;;  <-0-+-negative-2
                    ;;  ,step))
                    :do-not-induct t)
                   ,@hints
                   (and stable-under-simplificationp
                        '(:in-theory (enable))))))
       ,@(and top-returns '((set-ignore-ok t)))
       (defun-inline ,name ,formals
         ,@(if doc (list doc) nil)
         ,@decls
         ,@(and top-guard
                `((declare (xargs :guard ,top-guard))))
         ,(if top-returns
              `(b* (,@init-vals
                    (,returns
                     (mbe :logic (,iter ,last . ,(cdr iter-formals))
                          :exec (,tailrec ,first . ,(cdr iter-formals)))))
                 ,top-returns)
            `(b* ,init-vals
               (mbe :logic (,iter ,last . ,(cdr iter-formals))
                    :exec (,tailrec ,first . ,(cdr iter-formals))))))

       (in-theory (enable (:induction ,iter))))))


(defxdoc defiteration
  :parents (programming)
  :short "Define a simple for-loop-style iteration, counting up over some
range."
  :long "<p>This macro defines the logic version of this loop as a
non-tail-recursive function that counts down from the maximum value to the
minimum value.  This is often better for reasoning with.  The executable
version is a function that counts up from the minimum to the maximum value and
is tail-recursive, which may be better for execution, especially in terms of
avoiding stack overflows.</p>

<p>Syntax:</p>

@({
    (defiteration function-name (a b c)
      \"optional doc string\"
      (declare ...)        ;; optional declare forms
      (body idx-var a b c) ;; one step of the iteration
      :returns (mv b c)    ;; or a single variable, must be from the formals
      :index idx-var       ;; counter variable
      :first (foo a b)     ;; starting index, default 0
      :last  (bar a c)     ;; final index
      :hints ...           ;; optional, for proving that tailrec and non-tailrec
                           ;; are the same
      :guard-hints ...     ;; for defining the step function
      :package foo)        ;; package witness symbol, default is function-name
})")

(defmacro defiteration (name formals &rest args)
  ;; args contains:
  ;; (optional) declarations/doc string
  ;; body
  ;; keyword list
  (defiteration-fn name formals args))

(local
 (progn
   (defiteration countup (a b)
     (declare (xargs :guard (and (natp a) (acl2-numberp b))))
     (1+ b)
     :returns b
     :last a)

   (defiteration countup-from (s a b)
     (declare (xargs :guard (and (natp a) (natp s)
                                 (<= s a)
                                 (acl2-numberp b))))
     (1+ b)
     :index nn
     :returns b
     :first s
     :last a)

   (defiteration countup-more (s a b)
     (declare (xargs :guard (and (natp a) (natp s)
                                 (<= s a)
                                 (acl2-numberp b))))
     (+ nn b)
     :index nn
     :returns b
     :first s
     :last a)

   (defiteration countup-2 (s a b c)
     (declare (xargs :guard (and (natp a) (natp s)
                                 (<= s a)
                                 (acl2-numberp b)
                                 (acl2-numberp c))))
     (mv (+ nn b) (- c nn))
     :index nn
     :returns (mv b c)
     :first s
     :last a)

   (defiteration countup-3 (s a c)
     (declare (xargs :guard (and (natp a) (natp s)
                                 (<= s a)
                                 (acl2-numberp c))))
     (mv (+ nn b) (- c nn))
     :index nn
     :returns (mv b c)
     :first s
     :last a
     :init-vals ((b 0))
     :iter-guard (acl2-numberp b))))



(defstub listconstr-val (n formals) nil)
(defstub listconstr-last (formals) nil)

(defiteration listconstr (formals)
  (declare (xargs :verify-guards nil))
  (let ((val (listconstr-val n formals)))
    (update-nth n val lst))
  :returns lst
  :last (listconstr-last formals)
  :init-vals ((lst nil))
  :iter-guard (true-listp lst))

(defthm nth-of-listconstr-iter
  (equal (nth m (listconstr-iter n nil formals))
         (and (< (nfix m) (nfix n))
              (listconstr-val (nfix m) formals)))
  :hints (("goal" :induct (listconstr-iter n nil formals)
           :expand ((listconstr-iter n nil formals)))))

(defthm len-of-listconstr-iter
  (equal (len (listconstr-iter n nil formals))
         (nfix n))
  :hints (("goal" :induct (listconstr-iter n nil formals)
           :expand ((listconstr-iter n nil formals)))))

(defthm true-listp-of-listconstr-iter
  (true-listp (listconstr-iter n nil formals))
  :hints (("goal" :induct (listconstr-iter n nil formals)
           :expand ((listconstr-iter n nil formals)))))

(defthm nth-of-listconstr
  (equal (nth n (listconstr formals))
         (let ((n (nfix n)))
           (and (< n (nfix (listconstr-last formals)))
                (listconstr-val n formals)))))

(defthm len-of-listconstr
  (equal (len (listconstr formals))
         (nfix (listconstr-last formals))))

(defthm true-listp-of-listconstr
  (true-listp (listconstr formals)))


(defun def-list-constructor-fn (name formals args)
  (b* (((mv decls doc body kwlist) (defiteration-sort-args args))
       (index (get-kw :index (intern-in-package-of-symbol
                              "N" name)
                      kwlist))
       ((when (member index formals))
        (er hard? 'def-list-constructor "Index variable (~x0) must not be in formals" index))
       (list-var (get-kw :list-var (intern-in-package-of-symbol
                                    "LST" name)
                         kwlist))
       ((when (member list-var formals))
        (er hard? 'def-list-constructor "List variable (~x0) must not be in formals" list-var))
       (length (get-kw :length nil kwlist))
       ((unless length) (er hard? 'def-list-constructor "Need :length argument"))
       (iter-guard (get-kw :iter-guard t kwlist))
       (package (get-kw :package name kwlist))
       (iter (intern-in-package-of-symbol
              (concatenate 'string (symbol-name name) "-ITER")
              package))
       (tailrec (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name name) "-TAILREC")
                 package))
       (iter-formals (cons index (cons list-var formals)))
       (step-call (cons (intern-in-package-of-symbol
                         (concatenate 'string (symbol-name name) "-STEP")
                         package)
                        iter-formals))
       (step (intern-in-package-of-symbol
              (concatenate 'string (symbol-name name) "-STEP")
              package))
       (?nth-thmname (intern-in-package-of-symbol
                     (concatenate 'string "NTH-OF-" (symbol-name name))
                     package))
       (nth-split-thmname (intern-in-package-of-symbol
                           (concatenate 'string "NTH-OF-" (symbol-name name) "-SPLIT")
                           package))
       (?true-listp-thmname (intern-in-package-of-symbol
                            (concatenate 'string "TRUE-LISTP-OF-" (symbol-name
                                                                   name))
                            package))
       (?len-thmname (intern-in-package-of-symbol
                     (concatenate 'string "LEN-OF-" (symbol-name name))
                     package))
       (fsubst `((listconstr-val
                  (lambda (n formals)
                    (b* (((list . ,formals) formals)
                         (,index n))
                      ,body)))
                 (listconstr-last
                  (lambda (formals)
                    (b* (((list . ,formals) formals))
                      ,length)))
                 (listconstr-step$inline
                  (lambda (n lst formals)
                    (b* (((list . ,formals) formals)
                         (,index n)
                         (,list-var lst))
                      ,step-call)))
                 (listconstr-iter
                  (lambda (n lst formals)
                    (b* (((list . ,formals) formals)
                         (,index n)
                         (,list-var lst))
                      (,iter . ,iter-formals))))
                 (listconstr-tailrec
                  (lambda (n lst formals)
                    (b* (((list . ,formals) formals)
                         (,index n)
                         (,list-var lst))
                      (,tailrec . ,iter-formals))))
                 (listconstr$inline
                  (lambda (formals)
                    (b* (((list . ,formals) formals))
                      (,name . ,formals)))))))
    `(encapsulate nil
       (set-ignore-ok t)
       (set-irrelevant-formals-ok t)
       (defiteration ,name ,formals
         ,@decls ,@(and doc (list doc))
         (let ((val ,body))
           (update-nth ,index val ,list-var))
         :returns ,list-var
         :first 0
         :last ,length
         :init-vals ((,list-var nil))
         :iter-guard (and (true-listp ,list-var) ,iter-guard)
         . ,kwlist)

       (in-theory (disable ,name))

       (defthmd ,nth-split-thmname
         (equal (nth ,index (,name . ,formals))
                (let ((,index (nfix ,index)))
                  (and (< ,index (nfix ,length))
                       ,body)))
         :hints (("goal" :use ((:instance
                                (:functional-instance
                                 nth-of-listconstr
                                 . ,fsubst)
                                (formals (list . ,formals))
                                (n ,index)))
                    :in-theory '(,iter
                                 ,step
                                 ,name
                                 ,tailrec
                                 car-cons
                                 cdr-cons
                                 zp-when-integerp
                                 commutativity-of-+
                                 (equal) (ifix) (unary--) (zp)
                                 ifix-positive-to-non-zp
                                 unicity-of-0
                                 fix
                                 (:type-prescription ifix))
                    :do-not-induct t)))

       (defthm ,nth-thmname
         (implies (< (nfix ,index) (nfix ,length))
                  (equal (nth ,index (,name . ,formals))
                         (let ((,index (nfix ,index)))
                           ,body)))
         :hints(("Goal" :in-theory (enable ,nth-split-thmname))))

       (defthm ,len-thmname
         (equal (len (,name . ,formals))
                (nfix ,length))
         :hints (("goal" :use ((:instance
                                (:functional-instance
                                 len-of-listconstr
                                 . ,fsubst)
                                (formals (list . ,formals))))
                  :in-theory '(car-cons cdr-cons))))

       (defthm ,true-listp-thmname
         (true-listp (,name . ,formals))
         :hints (("goal" :use ((:instance
                                (:functional-instance
                                 true-listp-of-listconstr
                                 . ,fsubst)
                                (formals (list . ,formals))))
                  :in-theory '(car-cons cdr-cons)))
         :rule-classes (:rewrite :type-prescription)))))


(defxdoc def-list-constructor
  :parents (programming)
  :short "Define function that constructs a list, just by giving the length and
how to compute the Nth element in terms of the formals and index."
  :long
  "<p>This takes many of the same arguments as @(see defiteration), and in fact
it uses defiteration.  But instead of giving the step function for the
iteration, you give the value of the Nth element of the list.  You must also
provide the keyword :last, giving the length of the list.</p>

<p>What you end up with is your top-level function, definition disabled, and
four rules:</p>

<ul>
<li>@('nth-of-fnname') tells what the Nth element is, for N in bounds</li>
<li>@('nth-of-fnname-split') (disabled), tells what the Nth element is,
    causing a case-split on whether it's in bounds or not</li>
<li>@('len-of-fnname'): gives the length of the list</li>
<li>@('true-listp-of-fnname') shows that the list is true-listp.</li>
</ul>

<p>See @('centaur/misc/equal-by-nths') for a strategy that proves equivalences
between lists based on length and Nth value.</p>

<p>Syntax:</p>

@({
    (def-list-constructor foo (x y)
      \"optional doc string\"
      (declare (xargs ...))   ;; optional declare forms
      (+ idx-var x y)         ;; value of the IDX-VARth element
      :length  (bar x y)      ;; final index
      :index idx-var          ;; counter variable, default N
      ... defiteration args ...)
})")

(defmacro def-list-constructor (name formals &rest args)
  ;; args contains:
  ;; (optional) declarations/doc string
  ;; body
  ;; keyword list
  (def-list-constructor-fn name formals args))

(local
 (def-list-constructor foo (x y)
   (declare (xargs :guard (and (natp x)
                               (natp y))))
   (+ n x y)
   :length x))
