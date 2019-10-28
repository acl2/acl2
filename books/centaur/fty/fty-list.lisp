; FTY type support library
; Copyright (C) 2014 Centaur Technology
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

(in-package "FTY")
(include-book "database")
(include-book "fty-parseutils")
(program)

(defconst *flexlist-keywords*
  '(:pred
    :fix
    :equiv
    :count
    :elt-type
    :non-emptyp
    :measure
    :measure-debug
    :xvar
    :true-listp
    :elementp-of-nil
    :cheap
    :parents
    :short
    :long
    :no-count
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    :enable-rules
    :verbosep))

(define parse-flexlist (x xvar our-fixtypes fixtypes state)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (raise "Malformed flexlist: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// name args))
       ((mv kwd-alist rest)
        (extract-keywords name *flexlist-keywords* pre-/// nil))
       ((when rest)
        (raise "Malformed flexlist: ~x0: after kind should be a keyword/value list."
               name))
       (elt-type (getarg :elt-type nil kwd-alist))
       ((unless (and (symbolp elt-type) elt-type))
        (raise "Bad flexlist ~x0: Element type must be a symbol" name))
       ((mv elt-type elt-fix elt-equiv recp)
        (get-pred/fix/equiv (getarg :elt-type nil kwd-alist) our-fixtypes fixtypes))
       (pred  (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix   (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
       (non-emptyp (getarg :non-emptyp nil kwd-alist))
       (elementp-of-nil (getarg :elementp-of-nil :unknown kwd-alist))
       (cheap           (getarg :cheap           nil kwd-alist))
       (count (flextype-get-count-fn name kwd-alist))
       (xvar (or (getarg :xvar xvar kwd-alist)
                 (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                 (intern-in-package-of-symbol "X" name)))
       (measure (getarg! :measure `(acl2-count ,xvar) kwd-alist))
       ((mv already-defined true-listp)
        (check-flexlist-already-defined pred kwd-alist our-fixtypes 'deflist state))
       (fix-already-defined
        (check-flexlist-fix-already-defined fix kwd-alist our-fixtypes 'deflist state)))

    (make-flexlist :name name
                   :pred pred
                   :fix fix
                   :equiv equiv
                   :count count
                   :elt-type elt-type
                   :elt-fix elt-fix
                   :elt-equiv elt-equiv
                   :true-listp true-listp
                   :elementp-of-nil elementp-of-nil
                   :cheap cheap
                   :measure measure
                   :non-emptyp non-emptyp
                   :kwd-alist (if post-///
                                  (cons (cons :///-events post-///)
                                        kwd-alist)
                                kwd-alist)
                   :xvar xvar
                   :recp recp
                   :already-definedp already-defined
                   :fix-already-definedp fix-already-defined)))



(define flexlist-fns (x)
  (b* (((flexlist x)))
    (list x.pred
          x.fix)))

(define flexlist-collect-fix/pred-pairs (x)
  (b* (((flexlist x)))
    (and x.elt-type
         x.elt-fix   ;; BOZO how could this happen?
         (list (cons x.elt-fix x.elt-type)))))

(define flexlist-predicate-def (x)
  (b* (((flexlist x))
       ;; std::deflist-compatible variable names
       (stdx (intern-in-package-of-symbol "X" x.pred))
       ;; (stda (intern-in-package-of-symbol "A" 'acl2::foo)))
       )
    `(,@(if x.already-definedp
            '(progn)
          `(define ,x.pred (,x.xvar)
             ;; BOZO not exactly clear when/where to add docs for the predicate
             :parents nil
             :progn t
             :measure ,x.measure
             ,@(and (getarg :measure-debug nil x.kwd-alist)
                    `(:measure-debug t))
             ,(if x.non-emptyp
                  `(and (consp ,x.xvar)
                        (,x.elt-type (car ,x.xvar))
                        (let ((,x.xvar (cdr ,x.xvar)))
                          (if (atom ,x.xvar)
                              ,(if x.true-listp
                                   `(eq ,x.xvar nil)
                                 t)
                            (,x.pred ,x.xvar))))
                `(if (atom ,x.xvar)
                     ,(if x.true-listp
                          `(eq ,x.xvar nil)
                        t)
                   (and (,x.elt-type (car ,x.xvar))
                        (,x.pred (cdr ,x.xvar)))))
             ///))
       (local (in-theory (disable ,x.pred)))
       (std::deflist ,x.pred (,stdx)
         :parents (,x.name)
         (,x.elt-type ,stdx)
         :already-definedp t
         ,@(and (not (eq x.elementp-of-nil :unknown))
                `(:elementp-of-nil ,x.elementp-of-nil))
         :true-listp ,x.true-listp
         :non-emptyp ,x.non-emptyp
         :cheap ,x.cheap)
       ;; (defthm ,(intern-in-package-of-symbol (cat (symbol-name x.pred) "-OF-CONS")
       ;;                                       x.pred)
       ;;   ;; Use special symbols for std::deflist compatibility
       ;;   (equal (,x.pred (cons ,stda ,stdx))
       ;;          (and (,x.elt-type ,stda)
       ;;               (,x.pred ,stdx)))
       ;;   :hints (("Goal" :Expand ((,x.pred (cons ,stda ,stdx))))))

       ;; (defthm ,(intern-in-package-of-symbol (cat (symbol-name x.pred) "-OF-CDR")
       ;;                                       x.pred)
       ;;   (implies (,x.pred ,x.xvar)
       ;;            (,x.pred (cdr ,x.xvar)))
       ;;   :hints (("goal" :expand ((,x.pred ,x.xvar)))
       ;;           (and stable-under-simplificationp
       ;;                '(:expand ((,x.pred (cdr ,x.xvar)))))))

       ;; (defthm ,(intern-in-package-of-symbol
       ;;           (cat (symbol-name x.elt-type) "-CAR-OF-" (symbol-name x.pred))
       ;;           x.pred)
       ;;   (implies (and (consp ,stdx)
       ;;                 (,x.pred ,stdx))
       ;;            (,x.elt-type (car ,stdx)))
       ;;   :hints (("goal" :expand ((,x.pred ,stdx))))
       ;;   :rule-classes ((:rewrite :backchain-limit-lst (0 nil))))

       ;; ,@(and x.true-listp
       ;;        `((defthm ,(intern-in-package-of-symbol
       ;;                    (cat (symbol-name x.pred) "-COMPOUND-RECOGNIZER")
       ;;                    x.pred)
       ;;            (implies (,x.pred ,x.xvar)
       ;;                     (true-listp ,x.xvar))
       ;;            :hints (("goal" :expand ((,x.pred ,x.xvar))
       ;;                     :induct (true-listp ,x.xvar)
       ;;                     :in-theory (enable true-listp)))
       ;;            :rule-classes :compound-recognizer)))
       )))


(define flexlist-fix-def (x flagp)
  (b* (((flexlist x)))
    (if x.fix-already-definedp
        '(progn)
      `(define ,x.fix ((,x.xvar ,x.pred))
         :parents (,x.name)
         :short ,(cat "@(call " (xdoc::full-escape-symbol x.fix)
                      ") is a usual @(see fty::fty) list fixing function.")
         :long ,(cat "<p>In the logic, we apply @(see? "
                     (xdoc::full-escape-symbol x.elt-fix)
                     ") to each member of the x.  In the execution, none of
                    that is actually necessary and this is just an inlined
                    identity function.</p>")
         :measure ,x.measure
         ,@(and (getarg :measure-debug nil x.kwd-alist)
                `(:measure-debug t))
         ,@(and flagp `(:flag ,x.name))
         :returns (newx ,x.pred
                        :hints(,@(and (not flagp)
                                      `(("goal" :induct (,x.fix ,x.xvar))))
                                 '(:in-theory (disable ,x.fix ,x.pred)
                                   :expand ((,x.fix ,x.xvar)
                                            (:free (a b) (,x.pred (cons a b)))
                                            (,x.pred ,x.xvar)
                                            (,x.pred nil)))))
         :verify-guards nil
         :progn t
         ;; [Jared]: inlining this since it's just an identity function
         :inline t
         (mbe :logic
              ,(if x.non-emptyp
                   ;; ugly def to avoid needing ruler-extenders
                   `(if (consp (cdr ,x.xvar))
                        (cons (,x.elt-fix (car ,x.xvar))
                              (,x.fix (cdr ,x.xvar)))
                      (cons (,x.elt-fix (car ,x.xvar))
                            ,(if x.true-listp
                                 nil
                               `(cdr ,x.xvar))))
                 `(if (atom ,x.xvar)
                      ,(if x.true-listp
                           nil
                         x.xvar)
                    (cons (,x.elt-fix (car ,x.xvar))
                          (,x.fix (cdr ,x.xvar)))))
              :exec ,x.xvar)
         ///))))

(define flexlist-fix-postevents (x)
  (b* (((flexlist x))
       ;; std::defprojection-compatible variable names
       (stdx              (intern-in-package-of-symbol "X" x.pred))
       (stda              (intern-in-package-of-symbol "A" x.pred))
       (consp-of-foo-fix  (intern-in-package-of-symbol (cat "CONSP-OF-" (symbol-name x.fix)) x.fix))
       (consp-cdr-of-foo-fix  (intern-in-package-of-symbol (cat "CONSP-CDR-OF-" (symbol-name x.fix)) x.fix))
       (car-of-foo-fix    (intern-in-package-of-symbol (cat "CAR-OF-" (symbol-name x.fix)) x.fix))
       (foo-fix-under-iff (intern-in-package-of-symbol (cat (symbol-name x.fix) "-UNDER-IFF") x.fix))
       (foo-fix-of-cons   (intern-in-package-of-symbol (cat (symbol-name x.fix) "-OF-CONS") x.fix))
       (len-of-foo-fix    (intern-in-package-of-symbol (cat "LEN-OF-" (symbol-name x.fix)) x.fix))
       (foo-fix-of-append (intern-in-package-of-symbol (cat (symbol-name x.fix) "-OF-APPEND") x.fix)))
    `((deffixcong ,x.equiv ,x.elt-equiv (car x) x
        :pkg ,x.equiv
        :hints (("goal" :expand ((,x.fix x))
                 :in-theory (enable acl2::default-car))))

      (deffixcong ,x.equiv ,x.equiv (cdr x) x
        :pkg ,x.equiv
        :hints (("goal" :expand ((,x.fix x)
                                 ,@(and x.non-emptyp
                                        `((,x.fix (cdr x)))))
                 ,@(and x.non-emptyp
                        '(:in-theory (enable default-car))))))

      (deffixcong ,x.elt-equiv ,x.equiv (cons x y) x
        :pkg ,x.equiv
        :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))

      ,@(and (not x.non-emptyp)
             `((deffixcong ,x.equiv ,x.equiv (cons x y) y
                 :pkg ,x.equiv
                 :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))))

      (defthm ,consp-of-foo-fix
        ,(if x.non-emptyp
             `(consp (,x.fix x))
           `(equal (consp (,x.fix x))
                   (consp x)))
        :hints (("goal" :expand ((,x.fix x)))))

      ,@(and x.non-emptyp
             `((defthm ,consp-cdr-of-foo-fix
                 (equal (consp (cdr (,x.fix x)))
                        (consp (cdr x)))
                 :hints (("goal" :expand ((,x.fix x)))))

               (defthm ,car-of-foo-fix
                 (equal (car (,x.fix x))
                        (,x.elt-fix (car x)))
                 :hints (("goal" :expand ((,x.fix x)))))))

      ,@(and (or x.true-listp x.non-emptyp)
             `((defthm ,foo-fix-under-iff
                 ,(if x.non-emptyp
                      `(,x.fix x)
                    `(iff (,x.fix x)
                          (consp x)))
                 :hints (("goal" :expand ((,x.fix x)))))))

      (defthm ,foo-fix-of-cons
        ;; bozo make sure this is compatible with defprojection
        (equal (,x.fix (cons ,stda ,stdx))
               (cons (,x.elt-fix ,stda)
                     ,(if x.non-emptyp
                          (if x.true-listp
                              `(and (consp ,stdx)
                                    (,x.fix ,stdx))
                            `(if (consp ,stdx)
                                 (,x.fix ,stdx)
                               ,stdx))
                        `(,x.fix ,stdx))))
        :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))

      (defthm ,len-of-foo-fix
        (equal (len (,x.fix x))
               ,(if x.non-emptyp
                    `(max 1 (len x))
                  `(len x)))
        :hints (("goal" :induct (len x)
                 :expand ((,x.fix x))
                 :in-theory (enable len))))

      ,@(and (not x.non-emptyp)
             `((defthm ,foo-fix-of-append
                 (equal (,x.fix (append std::a std::b))
                        (append (,x.fix std::a) (,x.fix std::b)))
                 :hints (("goal" :induct (append std::a std::b)
                          :expand ((,x.fix std::a)
                                   (:free (a b) (,x.fix (cons a b)))
                                   (,x.fix nil)
                                   (:free (b) (append std::a b))
                                   (:free (b) (append nil b))
                                   (:free (a b c) (append (cons a b) c)))
                          :in-theory (enable (:i append))))))))))

(define flexlist-fix-when-pred-thm (x flagp)
  (b* (((flexlist x))
       (foo-fix-when-foo-p (intern-in-package-of-symbol
                            (cat (symbol-name x.fix) "-WHEN-" (symbol-name x.pred))
                            x.fix)))
    `(defthm ,foo-fix-when-foo-p
       (implies (,x.pred ,x.xvar)
                (equal (,x.fix ,x.xvar) ,x.xvar))
       :hints (,@(and (not flagp)
                      `(("goal" :induct (,x.fix ,x.xvar))))
                 '(:expand ((,x.pred ,x.xvar)
                          (,x.fix ,x.xvar))
                 :in-theory (disable ,x.fix ,x.pred)))
       . ,(and flagp `(:flag ,x.name)))))


(defun flexlist-count (x types)
  (b* (((flexlist x))
       ((unless x.count) nil)
       (eltcount (flextypes-find-count-for-pred x.elt-type types)))
    `((define ,x.count ((,x.xvar ,x.pred))
        :returns (count natp
                        :rule-classes :type-prescription
                        :hints ('(:expand (,x.count ,x.xvar)
                                  :in-theory (disable ,x.count))))
        :measure (let ((,x.xvar (,x.fix ,x.xvar)))
                   ,x.measure)
        ,@(and (getarg :measure-debug nil x.kwd-alist)
               `(:measure-debug t))
        :verify-guards nil
        :progn t
        ,(if x.non-emptyp
             ;; ugly def to avoid needing ruler-extenders
             `(if (consp (cdr ,x.xvar))
                  (+ 1
                     ,@(and eltcount `((,eltcount (car ,x.xvar))))
                     (,x.count (cdr ,x.xvar)))
                (+ 1
                   ,@(and eltcount `((,eltcount (car ,x.xvar))))))
           `(if (atom ,x.xvar)
                1
              (+ 1
                 ,@(and eltcount `((,eltcount (car ,x.xvar))))
                 (,x.count (cdr ,x.xvar)))))))))


(defun flexlist-count-post-events (x types)
  (b* (((flexlist x))
       ((unless x.count) nil)
       (eltcount (flextypes-find-count-for-pred x.elt-type types))
       ;; ((when (not eltcount)) nil)
       (foo-count-of-cons (intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-CONS") x.count))
       (foo-count-of-cdr  (intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-CDR") x.count))
       (foo-count-of-car  (intern-in-package-of-symbol (cat (symbol-name eltcount) "-OF-CAR") x.count)))
    `((defthm ,foo-count-of-cons
        ,(let ((body `(> (,x.count (cons a b))
                         ,(if eltcount
                              `(+ (,eltcount a) (,x.count b))
                            `(,x.count b)))))
           (if x.non-emptyp
               `(implies (consp b)
                         ,body)
             body))
        :hints (("goal" :expand ((:free (a b) (,x.count (cons a b))))))
        :rule-classes :linear)

      ,@(and eltcount
             `((defthm ,foo-count-of-car
                 (implies ,(if x.non-emptyp
                               t
                             `(consp ,x.xvar))
                          (< (,eltcount (car ,x.xvar)) (,x.count ,x.xvar)))
                 ,@(and x.non-emptyp
                        `(:hints (("goal" :expand ((,x.count ,x.xvar))))))
                 :rule-classes :linear)))

      (defthm ,foo-count-of-cdr
        (implies ,(if x.non-emptyp
                      `(consp (cdr ,x.xvar))
                    `(consp ,x.xvar))
                 (< (,x.count (cdr ,x.xvar)) (,x.count ,x.xvar)))
        :rule-classes :linear))))
