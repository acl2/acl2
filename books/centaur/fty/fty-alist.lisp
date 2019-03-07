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

(define flexalist-fns (x)
  (b* (((flexalist x) x))
    (list x.pred
          x.fix)))

(define flexalist-collect-fix/pred-pairs (alist)
  (b* (((flexalist alist) alist))
    (append (and alist.key-type
                 alist.key-fix ;; bozo how could this not hold?
                 (list (cons alist.key-fix alist.key-type)))
            (and alist.val-type
                 alist.val-fix ;; bozo how could this not hold?
                 (list (cons alist.val-fix alist.val-type))))))

(defconst *flexalist-keywords*
  '(:pred
    :fix
    :equiv
    :count
    :get
    :get-fast
    :set
    :set-fast
    :key-type
    :val-type
    :measure
    :measure-debug
    :xvar
    :parents
    :short
    :long
    :no-count
    :true-listp
    :unique-keys
    :prepwork
    :strategy
    :keyp-of-nil
    :valp-of-nil
    :post-pred-events
    :post-fix-events
    :post-events
    :enable-rules
    :already-definedp
    :verbosep))

(define parse-flexalist (x xvar our-fixtypes fixtypes state)
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (raise "Malformed flexalist: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///) (std::split-/// name args))
       ((mv kwd-alist rest)   (extract-keywords name *flexalist-keywords* pre-/// nil))
       ((when rest)
        (raise "Malformed flexalist: ~x0: after kind should be a keyword/value list." name))
       (key-type (getarg :key-type nil kwd-alist))
       ((unless (symbolp key-type))
        (raise "Bad flexalist ~x0: Element type must be a symbol" name))
       ((mv key-type key-fix key-equiv key-recp)
        (get-pred/fix/equiv (getarg :key-type nil kwd-alist) our-fixtypes fixtypes))
       (val-type (getarg :val-type nil kwd-alist))
       ((unless (symbolp val-type))
        (raise "Bad flexalist ~x0: Element type must be a symbol" name))
       ((mv val-type val-fix val-equiv val-recp)
        (get-pred/fix/equiv (getarg :val-type nil kwd-alist) our-fixtypes fixtypes))
       (pred  (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix   (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
       (count (flextype-get-count-fn name kwd-alist))
       (xvar (or (getarg :xvar xvar kwd-alist)
                 (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                 (intern-in-package-of-symbol "X" name)))
       (measure (getarg! :measure `(acl2-count ,xvar) kwd-alist))
       (strategy (getarg :strategy :fix-keys kwd-alist))
       (- (and (not (member strategy '(:fix-keys :drop-keys)))
               (raise "In flexalist ~x0: invalid strategy ~x1~%" name strategy)))
       ((mv already-defined true-listp)
        (check-flexlist-already-defined pred kwd-alist our-fixtypes name state))
       (fix-already-defined
        (check-flexlist-fix-already-defined fix kwd-alist our-fixtypes name state)))
    (make-flexalist :name name
                    :pred pred
                    :fix fix
                    :equiv equiv
                    :count count
                    :key-type key-type
                    :key-fix key-fix
                    :key-equiv key-equiv
                    :val-type val-type
                    :val-fix val-fix
                    :val-equiv val-equiv
                    :measure measure
                    :strategy strategy
                    :kwd-alist (if post-///
                                   (cons (cons :///-events post-///)
                                         kwd-alist)
                                 kwd-alist)
                    :xvar xvar
                    :true-listp true-listp
                    :recp (or key-recp val-recp)
                    :already-definedp already-defined
                    :fix-already-definedp fix-already-defined
                    :keyp-of-nil (getarg :keyp-of-nil :unknown kwd-alist)
                    :valp-of-nil (getarg :valp-of-nil :unknown kwd-alist)
                    :unique-keys (getarg :unique-keys nil kwd-alist))))

(define flexalist-predicate-def (alist)
  (b* (((flexalist alist) alist)
       ;; std::deflist-compatible variable names
       (stdx (intern-in-package-of-symbol "X" alist.pred))
       ;; (stda (intern-in-package-of-symbol "A" alist.pred)))
       (std-defalist-call (and (not alist.unique-keys)
                               `((std::defalist ,alist.pred (,stdx)
                                   ,@(and alist.key-type `(:key (,alist.key-type ,stdx)))
                                   ,@(and alist.val-type `(:val (,alist.val-type ,stdx)))
                                   :true-listp ,alist.true-listp
                                   :keyp-of-nil ,alist.keyp-of-nil
                                   :valp-of-nil ,alist.valp-of-nil
                                   :already-definedp t
                                   ;; Try to turn off all doc generation here
                                   :parents nil
                                   :short nil
                                   :long nil)))))
    (if alist.already-definedp
        `(progn
           (local (in-theory (disable ,alist.pred)))
           . ,std-defalist-call)
      `(define ,alist.pred (,alist.xvar)
         :parents (,alist.name)
         :progn t
         :short ,(str::cat "Recognizer for @(see " (xdoc::full-escape-symbol alist.name) ").")
         :measure ,alist.measure
         ,@(and (getarg :measure-debug nil alist.kwd-alist)
                `(:measure-debug t))
         (if (atom ,alist.xvar)
             ,(if alist.true-listp
                  `(eq ,alist.xvar nil)
                t)
           (and (consp (car ,alist.xvar))
                ,@(and alist.unique-keys `((not (hons-assoc-equal (caar ,alist.xvar) (cdr ,alist.xvar)))))
                ,@(and alist.key-type `((,alist.key-type (caar ,alist.xvar))))
                ,@(and alist.val-type `((,alist.val-type (cdar ,alist.xvar))))
                (,alist.pred (cdr ,alist.xvar))))
         ///
         (local (in-theory (disable ,alist.pred)))
         ,@(and alist.unique-keys
                ;; Enough theorems to get on with for now...
                `((defthm ,(intern-in-package-of-symbol (cat (symbol-name alist.pred) "-OF-CDR")
                                                        alist.pred)
                    (implies (,alist.pred ,alist.xvar)
                             (,alist.pred (cdr ,alist.xvar)))
                    :hints (("goal" :expand ((,alist.pred ,alist.xvar)))))

                  ,@(and alist.key-type
                         `((defthm ,(intern-in-package-of-symbol (cat (symbol-name alist.key-type) "-OF-CAAR-WHEN-"
                                                                      (symbol-name alist.pred))
                                                                 alist.pred)
                             (implies (and (,alist.pred ,alist.xvar)
                                           (consp ,alist.xvar))
                                      (,alist.key-type (caar ,alist.xvar)))
                             :hints (("goal" :expand ((,alist.pred ,alist.xvar)))))))
                  ,@(and alist.val-type
                         `((defthm ,(intern-in-package-of-symbol (cat (symbol-name alist.val-type) "-OF-CDAR-WHEN-"
                                                                      (symbol-name alist.pred))
                                                                 alist.pred)
                             (implies (and (,alist.pred ,alist.xvar)
                                           (consp ,alist.xvar))
                                      (,alist.val-type (cdar ,alist.xvar)))
                             :hints (("goal" :expand ((,alist.pred ,alist.xvar)))))))
                  (defthm ,(intern-in-package-of-symbol (cat (symbol-name alist.pred) "-OF-CONS")
                                                        alist.pred)
                    (equal (,alist.pred (cons a ,alist.xvar))
                           (and (and (consp a)
                                     ,@(and alist.key-type `((,alist.key-type (car a))))
                                     ,@(and alist.val-type `((,alist.val-type (cdr a))))
                                     (not (hons-assoc-equal (car a) ,alist.xvar)))
                                (,alist.pred ,alist.xvar)))
                    :hints (("goal" :expand ((,alist.pred (cons a ,alist.xvar))))))
                  ))
         . ,std-defalist-call))))

(define flexalist-fix-def (x flagp)
  (b* (((flexalist x) x))
    (if x.fix-already-definedp
        '(progn)
      `(define ,x.fix ((,x.xvar ,x.pred))
         :parents (,x.name)
         :short ,(cat "@(call " (xdoc::full-escape-symbol x.fix)
                      ") is an @(see fty::fty) alist fixing function that follows the "
                      (str::downcase-string (symbol-name x.strategy)) " strategy.")
         ;; BOZO it would be nice to describe the fixing strategy that is used
         ;; and connect it to discussion of the non-alist convention, etc.  However
         ;; the fixing strategy to use is parameterized and I don't remember all the
         ;; options and what they do, so for now I'll omit that.
         :long "<p>Note that in the execution this is just an inline
              identity function.</p>"
         :measure ,x.measure
         ,@(and (getarg :measure-debug nil x.kwd-alist)
                `(:measure-debug t))
         ,@(and flagp `(:flag ,x.name))
         :returns (newx ,x.pred
                        :hints('(:in-theory (disable ,x.fix ,x.pred)
                                 :expand ((,x.fix ,x.xvar)
                                          (:free (a b) (,x.pred (cons a b)))
                                          (,x.pred ,x.xvar)
                                          (,x.pred nil)))))
         :verify-guards nil
         :progn t
         ;; [Jared]: inlining this since it's just an identity function
         :inline t
         (mbe :logic (if (atom ,x.xvar)
                         ,(if x.true-listp nil x.xvar)
                       ,(if (and (or (not x.key-fix)
                                     (eq x.strategy :fix-keys))
                                 (not x.unique-keys))
                            
                            `(if (consp (car ,x.xvar))
                                 (cons (cons ,(if x.key-fix
                                                  `(,x.key-fix (caar ,x.xvar))
                                                `(caar ,x.xvar))
                                             ,(if x.val-fix
                                                  `(,x.val-fix (cdar ,x.xvar))
                                                `(cdar ,x.xvar)))
                                       (,x.fix (cdr ,x.xvar)))
                               (,x.fix (cdr ,x.xvar)))
                          `(let ((rest (,x.fix (cdr ,x.xvar))))
                             (if (and (consp (car ,x.xvar))
                                      ,@(and x.key-fix
                                             (not (eq x.strategy :fix-keys))
                                             `((,x.key-type (caar ,x.xvar)))))
                                 (let ((first-key ,(if (and x.key-fix
                                                            (eq x.strategy :fix-keys))
                                                       `(,x.key-fix (caar ,x.xvar))
                                                     `(caar ,x.xvar)))
                                       (first-val ,(if x.val-fix
                                                       `(,x.val-fix (cdar ,x.xvar))
                                                     `(cdar ,x.xvar))))
                                   ,(if x.unique-keys
                                        `(if (hons-assoc-equal first-key rest)
                                             rest
                                           (cons (cons first-key first-val) rest))
                                      `(cons (cons first-key first-val) rest)))
                               rest))))
              :exec ,x.xvar)
         ///))))

(define flexalist-fix-postevents (x)
  (b* (((flexalist x) x)
       ;; std::defprojection-compatible variable names
       (stdx (intern-in-package-of-symbol "X" x.pred)))
    `(,@(and x.key-type (eq x.strategy :fix-keys)
             `((deffixcong ,x.key-equiv ,x.equiv (cons (cons k v) x) k
                 :pkg ,x.equiv
                 :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))))

      ,@(and x.val-type
             `((deffixcong ,x.val-equiv ,x.equiv (cons (cons k v) x) v
                 :pkg ,x.equiv
                 :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))))

      (deffixcong ,x.equiv ,x.equiv (cons x y) y
        :pkg ,x.equiv
        :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))

      (defthm ,(intern-in-package-of-symbol (cat (symbol-name x.fix) "-OF-ACONS")
                                            x.fix)
        ;; bozo make sure this is compatible with defprojection
        (equal (,x.fix (cons (cons a b) ,stdx))
               ,(if (and (or (eq x.strategy :fix-keys) (not x.key-fix))
                         (not x.unique-keys))
                    `(cons (cons ,(if x.key-fix `(,x.key-fix a) 'a)
                                 ,(if x.val-fix `(,x.val-fix b) 'b))
                           (,x.fix ,stdx))
                  `(let ((rest (,x.fix ,stdx)))
                     (if (and ,@(and x.key-fix
                                     (not (eq x.strategy :fix-keys))
                                     `((,x.key-type a))))
                         (let ((first-key ,(if (and x.key-fix
                                                    (eq x.strategy :fix-keys))
                                               `(,x.key-fix a)
                                             'a))
                               (first-val ,(if x.val-fix
                                               `(,x.val-fix b)
                                             'b)))
                           ,(if x.unique-keys
                                `(if (hons-assoc-equal first-key rest)
                                     rest
                                   (cons (cons first-key first-val) rest))
                              `(cons (cons first-key first-val) rest)))
                       rest))))
        :hints (("goal" :Expand ((:free (a b) (,x.fix (cons a b)))))))

      ,@(and (not (eq x.strategy :fix-keys))
             (not x.unique-keys)
             `((defthm ,(intern-in-package-of-symbol
                         (cat "HONS-ASSOC-EQUAL-OF-" (symbol-name x.fix))
                         x.fix)
                 (equal (hons-assoc-equal k (,x.fix x))
                        (let ((pair (hons-assoc-equal k x)))
                          (and ,@(and x.key-fix `((,x.key-type k)))
                               pair
                               (cons k ,(if x.val-fix
                                            `(,x.val-fix (cdr pair))
                                          `(cdr pair))))))
                 :hints (("goal" :induct (len x)
                          :in-theory (enable (:i len))
                          :expand ((,x.fix x)
                                   (hons-assoc-equal k x)
                                   (:free (a b) (hons-assoc-equal k (cons a b)))))))))

      ,@(and (not x.unique-keys)
             `((defthm ,(intern-in-package-of-symbol (cat (symbol-name x.fix) "-OF-APPEND") x.fix)
                 (equal (,x.fix (append std::a std::b))
                        (append (,x.fix std::a) (,x.fix std::b)))
                 :hints (("goal" :induct (append std::a std::b)
                          :expand ((,x.fix std::a)
                                   (:free (a b) (,x.fix (cons a b)))
                                   (,x.fix nil)
                                   (:free (b) (append std::a b))
                                   (:free (b) (append nil b))
                                   (:free (a b c) (append (cons a b) c)))
                          :in-theory (enable (:i append)))))))

      (defthm ,(intern-in-package-of-symbol (cat "CONSP-CAR-OF-" (symbol-name x.fix)) x.fix)
        (equal (consp (car  (,x.fix ,x.xvar)))
               (consp (,x.fix ,x.xvar)))
        :hints (("goal" :induct (len ,x.xvar)
                 :expand ((,x.fix ,x.xvar))
                 :in-theory (e/d ((:i len)) ((:d ,x.fix)))))))))

(define flexalist-fix-when-pred-thm (x flagp)
  (b* (((flexalist x) x)
       (foo-fix-when-foo-p (intern-in-package-of-symbol
                            (cat (symbol-name x.fix) "-WHEN-" (symbol-name x.pred))
                            x.fix)))
    `(defthm ,foo-fix-when-foo-p
       (implies (,x.pred ,x.xvar)
                (equal (,x.fix ,x.xvar) ,x.xvar))
       :hints ('(:expand ((,x.pred ,x.xvar)
                          (,x.fix ,x.xvar))
                 :in-theory (disable ,x.fix ,x.pred)))
       . ,(and flagp `(:flag ,x.name)))))


(defun flexalist-count (x types)
  (b* (((flexalist x))
       ((unless x.count) nil)
       (keycount (flextypes-find-count-for-pred x.key-type types))
       (valcount (flextypes-find-count-for-pred x.val-type types)))
    `((define ,x.count ((,x.xvar ,x.pred))
        :returns (count natp :rule-classes :type-prescription
                        :hints ('(:expand (,x.count ,x.xvar)
                                  :in-theory (disable ,x.count))))
        :measure (let ((,x.xvar (,x.fix ,x.xvar)))
                   ,x.measure)
       ,@(and (getarg :measure-debug nil x.kwd-alist)
              `(:measure-debug t))
        :verify-guards nil
        :progn t
        (let ((,x.xvar (mbe :logic (,x.fix ,x.xvar) :exec ,x.xvar)))
          (if (atom ,x.xvar)
              1
            (+ 1
               ,@(and (or keycount valcount)
                      (if keycount
                          (if valcount
                              `((+ (,keycount (caar ,x.xvar))
                                   (,valcount (cdar ,x.xvar))))
                            `((,keycount (caar ,x.xvar))))
                        `((,valcount (cdar ,x.xvar)))))
               (,x.count (cdr ,x.xvar)))))))))


(defun flexalist-count-post-events (x types)
  (b* (((flexalist x))
       ((unless x.count) nil)
       (keycount (flextypes-find-count-for-pred x.key-type types))
       (valcount (flextypes-find-count-for-pred x.val-type types))
       ;; ((when (not eltcount)) nil)
       (foo-count-of-cons (intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-CONS") x.count))
       (foo-count-of-acons (intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-ACONS") x.count)))
    `((defthm ,foo-count-of-cons
        (>= (,x.count (cons a b))
            (,x.count b))
        :hints (("goal" :expand ((:free (a b) (,x.count (cons a b)))
                                 (,x.fix (cons a b))))
                (and stable-under-simplificationp
                     '(:expand ((,x.count b)))))
        :rule-classes :linear)

      ,@(and (or keycount valcount)
             `((defthm ,foo-count-of-acons
                 ,(if (and (or (eq x.strategy :fix-keys)
                               (not x.key-fix))
                           (not x.unique-keys))
                      `(> (,x.count (cons (cons a b) c))
                          (+ ,@(if keycount
                                   (if valcount
                                       `((,keycount a)
                                         (,valcount b))
                                     `((,keycount a)))
                                 `((,valcount b)))
                             (,x.count c)))
                    `(implies (and ,@(and x.key-type (not (eq x.strategy :fix-keys))
                                         `((,x.key-type a)))
                                   ,@(and x.unique-keys
                                          `((not (hons-assoc-equal
                                                  ,(if (and x.key-type (eq x.strategy :fix-keys))
                                                       `(,x.key-fix a)
                                                     'a)
                                                  (,x.fix c))))))
                              (> (,x.count (cons (cons a b) c))
                                 (+ ,@(if keycount
                                          (if valcount
                                              `((,keycount a)
                                                (,valcount b))
                                            `((,keycount a)))
                                        `((,valcount b)))
                                    (,x.count c)))))
                 :hints (("goal" :expand ((:free (a b) (,x.count (cons a b))))))
                 :rule-classes :linear)))

      ,@(and keycount
             `((defthm ,(intern-in-package-of-symbol (cat (symbol-name keycount) "-OF-CAAR-"
                                                          (symbol-name x.count))
                                                     x.count)
                 (implies (and (consp ,x.xvar)
                               (or (consp (car ,x.xvar))
                                   (,x.pred ,x.xvar))
                               ,@(and (not (eq x.strategy :fix-keys))
                                      `((,x.key-type (caar ,x.xvar)))))
                          (< (,keycount (caar ,x.xvar)) (,x.count ,x.xvar)))
                 :rule-classes :linear)))

      ,@(and valcount
             `((defthm ,(intern-in-package-of-symbol (cat (symbol-name valcount) "-OF-CDAR-"
                                                          (symbol-name x.count))
                                                     x.count)
                 (implies (and (consp ,x.xvar)
                               (or (consp (car ,x.xvar))
                                   (,x.pred ,x.xvar))
                               ,@(and (not (eq x.strategy :fix-keys))
                                      x.key-fix
                                      `((,x.key-type (caar ,x.xvar))))
                               ,@(and x.unique-keys
                                      `((not (hons-assoc-equal
                                              ,(if (and x.key-fix (eq x.strategy :fix-keys))
                                                   `(,x.key-fix (caar ,x.xvar))
                                                 `(caar ,x.xvar))
                                              (,x.fix (cdr ,x.xvar)))))))
                          (< (,valcount (cdar ,x.xvar)) (,x.count ,x.xvar)))
                 :rule-classes :linear)))

      (defthm ,(intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-CDR")
                                            x.count)
        (<= (,x.count (cdr ,x.xvar)) (,x.count ,x.xvar))
        :hints (("goal" :expand ((,x.fix ,x.xvar)
                                 (,x.count ,x.xvar)
                                 (,x.count (cdr ,x.xvar))
                                 (:free (a b) (,x.count (cons a b))))
                 :in-theory (enable acl2::default-cdr)))
        :rule-classes :linear)

      (defthm ,(intern-in-package-of-symbol (cat (symbol-name x.count) "-OF-CDR-STRONG")
                                            x.count)
        (implies (and (,x.pred ,x.xvar)
                      (consp ,x.xvar))
                 (< (,x.count (cdr ,x.xvar)) (,x.count ,x.xvar)))
        :hints (("goal" :expand ((,x.fix ,x.xvar)
                                 (,x.count ,x.xvar)
                                 (,x.count (cdr ,x.xvar))
                                 (:free (a b) (,x.count (cons a b))))
                 :in-theory (enable acl2::default-cdr)))
        :rule-classes :linear))))
