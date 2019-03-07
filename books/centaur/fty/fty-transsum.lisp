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
(include-book "fty-parseutils")
(include-book "xdoc/names" :dir :system)
(set-state-ok t)
(program)


(define some-flextranssum-member-recursivep (x)
  (if (atom x)
      nil
    (or (flextranssum-member->recp (car x))
        (some-flextranssum-member-recursivep (cdr x)))))

(defun flextranssum-memberlist->tags (x)
  (if (atom x)
      nil
    (append (flextranssum-member->tags (car x))
            (flextranssum-memberlist->tags (cdr x)))))


; Inferring Tags for Member Types ---------------------------------------------

(define infer-possible-tags-from-flextype
  ((ctx         "Context for error messages.")
   (member-name "Name of the transsum member we are inferring tags for.")
   (x           "The top-level flextype object for member-name."))
  (cond ((eq (tag x) :sum)
         ;; We will support using defprods and deftagsums as members.
         (b* (((flexsum x)))
           (if (or (eq x.typemacro 'deftagsum)
                   (eq x.typemacro 'defprod))
               (flexprods->kinds x.prods)
             (er hard? ctx
                 "Can't infer tags for ~x0: not supported: ~x1."
                 member-name x.typemacro))))
        ((eq (tag x) :transsum)
         ;; We will support using transsums as members.
         (flextranssum-memberlist->tags (flextranssum->members x)))
        (t
         ;; We won't try to support other types (flexlists, flexalists,
         ;; etc.) because they don't have clear tags.
         (er hard? ctx
             "Can't infer tags for ~x0: unsupported flextype ~x1."
             member-name (tag x)))))

(define infer-possible-tags-from-typename
  ((ctx         "Context for error messages.")
   (member-type "Name of the member type.")
   (table       "The whole flextypes database."))
  (b* (((mv ?flextypes-obj this-type)
        (search-deftypes-table member-type table))
       ((unless this-type)
        (er hard? ctx
            "Type ~x0 not found in the flextypes table."
            member-type)))
    (infer-possible-tags-from-flextype ctx member-type this-type)))


; Transsum Parsing ------------------------------------------------------------

(defconst *transsum-keywords*
  '(:pred
    :fix
    :equiv
    :case
    :count
    :kind
    :measure
    :measure-debug
    :xvar
    :no-count
    :parents
    :short
    :long
    :inline
    :layout
    :base-case-override
    :prepwork
    :post-pred-events
    :post-fix-events
    :post-events
    :enable-rules
    :verbosep))

(define parse-transsum-member
  ((ctx          "Context for error messages.")
   (x            "User-level member name.")
   (our-fixtypes "Fixtypes for the new types we're currently defining.")
   (fixtypes     "Existing fixtypes that have already been defined previously.")
   (table        "The whole flextypes database."))
  :returns (member "A flextranssum-member.")
  (b* (((unless (symbolp x))
        (er hard? ctx "invalid transsum member: ~x0" x))
       (name
        ;; Get the real type name.
        (b* ((fixtype (or (find-fixtype x our-fixtypes)
                          (find-fixtype x fixtypes)))
             ((unless fixtype)
              (er hard? ctx "not a known type for transsum member: ~x0" x)))
          (fixtype->name fixtype)))
       ((mv pred fix equiv recp)
        (get-pred/fix/equiv name our-fixtypes fixtypes))
       ((when recp)
        ;; We might eventually lift this restriction, but to do that we'd need
        ;; some way to look up what tags are in the type that we haven't
        ;; defined yet, which seems tricky.
        (er hard? ctx
            "mutually recursive transsum members aren't supported: ~x0" x))
       (tags (infer-possible-tags-from-typename ctx name table)))
    (make-flextranssum-member :name name
                              :pred pred
                              :fix fix
                              :equiv equiv
                              :tags tags
                              :recp recp)))

(define parse-transsum-members (ctx x our-fixtypes fixtypes table)
  :returns (members)
  (if (atom x)
      (if x
          (er hard? ctx
              "deftranssum members should be nil-terminated; found ~
                 final cdr ~x1.~%" ctx x)
        nil)
    (cons (parse-transsum-member ctx (car x) our-fixtypes fixtypes table)
          (parse-transsum-members ctx (cdr x) our-fixtypes fixtypes table))))

(define parse-transsum (x xvar our-fixtypes fixtypes state)
  (declare (ignorable state))
  (b* (((cons name args) x)
       ((unless (symbolp name))
        (raise "Malformed transsum: ~x0: name must be a symbol" x))
       ((mv pre-/// post-///)     (std::split-/// name args))
       ((mv kwd-alist other-args) (extract-keywords name *transsum-keywords* pre-/// nil))
       ((when (atom other-args))
        (raise "Malformed transsum ~x0: no members list." name))
       ((unless (eql (len other-args) 1))
        (raise "Malformed transsum ~x0: too many arguments." name))
       (members  (parse-transsum-members name (first other-args) our-fixtypes fixtypes (get-flextypes (w state))))
       ((unless (consp members))
        (raise "Malformed transsum ~x0: no members." name))

       (pred     (getarg! :pred  (intern-in-package-of-symbol (cat (symbol-name name) "-P") name) kwd-alist))
       (fix      (getarg! :fix   (intern-in-package-of-symbol (cat (symbol-name name) "-FIX") name) kwd-alist))
       (equiv    (getarg! :equiv (intern-in-package-of-symbol (cat (symbol-name name) "-EQUIV") name) kwd-alist))
       (case     (getarg! :case  (intern-in-package-of-symbol (cat (symbol-name name) "-CASE") name) kwd-alist))
       (kind     (getarg! :kind  (intern-in-package-of-symbol (cat (symbol-name name) "-KIND") name) kwd-alist))
       (inline   (get-deftypes-inline-opt *inline-defaults* kwd-alist))
       (count    (flextype-get-count-fn name kwd-alist))
       (xvar     (or (getarg :xvar xvar kwd-alist)
                     (car (find-symbols-named-x (getarg :measure nil kwd-alist)))
                     (intern-in-package-of-symbol "X" name)))
       (measure  (getarg! :measure `(acl2-count ,xvar) kwd-alist))
       (kwd-alist (if post-///
                      (cons (cons :///-events post-///)
                            kwd-alist)
                    kwd-alist)))
    (make-flextranssum :name name
                       :pred pred
                       :fix fix
                       :equiv equiv
                       :case case
                       :kind kind
                       :count count
                       :members members
                       :measure measure
                       :xvar xvar
                       :inline inline
                       :kwd-alist kwd-alist
                       :recp (some-flextranssum-member-recursivep members))))



; Filling in Tags -------------------------------------------------------------

(define dts-member-implies-sum-thm (x member)
  ;; (defthm vl-atomguts-p-when-vl-constint-p
  ;;   (implies (vl-constint-p x)
  ;;            (vl-atomguts-p x)))
  (b* (((flextranssum x))
       ((flextranssum-member member))
       (foo-p-when-subfoo-p (intern-in-package-of-symbol
                             (cat (symbol-name x.pred) "-WHEN-" (symbol-name member.pred))
                             x.pred)))
    `(defthm ,foo-p-when-subfoo-p
       (implies (,member.pred ,x.xvar)
                (,x.pred ,x.xvar))
       :hints(("Goal" :in-theory (enable* ,x.pred std::tag-reasoning)))
       ;; Without this we got KILLED by vl-modelement-p reasoning in the proofs
       ;; of sizing, etc.
       :rule-classes ((:rewrite :backchain-limit-lst 1)))))

(define dts-member-implies-sum-thms (x members)
  (if (atom members)
      nil
    (cons (dts-member-implies-sum-thm x (car members))
          (dts-member-implies-sum-thms x (cdr members)))))


(define dts-tag-equalities (xvar tags)
  (if (atom tags)
      nil
    (cons `(equal (tag ,xvar) ,(car tags))
          (dts-tag-equalities xvar (cdr tags)))))

(define dts-tag-inequalities (xvar tags)
  (if (atom tags)
      nil
    (cons `(not (equal (tag ,xvar) ,(car tags)))
          (dts-tag-inequalities xvar (cdr tags)))))

(define dts-by-tag-thm (x member)
  ;; (defthm vl-constint-p-by-tag-when-vl-atomguts-p
  ;;   (implies (and (equal (tag x) :vl-constint)
  ;;                 (vl-atomguts-p x))
  ;;            (vl-constint-p x)))
  (b* (((flextranssum x))
       ((flextranssum-member member))
       (subfoo-p-by-tag-when-foo-p (intern-in-package-of-symbol
                                    (cat (symbol-name member.pred) "-BY-TAG-WHEN-" (symbol-name x.pred))
                                    x.name)))
    `(;; [Jared] leaving this enabled by default because basically any sort of
      ;; transsum code is going to rely on being able to look at the tag.  We
      ;; might eventually switch to a -kind function instead of using tag to
      ;; avoid this.
      (defthm ,subfoo-p-by-tag-when-foo-p
        (implies (and (or . ,(dts-tag-equalities x.xvar member.tags))
                      (,x.pred ,x.xvar))
                 (,member.pred ,x.xvar))
        :hints(("Goal" :in-theory (enable ,x.pred)))
        ;; Like the single-member case, this rule can get very expensive.
        :rule-classes ((:rewrite :backchain-limit-lst 1)))
      (add-to-ruleset std::tag-reasoning '(,subfoo-p-by-tag-when-foo-p)))))

(define dts-by-tag-thms (x members)
  (if (atom members)
      nil
    (append (dts-by-tag-thm x (car members))
            (dts-by-tag-thms x (cdr members)))))

(define dts-when-invalid-tag-thms (x)
  ;; (defthm vl-atomicstmt-p-when-invalid-tag
  ;;   (implies (and (not (equal (tag x) :vl-nullstmt))
  ;;                 (not (equal (tag x) :vl-assignstmt))
  ;;                 (not (equal (tag x) :vl-deassignstmt))
  ;;                 (not (equal (tag x) :vl-enablestmt))
  ;;                 (not (equal (tag x) :vl-disablestmt))
  ;;                 (not (equal (tag x) :vl-eventtriggerstmt)))
  ;;            (not (vl-atomicstmt-p x))))
  (b* (((flextranssum x))
       (foo-p-when-invalid-tag (intern-in-package-of-symbol
                                (cat (symbol-name x.pred) "-WHEN-INVALID-TAG")
                                x.name))
       (all-tags (flextranssum-memberlist->tags x.members)))
    `(;; [Jared] leaving this one enabled also, because it's needed to know
      ;; that you are covering all of the possible cases.  This probably isn't
      ;; too expensive since we only target the sum predicate and have the
      ;; backchain limit.
      (defthm ,foo-p-when-invalid-tag
        (implies (and . ,(dts-tag-inequalities x.xvar all-tags))
                 (not (,x.pred ,x.xvar)))
        :hints(("Goal" :in-theory (enable* ,x.pred std::tag-reasoning)))
        :rule-classes ((:rewrite :backchain-limit-lst 0)))
      (add-to-ruleset std::tag-reasoning '(,foo-p-when-invalid-tag)))))

(define dts-fwd-thms (x)
  ;; (defthm tag-when-vl-genelement-p-forward
  ;;   (implies (vl-genelement-p x)
  ;;            (or (equal (tag x) :vl-genbase)
  ;;                (equal (tag x) :vl-genif)
  ;;                (equal (tag x) :vl-gencase)
  ;;                (equal (tag x) :vl-genloop)
  ;;                (equal (tag x) :vl-genblock)
  ;;                (equal (tag x) :vl-genarray)))
  ;;   :rule-classes :forward-chaining)
  (b* (((flextranssum x))
       (foo-p-when-invalid-tag (intern-in-package-of-symbol
                                (cat (symbol-name x.pred) "-WHEN-INVALID-TAG")
                                x.name))
       (tag-when-foo-p-forward (intern-in-package-of-symbol
                                (cat "TAG-WHEN-" (symbol-name x.pred) "-FORWARD")
                                x.name))
       (all-tags (flextranssum-memberlist->tags x.members)))
    `((defthm ,tag-when-foo-p-forward
        (implies (,x.pred ,x.xvar)
                 (or . ,(dts-tag-equalities x.xvar all-tags)))
        :hints(("Goal" :by ,foo-p-when-invalid-tag))
        :rule-classes ((:forward-chaining)))
      (add-to-ruleset std::tag-reasoning '(,tag-when-foo-p-forward)))))


(define flextranssum-pred-cases (members xvar)
  ;; Generates bindings for within the case statement, e.g.,
  ;;   (:foo        (foo-p x))
  ;;   ((:bar :baz) (baz-p x))
  (b* (((when (atom members))
        (raise "never get here"))
       ((flextranssum-member x1) (car members))
       ((when (atom (cdr members)))
        (list `(otherwise (,x1.pred ,xvar)))))
    (cons `(,x1.tags (,x1.pred ,xvar))
          (flextranssum-pred-cases (cdr members) xvar))))

(define flextranssum-predicate-def (x)
  (b* (((flextranssum x))
       (consp-when-foop (intern-in-package-of-symbol (cat "CONSP-WHEN-" (symbol-name x.pred)) x.name)))
    `(define ,x.pred (,x.xvar)
       :parents (,x.name)
       :progn t
       :short ,(str::cat "Recognizer for @(see " (xdoc::full-escape-symbol x.name) ").")
       :measure ,x.measure
       ,@(and (getarg :measure-debug nil x.kwd-alist)
              `(:measure-debug t))
       (case (tag ,x.xvar)
         ,@(flextranssum-pred-cases x.members x.xvar))
       ///
       (defthm ,consp-when-foop
         (implies (,x.pred ,x.xvar)
                  (consp ,x.xvar))
         :rule-classes :compound-recognizer)
       ,@(dts-member-implies-sum-thms x x.members)
       ,@(dts-by-tag-thms x x.members)
       ,@(dts-when-invalid-tag-thms x)
       ,@(dts-fwd-thms x))))





(define flextranssum-fix-cases (members xvar)
  ;; Generates bindings for within the case statement, e.g.,
  ;;   (:foo        (foo-fix x))
  ;;   ((:bar :baz) (baz-fix x))
  (b* (((when (atom members))
        (raise "never get here"))
       ((flextranssum-member x1) (car members))
       ((when (atom (cdr members)))
        (list `(otherwise (,x1.fix ,xvar)))))
    (cons `(,x1.tags (,x1.fix ,xvar))
          (flextranssum-fix-cases (cdr members) xvar))))

(define flextranssum-fix-def (x flagp)
  (b* (((flextranssum x)))
    `(define ,x.fix ((,x.xvar ,x.pred))
       :parents (,x.name)
       :short ,(cat "@(call " (xdoc::full-escape-symbol x.fix)
                    ") is a @(see fty::fty) fixing function.")
       :long "<p>Note that in the execution this is just an inline identity function.</p>"
       :measure ,x.measure
       ,@(and (getarg :measure-debug nil x.kwd-alist)
              `(:measure-debug t))
       ,@(and flagp `(:flag ,x.name))
       :returns (newx ,x.pred :hints(("Goal"
                                      :in-theory (enable* ,x.pred std::tag-reasoning)
                                      :expand ((,x.fix ,x.xvar)))))
       :verify-guards nil
       :progn t
       :inline t
       (mbe :logic (case (tag ,x.xvar)
                     ,@(flextranssum-fix-cases x.members x.xvar))
            :exec ,x.xvar)
       ///)))

(define flextranssum-fix-postevents (x)
  ;; (defthm tag-of-vl-genelement-fix-forward
  ;;   (or (equal (tag (vl-genelement-fix x)) :vl-genbase)
  ;;       (equal (tag (vl-genelement-fix x)) :vl-genif)
  ;;       ...)
  ;;   :rule-classes ((:forward-chaining :trigger-terms ((tag (vl-genelement-fix x))))))
  (b* (((flextranssum x))
       (tag-when-foo-p-forward (intern-in-package-of-symbol
                                (cat "TAG-WHEN-" (symbol-name x.pred) "-FORWARD")
                                x.name))
       (tag-of-foo-fix-forward (intern-in-package-of-symbol
                                (cat "TAG-OF-" (symbol-name x.fix) "-FORWARD")
                                x.name))
       (all-tags (flextranssum-memberlist->tags x.members)))
    `((defthm ,tag-of-foo-fix-forward
        (or ,@(dts-tag-equalities `(,x.fix ,x.xvar) all-tags))
        :rule-classes ((:forward-chaining :trigger-terms ((tag (,x.fix ,x.xvar)))))
        :hints(("Goal"
                :in-theory (theory 'minimal-theory)
                :use ((:instance ,tag-when-foo-p-forward
                       (,x.xvar (,x.fix ,x.xvar)))))))
      (add-to-ruleset std::tag-reasoning '(,tag-of-foo-fix-forward)))))


(define flextranssum-count (x types) ;; bozo wtf are types?
  (declare (ignorable types))
  (b* (((flextranssum x))
       ((unless x.count) nil))
    `((define ,x.count ((,x.xvar ,x.pred))
        :returns (count natp :rule-classes :type-prescription)
        :measure (let ((,x.xvar (,x.fix ,x.xvar)))
                   ,x.measure)
       ,@(and (getarg :measure-debug nil x.kwd-alist)
              `(:measure-debug t))
        :verify-guards nil
        :progn t
        ;; bozo
        (bozo-implement-flextranssum-count ,x.name)))))

(define flextranssum-count-post-events (x types)
  (declare (ignorable types))
  (b* (((flextranssum x))
       ((unless x.count) nil))
    ;; bozo 
    nil))

(define flextranssum-fns (x)
  (b* (((flextranssum x) x))
    (list x.pred
          x.fix)))

(define flextranssum-fix-when-pred-thm (x flagp)
  (b* (((flextranssum x))
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

(defun flextranssum-members-collect-fix-pred-pairs (members)
  (b* (((when (atom members))
        nil)
       ((flextranssum-member x1) (car members)))
    (cons (cons x1.fix x1.pred)
          (flextranssum-members-collect-fix-pred-pairs (cdr members)))))

(defun flextranssum-collect-fix/pred-pairs (x)
  (flextranssum-members-collect-fix-pred-pairs (flextranssum->members x)))
