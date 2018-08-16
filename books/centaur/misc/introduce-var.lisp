; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; introduce-var.lisp
;
; Original authors: Jared Davis <jared@centtech.com>
;                   Anna Slobadova <anna@centtech.com>
;                   Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "clause-processors/generalize" :dir :system)
(include-book "centaur/vl/util/namedb" :dir :system)
(include-book "beta-reduce-full")

; We introduce the INTRODUCE-VARS clause processor.  To use this clause
; processor you should just do this:
;
;   :hints(("Goal" ... your hints ...)
;          (introduce-vars))
;
; Whenever this clause processor runs, it examines your goal for any
; occurrences of (INTRODUCE-VAR 'NAME TERM), and replaces them with fresh
; variables that are based on NAME.
;
; The function INTRODUCE-VAR is just an identity that returns TERM and ignores
; NAME.  Typically you will want to write rewrite rules that produce
; INTRODUCE-VAR forms anywhere that you don't want to see an offensive term.
;
; For instance, a rewrite rule like:
;
;   (implies (and (true-listp x)
;                 (true-listp y))
;            (equal (equal x y)
;                   (let ((n (look-for-mismatching-elt x y)))
;                     (equal (nth n x) (nth n y)))))
;
; Where look-for-mismatching-elt presumably goes through the lists to find
; the first index where they disagree.  The problem with a rule like this is
; that when it fires, you'll end up with large, yucky terms like
;
;        (look-for-mismatching-elt (cons ...) (foo ...))
;
; Where you really just want a new variable, say "idx".  The fix for this rule
; is just:
;
;   (implies (and (true-listp x)
;                 (true-listp y))
;            (equal (equal x y)
;                   (let ((n (introduce-var 'idx (hide (look-for-mismatching-elt x y)))))
;                     (equal (nth n x) (nth n y)))))
;
; The hide is optional but probably a good idea.  After this rule has fired, the
; INTRODUCE-VARS clause processor will notice the new, even uglier term:
;
;      (introduce-var 'idx
;       (hide
;        (look-for-mismatching-elt (cons ...) (foo ...))))
;
; And will replace it with something like IDX, IDX_1, etc., as appropriate to
; avoid name clashes.



(local
 (defthm beta-reduce-full-correct-for-gen-eval
   (implies (pseudo-termp x)
            (equal (gen-eval (beta-reduce-full x) a)
                   (gen-eval x a)))
   :hints (("goal" :use ((:functional-instance
                          beta-reduce-full-correct
                          (beta-eval gen-eval)
                          (beta-eval-list gen-eval-lst)))
            :in-theory (enable gen-eval-of-fncall-args)))))

(local
 (defthm beta-reduce-full-list-correct-for-gen-eval
   (implies (pseudo-term-listp x)
            (equal (gen-eval-lst (beta-reduce-full-list x) a)
                   (gen-eval-lst x a)))
   :hints (("goal" :use ((:functional-instance
                          beta-reduce-full-list-correct
                          (beta-eval gen-eval)
                          (beta-eval-list gen-eval-lst)))
            :in-theory (enable gen-eval-of-fncall-args)))))



(defund introduce-var (name term)
  (declare (xargs :guard t)
           (ignore name))
  term)


;; Note: We've seen problems where sometimes two apparently-identical terms get
;; generalized to two different variables because they differ in something like
;; the order of lambda formals, e.g. one is
;; (hide ((lambda (a b) (list a b)) aa bb))
;; and the other is
;; (hide ((lambda (b a) (list a b)) bb aa)).
;; So we normalize these (and also differences in bound variable names)
;; by fully beta-reducing introduce-var terms.
(mutual-recursion
 (defun beta-reduce-introduce-vars (x)
   (declare (xargs :guard (pseudo-termp x)))
   (b* (((when (or (variablep x) (fquotep x))) x)
        (fn (ffn-symb x))
        ((when (eq fn 'introduce-var))
         (beta-reduce-full x)))
     (cons fn (beta-reduce-introduce-vars-list (fargs x)))))
 (defun beta-reduce-introduce-vars-list (x)
   (declare (xargs :guard (pseudo-term-listp x)))
   (if (atom x)
       nil
     (cons (beta-reduce-introduce-vars (car x))
           (beta-reduce-introduce-vars-list (cdr x))))))

(defthm len-of-beta-reduce-introduce-vars-list
  (equal (len (beta-reduce-introduce-vars-list x))
         (len x)))

(defthm-beta-reduce-flg
  (defthm beta-reduce-introduce-vars-correct
    (implies (pseudo-termp x)
             (equal (gen-eval (beta-reduce-introduce-vars x) a)
                    (gen-eval x a)))
    :hints ('(:in-theory (enable gen-eval-of-fncall-args)))
    :flag term)
  (defthm beta-reduce-introduce-vars-list-correct
    (implies (pseudo-term-listp x)
             (equal (gen-eval-lst (beta-reduce-introduce-vars-list x) a)
                    (gen-eval-lst x a)))
    :flag list))

(defthm-beta-reduce-flg
  (defthm pseudo-termp-beta-reduce-introduce-vars
    (implies (pseudo-termp x)
             (pseudo-termp (beta-reduce-introduce-vars x)))
    :flag term)
  (defthm pseudo-term-listp-beta-reduce-introduce-vars-list
    (implies (pseudo-term-listp x)
             (pseudo-term-listp (beta-reduce-introduce-vars-list x)))
    :flag list))

(mutual-recursion

; These scanning functions look for occurrences of (INTRODUCE-VAR 'VAR TERM)
; and construct an alist with (TERM . VAR) entries.  In practice we expect that
; VAR should generally be a string or symbol, but we allow it to be any object.

 (defun scan-term-for-introduce-var (x)
   (declare (xargs :guard t))
   (cond ((atom x) nil)
         ((quotep x) nil)
         (t (case-match x
              (('introduce-var ('quote v . &) . &)
               (list (cons x v)))
              (& (scan-termlist-for-introduce-var (cdr x)))))))
 (defun scan-termlist-for-introduce-var (x)
   (declare (xargs :guard t))
   (if (atom x)
       nil
     (append (scan-term-for-introduce-var (car x))
             (scan-termlist-for-introduce-var (cdr x))))))


; We need to be careful to avoid name clashes.  There can be two kinds of name
; clashes:
;
; (1) There might be separate occurrences of INTRODUCE-VAR that use the same VAR,
; for instance our goal might be:
;
;    (let ((a (introduce-var 'key (hide (find-key x y))))
;          (b (introduce-var 'key (hide (find-key y x)))))
;      (conclusion a b))
;
; Here we need to be sure to introduce separate keys, e.g., KEY and KEY_2.
;
; (2) The variable we want to introduce might already be used somewhere else in
; the goal, e.g.,
;
;    (let ((a (introduce-var 'key (hide (find-key x y)))))
;      (implies (member key x)
;               ...))
;
; In which case we must not try to introduce generalize the term to just KEY.
; We use a VL name database to generate fresh keys.  This is slightly
; complicated because name databases only deal with strings.

(defund names-for-introduce-var-to-avoid (current-pkg var-lst)
  "Returns a string list."
  (declare (xargs :guard (and (stringp current-pkg)
                              (not (equal current-pkg "")))))

; VAR-LST should initially be the output of TERM-VARS-LIST on the clause.
; I.e., it's a list of all the variables we need to avoid due to #2 above.
; We're always going to generate symbols in the current-package, so we only
; need to avoid symbols in var-lst that are in the current package.

  (cond ((atom var-lst)
         nil)
        ((and (symbolp (car var-lst))
              (equal (car var-lst) (intern$ (symbol-name (car var-lst)) current-pkg)))
         ;; It's a symbol that's effectively in the current package, so we need
         ;; to avoid it.
         (cons (symbol-name (car var-lst))
               (names-for-introduce-var-to-avoid current-pkg (cdr var-lst))))
        (t
         (names-for-introduce-var-to-avoid current-pkg (cdr var-lst)))))

(local (defthm string-listp-of-names-for-introduce-var-to-avoid
         (string-listp (names-for-introduce-var-to-avoid current-pkg var-lst))
         :hints(("Goal" :in-theory (enable names-for-introduce-var-to-avoid)))))


(defund uniquify-introduce-var-alist (current-pkg alist namedb)
  "Returns (MV ALIST' NAMEDB')"
  (declare (xargs :guard (and (stringp current-pkg)
                              (not (equal current-pkg ""))
                              (vl::vl-namedb-p namedb))))

; ALIST is the alist of (TERM . VAR) entries that we found, where each TERM
; should be replaced by VAR.  But the VARs in ALIST are not necessarily unique.
; Make a new alist where each term is bound to a new, unique symbol in the
; current package.

  (b* (((when (atom alist))
        (mv alist namedb))

       ((when (atom (car alist)))
        ;; Bad alist convention
        (uniquify-introduce-var-alist current-pkg (cdr alist) namedb))

       ((cons term var) (car alist))
       (preferred-varname (cond ((symbolp var) (symbol-name var))
                                ((stringp var) var)
                                (t             "VAR")))
       ((mv fresh-name namedb)
        (vl::vl-namedb-plain-name-quiet preferred-varname namedb))
       (fresh-sym (intern$ fresh-name current-pkg))
       ((mv rest namedb)
        (uniquify-introduce-var-alist current-pkg (cdr alist) namedb)))
    (mv (cons (cons term fresh-sym) rest)
        namedb)))

(local (defthm vl-namedb-p-of-uniquify-introduce-var-alist
         (implies (vl::vl-namedb-p namedb)
                  (vl::vl-namedb-p (mv-nth 1 (uniquify-introduce-var-alist current-pkg alist namedb))))
         :hints(("Goal" :in-theory (enable uniquify-introduce-var-alist)))))


(defund scan-for-introduce-var (current-pkg clause)
  (declare (xargs :guard (and (stringp current-pkg)
                              (not (equal current-pkg ""))
                              (pseudo-term-listp clause))))
  (b* ((initial-alist (scan-termlist-for-introduce-var clause))
       ((unless initial-alist)
        ;; Optimization: avoid looking at the term vars if there's nothing to do
        nil)
       (clause-vars (simple-term-vars-lst clause))
       (avoid-names (names-for-introduce-var-to-avoid current-pkg clause-vars))
       (namedb      (vl::vl-starting-namedb avoid-names))
       ((mv fresh-alist namedb)
        (uniquify-introduce-var-alist current-pkg initial-alist namedb)))
    (vl::vl-free-namedb namedb)
    fresh-alist))

(defun introduce-vars-cp (clause pkg)
  (declare (xargs :guard (pseudo-term-listp clause)))
  (let* ((clause (beta-reduce-introduce-vars-list clause))
         (al (mbe :logic (scan-for-introduce-var pkg clause)
                  :exec (if (and (stringp pkg)
                                 (not (equal pkg "")))
                            (scan-for-introduce-var pkg clause)
                          (ec-call (scan-for-introduce-var pkg clause))))))
    (ec-call (simple-generalize-cp clause al))))

(defthm eval-disjoin-of-beta-reduce-introduce-vars-list
  (implies (pseudo-term-listp clause)
           (iff (gen-eval (disjoin (beta-reduce-introduce-vars-list clause)) a)
                (gen-eval (disjoin clause) a)))
  :hints (("goal" :induct (len clause)
           :in-theory (enable gen-eval-disjoin-when-consp))))

(defthm introduce-vars-cp-correct
  (implies (and (pseudo-term-listp clause)
                (alistp a)
                (gen-eval (conjoin-clauses (introduce-vars-cp clause pkg))
                          (alist-for-simple-generalize-cp
                           (beta-reduce-introduce-vars-list clause)
                           (scan-for-introduce-var
                            pkg (beta-reduce-introduce-vars-list clause))
                           a)))
           (gen-eval (disjoin clause) a))
  :hints (("goal" :use ((:instance simple-generalize-cp-correct
                         (clause (beta-reduce-introduce-vars-list clause))
                         (env a)
                         (alist (scan-for-introduce-var
                                 pkg (beta-reduce-introduce-vars-list clause)))))
           :in-theory (disable simple-generalize-cp
                               alist-for-simple-generalize-cp)))
  :rule-classes :clause-processor)

(defmacro introduce-vars ()
  '(let* ((pkg (current-package state))
          (al (scan-for-introduce-var pkg clause)))
     (and al ;; this just tells us whether we have any before we go ahead and
          ;; run the clause-processor
          `(:computed-hint-replacement
            t
            :clause-processor (introduce-vars-cp clause ',pkg)))))



#||

(defstub foo () nil)
(defstub bar () nil)
(defstub baz () nil)

(set-gag-mode nil)

(thm
 ;; Good, we properly get (equal key FOO) and (equal key FOO_1) instead
 ;; of thinking that KEY is equal to both.
 (implies (and (equal key (introduce-var 'foo (foo)))
               (equal key (introduce-var 'foo (bar))))
          (baz))
 :hints((introduce-vars)))

(thm
 ;; Good, we get FOO and KEY_1 instead of FOO and KEY.
 (implies (and (equal key (introduce-var 'foo (foo)))
               (equal key (introduce-var 'key (bar))))
          (equal key (baz)))
 :hints((introduce-vars)))


(thm
 ;; Nice, we get ACL2-package variables even though we're using VL-package
 ;; names in the introduce-var calls
 (implies (and (equal key (introduce-var 'vl::foo (foo)))
               (equal key (introduce-var 'vl::key (bar))))
          (equal key (baz)))
 :hints((introduce-vars)))


(thm
 ;; Good enough, strings and other keys work, although not in a great way.
 (implies (and (equal key (introduce-var 1 (foo)))
               (equal key (introduce-var "bar" (bar))))
          (equal key (baz)))
 :hints((introduce-vars)))

||#




; TRICK.
;
; It may be pretty easy to fiddle with the introduce-var that you've introduced
; before the clause processor gets to it.  Here's a funny example that rewrites
; (ST-GET KEY (INTRODUCE-VAR 'FOO ...)) to (INTRODUCE-VAR FOO[KEY] ...).  This
; could be pretty nice, but it might be a little bit risky because you'll lose
; information (e.g., types) about what ST-GET returns, but you could maybe fix
; this up with an appropriate fixing function around the new introduce-var.  It
; also might be somehow more likely when using this trick that you'd
; accidentally abstract some term into two different variables?

(local
 (progn

   (defstub run (n program st)
     ;; Suppose this is the RUN function for a processor model
     st)

   (defstub st-get (key rec)
     ;; Suppose this is a GET function for a field of the model
     t)

   (defun make-var-for-st-get-of-introduce-var (key var mfc state)
     (declare (xargs :stobjs state :mode :program)
              (ignore mfc))
     (and (quotep key)
          (quotep var)
          (let* ((var (cadr var))
                 (key (cadr key))
                 (varname (cond ((symbolp var) (symbol-name var))
                                ((stringp var) var)
                                (t             "VAR")))
                 (keyname (cond ((symbolp key) (symbol-name key))
                                ((stringp key) key)
                                ((natp key)    (str::natstr key))
                                (t             "KEY")))
                 (name (intern-in-package-of-symbol
                        (str::cat varname "[" keyname "]")
                        (pkg-witness (current-package state)))))
            `((newvar . ',name)))))

   (defthm move-introduce-vars-over-st-get
     (implies (bind-free (make-var-for-st-get-of-introduce-var key var mfc state)
                         (newvar))
              (equal (st-get key (introduce-var var st))
                     (introduce-var newvar (hide (st-get key st)))))
     :hints(("Goal"
             :in-theory (enable introduce-var)
             :expand ((:free (x) (hide x))))))

   (defund prop (x) (declare (ignore x)) t)
   (in-theory (disable (:type-prescription prop)))
   (in-theory (disable (:executable-counterpart tau-system)))

   (defthm example
     ;; Look at the proof here and you'll see that we introduce ST[FOO],
     ;; which is pretty neat.
     (prop (st-get :foo (introduce-var 'st (hide (run 11 prog st)))))
     :hints((and stable-under-simplificationp
                 (introduce-vars))
            (and stable-under-simplificationp
                 '(:in-theory (enable prop)))))))
