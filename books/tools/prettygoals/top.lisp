; Pretty Goals for ACL2
; Copyright (C) 2016 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "PRETTYGOALS")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/strings/defs-program" :dir :system)
(include-book "defsort/defsort" :dir :system)
(include-book "defsort/duplicated-members" :dir :system)
(include-book "misc/total-order" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "tools/include-raw" :dir :system)
(program)

(defsection prettygoals
  :short "Experimental tool for displaying proof goals in a prettier way."

  :long "<p>This tool changes how ACL2 prints proof goals to be ``prettier,''
 so that you can more quickly read them and understand why ACL2 is stuck.</p>

 <p>Note: this is experimental and may change drastically in the future.  It is
 also an unprincipled tool that may screw up your goals.  Please use it with
 caution.  Send any feedback on it to Jared Davis.</p>


 <h3>Usage</h3>

 <p>Either manually or via your @(see acl2-customization) file, do:</p>

 @({
      (include-book \"tools/prettygoals/top\" :dir :system)
 })

 <p>Subsequent proof goals will now be made prettier.  You can also turn
 this on an off:</p>

 @({
      (include-book \"tools/prettygoals/top\" :dir :system)

      (defthm foo ...)          ;; proof goals will be pretty

      (set-pretty-goals nil)
      (defthm bar ...)          ;; proof goals will be ugly

      (set-pretty-goals t)
      (defthm baz ...)          ;; proof goals will be pretty
 })


 <h3>Effects</h3>

 <h4>Readable B* Binders for Structure Accessors</h4>

 <p>Background: macros like @(see std::defaggregate) and @(see fty::defprod)
 introduce fancy @(see b*) binders that let you refer to accessors using a
 concise, dot-style notation like @('mystudent.name') in place of the more
 verbose @('(student->name mystudent)').</p>

 <p>ACL2's ``untranslate'' mechanisms don't know about or preserve this
 syntax, so when you give it a goal like this:</p>

 @({
      (defthm xx
        (b* (((student x))
             ((airplane y)))
          (concl (list x.name x.age x.major y.wings y.wheels))))
 })

 <p>It prints out all the accessors in full, like this:</p>

 @({
      *** Key checkpoint at the top level: ***

      Goal''
      (CONCL (LIST (STUDENT->NAME X)
                   (STUDENT->AGE X)
                   (STUDENT->MAJOR X)
                   (AIRPLANE->WINGS Y)
                   (AIRPLANE->WHEELS Y)))
 })

 <p>Prettygoals reintroduces the @(see b*) binders so you instead see:</p>

 @({
      *** Key checkpoint at the top level: ***

      (B* (((STUDENT X)) ((AIRPLANE Y)))
          (CONCL (LIST X.NAME X.AGE X.MAJOR Y.WINGS Y.WHEELS)))
 })


 <h4>Type Error Warnings</h4>

 <p>Occasionally you may submit a theorem with a typo, for instance, notice how
 we are accessing both @('(student->... x)') and @('(airplane->... x)') in the
 following goal:</p>

 @({
      (defthm yy
        (concl (list (student->name x)
                     (student->age x)
                     (airplane->wings x)
                     (airplane->wheels y))))
 })

 <p>When pretty goals are enabled and you try to access the same structure in
 different ways, we may be able to notice and add a warning, e.g.,:</p>

 @({
      *** Key checkpoint at the top level: ***

      Goal
      (B* (((STUDENT X))
           ((AIRPLANE X))
           ((AIRPLANE Y)))
          \"WARNING: type confusion: ((X STUDENT X) (X AIRPLANE X))\"
          (CONCL (LIST X.NAME X.AGE X.WINGS Y.WHEELS))) 
 })


 <h4>Simpler Hyps First</h4>



 <h4>Original Motivation</h4>

 <p>I was working on a proof when I encountered the following subgoal:</p>

 @({
      (IMPLIES (AND (SIGNED-BYTE-P (BIGBOUND->SIZE BOUND1)
                                   (BIGINT->VAL (BIGEVAL ARG1 ENV)))
                    (NOT (BIGBOUND->MIN BOUND1))
                    (<= (BIGINT->VAL (BIGEVAL ARG1 ENV))
                        (BIGBOUND->MAX BOUND1))
                    (SIGNED-BYTE-P (BIGBOUND->SIZE BOUND2)
                                   (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                    (<= (BIGBOUND->MIN BOUND2)
                        (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                    (NOT (BIGBOUND->MAX BOUND2))
                    (BIGBOUND->MAX BOUND1)
                    (< 0 (BIGBOUND->MAX BOUND1))
                    (BIGBOUND->MIN BOUND2)
                    (<= 0 (BIGBOUND->MIN BOUND2))
                    (<= (+ 1 (BIGBOUND->MAX BOUND1))
                        (BIGBOUND->SIZE BOUND2)))
               (<= (LOGHEAD (BIGINT->VAL (BIGEVAL ARG1 ENV))
                            (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                   (+ -1 (ASH 1 (BIGBOUND->SIZE BOUND1)))))
 })

 <p>This goal is really messy and annoying.  I at least wanted ACL2 to replace
 things like @('(bigbound->min bound1)') with @('bound1.min').  After doing
 that, the goal was still a mess because simple things like @('bound1.max')
 were jammed between complicated goals, which suggested reordering the
 hypotheses based on how complex they are.  The above goal now prints instead
 as follows, which I think is a lot more pleasant.</p>

 @({
      (B* (((BIGBOUND BOUND1))
           ((BIGBOUND BOUND2)))
        (IMPLIES (AND BOUND1.MAX BOUND2.MIN (NOT BOUND1.MIN)
                      (NOT BOUND2.MAX)
                      (< 0 BOUND1.MAX)
                      (<= 0 BOUND2.MIN)
                      (<= (+ 1 BOUND1.MAX) BOUND2.SIZE)
                      (<= BOUND2.MIN
                          (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                      (<= (BIGINT->VAL (BIGEVAL ARG1 ENV))
                          BOUND1.MAX)
                      (SIGNED-BYTE-P BOUND1.SIZE
                                     (BIGINT->VAL (BIGEVAL ARG1 ENV)))
                      (SIGNED-BYTE-P BOUND2.SIZE
                                     (BIGINT->VAL (BIGEVAL ARG2 ENV))))
                 (<= (LOGHEAD (BIGINT->VAL (BIGEVAL ARG1 ENV))
                              (BIGINT->VAL (BIGEVAL ARG2 ENV)))
                     (+ -1 (ASH 1 BOUND1.SIZE)))))
 })

 <p>There are probably a lot of other ways to improve this.  For instance it
 might be nice to put hyps about related variables close together, or otherwise
 try to group up the hyps into a sensible order.  We could also look for
 potential typos in variable names, and so on...</p>")

(defines collect-simple-accessor-calls
  (define collect-simple-accessor-calls (x)
    ;; X should be an already untranslated term.  We want to look for calls of
    ;; things that look like accessors within X, such as (foo->bar var), where
    ;; var is a simple variable.  We return a list of all such terms we have
    ;; found.
    (cond ((or (atom x)
               (eq (car x) 'quote))
           nil)
          ((symbolp (first x))
           ;; Looks like a function call.
           (if (and (consp (cdr x))
                    (not (cddr x))
                    (str::substrp "->" (symbol-name (first x)))
                    (acl2::legal-variablep (second x)))
               ;; Found (foo->bar var), so collect that.
               (list x)
             (collect-simple-accessor-calls-list (cdr x))))
          (t
           ;; Not sure what kind of term this is.  It's probably safest (but
           ;; possibly least useful) to not look at it.  If we find cases
           ;; where (foo->bar var) aren't being matched, we might perhaps
           ;; change this to append all simple calls from the car/cdr of X
           ;; and see if that works.  If you edit this, also update
           ;; apply-simple-accessors-subst.
           nil)))
  (define collect-simple-accessor-calls-list (x)
    (if (atom x)
        nil
      (append (collect-simple-accessor-calls (car x))
              (collect-simple-accessor-calls-list (cdr x))))))

(defines apply-simple-accessors-subst
  (define apply-simple-accessors-subst (x (subst alistp))
    ;; This should agree with collect-simple-accessor-calls
    (cond ((or (atom x)
               (eq (car x) 'quote))
           x)
          ((symbolp (first x))
           ;; Looks like a function call.
           (if (and (consp (cdr x))
                    (not (cddr x))
                    (str::substrp "->" (symbol-name (first x)))
                    (acl2::legal-variablep (second x)))
               (b* ((replacement (cdr (assoc-equal x subst))))
                 (or replacement
                     (raise "No replacement for ~x0?" x)))
             (cons (car x)
                   (apply-simple-accessors-subst-list (cdr x) subst))))
          (t
           x)))
  (define apply-simple-accessors-subst-list (x (subst alistp))
    (if (atom x)
        x
      (cons (apply-simple-accessors-subst (car x) subst)
            (apply-simple-accessors-subst-list (cdr x) subst)))))

(define deconstruct-simple-accessor-calls (calls)
  ;; Calls is a list of (foo->bar var) calls.
  ;; Turn it into:
  ;;    A binders alist, that binds: var            to  (foo var)
  ;;    A replace alist, that binds: (foo->bar var) to var.bar
  ;; Returns (mv binders-alist replace-alist)
  (b* (((when (atom calls))
        (mv nil nil))
       ((mv binders-alist replace-alist)
        (deconstruct-simple-accessor-calls (cdr calls)))
       ((list foo->bar var) (car calls))
       (str (symbol-name foo->bar))
       (idx (str::strpos "->" str))
       (foo (intern-in-package-of-symbol (subseq str 0 idx) foo->bar))
       (var.bar (intern-in-package-of-symbol
                 (str::cat (symbol-name var) "." (subseq str (+ 2 idx) nil))
                 foo->bar))
       (bind1 (cons var (list foo var)))
       (repl1 (cons (car calls) var.bar)))
    (mv (cons bind1 binders-alist)
        (cons repl1 replace-alist))))

#||
Example:
(deconstruct-simple-accessor-calls '((student->name x) (student->age x) (student->name y)))
 -->
(((X STUDENT X)
  (X STUDENT X)
  (Y STUDENT Y))
 (((STUDENT->NAME X) . X.NAME)
  ((STUDENT->AGE X) . X.AGE)
  ((STUDENT->NAME Y) . Y.NAME)))
||#

(define my-count-fncalls (x)
  (cond ((or (atom x)
             (eq (car x) 'quote))
         0)
        ((eq (car x) 'not)
         (my-count-fncalls (cdr x)))
        ((symbolp (car x))
         (+ 1 (my-count-fncalls (cdr x))))
        (t
         (+ (my-count-fncalls (car x))
            (my-count-fncalls (cdr x))))))

(define my-count-vars (x)
  (cond ((atom x)
         1)
        ((eq (car x) 'quote)
         0)
        ((symbolp (car x))
         (my-count-vars (cdr x)))
        (t
         (+ (my-count-vars (car x))
            (my-count-vars (cdr x))))))

(define my-term< (x y)
  (b* (((when (atom x))
        (if (atom y) (acl2::<< x y) t))
       ((when (atom y)) nil)
       ((when (eq (car x) 'quote))
        (if (eq (car y) 'quote)
            (acl2::<< x y)
          t))
       ((when (eq (car y) 'quote)) nil)
       (xcalls (my-count-fncalls x))
       (ycalls (my-count-fncalls y))
       ((when (< xcalls ycalls)) t)
       ((when (< ycalls xcalls)) nil)
       (xvars (my-count-vars x))
       (yvars (my-count-vars y))
       ((when (< xvars yvars)) t)
       ((when (< yvars xvars)) t))
    (acl2::<< x y)))

(acl2::defsort my-term-sort :compare< my-term<)

(define reorder-toplevel-hyps (x)
  ;; X should be an already untranslated term.  If it happens to be of
  ;; the typical form (implies (and hyp1 ... hypN) concl), then we
  ;; rewrite it by mergesorting the hyps.
  (if (and (consp x)
           (eq (first x) 'implies)
           (consp (cdr x))
           (consp (cddr x))
           (not (cdddr x))
           (consp (second x))
           (equal (car (second x)) 'and))
      (list 'implies
            (cons 'and (my-term-sort (cdr (second x))))
            (third x))
    x))

(define keep-from-alist (keys alist)
  (cond ((atom alist)
         nil)
        ((member (caar alist) keys)
         (cons (car alist)
               (keep-from-alist keys (cdr alist))))
        (t
         (keep-from-alist keys (cdr alist)))))

(define type-check-messages (binders-alist)
  ;; The binders alist binds var to (foo var), where we have found (foo->bar
  ;; var) somewhere in the goal.  So, if after removing duplicates from the
  ;; whole alist, there are any duplicate occurrences of any variable, then
  ;; this seems like a type error because the same variable is being bound to
  ;; different structures.
  (b* ((vars (strip-cars binders-alist))
       (dupes (duplicated-members vars))
       ((unless dupes)
        nil))
    (list (str::cat
    "-----------------------------------------------------------------
     WARNING: type confusion -- look above at "
                    (str::join (str::symbol-list-names dupes) ", ")
                    "!  Typo in theorem?
  -----------------------------------------------------------------"))))

(define b*ify-simple-accessors (x)
  ;; X should be an already untranslated term.  We try to rewrite it by
  ;; replacing (foo->bar var) calls into b* binders.
  (b* ((calls (collect-simple-accessor-calls x))
       ((unless calls)
        ;; No accessors.  Previously I just returned X because there was
        ;; nothing to do.  But we can at least order the hyps nicely.
        (reorder-toplevel-hyps x))
       (calls (remove-duplicates-equal calls))
       ((mv binders-alist replace-alist) (deconstruct-simple-accessor-calls calls))
       (binders-alist (remove-duplicates-equal binders-alist))
       (rewritten-x   (apply-simple-accessors-subst x replace-alist)))
    `(b* ,(pairlis$ (strip-cdrs binders-alist) nil)
       ,@(type-check-messages binders-alist)
       ,(reorder-toplevel-hyps rewritten-x))))


(defstub acl2::post-untranslate-hook (x) t)


(defttag :prettygoals)
;; (depends-on "prettygoals-raw.lsp")
(acl2::include-raw "prettygoals-raw.lsp")


(defmacro set-pretty-goals (enabled-p)
  (if enabled-p
      `(progn
         (defttag :prettygoals)
         (defattach (acl2::post-untranslate-hook b*ify-simple-accessors)
           :skip-checks t))
    `(defattach acl2::post-untranslate-hook identity)))

(set-pretty-goals t)


#||

(logic)

(include-book
 "std/util/defaggregate" :dir :system)

(std::defaggregate student
  ((name stringp)
   (age natp)
   (major symbolp)))

(std::defaggregate airplane
  ((wings natp)
   (wheels natp)))

(defstub concl (x) t)


;; Example theorem:

(defthm xx
  (b* (((student x))
       ((airplane y)))
    (concl (list x.name x.age x.major y.wings y.wheels))))

; With (set-pretty-goals nil):

;; *** Key checkpoint at the top level: ***
;;
;; Goal''
;; (CONCL (LIST (STUDENT->NAME X)
;;              (STUDENT->AGE X)
;;              (STUDENT->MAJOR X)
;;              (AIRPLANE->WINGS Y)
;;              (AIRPLANE->WHEELS Y)))

; With (set-pretty-goals t):

;; *** Key checkpoint at the top level: ***
;;
;; (B* (((STUDENT X)) ((AIRPLANE Y)))
;;     (CONCL (LIST X.NAME X.AGE X.MAJOR Y.WINGS Y.WHEELS)))



;; Example theorem 2 -- this one looks like it has a "type error" because we're
;; calling student->... on X and also airplane->wings on x.

(defthm yy
  (concl (list (student->name x)
               (student->age x)
               (airplane->wings x)
               (airplane->wheels y))))

||#
