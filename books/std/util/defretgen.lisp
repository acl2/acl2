; Standard Utilities Library
; Copyright (C) 2019 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "STD")

(include-book "defret-mutual-generate")


(program)
(defun function-deps (fn wrld)
  (b* ((body (getpropc fn 'acl2::unnormalized-body nil wrld)))
    (acl2::all-fnnames body)))

(defun function-deps-lst (fns wrld acc)
  (if (atom fns)
      acc
    (b* ((body (getpropc (car fns) 'acl2::unnormalized-body nil wrld)))
      (function-deps-lst (cdr fns) wrld (acl2::all-fnnames1 nil body acc)))))


;; Deps is a list of (proper) function names, which could be the name-fn of of
;; some of our functions.  Elem-map maps the name-fn of each function we're
;; concerned with to its corresponding :function or :mutrec element.  We return
;; the set of elements corresponding to the deps.
(defun drg-map-function-deps (deps elem-map)
  (b* (((when (atom deps)) nil)
       (look (assoc-eq (car deps) elem-map))
       ((unless look) (drg-map-function-deps (cdr deps) elem-map)))
    (add-to-set-equal (cdr look)
                      (drg-map-function-deps (cdr deps) elem-map))))
       
    

(defun drg-function-deps (guts elem-map wrld)
  (drg-map-function-deps
   (function-deps (defguts->name-fn guts) wrld)
   elem-map))

(define defgutslist->name-fns (gutslist)
  (if (atom gutslist)
      nil
    (cons (defguts->name-fn (car gutslist))
          (defgutslist->name-fns (cdr gutslist)))))

(defun drg-mutrec-deps (guts elem-map wrld)
  (drg-map-function-deps
   (function-deps-lst (defgutslist->name-fns
                        (defines-guts->gutslist guts))
                      wrld nil)
   elem-map))


(defun drg-function-guts? (name wrld)
  (cdr (assoc-eq name (get-define-guts-alist wrld))))

(defun drg-mutrec-guts? (name wrld)
  (cdr (assoc-eq name (get-defines-alist wrld))))

(defun drg-function-guts (name wrld)
  (b* ((guts (drg-function-guts? name wrld))
       ((unless guts)
        (er hard? 'defretgen "Error: function must be introduced with ~x0, but ~x1 is not"
            'define name)))
    guts))

(defun drg-mutrec-guts (name wrld)
  (b* ((guts (drg-mutrec-guts? name wrld))
       ((unless guts)
        (er hard? 'defretgen "Error: mutrec must be introduced with ~x0, but ~x1 is not"
            'defines name)))
    guts))

;; Each element is one of (:function name) where name is the name of a DEFINEd
;; function -- but not necessarily the name-fn, or (:mutrec name) where name is
;; the name of the DEFINES mutual recursion.  We map the name-fns of each of
;; the functions to the element.
(defun drg-function->elem-map (elems wrld)
  (b* (((when (atom elems)) nil)
       (x (car elems)))
    (case-match x
      ((':function name)
       (b* ((guts (drg-function-guts name wrld)))
         (cons (cons (defguts->name-fn guts) x)
               (drg-function->elem-map (cdr elems) wrld))))
      ((':mutrec name)
       (b* ((guts (drg-mutrec-guts name wrld))
            (gutslist (defines-guts->gutslist guts)))
         (append (pairlis$ (defgutslist->name-fns gutslist)
                           (make-list (len gutslist) :initial-element x))
                 (drg-function->elem-map (cdr elems) wrld))))
      (& (er hard? 'defretgen "Bad element: ~x0" x)))))


(defun drg-dependency-graph-aux (elems elem-map wrld)
  ;; Returns a dependency graph that maps elems to lists of elems on which they
  ;; depend.
  (b* (((when (atom elems)) nil)
       (x (car elems)))
    (case-match x
      ((':function name)
       (b* ((guts (drg-function-guts name wrld))
            (deps (drg-function-deps guts elem-map wrld)))
         (cons (cons x (remove-equal x deps))
               (drg-dependency-graph-aux (cdr elems) elem-map wrld))))
      ((':mutrec name)
       (b* ((guts (drg-mutrec-guts name wrld))
            (deps (drg-mutrec-deps guts elem-map wrld)))
         (cons (cons x (remove-equal x deps))
               (drg-dependency-graph-aux (cdr elems) elem-map wrld))))
      (& (er hard? 'defretgen "Bad element: ~x0" x)))))

(defun drg-dependency-graph (elems wrld)
  (b* ((elem-map (drg-function->elem-map elems wrld)))
    (drg-dependency-graph-aux elems elem-map wrld)))

(mutual-recursion
 (defun drg-toposort-aux (elem rev-depgraph postorder)
   (b* (((when (member-equal elem postorder)) postorder)
        (deps (cdr (assoc-equal elem rev-depgraph)))
        (postorder (drg-toposort-aux-list deps rev-depgraph postorder)))
     (cons elem postorder)))
 (defun drg-toposort-aux-list (deps rev-depgraph postorder)
   (if (atom deps)
       postorder
     (drg-toposort-aux-list (cdr deps) rev-depgraph (drg-toposort-aux (car deps) rev-depgraph postorder)))))

(defun drg-add-to-each (keys new-val acc)
  (if (atom keys)
      acc
    (drg-add-to-each (cdr keys) new-val
                     (let ((key (car keys)))
                       (hons-acons key (cons new-val (cdr (hons-get key acc)))
                                   acc)))))

(defun drg-reverse-graph (graph acc)
  (if (atom graph)
      (fast-alist-free (fast-alist-clean acc))
    (drg-reverse-graph (cdr graph)
                       (drg-add-to-each (cdar graph) (caar graph) acc))))
   

(defun drg-dependency-order (elems wrld)
  (b* ((depgraph (drg-dependency-graph elems wrld))
       (rev-depgraph (drg-reverse-graph depgraph nil)))
    (drg-toposort-aux-list elems rev-depgraph nil)))



(defun drg-fnsets-table (wrld)
  (table-alist 'drg-fnsets wrld))

(defun drg-fnsetname-expand (name wrld)
  (b* ((look (assoc-eq name (drg-fnsets-table wrld)))
       ((unless look)
        (er hard? 'defretgen "Error: fnset must be introduced with ~x0, but ~x1 is not"
            'def-retgen-fnset name)))
    (cdr look)))

(defun drg-fnsetname-p (name wrld)
  (consp (assoc-eq name (drg-fnsets-table wrld))))

(defun drg-fnset-fully-expand (elems wrld)
  (if (atom elems)
      nil
    (let ((elem (car elems)))
      (case-match elem
        ((':fnset name)
         (append (drg-fnset-fully-expand (drg-fnsetname-expand name wrld) wrld)
                 (drg-function->elem-map (cdr elems) wrld)))
        ((':function name)
         (b* ((?ignore (drg-function-guts name wrld)))
           (cons (car elems)
                 (drg-fnset-fully-expand (cdr elems) wrld))))
        ((':mutrec name)
         (b* ((?ignore (drg-mutrec-guts name wrld)))
           (cons (car elems)
                 (drg-fnset-fully-expand (cdr elems) wrld))))
        (name (b* (((unless (and name (symbolp name)))
                    (er hard? 'defretgen "Bad elem: ~x0" name))
                   ((when (drg-fnsetname-p name wrld))
                    (append (drg-fnset-fully-expand (drg-fnsetname-expand name wrld) wrld)
                            (drg-fnset-fully-expand (cdr elems) wrld)))
                   ((when (drg-mutrec-guts? name wrld))
                    (cons `(:mutrec ,name)
                          (drg-fnset-fully-expand (cdr elems) wrld)))
                   (?ign (drg-function-guts name wrld)))
                (cons `(:function ,name)
                      (drg-fnset-fully-expand (cdr elems) wrld))))))))


(defun defretgen-entry-events (elem thmname dmgen-rules kwd-alist wrld)
  (case-match elem
    ((':function name)
     (dmgen-generate-defrets-for-fn thmname dmgen-rules (drg-function-guts name wrld) wrld))
    ((':mutrec name)
     (b* ((guts (drg-mutrec-guts name wrld))
          (gutslist (defines-guts->gutslist guts))
          (defrets (dmgen-generate-defrets thmname dmgen-rules gutslist wrld))
          ((when (atom defrets))
           nil))
       `((defret-mutual ,thmname
           ,@defrets
           :skip-others t
           :mutual-recursion ,name
           ,@(kwd-alist-to-keyword-value-list
              '(:hints :no-induction-hint :instructions :otf-flg)
              kwd-alist)))))))

(defun defretgen-ordered-events (order thmname dmgen-rules kwd-alist wrld)
  (if (atom order)
      nil
    (append (defretgen-entry-events (car order) thmname dmgen-rules kwd-alist wrld)
            (defretgen-ordered-events (cdr order) thmname dmgen-rules kwd-alist wrld))))


(defun defretgen-fn (name args wrld)
  (b* (((mv kwd-alist rest-args)
        (extract-keywords `(:defretgen ,name)
                          (append '(:functions :hints :instructions :no-induction-hint :otf-flg)
                                  *defret-generate-keywords*)
                          args
                          nil))
       ((when rest-args) (er hard? 'defretgen "Extra junk: ~x0" rest-args))
       (fnset-look (assoc :functions kwd-alist))
       ((unless fnset-look)
        (er hard? 'defretgen "A ~x0 argument is required" :functions))
       (fnset (cdr fnset-look))
       (fnset (if (symbolp fnset) (list fnset) fnset))
       (fnset-elems (drg-fnset-fully-expand fnset wrld))
       (order (drg-dependency-order fnset-elems wrld))
       (dmgen-rules (append (dmgen-process-formal-hyps (cdr (assoc :formal-hyps kwd-alist)))
                            (dmgen-process-return-concls (cdr (assoc :return-concls kwd-alist)))
                            (dmgen-process-function-keys (cdr (assoc :function-keys kwd-alist)))
                            (cdr (assoc :rules kwd-alist))))
       (errmsg (dmgen-check-rules dmgen-rules))
       ((when errmsg)
        (er hard? 'defretgen
            "Bad rule found: ~@0" errmsg)))
    (cons 'progn (defretgen-ordered-events order name dmgen-rules kwd-alist wrld))))
  



(defxdoc defretgen
  :parents (defret)
  :short "Generate some @(see defret) and @(see defret-mutual) forms for a set
          of functions and mutual recursions."
  :long "<p>This macro generates theorems based on the same kinds of rules as
@(see defret-mutual-generate).  However, instead of generating those theorems
for a single mutually-recursive clique, it generates them for a user-specified
list of functions and mutual recursions, which must be defined using @(see
define) or @(see defines) respectively.</p>

<p>The syntax of @('defretgen') works as follows:</p>

@({
 (defretgen my-theorem-about-<fn>
    ;; rules to generate the theorems
    :rules ((condition1 action1 ...)
            (condition2 action2 ...)
            ...)
   ;; abbreviations that generate more rules
   :formal-hyps ...
   :return-concls ...
   :function-keys ...

   ;; optional keywords
   :hints top-level-hints-for-defret-mutual
   :no-induction-hint nil ;; for defret-mutual
   :otf-flg nil

   ;; specifies the set of functions for which to generate the theorems
   :functions my-function-set)
 })

<p>See @(see defretgen-rules) for documentation on the @(':rules'),
@(':formal-hyps'), @(':return-concls'), and @(':function-keys') arguments.  The
@(':hints'), @(':no-induction-hint'), and @(':otf-flg') arguments are passed to
@(see defret-mutual) forms at the top level; hints for @('defret') forms (both
standalone and within defret-mutual forms) may be specified by the @(':rules')
and @(':function-keys') arguments.</p>

<p>The argument to @(':functions') must be a list of descriptors (described
below) or a single symbol, which is an abbreviation for the singleton list
containing that symbol.  A descriptor may be a symbol or one of the following
kinds of pairs:</p>
<ul>
<li>@('(:fnset <name>)') denotes a set of functions as defined by @(see
def-retgen-fnset).</li>
<li>@('(:mutrec <name>)') names a mutually-recursive clique of functions
defined using @(see defines); note that @('<name>') must be the name given to
the mutually-recursive clique as a whole (the first argument to @('defines'),
which is not necessarily the name of one of the functions.</li>
<li>@('(:function <name>)') names a function defined using @(see define).</li>
</ul>

<p>If it is a symbol, it is treated as @('(:fnset <name>)') if such a function
set exists, then @('(:mutrec <name>)') if such a mutual recursion exists, then
@('(:function <name>)') otherwise.</p> ")

(defxdoc def-retgen-fnset
  :parents (defretgen)
  :short "Give a name to a set of functions and mutual recursions that may be
          used in @(see defretgen)."
  :long "<p>Usage:</p>

@({
 (defretgen my-function-set
    (a-name
     (:fnset a-fnset-name)
     (:function a-function-name)
     (:mutrec a-mutrec-name)))
 })

<p>The first argument to @('defretgen') is the new name for the set; the second
argument is the set of functions, mutual recursions, and preexisting sets that
are included in the new set.</p>")



(defmacro defretgen (name &rest args)
  `(make-event (defretgen-fn ',name ',args (w state))))
  

(defun def-retgen-fnset-fn (name fnset wrld)
  (declare (ignorable wrld))
  (b* ((?exp (drg-fnset-fully-expand fnset wrld)))
    `(table drg-fnsets ',name ',fnset)))

(defmacro def-retgen-fnset (name fnset)
  `(make-event (def-retgen-fnset-fn ',name ',fnset (w state))))
