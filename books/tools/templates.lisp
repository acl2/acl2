; Tools for event templates
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(include-book "bstar")
(include-book "defmacfun")
(include-book "xdoc/top" :dir :system)

(defxdoc template-subst
  :parents (event-generation)
  :short "Process a template to generate some events"
  :long "
<p>Template-subst is a function for manipulating templates that
may be used to generate events.  For example, we might want to generate a
function that runs some function on all the atoms of a tree.  Also, if the
function to be run on the leaves is acl2-count preserving, we'd like to
prove that the tree function is as well.  So we might define the following
constant as a template for generating these sorts of functions/proofs:
@({
 (defconst *maptree-template*
   '((progn (defun _treefn_ (x _other-args_)
              (if (atom x)
                  (_leaffn_ x _other-args_)
                (cons (_treefn_ (car x) _other-args_)
                      (_treefn_ (cdr x) _other-args_))))
            (:@ :preserves-acl2-count
             (defthm _treefn_-preserves-acl2-count
               (equal (acl2-count (_treefn_ x _other-args_))
                      (acl2-count x)))))))
@})
Now to instantiate this template we might do
@({
 (template-subst *maptree-template*
                 :features '(:preserves-acl2-count)
                 :subtree-alist nil
                 :splice-alist '((_other-args_ . (n)))
                 :atom-alist '((_treefn_ . add-to-leaves)
                               (_leaffn_ . +))
                 :str-alist '((\"_TREEFN_\" . \"ADD-TO-LEAVES\"))
                 :pkg-sym 'acl2::asdf)
@})
 </p>

<p>The process has two main steps.</p>

<h3>Preprocessing</h3>
<p>The first step involves the :features argument and
parts of the template beginning with :@.  It does something like the #+
reader macro in Lisp.  When :@ occurs as the first element of a list, the
second element of that list is treated as a feature expression, much like in
the #+ reader macro.</p>
<p>A feature expression is:
<ul>
<li>a symbol</li>
<li>(NOT &lt;subexpression&gt;)</li>
<li>(AND [&lt;subexpression&gt;])</li>
<li>(OR [&lt;subexpression&gt;])</li>
</ul></p>

<p>Each symbol present in the features list becomes true, any not present
become false, and the resulting Boolean expression is evaluated.  If it
evaluates to T, the rest of the list (not including the feature expression)
is spliced into the template and recursively preprocessed.
Therefore in our example, since the feature :preserves-acl2-count is present
in our :features argument to template-subst, we paste in the DEFTHM form.
If it was not present, that defthm would effectively disappear.
</p>

<h3>Substitution</h3>
<p> The second step involves substitution of various kinds into the tree.</p>
<ul>
<li>At each cons node of the tree:
<ul>
<li> We check whether the tree is bound in subtree-alist, and if so we
    return its corresponding value.</li>
<li> We check whether the car of the tree is bound in splice-alist, and if so
    we append its corresponding value to the recursive substitution of the
    cdr of the tree.</li>
<li> Otherwise, we return the cons of the recursive substitutions into the
    car and cdr.</li>
</ul></li>
<li>
At each atom in the tree:
<ul>
<li> We check whether the leaf is bound in atom-alist; if so, we return its
    corresponding value.</li>
<li> If the leaf is a symbol, we apply str-alist as a substitution to its
    symbol-name.  If any substitutions are made, we intern the resulting
    string in the package of pkg-sym.</li>
</ul></li>
</ul>

<p>Therefore, in our example we make the following replacements:</p>
<ul>
<li> the symbol _treefn_ is replaced with add-to-leaves and _leaffn_ is
    replaced with +</li>
<li> by string substitution, the symbol _treefn_-preserves-acl2-count
    is replaced with add-to-leaves-preserves-acl2-count</li>
<li> each occurrence of _other-args_ is replaced by splicing in the list (n),
    effectively replacing _other-args_ with n.</li>
</ul>
<p>(Of course, the proof fails since our leaf transformation isn't actually
 acl2-count preserving.)</p>
")


;; Program mode because the guards would require standard-char-listp of
;; everything.
(program)




;; This does complete but non-recursive, non-compositional string list
;; substitution.  Alist is the full list of substitutions; these are done "in
;; parallel", meaning the result of one substitution never undergoes another
;; substitution; but earlier elements have precedence over later ones, meaning
;; if you have '(("foo" . "bar) ("afoo" . "abar")) the second substitution
;; will never happen.

(defun tmpl-str-sublis-iter (remainder alist x start end len pkg)
  (b* (((when (atom remainder))
        ;; if both start and end are nil, we don't need to make a copy
        (mv (if (or (not (int= start 0))
                    (not (int= end len)))
                (subseq x start end)
              x) pkg))
       ((cons old-str pair) (car remainder))
       (new-str (if (consp pair) (car pair) pair))
       (loc (search old-str x :start2 start :end2 end))
       ((unless loc)
        (tmpl-str-sublis-iter (cdr remainder) alist x start end len pkg))
       (pkg (or pkg (and (consp pair) (cdr pair))))
       ;; since we're searching from the beginning of the string, we've already
       ;; ruled out existence of any previous keys in the prefix
       ((mv prefix-rw pkg)
        (tmpl-str-sublis-iter
         (cdr remainder) alist x start loc len pkg))
       ;; but for the suffix, we need to try each of them
       ((mv suffix-rw pkg)
        (tmpl-str-sublis-iter
         alist alist x
         (+ loc (length old-str)) end len pkg)))
    (mv (if (and (string-equal prefix-rw "")
                 (string-equal suffix-rw ""))
            new-str
          (concatenate 'string prefix-rw new-str suffix-rw))
        pkg)))


(defun tmpl-str-sublis (alist str)
  (declare (xargs :mode :program))
  (let ((len (length str)))
    (tmpl-str-sublis-iter alist alist str 0 len len nil)))

(make-event
 (if (equal (mv-list 2 (tmpl-str-sublis
                        '(("foo" . "bar")
                          ("fuz" "biz" . pkg)
                          ("bar" . "boz"))
                        "afuzbarcfoobbarfooafuz"))
            (list "abizbozcbarbbozbarabiz" 'pkg))
     '(value-triple :ok)
   (er hard? 'tmpl-str-sublis "Test failed~%")))

(defun tmpl-sym-sublis (alist sym pkg-sym)
  (b* ((str1 (symbol-name sym))
       ((mv str pkg?) (tmpl-str-sublis alist str1)))
    (if (equal str1 str) sym
      (intern-in-package-of-symbol
       str (or pkg? pkg-sym)))))


(mutual-recursion
 (defun check-features (features feature-form)
   (if (atom feature-form)
       (and (member-eq feature-form features) t)
     (case (car feature-form)
       (or (or-list (check-features-list features (cdr feature-form))))
       (and (and-list (check-features-list features (cdr feature-form))))
       (not (not (check-features features (cadr feature-form)))))))

 (defun check-features-list (features forms)
   (if (atom forms)
       nil
     (cons (check-features features (car forms))
           (check-features-list features (cdr forms))))))


;; Template-preproc allows 

(defun template-preproc (features forms)
  (b* (((when (atom forms)) forms)
       ((unless (and (consp (car forms))
                     (eq (caar forms) :@)))
        (cons (template-preproc features (car forms))
              (template-preproc features (cdr forms))))
       (template-form (car forms))
       (feature-form (cadr template-form))
       (subforms (cddr template-form))
       ((unless (check-features features feature-form))
        (template-preproc features (cdr forms))))
    (append (template-preproc features subforms)
            (template-preproc features (cdr forms)))))


;; returns (mv changedp tree), avoids unnecessary consing.
;; The precedence among the substitutions is as the argument ordering suggests:
;; subtrees are substituted first, then atoms, and strings into symbols only if
;; that symbol was not bound in atom-alist.
;; The subtree and atom alists are kept separate just for efficiency.
(defun template-subst-rec (subtree-alist splice-alist atom-alist str-alist tree pkg-sym)
  (b* (((when (atom tree))
        (b* ((look (assoc-equal tree atom-alist))
             ((when look) (mv t (cdr look)))
             ((unless (symbolp tree))
              (mv nil tree))
             (res (tmpl-sym-sublis str-alist tree pkg-sym)))
          (if (eq res tree)
              (mv nil tree)
            (mv t res))))
       (look (assoc-equal tree subtree-alist))
       ((when look) (mv t (cdr look)))
       (splice-look (and (atom (car tree))
                         (assoc-equal (car tree) splice-alist)))
       ((when splice-look)
        (b* (((mv & cdr)
              (template-subst-rec
               subtree-alist splice-alist atom-alist str-alist (cdr tree)
               pkg-sym)))
          (mv t (append (cdr splice-look) cdr))))
       ((mv chcar car)
        (template-subst-rec subtree-alist splice-alist atom-alist str-alist (car tree) pkg-sym))
       ((mv chcdr cdr)
        (template-subst-rec subtree-alist splice-alist atom-alist str-alist (cdr tree) pkg-sym)))
    (if (or chcar chcdr)
        (mv t (cons car cdr))
      (mv nil tree))))

(defmacfun template-subst (tree &key features
                                subtree-alist
                                splice-alist
                                atom-alist
                                str-alist
                                (pkg-sym ''acl2::foo))
  (b* ((preproc-tree (template-preproc features tree))
       ((mv & new-tree) (template-subst-rec
                         subtree-alist splice-alist atom-alist str-alist
                         preproc-tree pkg-sym)))
    new-tree))

;; This can be used to generate a string substitution from a symbol substitution.
(defun tmpl-symbol-alist-to-str-alist (x)
  (if (atom x)
      nil
    (if (and (consp (car x))
             (symbolp (caar x))
             (symbolp (cdar x)))
        (cons (cons (symbol-name (caar x))
                    (symbol-name (cdar x)))
              (tmpl-symbol-alist-to-str-alist (cdr x)))
      (tmpl-symbol-alist-to-str-alist (cdr x)))))


(logic)

(local
 (progn
   (defconst *maptree-template*
     '(progn (defun _treefn_ (x _other-args_)
               (if (atom x)
                   (_leaffn_ x _other-args_)
                 (cons (_treefn_ (car x) _other-args_)
                       (_treefn_ (cdr x) _other-args_))))
             (:@ :preserves-acl2-count
              (defthm _treefn_-preserves-acl2-count
                (equal (acl2-count (_treefn_ x _other-args_))
                       (acl2-count x))))))

   ;; Now to instantiate this template we might do
   (make-event
    (if (equal
         (template-subst *maptree-template*
                         :features '(:preserves-acl2-count)
                         :subtree-alist nil
                         :splice-alist '((_other-args_ . (n)))
                         :atom-alist '((_treefn_ . add-to-leaves)
                                       (_leaffn_ . +))
                         :str-alist '(("_TREEFN_" . "ADD-TO-LEAVES"))
                         :pkg-sym 'acl2::asdf)
         '(PROGN (DEFUN ADD-TO-LEAVES (X N)
                   (IF (ATOM X)
                       (+ X N)
                       (CONS (ADD-TO-LEAVES (CAR X) N)
                             (ADD-TO-LEAVES (CDR X) N))))
                 (DEFTHM ADD-TO-LEAVES-PRESERVES-ACL2-COUNT
                   (EQUAL (ACL2-COUNT (ADD-TO-LEAVES X N))
                          (ACL2-COUNT X)))))
        '(value-triple :ok)
      (er hard? 'template-subst "Test failed~%")))))

