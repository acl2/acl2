; Tools for event templates
; Copyright (C) 2013 Centaur Technology
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
(include-book "defmacfun")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/da-base" :dir :system)

(defxdoc template-subst
  :parents (macro-libraries)
  :short "Template-subst is a function for manipulating templates that may be
used to generate events."

  :long "<p>As an example, suppose that we want to develop a general way to map
a function over all of the atoms of a tree.  Also, when the function to be run
on the leaves is @(see acl2-count) preserving, we'd like to prove that the tree
function is as well.  So we might define the following constant as a template
for generating these sorts of functions/proofs:</p>

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
})

<p>Now, to instantiate this template, we might do:</p>

@({
    (template-subst *maptree-template*
                    :features      '(:preserves-acl2-count)
                    :subtree-alist nil
                    :splice-alist  '((_other-args_ . (n)))
                    :atom-alist    '((_treefn_ . add-to-leaves)
                                     (_leaffn_ . +))
                    :str-alist     '((\"_TREEFN_\" . \"ADD-TO-LEAVES\"))
                    :pkg-sym       'acl2::asdf)
})

<p>The process has two main steps.</p>

<h3>Preprocessing</h3>

<p>The first step involves the @(':features') argument and parts of the
template beginning with @(':@').  It does something like the @('#+') reader
macro in Lisp.</p>

<p>When @(':@') occurs as the first element of a list, the second element of
that list is treated as a feature expression, much like in the @('#+') reader
macro.  A feature expression is:</p>

<ul>
<li>A symbol</li>
<li>@('(NOT <subexpression>)')</li>
<li>@('(AND [<subexpression>]*)')</li>
<li>@('(OR [<subexpression>]*])')</li>
</ul>

<p>When templates are expanded using @('template-subst'), each symbol present
in the features list becomes true, any not present become false, and the
resulting Boolean expression is evaluated.  If the feature expression evaluates
to true, the rest of the list (not including the feature expression) is spliced
into the template and recursively preprocessed.</p>

<p>In our @('*maptree-template*') example, then, since the feature
@(':preserves-acl2-count') is present in our @(':features') argument to
@('template-subst'), we paste in the DEFTHM form.  If it was not present, that
defthm would effectively disappear.</p>

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
       str (if (keywordp sym)
               sym
             (or pkg? pkg-sym))))))

(defun tmpl-sym-tree-sublis (alist tree pkg-sym)
  (declare (xargs :mode :program))
  (if (atom tree)
      (if (symbolp tree)
          (tmpl-sym-sublis alist tree pkg-sym)
        tree)
    (cons (tmpl-sym-tree-sublis alist (car tree) pkg-sym)
          (tmpl-sym-tree-sublis alist (cdr tree) pkg-sym))))


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


(defun template-preproc (forms features)
  (b* (((when (atom forms)) forms)
       ((unless (and (consp (car forms))
                     (eq (caar forms) :@)))
        (cons (template-preproc (car forms) features)
              (template-preproc (cdr forms) features)))
       (template-form (car forms))
       (feature-form (cadr template-form))
       (subforms (cddr template-form))
       ((unless (check-features features feature-form))
        (template-preproc (cdr forms) features)))
    (append (template-preproc subforms features)
            (template-preproc (cdr forms) features))))


(std::def-primitive-aggregate tmplsubst
  (atoms          ;; replacements for atoms (alist of old . new)
   strs           ;; replacements for substrings of symbol names
                  ;; either ("old" . "new") or ("old" "new" . pkg-sym)
   pkg-sym        ;; default package symbol for symbol substring replacements
   subtrees       ;; replacements for whole (non-atom) subtrees

   splices        ;; atoms -> lists, e.g., to replace (foo x) with (bar 'blah x),
                  ;; bind foo to (bar 'blah)
   features       ;; list of keywords for conditional features
   ))


;; returns (mv changedp tree), avoids unnecessary consing.
;; The precedence among the substitutions is as the argument ordering suggests:
;; subtrees are substituted first, then atoms, and strings into symbols only if
;; that symbol was not bound in atom-alist.
;; The subtree and atom alists are kept separate just for efficiency.
(defun template-subst-rec (tree subst)
  (b* (((tmplsubst subst))
       ((when (atom tree))
        (b* ((look (assoc-equal tree subst.atoms))
             ((when look) (mv t (cdr look)))
             ((unless (symbolp tree))
              (mv nil tree))
             (res (tmpl-sym-sublis subst.strs tree subst.pkg-sym)))
          (if (eq res tree)
              (mv nil tree)
            (mv t res))))
       (look (assoc-equal tree subst.subtrees))
       ((when look) (mv t (cdr look)))
       (splice-look (and (atom (car tree))
                         (assoc-equal (car tree) subst.splices)))
       ((when splice-look)
        (b* (((mv & cdr)
              (template-subst-rec (cdr tree) subst)))
          (mv t (append (cdr splice-look) cdr))))
       ((mv chcar car)
        (template-subst-rec (car tree) subst))
       ((mv chcdr cdr)
        (template-subst-rec (cdr tree) subst)))
    (if (or chcar chcdr)
        (mv t (cons car cdr))
      (mv nil tree))))

(defun template-subst-top (tree subst)
  (b* ((preproc-tree (template-preproc tree (tmplsubst->features subst)))
       ((mv & new-tree) (template-subst-rec preproc-tree subst)))
    new-tree))

(defmacfun template-subst (tree &key features
                                subtree-alist
                                splice-alist
                                atom-alist
                                str-alist
                                (pkg-sym ''acl2::foo))
  (template-subst-top tree
                      (make-tmplsubst :features features
                                      :subtrees subtree-alist
                                      :splices splice-alist
                                      :atoms atom-alist
                                      :strs str-alist
                                      :pkg-sym pkg-sym)))

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


;; Functions for using a list of substitutions -- applying them all to one
;; template and either consing or appending together the results

;; Add some string substitution to a list of tmplsubsts, possibly overriding
;; their existing ones
(defun tmplsubsts-add-strsubsts (x strsubsts)
  (if (atom x)
      nil
    (cons (change-tmplsubst
           (car x) :strs (append strsubsts (tmplsubst->strs (car x))))
          (tmplsubsts-add-strsubsts (cdr x) strsubsts))))

;; Add some features to a list of tmplsubsts
(defun tmplsubsts-add-features (x features)
  (if (atom x)
      nil
    (cons (change-tmplsubst (car x) :features (append features (tmplsubst->features (car x))))
          (tmplsubsts-add-features (cdr x) features))))

(defun template-proj (template substs)
  (declare (xargs :mode :program))
  (if (atom substs)
      nil
    (cons (template-subst-top template (car substs))
          (template-proj template (cdr substs)))))

(defun template-append (template substs)
  (declare (xargs :mode :program))
  (if (atom substs)
      nil
    (append (template-subst-top template (car substs))
            (template-append template (cdr substs)))))



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

