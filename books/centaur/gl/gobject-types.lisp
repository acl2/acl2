
(in-package "GL")

(include-book "defagg")
(include-book "tools/pattern-match" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)


(defmacro tag (x) `(vl::tag ,x))

(add-macro-alias tag vl::tag)

(add-untranslate-pattern (vl::tag ?x) (tag ?x))

(set-verify-guards-eagerness 2)

(defagg-fns g-concrete (obj) :tag :g-concrete :legiblep nil)
(defagg-fns g-boolean (bool) :tag :g-boolean :legiblep nil)
(defagg-fns g-number (num) :tag :g-number :legiblep nil)
(defagg-fns g-ite (test then else) :tag :g-ite :legiblep nil)
(defagg-fns g-apply (fn args) :tag :g-apply :legiblep nil)
(defagg-fns g-var (name) :tag :g-var :legiblep nil)

(set-verify-guards-eagerness 1)

(defconst *g-keywords*
  '(:g-boolean :g-number :g-concrete :g-ite :g-apply :g-var))

;; Performance considerations: We'll be calling this function a lot on various
;; atoms.  We check symbolp first so that we skip the more expensive member
;; check on non-symbols.  Oddly, it doesn't seem to help to also check keywordp
;; -- it seems that's more expensive than member.  Also, in CCL benchmarks, in
;; general (member-eq x lst) is faster than (member x lst), but for some reason
;; (and (symbolp x) (member x lst)) is faster than
;; (and (symbolp x) (member-eq x lst)).
(defun g-keyword-symbolp (x)
  (declare (xargs :guard t))
  (and (symbolp x)
       (member x *g-keywords*)))

(in-theory (disable g-keyword-symbolp))
