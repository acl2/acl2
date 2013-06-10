


(in-package "GL")

(include-book "defagg")
(include-book "tools/pattern-match" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "tools/rulesets" :dir :system)

;; OBSOLETE

(include-book "gobject-types") ;; make sure things are redundant




;; (set-verify-guards-eagerness 2)

;; (da-with-extras g-concrete (obj) :tag :g-concrete :legiblep nil)
;; (da-with-extras g-boolean (bool) :tag :g-boolean :legiblep nil)
;; (da-with-extras g-number (num) :tag :g-number :legiblep nil)
;; (da-with-extras g-ite (test then else) :tag :g-ite :legiblep nil)
;; (da-with-extras g-apply (fn args) :tag :g-apply :legiblep nil)
;; (da-with-extras g-var (name) :tag :g-var :legiblep nil)

;; (set-verify-guards-eagerness 1)

;; (def-ruleset gl-tag-rewrites
;;   '((:rewrite tag-when-g-concrete-p)
;;     (:rewrite tag-when-g-boolean-p)
;;     (:rewrite tag-when-g-number-p)
;;     (:rewrite tag-when-g-ite-p)
;;     (:rewrite tag-when-g-apply-p)
;;     (:rewrite tag-when-g-var-p)))

;; (def-ruleset gl-tag-forward
;;   '((:forward-chaining tag-when-g-concrete-p)
;;     (:forward-chaining tag-when-g-boolean-p)
;;     (:forward-chaining tag-when-g-number-p)
;;     (:forward-chaining tag-when-g-ite-p)
;;     (:forward-chaining tag-when-g-apply-p)
;;     (:forward-chaining tag-when-g-var-p)))

;; (def-ruleset gl-type-forward-consp

;; ; [Jared]: Hi Sol, I got rid of these forward chaining rules.  They've
;; ; now been converted into compound-recognizer rules, which I think is 
;; ; more appropriate.

;;   '(;(:forward-chaining g-concrete-p-forward-to-consp)
;;     ;(:forward-chaining g-boolean-p-forward-to-consp)
;;     ;(:forward-chaining g-number-p-forward-to-consp)
;;     ;(:forward-chaining g-ite-p-forward-to-consp)
;;     ;(:forward-chaining g-apply-p-forward-to-consp)
;;     ;(:forward-chaining g-var-p-forward-to-consp)

;; ; [Jared]: I'm hoping that this is the right fix.  Note that the name of the
;; ; rule-set above is now kind of wrong.  Also note that you might not really 
;; ; need this ruleset at all now, since I think the compound recognizer rules
;; ; may be much cheaper than the forward chaining rules, and it looks like you
;; ; only had to disable the above rules in one theorem, the guard verification 
;; ; for g-equal.

;;     (:compound-recognizer consp-when-g-concrete-p)
;;     (:compound-recognizer consp-when-g-boolean-p)
;;     (:compound-recognizer consp-when-g-number-p)
;;     (:compound-recognizer consp-when-g-ite-p)
;;     (:compound-recognizer consp-when-g-apply-p)
;;     (:compound-recognizer consp-when-g-var-p)

;;     ))

;; (def-ruleset gl-wrong-tag-rewrites
;;   '((:rewrite g-concrete-p-when-wrong-tag)
;;     (:rewrite g-boolean-p-when-wrong-tag)
;;     (:rewrite g-number-p-when-wrong-tag)
;;     (:rewrite g-ite-p-when-wrong-tag)
;;     (:rewrite g-apply-p-when-wrong-tag)
;;     (:rewrite g-var-p-when-wrong-tag)))



