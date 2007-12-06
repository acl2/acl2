; Abbreviations from Bob Boyer and Warren Hunt for hons.

(in-package "ACL2")

(include-book "hons-help")

(defmacro def-macro-alias (mac fn arity-or-args)
  (let ((args (if (integerp arity-or-args)
                  (make-var-lst 'x arity-or-args)
                arity-or-args)))
    `(progn (defmacro ,mac ,args
              (list (quote ,fn) ,@(remove1-eq '&optional args)))

; Could call add-binop for arity 2.  Or better yet, modify ACL2 so
; that untranslate is sensitive to something like the
; macro-aliases-table.

            (add-macro-alias ,mac ,fn))))

; Primitives:

(def-macro-alias hqual hons-equal 2)

(def-macro-alias hopy hons-copy 1)

(def-macro-alias assoc-hqual hons-assoc-equal 2)

(def-macro-alias het hons-get-fn-do-hopy (x a))

(def-macro-alias hut hons-acons 3)

(def-macro-alias hhut hons-acons! 3)

(encapsulate
 ()
 (set-state-ok t)
 (def-macro-alias head-object hons-read-object (channel st)))

(def-macro-alias init-hut-table init-hons-acons-table 0)

(def-macro-alias hhshrink-alist hons-shrink-alist! 2)

(def-macro-alias hshrink-alist hons-shrink-alist 2)

; From hons-help.lisp:

(defmacro hist (&rest x)
  `(hons-list ,@x))

(defmacro hist* (&rest x)
  `(hons-list* ,@x))

(def-macro-alias hen1 hons-len1 2)

(def-macro-alias hen hons-len 1)

(def-macro-alias member-hqual hons-member-equal 2)

(def-macro-alias binary-hppend hons-binary-append 2)

(defmacro hppend (&rest args)
  `(hons-append ,@args))

(def-macro-alias revhppend hons-revappend 2)

(def-macro-alias heverse hons-reverse 1)

(def-macro-alias hetprop hons-getprop 3)

(def-macro-alias hutprop hons-putprop 4)

(def-macro-alias hut-list hons-put-list 3)

(def-macro-alias hintersection hons-intersection 2)

(def-macro-alias hunion hons-union 2)

(def-macro-alias hmerge-sort hons-merge-sort 2)

(def-macro-alias hopy-r hons-copy-r 1)

(def-macro-alias hopy-list-r hons-copy-list-r 1)
