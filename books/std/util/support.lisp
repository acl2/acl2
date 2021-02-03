; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "STD")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)

(defxdoc support
  :parents (std/util)
  :short "Miscellaneous supporting functions used by the @(see std/util) library.")

(defsection tuplep
  :parents (support)
  :short "@(call tuplep) recognizes nil-terminated @('n')-tuples."

  (defun tuplep (n x)
    (declare (xargs :guard (natp n)))
    (mbe :logic (and (true-listp x)
                     (equal (len x) n))
         :exec (and (true-listp x)
                    (eql (length x) n)))))

(defsection tuple-listp
  :parents (support)
  :short "@(call tuple-listp) recognizes a list of nil-terminated @('n')-tuples."

  (defun tuple-listp (n x)
    (declare (xargs :guard (natp n)))
    (if (consp x)
        (and (tuplep n (car x))
             (tuple-listp n (cdr x)))
      t)))

(defsection cons-listp
  :parents (support)
  :short "@(call cons-listp) is like @(see alistp) but does not require the
list to be nil-terminated."

  (defun cons-listp (x)
    (declare (xargs :guard t))
    (if (consp x)
        (and (consp (car x))
             (cons-listp (cdr x)))
      t)))



(defsection raise
  :parents (support define er)
  :short "Shorthand for causing hard errors."

  :long "<p>@(call raise) is equivalent to @('(er hard? ...)'), but it
automatically fills in the function name using @('__function__').</p>

<p>This only works in contexts where @('__function__') is bound, e.g., the body
of a @(see define) or within a @(see defconsts) form.  In these contexts,
rather than write something like:</p>

@({
 (er hard? __function__ \"bad input value ~x0~%\" x)
})

<p>You can just write:</p>

@({
 (raise \"bad input value ~x0~%\" x)
})

<p>Logically @('raise') just returns @('nil').</p>

@(def raise)"

  (defmacro raise (&rest args)
    `(er hard? __function__ . ,args)))


(defsection legal-kwds-p
  :parents (support)
  :short "List of legal keywords for extract-keywords."
  :long "<p>Recognizes a list where each element is either a symbol a singleton
list containing a symbol.  In @(see extract-keywords), a bare symbol is a legal
keyword and a symbol in a singleton list is a keyword that can occur multiple
times in an argument list.</p>"
  (defun legal-kwds-p (x)
    (declare (Xargs :guard t))
    (if (atom x)
        (eq x nil)
      (and (or (symbolp (car x))
               (and (consp (car x))
                    (symbolp (caar x))
                    (not (cdar x))))
           (legal-kwds-p (cdr x))))))

(defsection keyword-legality
  :parents (support)
  :short "Check whether x is a legal keyword"
  :long "<p>Returns :single if x is allowed to occur once in the argument
list, :multiple if it is allowed to occur more than once, and NIL if not
allowed.</p>"
  (defun keyword-legality (x legals)
    (declare (xargs :guard (and (symbolp x)
                                (legal-kwds-p legals))))
    (cond ((atom legals) nil)
          ((eq x (car legals)) :single)
          ((and (consp (car legals))
                (eq x (caar legals)))
           :multiple)
          (t (keyword-legality x (cdr legals))))))
          


(defsection extract-keywords
  :parents (support)
  :short "Extract legal keyword/value pairs from an argument list."
  :long "<p>If a keyword occurs as a singleton list in legal-kwds, it may have
mulitple occurrences in the args, and the result stored in the kwd-alist will
be a list of the arguments to the occurrences.  For example:</p>
@({
 (extract-keywords 'foo '((:bar)) '(:bar x :bar y) nil)
 })
<p>produces @('((:bar y x))') as its keyword alist result.</p>"
  (defun extract-keywords
    (ctx        ; context for error messages
     legal-kwds ; what keywords the args are allowed to contain
     args       ; args that the user supplied
     kwd-alist  ; accumulator alist of extracted keywords to values
     )
  "Returns (mv kwd-alist other-args)"
  (declare (xargs :guard (and (legal-kwds-p legal-kwds)
                              ; (no-duplicatesp legal-kwds)
                              (alistp kwd-alist))))
  (b* ((__function__ 'extract-keywords)
       ((when (atom args))
        (mv kwd-alist args))
       (arg1 (first args))
       ((unless (keywordp arg1))
        (b* (((mv kwd-alist other-args)
              (extract-keywords ctx legal-kwds (cdr args) kwd-alist)))
          (mv kwd-alist (cons arg1 other-args))))
       (legality (keyword-legality arg1 legal-kwds))
       ((unless legality)
        (raise (concatenate 'string
                            "~x0: invalid keyword ~x1."
                            (if legal-kwds
                                "  Valid keywords: ~&2."
                              "  No keywords are valid here."))
               ctx arg1 legal-kwds)
        (mv nil nil))
       ((when (atom (rest args)))
        (raise "~x0: keyword ~x1 has no argument." ctx arg1)
        (mv nil nil))
       ((when (and (not (eq legality :multiple))
                   (assoc arg1 kwd-alist)))
        (raise "~x0: multiple occurrences of keyword ~x1." ctx arg1)
        (mv nil nil))
       (value (second args))
       (kwd-alist (if (eq legality :multiple)
                      (acons arg1 (cons value (cdr (assoc arg1 kwd-alist)))
                             (remove1-assoc arg1 kwd-alist))
                    (acons arg1 value kwd-alist))))
    (extract-keywords ctx legal-kwds (cddr args) kwd-alist))))

(defsection getarg
  :parents (support)
  :short "Get a value from the keyword-value alist produced by @(see
extract-keywords), with default-value support."

  (defun getarg (arg default alist)
    (declare (xargs ;; :mode :program
                    :guard (and (eqlablep arg)
                                (alistp alist))))
    (b* ((look (assoc arg alist)))
      (if look
          (cdr look)
        default))))

(defsection getarg+
  :parents (support)
  :short "Get a value from the keyword-value alist produced by @(see
extract-keywords), with default-value support, and additionally return a flag
saying whether the key was bound.  Returns (mv value boundp)."

  (defun getarg+ (arg default alist)
    (declare (xargs ;; :mode :program
                    :guard (and (eqlablep arg)
                                (alistp alist))))
    (b* ((look (assoc arg alist)))
      (if look
          (mv (cdr look) t)
        (mv default nil)))))

(program)


(defun assigns-for-getargs (args alist lazyp)
  (if (atom args)
      nil
    (append (let ((arg (car args)))
              (case-match arg
                ((var default boundp)
                 (b* (((mv basevar ?ign) (acl2::decode-varname-for-patbind var))
                      (key (intern-in-package-of-symbol (symbol-name basevar) :key)))
                   (if (and lazyp (consp default) (not (eq (car default) 'quote)))
                       `((,boundp (assoc ,key ,alist))
                         (,var (if boundp (cdr boundp) ,default)))
                     `(((mv ,var ,boundp)
                        (getarg+ ,key ,default ,alist))))))
                ((var default)
                 (b* (((mv basevar ?ign) (acl2::decode-varname-for-patbind var))
                      (key (intern-in-package-of-symbol (symbol-name basevar) :key)))
                   (if (and lazyp (consp default) (not (eq (car default) 'quote)))
                       `((,var (let ((tmp-look (assoc ,key ,alist)))
                                 (if tmp-look (cdr tmp-look)
                                   (check-vars-not-free (tmp-look) ,default)))))
                     `((,var
                        (getarg ,key
                                ,default ,alist))))))
                (var (b* (((mv basevar ?ign) (acl2::decode-varname-for-patbind var))
                          (key (intern-in-package-of-symbol (symbol-name basevar) :key)))
                       `((,var
                          (getarg ,key nil ,alist)))))))
            (assigns-for-getargs (cdr args) alist lazyp))))


(acl2::def-b*-binder getargs
  :short "@(see b*) binder for getargs on a keyword alist."
  :long "<p>Usage:</p>
@({
    (b* (((getargs :lazyp t
                   a
                   (b b-default-term)
                   (c c-default-term cp)
                   d)
          alst))
      form)
})

<p>is equivalent to</p>

@({
    (b* ((a (getarg :a nil alst))
         (b (getarg :b b-default-term alst))
         ((mv c cp) (getarg+ :c nil alst))
         (d (getarg :d nil alist)))
      form)
})"

  :body
  (b* (((mv kwd-alist args)
        (extract-keywords 'getargs '(:lazyp) args nil))
       (lazyp (cdr (assoc :lazyp kwd-alist))))
    (mv-let (pre-bindings name rest)
      (if (and (consp (car acl2::forms))
               (not (eq (caar acl2::forms) 'quote)))
          (mv `((?tmp-for-getargs ,(car acl2::forms)))
              'tmp-for-getargs
              `(check-vars-not-free (tmp-for-getargs)
                                    ,acl2::rest-expr))
        (mv nil (car acl2::forms) acl2::rest-expr))
      `(b* (,@pre-bindings
            . ,(assigns-for-getargs args name lazyp))
         ,rest))))


(defun keys-for-getargs (args)
  (if (atom args)
      nil
    (b* ((arg (car args))
         (var (if (consp arg) (car arg) arg))
         ((mv basevar ?ign) (acl2::decode-varname-for-patbind var))
         (key (intern-in-package-of-symbol (symbol-name basevar) :key)))
      (cons key (keys-for-getargs (cdr args))))))

(acl2::def-b*-binder extract-keyword-args
  :short "@(see b*) binder for getargs on a keyword alist."
  :long "<p>Usage:</p>
@({
    (b* (((extract-keyword-args
            :other-args other-args-var
            :allowed-keys allowed-keys-term
            :kwd-alist kwd-alist-var
            :defaults default-kwd-alist
            :ctx context
            :lazyp lazyp
             a
            (b b-default-term)
            (c c-default-term cp)
            d)
          args))
      form)
})

<p>is equivalent to</p>

@({
    (b* (((mv kwd-alist-var other-args-var)
          (extract-keywords context
               (append '(:a :b :c :d) allowed-keys-term) ;; allowed keys
                args nil))
         ((getargs :lazyp lazyp
             a
            (b b-default-term)
            (c c-default-term cp)
            d)
          (append kwd-alist-var default-kwd-alist)))
      form)
})"

  :body
  (b* (((mv keywords args)
        (extract-keywords 'extract-keyword-args '(:lazyp :other-args :kwd-alist :ctx :allowed-keys :defaults)
                          args nil))
       ((getargs lazyp
                 allowed-keys
                 (other-args '?other-args)
                 (kwd-alist '?kwd-alist)
                 (ctx '__function__)
                 (defaults nil))
        keywords)
       (getarg-keys (keys-for-getargs args))
       ((mv kwd-alist-var ?ign) (acl2::decode-varname-for-patbind kwd-alist))
       ((mv pre-bindings name rest)
        (if (and (consp (car acl2::forms))
                 (not (eq (caar acl2::forms) 'quote)))
            (mv `((?tmp-for-extract-keyword-args ,(car acl2::forms)))
                'tmp-for-extract-keyword-args
                `(check-vars-not-free (tmp-for-extract-keyword-args)
                                      ,acl2::rest-expr))
          (mv nil (car acl2::forms) acl2::rest-expr))))
    `(b* (,@pre-bindings
          ((mv ,kwd-alist ,other-args)
           (extract-keywords ,ctx
                             ,(if allowed-keys
                                  (if getarg-keys
                                      `(append ',getarg-keys ,allowed-keys)
                                    allowed-keys)
                                `',getarg-keys)
                             ,name nil))
          ((getargs :lazyp ,lazyp . ,args)
           ,(if defaults `(append ,kwd-alist-var ,defaults) kwd-alist-var)))
       ,rest)))





(defsection split-///
  :parents (support)
  :short "Split an argument list into pre- and post-@('///') contents."

  (defun split-/// (ctx x)
    "Returns (mv pre-/// post-///)"
    (declare (xargs :guard t))
    (b* ((__function__ 'split-///)
         ((when (not x))
          (mv nil nil))
         ((when (atom x))
          (raise "~x0: expected nil-terminated arguments but found ~x1." ctx x)
          (mv nil nil))
         ((when (eq (car x) '///))
          (mv nil (cdr x)))
         ((mv pre post)
          (split-/// ctx (cdr x))))
      (mv (cons (car x) pre) post))))

(defsection ends-with-period-p
  :parents (support)
  :short "Determines if a string ends with a period."

  (defun ends-with-period-p (x)
    (declare (xargs :guard (stringp x)))
    (let ((xl (length x)))
      (and (> xl 0)
           (eql (char x (- (length x) 1)) #\.)))))





(defsection dumb-string-sublis
  :parents (support)
  :short "Non-recursively applies a list of substring substitutions to a string."
  :long "<p>Earlier key/value pairs take precedence over later ones, and no
substitutions are reapplied to the result of other substitutions.</p>"

  (defun dumb-str-sublis-iter (remainder alist x start end len)
    ;; remainder is a tail of alist, which contains the full list of substutions.
    ;; len is the length of x
    (b* (((when (atom remainder))
          (if (or (not (int= start 0))
                  (not (int= end len)))
              (subseq x start end)
            ;; we got through all the substitutions without any hits
            x))
         ((cons old-str new-str) (car remainder))
         (loc (search old-str x :start2 start :end2 end))
         ((unless loc)
          ;; not found, look for other substitutions
          (dumb-str-sublis-iter (cdr remainder) alist x start end len))
         ;; since we're searching from the beginning of the string, we've already
         ;; ruled out existence of any previous keys in the prefix
         (prefix-rw
          (dumb-str-sublis-iter
           (cdr remainder) alist x start loc len))
         ;; but for the suffix, we need to try each of them, starting over with the full alist
         (suffix-rw
          (dumb-str-sublis-iter
           alist alist x (+ loc (length old-str)) end len)))
      (if (and (string-equal prefix-rw "")
               (string-equal suffix-rw ""))
          new-str
        (concatenate 'string prefix-rw new-str suffix-rw))))


  (defun dumb-str-sublis (alist str)
    (declare (xargs :mode :program))
    (let ((len (length str)))
      (dumb-str-sublis-iter alist alist str 0 len len))))


(defsection generic-eval-requirement
  :parents (acl2::std/lists/abstract)
  :short "Evaluate a requirement of a generic theorem for deflist/defprojection/defmapappend"
  :long "<p>See @(see acl2::std/lists/abstract).</p>"

  (mutual-recursion
   (defun generic-eval-requirement (req req-alist)
     (if (atom req)
         (let ((look (assoc req req-alist)))
           (if look
               (cdr look)
             (er hard? 'generic-eval-requirement
                 "Unrecognized requirement variable: ~x0~%" req)))
       (case (car req)
         ('not (not (generic-eval-requirement (cadr req) req-alist)))
         ('and (generic-and-requirements (cdr req) req-alist))
         ('or  (generic-or-requirements (cdr req) req-alist))
         ('if  (if (generic-eval-requirement (cadr req) req-alist)
                   (generic-eval-requirement (caddr req) req-alist)
                 (generic-eval-requirement (cadddr req) req-alist)))
         (otherwise (er hard? 'generic-eval-requirement
                        "malformed requirement term: ~x0~%" req)))))
   (defun generic-and-requirements (reqs req-alist)
     (if (atom reqs)
         t
       (and (generic-eval-requirement (car reqs) req-alist)
            (generic-and-requirements (cdr reqs) req-alist))))
   (defun generic-or-requirements (reqs req-alist)
     (if (atom reqs)
         nil
       (or (generic-eval-requirement (car reqs) req-alist)
           (generic-or-requirements (cdr reqs) req-alist))))))





;; Collects up any calls of functions listed in FNS that are present in x.
(mutual-recursion
 (defun find-calls-of-fns-term (x fns acc)
   (cond ((or (atom x) (eq (car x) 'quote)) acc)
         ((member-eq (car x) fns)
          (find-calls-of-fns-list (cdr x) fns (cons x acc)))
         (t
          (find-calls-of-fns-list (cdr x) fns acc))))
 (defun find-calls-of-fns-list (x fns acc)
   (if (atom x)
       acc
     (find-calls-of-fns-term
      (car x) fns
      (find-calls-of-fns-list (cdr x) fns acc)))))

;; Gives an expand hint for any function in FNS present in the
;; conclusion of the clause.
(defun expand-calls-computed-hint (clause fns)
 (let ((expand-list (find-calls-of-fns-term (car (last clause)) fns nil)))
   `(:expand ,expand-list)))

(defmacro expand-calls (&rest fns)
  `(expand-calls-computed-hint clause ',fns))


