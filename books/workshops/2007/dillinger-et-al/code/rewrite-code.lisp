#|$ACL2s-Preamble$;
(defpkg "REWRITE-CODE"
        (append
         ; "imports":
         '(value er-let* er-decode-logical-name getprop current-acl2-world
           stobjs-in cltl-command global-value soft)
         ; "exports":
         '(er-rewrite-form
           get-defun
	   compute-copy-defun+rewrite
	   assert-include-defun-matches-certify-defun
	   copy-defun+rewrite
	   copy-defun)
         (union-eq *acl2-exports*
                   *common-lisp-symbols-from-main-lisp-package*)))

(acl2::begin-book);$ACL2s-Preamble$|#


(in-package "REWRITE-CODE")

(program)
(set-state-ok t)

; recognizer for ``augmented naturals'', which include 'inf as infinity
(defun aug-natp (x)
  (or (natp x)
      (equal x 'inf)))

; < relation for ``augmented naturals''
(defun aug-nat-< (x y)
  (and (not (eq x 'inf))
       (or (eq y 'inf)
           (< x y))))

; decrement function for ``augmented naturals''
(defun aug-nat-dec (x)
  (cond ((eq x 'inf) 'inf)
        ((zp x) 0)
        (t (1- x))))

; recognizer for intervals over ``augmented naturals''
(defun multiplicity-rangep (x)
  (or (null x) ; empty range
      (and (consp x)
           (aug-natp (car x))
           (aug-natp (cdr x))
           (not (aug-nat-< (cdr x) (car x))))))

; decrement function for intervals over ``augmented naturals''
(defun multiplicity-range-dec (x)
  (if (or (endp x) (equal (cdr x) 0))
    nil ; empty range
    (cons (aug-nat-dec (car x))
          (aug-nat-dec (cdr x)))))


; prepend the reverse of one list onto another
(defun rev-prepend (torev onto)
  ; (declare (xargs :guard (and (true-listp torev) (true-listp onto))))
  (if (endp torev)
    onto
    (rev-prepend (cdr torev) (cons (car torev) onto))))


; n times, pops an element from ,from and pushes it on ,to
(defun pop-push-n (n from to)
  (if (or (zp n)
          (endp from))
    (mv from to)
    (pop-push-n (1- n) (cdr from) (cons (car from) to))))


; update an entry in an alist, or add it to the end
(defun update-alist (key val lst)
  (cond ((endp lst)
         (list (cons key val)))
        ((and (consp (car lst))
              (equal (caar lst) key))
         (cons (cons key val)
               (cdr lst)))
        (t
         (cons (car lst)
               (update-alist key val (cdr lst))))))


; replaces occurances in ,expr of the symbols that are keys in ,assn-alist
; with their bindings in ,assn-alist.
;
(defun replace-assns (expr assn-alist)
  ;(declare (xargs :guard (symbol-alistp assn-alist)))
  (if (consp expr)
    (cons (replace-assns (car expr) assn-alist)
          (replace-assns (cdr expr) assn-alist))
    (if (symbolp expr)
      (let ((assn (assoc-eq expr assn-alist)))
        (if (consp assn)
          (cdr assn)
          expr))
      expr)))


; ,a1 and ,a2 are each assumed an alist with no keys duplicated.  if the keys
; don't overlap between ,a1 and ,a2 or they agree on all the bindings, the
; "union" is returned.  if they disagree on any bindings, ,t is returned.
;
(defun merge-matches (a1 a2)
  (cond ((endp a1)
         a2)
        ((endp a2)
         a1)
        (t
         (let* ((sym (caar a1))
                (binding2 (assoc-eq sym a2)))
           (if (consp binding2)
             (let ((val1 (cdar a1))
                   (val2 (cdr binding2)))
               (if (equal val1 val2)
                 (merge-matches (cdr a1) a2)
                 t))
             (merge-matches (cdr a1) (cons (car a1) a2)))))))


; returns (smallest) assn-alist satisfying
;   (equal (replace-assns pat assn-alist) expr)
; if one exists.  otherwise, returns t (indicating, roughly, that
; no assignments to ,vars in ,pat generate ,expr)
;
(defun match-pattern (expr pat vars)
  ;(declare (xargs :guard (symbol-listp vars)))
  (cond ((member-eq pat vars)
         (list (cons pat expr)))
        ((and (consp pat)
              (consp expr))
         (let ((car-result (match-pattern (car expr) (car pat) vars))
               (cdr-result (match-pattern (cdr expr) (cdr pat) vars)))
           (if (or (equal car-result t) (equal cdr-result t))
             t ; bad match
             (merge-matches car-result cdr-result))))
        ((equal pat expr)
         ())
        (t
         t) ; bad match
        ))

; predicates for the parsed pieces of a rewrite-spec, a rewrite-def and its
; constituent pieces
(mutual-recursion
 (defun rewrite-defp (v) ; a list (sequenced) of lists (simultaneous)
   (declare (xargs :measure (acl2-count v)
                   :hints (("Goal"
                            :in-theory (disable
                                        (:definition multiplicity-rangep))))))
   (or (null v)
       (and (consp v)
            (rewrite-simul-defp (car v))
            (rewrite-defp (cdr v)))))
 (defun rewrite-simul-defp (v) ; a list (simultaneous) of entries
   (declare (xargs :measure (acl2-count v)))
   (or (null v)
       (and (consp v)
            (rewrite-entryp (car v))
            (rewrite-simul-defp (cdr v)))))
 (defun rewrite-entryp (v)
   (declare (xargs :measure (acl2-count v)))
   (and (consp v)
        (multiplicity-rangep (car v)) ; global
        (consp (cdr v))
        (rewrite-var-entry-lstp (cadr v)) ; no binding -> recursive
        (consp (cddr v))
        (symbol-listp (caddr v)) ; vars
        (consp (cdddr v))
        ; (cadddr v) is pat
        ; (cddddr v) is repl
        ))
 (defun rewrite-var-entry-lstp (v) ; var -> rewrite-def alist
   (declare (xargs :measure (acl2-count v)))
   (or (null v)
       (and (consp v)
            (rewrite-var-entryp (car v))
            (rewrite-var-entry-lstp (cdr v)))))
 (defun rewrite-var-entryp (v) ; ( var . rewrite-def )
   (declare (xargs :measure (acl2-count v)))
   (and (consp v)
        (symbolp (car v))
        (rewrite-defp (cdr v)))))

; some accessors
(defmacro entry-multrng (v) `(car ,v))
(defmacro entry-alist   (v) `(cadr ,v))
(defmacro entry-vars    (v) `(caddr ,v))
(defmacro entry-pat     (v) `(cadddr ,v))
(defmacro entry-repl    (v) `(cddddr ,v))

; some modifiers
(defun    dec-entry     (v)
  (cons (multiplicity-range-dec (car v))
        (cdr v)))
(defun update-entry-alist (v alist)
  (cons (car v)
        (cons alist
              (cddr v))))
(defun update-entry-alist-entry (v var def)
  (update-entry-alist v (update-alist var def (entry-alist v))))

; the guts of code rewriting
(mutual-recursion
 (defun rewrite-seq (form seq-from seq-to)
   (declare (xargs :guard (and (rewrite-defp seq-from)
                               (rewrite-defp seq-to))))
   (if (consp seq-from)
     (mv-let (form updated)
             (rewrite-simul form (car seq-from) nil)
             (rewrite-seq form (cdr seq-from) (cons updated seq-to)))
     (mv form (reverse seq-to))))
 (defun rewrite-simul (form simul-from simul-to)
   (declare (xargs :guard (and (rewrite-simul-defp simul-from)
                               (rewrite-simul-defp simul-to))))
   (if (consp simul-from)
     (let* ((entry (car simul-from))
            (assns-opt (match-pattern form
                                      (entry-pat entry)
                                      (entry-vars entry))))
       (if (eq 't assns-opt)
         ; no match
         (rewrite-simul form
                        (cdr simul-from)
                        (cons entry simul-to))
         ; match!
         (let* ((entry (dec-entry entry))
                (simul-from (cons entry (cdr simul-from)))
                (idx (len simul-to)))
           (rewrite-assns (entry-repl entry)
                          assns-opt
                          idx
                          (rev-prepend simul-to simul-from)))))
     ;; no more rules to try
     (let ((simul-all (reverse simul-to)))
       (if (consp form)
         ;; descend
         (mv-let (car-form simul-all)
                 (rewrite-simul (car form) simul-all nil)
                 (mv-let (cdr-form simul-all)
                         (rewrite-simul (cdr form) simul-all nil)
                         (mv (cons car-form cdr-form) simul-all)))
         (mv form simul-all)))))
 (defun rewrite-assns (repl assns entry-idx simul-all)
   (declare (xargs :guard (and (rewrite-simul-defp simul-all)
                               (natp entry-idx)
                               (< entry-idx (len simul-all))
                               (symbol-alistp assns))))
   (cond ((consp repl)
          (mv-let (car-form simul-all)
                  (rewrite-assns (car repl) assns entry-idx simul-all)
                  (mv-let (cdr-form simul-all)
                          (rewrite-assns (cdr repl) assns entry-idx simul-all)
                          (mv (cons car-form cdr-form) simul-all))))
         ((symbolp repl)
          (let ((assn-opt (assoc-eq repl assns)))
            (if (consp assn-opt)
              (let* ((form (cdr assn-opt))
                     (entry (nth entry-idx simul-all))
                     (non-rec-defs (entry-alist entry))
                     (non-rec-def-opt (assoc-eq repl non-rec-defs)))
                (if (consp non-rec-def-opt)
                  ; some non-recursive specification
                  (mv-let (form updated-def)
                          (rewrite-seq form (cdr non-rec-def-opt) nil)
                          (mv form (update-nth entry-idx
                                               (update-entry-alist-entry entry
                                                                         repl
                                                                         updated-def)
                                               simul-all)))
                  ; no non-rec-def => recursively apply simul-all
                  (if (and (symbolp (entry-pat entry))
                           (member-eq (entry-pat entry) (entry-vars entry)))
                    ; illegal recursive rewrite that matches everything.
                    ; for now, we'll just break the recursion.
                    (mv form simul-all)
                    ; text to match against getting smaller =>
                    ;   recursively apply simul-all
                    (rewrite-simul form simul-all nil))))
              (mv repl simul-all))))
         (t
          (mv repl simul-all)))))

; code for checking that the multiplicities allow zero.  used after they have
; been decremented as many times as they have been used.
(mutual-recursion
 (defun assert-zero-allowed-def (v state)
   (if (endp v)
     state
     (pprogn
      (assert-zero-allowed-simul-def (car v) state)
      (assert-zero-allowed-def (cdr v) state))))
 (defun assert-zero-allowed-simul-def (v state)
   (if (endp v)
     state
     (pprogn
      (assert-zero-allowed-entry (car v) state)
      (assert-zero-allowed-simul-def (cdr v) state))))
 (defun assert-zero-allowed-entry (v state)
   (if (or (endp v) (endp (cdr v)))
     state
     (let ((rng (car v))
           (var-entries (cadr v)))
       (pprogn
        (if (or (endp rng) (not (equal (car rng) 0)))
          ; zero not allowed
          (pprogn
           (acl2::f-put-global 'erp t state)
           (fms (if (endp rng)
                "Code rewrite entry used too many times:~%  ~xp -> ~xr~%"
                "Code rewrite entry used too few times (at least ~xn applications remaining):~%  ~xp -> ~xr~%")
              `((#\p . ,(entry-pat  v))
                (#\r . ,(entry-repl v))
                (#\n . ,(and (consp rng) (car rng))))
              (standard-co state)
              state
              (acl2::abbrev-evisc-tuple state)))
          ; ok
          state)
        (assert-zero-allowed-entry-lst var-entries state)))))
 (defun assert-zero-allowed-entry-lst (v state)
   (if (endp v)
     state
     (pprogn
      (assert-zero-allowed-var-entry (car v) state)
      (assert-zero-allowed-entry-lst (cdr v) state))))
 (defun assert-zero-allowed-var-entry (v state)
   (if (endp v)
     state
     (assert-zero-allowed-def (cdr v) state))))

(defun er-if-zero-not-allowed-def (def state)
  (acl2::state-global-let*
   ((erp nil))
   (pprogn
    (assert-zero-allowed-def def state)
    (mv (@ erp) :invisible state))))

(defun rewrite-fn (form def state)
  (if (not (rewrite-defp def))
    (er acl2::soft 'rewrite "Code rewrite definition illegal:~%~x0" def)
    (mv-let (result new-def)
            (rewrite-seq form def nil)
            (er-progn
             (er-if-zero-not-allowed-def new-def state)
             (acl2::value result)))))

#|
(rewrite-fn '(a b (c (c d)) (x c v))
            '((((0 . 2) ((%)) (%) (c . %) . (f . %))))
            state)
|#

; now i build up a more convenient specification language

; first, instead of always (n . m) as range, we also allow
; + == (1 . inf)
; * == (0 . inf)
; n == (n . n)

; predicate for new multiplicity specs
(defun multiplicity-specp (x)
  (declare (xargs :guard t))
  (or (and (multiplicity-rangep x)
           (not (equal (car x) 'inf)))
      (equal x '*)
      (equal x '+)
      (natp x)))

(defun multiplicity-spec-to-noninf-range (x)
  (declare (xargs :guard (multiplicity-specp x)))
  (cond ((and (multiplicity-rangep x)
              (not (equal (car x) 'inf)))
         x)
        ((equal x '*) '(0 . inf))
        ((equal x '+) '(1 . inf))
        ((natp x) (cons x x))
        (t nil) ; invalid / unrecognized
        ))


; now we build up some macros that build rewrite-defs from a more natural,
; flexible specification language.

; roughly speaking, entries/rules consist of some pieces:
;   :pat  = "pattern" to match   or  :carpat = pattern that must be in a car
;   :repl = "replacement" to put in place of pattern (defaults to the pattern)
;   :vars = "variables" = a list of symbols that should not be taken
;           literally in the pattern, but can stand for any substructure
;   :recvars = "recursive variables" = like :vars but the current rules also
;           get applied to what these variables match
;   :mult = "multiplicity" = an assertion on how many applications of this
;           rule are to be made.  (violation results in post facto error)
;
; entries can be combined using "simultaneous" combination:
;   (:simul e1 e2 e3)
; to indicate that at each step in our pre-order search we attempt to match
; e1, then e2, then e3.  if no matches, we go deeper.
;
; entries and/or :simul combinations can be combined with "sequences":
;   (:seq s1 s2 s3)
; to indicate that we apply s1 to our form, apply that result to s1, and
; apply that result to s3.

; syntax more precisely:
; above relevant functions, i have kind-of a BNF for the language.  the
; parentheses and dots are required cons structure.  symbols are also
; matched literally, unless they are surrounded with _ _.  items in [] are
; optional, with a default value given after an =.  ... is a postfix shorthand
; for 0 or more of something.

; to the right is an indication of what is shorthand for what.  if something
; is canonical, "(canonical)" appears, meaning it should be pretty obvious
; how this maps to the lower level structure, if you understand it.  ;)

; _def_ ::= ()                          => (:seq)
;         | (_def_)                     => _def_
;         | (:seq _simul-def_...)       (canonical)
;         | _simul-def_                 => (:seq _simul-def_)

(defmacro quote-rewrite-def (&rest v)
  (cond
   ((endp v)
    ''nil)
   ((and (consp (car v))
         (null (cdr v)))
    `(quote-rewrite-def . ,(car v)))
   ((eq ':seq (car v))
    `(quote-rewrite-def-rest . ,(cdr v)))
   (t
    `(list (quote-rewrite-simul-def . ,v)))))

(defmacro quote-rewrite-def-rest (&rest v)
  (if (endp v)
    ''nil
    `(cons
      (quote-rewrite-simul-def . ,(car v))
      (quote-rewrite-def-rest . ,(cdr v)))))

; _simul-def_ ::= ()                       => (:simul)
;               | (:simul _entry_...)      (canonical)
;               | _entry_                  => (:simul _entry_)

(defmacro quote-rewrite-simul-def (&rest v)
  (cond
   ((endp v)
    ''nil)
   ((eq ':simul (car v))
    `(quote-rewrite-simul-def-rest . ,(cdr v)))
   (t
    `(list (quote-rewrite-entry . ,v)))))

(defmacro quote-rewrite-simul-def-rest (&rest v)
  (if (endp v)
    ''nil
    `(cons
      (quote-rewrite-entry . ,(car v))
      (quote-rewrite-simul-def-rest . ,(cdr v)))))

; some stuff for entries
(defun namep (v)
  (and (symbolp v)
       (not (null v))
       (not (keywordp v))))

; _var-spec_ ::= ()                                (canonical)
;              | _name_                            => ((_name_))
;              | (_name_ . _var-spec_)             => ((_name_) . _var-spec_)
;              | ((_name_ . _def_) . _var-spec_)   (canonical)

(defun var-specp (v)
  (or (null v)
      (namep v)
      (and (consp v)
           (or (namep (car v))
               (and (consp (car v))
                    (namep (caar v))))
           (var-specp (cdr v)))))

; _recvar-spec_ ::= ()                             (canonical)
;                 | _name_                         => (_name_)
;                 | (_name_ . _var-spec_)          (canonical)

(defun recvar-specp (v)
  (or (null v)
      (namep v)
      (and (consp v)
           (namep (car v))
           (recvar-specp (cdr v)))))

(defun get-var-names (var-spec)
  (if (consp var-spec)
    (cons (if (consp (car var-spec))
            (caar var-spec)
            (car var-spec))
          (get-var-names (cdr var-spec)))
    (if (null var-spec)
      nil
      (list var-spec))))

(defun canonicalize-var-bindings (var-spec)
  (if (consp var-spec)
    (cons (if (consp (car var-spec))
            (car var-spec)
            (list (car var-spec)))
          (canonicalize-var-bindings (cdr var-spec)))
    (if (null var-spec)
      nil
      (list (list var-spec)))))

; _entry_ ::= (:pat _pat_                     (canonical)
;              [:repl _repl_=_pat_]
;              [:mult _mult_=*]
;              [:vars _var-spec_=()]
;              [:recvars _recvar-spec_=()])
;           | (:carpat _pat_                  => (:pat  (_pat_  . %cdr%)
;              [:repl _repl_=_pat_]               :repl (_repl_ . %cdr%)
;              [:mult _mult_=*]                :recvars (%cdr% . _recvar-spec_)
;              [:vars _var-spec_=()]           :vars _var-spec_ :mult _mult_)
;              [:recvars _recvar-spec_=()])

(defmacro quote-rewrite-entry (&key (pat '() patp)
				    (carpat '() carpatp)
                                    (repl '() replp)
                                    (mult '*)
                                    (vars '())
                                    (recvars '()))
  (declare (xargs :guard (and (multiplicity-specp mult)
                              (var-specp vars)
                              (recvar-specp recvars)
			      (not (and patp carpatp))
                              (or (and patp
				       (not (member pat (get-var-names recvars))))
				  (and carpatp
				       (not (member carpat (get-var-names recvars)))))
                              (not (intersectp-eq (get-var-names vars)
                                                  (get-var-names recvars))))))
  (let* ((cdrvar '%cdr-reserved%)
	 (nrcvar-names (get-var-names vars))
         (recvar-names (append (if carpatp (list cdrvar) '())
			       (get-var-names recvars)))
         (var-names (append nrcvar-names recvar-names))
         (pat (if patp
		pat
		(cons carpat cdrvar)))
	 (repl (if replp
		 (if carpatp
		   (cons repl cdrvar)
		   repl)
		 pat)))
    `(list* ',(multiplicity-spec-to-noninf-range mult)
            (quote-rewrite-var-entry-lst . ,(canonicalize-var-bindings vars))
            ',var-names
            ',pat
            ',repl)))

; see _var-spec_ above

(defmacro quote-rewrite-var-entry-lst (&rest bindings)
  (if (endp bindings)
    ''nil
    `(cons (quote-rewrite-var-entry ,(car bindings))
           (quote-rewrite-var-entry-lst . ,(cdr bindings)))))

(defmacro quote-rewrite-var-entry (v)
  (declare (xargs :guard (and (consp v)
                              (namep (car v)))))
  `(cons ',(car v)
         (quote-rewrite-def . ,(cdr v))))



; and now to put the more convenient language on top of the code rewriting:

; for "export"
(defmacro er-rewrite-form (form &rest def)
  `(rewrite-fn
    ,form
    (quote-rewrite-def . ,def)
    state))



; EXAMPLES, for understanding the semantics more precisely:
#|
ACL2 !>(er-rewrite-form 'a)
 A
ACL2 !>(er-rewrite-form 'a (:pat a :repl b))
 B
ACL2 !>(er-rewrite-form 'a (:seq (:pat a :repl b) (:pat b :repl c)))
 C
ACL2 !>(er-rewrite-form '(a . b) (:seq (:pat a :repl b) (:pat b :repl c)))
 (C . C)
ACL2 !>(er-rewrite-form '(a . b) (:simul (:pat a :repl b) (:pat b :repl c)))
 (B . C)
ACL2 !>(er-rewrite-form '(b . a) (:simul (:pat a :repl b) (:pat b :repl c)))
 (C . B)
ACL2 !>(er-rewrite-form '(+ (fn1 42) (fn1 53))
                        (:pat (fn1 %) :repl (fn2 %) :vars (%)))
 (+ (FN2 42) (FN2 53))
ACL2 !>(er-rewrite-form '(+ (fn1 42) (fn1 53))
                        (:pat (fn1 %) :repl (fn2 %) :vars %))
 (+ (FN2 42) (FN2 53))
ACL2 !>(er-rewrite-form '(+ (fn1 (fn1 42)) (fn1 53))
                        (:pat (fn1 %) :repl (fn2 %) :vars %))
 (+ (FN2 (FN1 42)) (FN2 53))
ACL2 !>(er-rewrite-form '(+ (fn1 (fn1 42)) (fn1 53))
                        (:pat (fn1 %) :repl (fn2 %) :recvars %))
 (+ (FN2 (FN2 42)) (FN2 53))
ACL2 !>(er-rewrite-form '(+ (stuff fn1 42) (fn1 42))
                        (:pat (fn1 %) :repl (fn2 %) :vars %))
 (+ (STUFF FN2 42) (FN2 42))
ACL2 !>(er-rewrite-form '(+ (stuff fn1 42) (fn1 42))
                (:pat ((fn1 %1) . %2) :repl ((fn2 %1) . %2) :vars (%1 %2)))
 (+ (STUFF FN1 42) (FN2 42))
ACL2 !>(er-rewrite-form '(+ (stuff fn1 42) (fn1 42) (fn1 53))
                (:pat ((fn1 %1) . %2) :repl ((fn2 %1) . %2) :vars (%1 %2)))
 (+ (STUFF FN1 42) (FN2 42) (FN1 53))
ACL2 !>(er-rewrite-form '(+ (stuff fn1 42) (fn1 42) (fn1 53))
                (:pat ((fn1 %1) . %2) :repl ((fn2 %1) . %2) :recvars (%1 %2)))
 (+ (STUFF FN1 42) (FN2 42) (FN2 53))

|#
; this demonstrates that in order to rewrite a function call in a more
; robust way, we should do
;   (:pat  ((old-fn . %params%) . %cdr%)
;    :repl ((new-fn . %params%) . %cdr%)
;    :vars %params%  :recvars %cdr%)
; rather than
;   (:pat  (old-fn . %params%)
;    :repl (new-fn . %params%)
;    :vars %params%)
; but if we do it this way, will we match a function called in the
; top level of a function?  consider (defun x (v) (y v)).  rather than
; rewriting (y v) at the top level, we shall rewrite ((y v)), which is the
; last cons of the defun.  we will use this below in
; compute-copy-defun+rewrite.
;
; however, we offer :carpat as a shortcut for such specifications.  the
; following are equivalent:
#|
ACL2 !>(er-rewrite-form '(+ (stuff fn1 42) (fn1 42) (fn1 53))
                (:pat ((fn1 %1) . %2) :repl ((fn2 %1) . %2) :recvars (%1 %2)))
 (+ (STUFF FN1 42) (FN2 42) (FN2 53))
ACL2 !>(er-rewrite-form '(+ (stuff fn1 42) (fn1 42) (fn1 53))
                (:carpat (fn1 %1) :repl (fn2 %1) :recvars %1))
 (+ (STUFF FN1 42) (FN2 42) (FN2 53))
|#

; also, note that I, by convention, wrap my variables in %% to make them
; stand out.  but any non-keyword, non-nil symbol can be a variable.


; and now we want to support rewriting function definitions:

; for "export"
;
; looks up a function definition, returning it in an error triple
(defun get-defun (name state)
  (let*
   ((ev-wrld (acl2::decode-logical-name name (w state)))
    (cltl-command
     (and ev-wrld
          (let ((cltl-cmd (getprop 'cltl-command 'global-value
                                   nil 'current-acl2-world ev-wrld)))
            (and (consp cltl-cmd)
                 (equal (car cltl-cmd) 'defuns)
                 (= (len cltl-cmd) 4)
                 cltl-cmd)))))
   (and cltl-command
        (let* ((mode (second cltl-command))
               (defuns-body (fourth cltl-command))
               (ll (cadr defuns-body))
               (tail (cddr defuns-body))
               (stobjs (remove nil (getprop name 'stobjs-in
                                            nil 'current-acl2-world ev-wrld)))
               (dec `(declare (xargs :mode ,mode
                                     :stobjs ,stobjs))))
           `(defun ,name ,ll ,dec . ,tail)))))


; for "export"
;
; compute the ,defun-like event to execute if we want to define ,dst to be
; like ,src except for rewriting the code according to ,rwdef.
;
; ,src and ,dst may certainly be the same
;
; as mentioned above, ,rwdef is applied to the body in a singleton list;
; e.g. (defun x (v) (y v)) applies rwdef to ((y v)), so if we want to, for
; example, put a let around the body, we would use either
;  (:pat (%body%)
;   :repl ((let (...) %body%))
;   :vars %body%)
; or
;  (:pat %bodycons%
;   :repl ((let (...) . %bodycons%))  ; notice the dot!
;   :vars %bodycons%)
; or
;  (:carpat %body%
;   :repl (let (...) %body%)
;   :vars %body%)
(defun compute-copy-defun+rewrite (src dst rwdef defun-like state)
  (if (and (null rwdef) (eq src dst))
    (value '(value-triple :nothing-to-do))
    (let*
     ((src-defun (get-defun src state)))
     (if src-defun
       (value
        (let* ((tuple (cddr src-defun)) ; remove 'defun and name
               (bodycons (last tuple))
               (tuple-no-body (butlast tuple 1)))
          (if (null rwdef)
            (list* defun-like dst tuple)
            `(make-event
              (er-let* ((b2 (er-rewrite-form ',bodycons . ,rwdef)))
                (value `(,',defun-like ,',dst ,@',tuple-no-body . ,b2)))))))
       (er soft 'compute-copy-defun+rewrite
           "Illegal or missing defun for ~x0." src)))))


; for "export"
;
; asserts that the definition of a function at certify-book time
; time matches that at include-book time.  this is an extra check that
; can be useful in the presence of redefinitions.
(defmacro assert-include-defun-matches-certify-defun (name)
  (declare (xargs :guard (symbolp name)))
  `(make-event
    `(acl2::assert-event
      (let ((certify-time-defun ',(get-defun ',name state))
            (include-time-defun (get-defun ',',name state)))
        (equal certify-time-defun include-time-defun))
      :on-skip-proofs t)))



; for "export"
;
; defun ,dst to be like ,src except for rewriting the code according to
; ,rewrite-spec
;
; ,src and ,dst may be the same (if redefinition allowed)
;
; see compute-copy-defun+rewrite for more info
;
(defmacro copy-defun+rewrite (src dst &rest rewrite-spec)
  (declare (xargs :guard (and (symbolp src)
                              (symbolp dst))))
  `(progn
    (assert-include-defun-matches-certify-defun ,src)
    (make-event (compute-copy-defun+rewrite
                 ',src ',dst ',rewrite-spec 'defun state))))


; for "export"
;
; defun ,dst to be like ,src
;
; ,src and ,dst may be the same (if redefinition allowed)
;
; see compute-copy-defun+rewrite for more info
;
(defmacro copy-defun (src dst)
  `(copy-defun+rewrite ,src ,dst))
