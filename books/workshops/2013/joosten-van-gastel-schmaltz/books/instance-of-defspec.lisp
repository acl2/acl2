#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")
(include-book "make-event/defspec" :dir :system) ; get the function "constraint"

(defun get-defun-wrld (name wrld)  ; used by copyfun to lookup a function in the world
  (declare (xargs :mode :program)) ; for use of ACL2::DECODE-LOGICAL-NAME
  (let*
    ((ev-wrld (acl2::decode-logical-name name wrld))
     (cltl-command
      (and ev-wrld ; some code taken from the :pe function
           (let ((cltl-cmd (getprop 'cltl-command 'global-value
                                    nil 'current-acl2-world ev-wrld)))
             (and (consp cltl-cmd)
                  (equal (car cltl-cmd) 'defuns)
                  (= (len cltl-cmd) 4)
                  cltl-cmd)))))
    (and cltl-command
         (let* ((defuns-body (fourth cltl-command))
                (ll (cadr defuns-body))
                (tail (cddr defuns-body))
                ; commented for redundancy: it is already in the variable `tail'
                ;(mode (second cltl-command))
                ;(stobjs (remove nil (getprop name 'stobjs-in
                ;                             nil 'current-acl2-world ev-wrld)))
                ;(dec `(declare (xargs :mode ,mode
                ;                      :stobjs ,stobjs)))
                )
           `(defun ,name ,ll  . ,tail)))))
; (get-defun-wrld 'get-defun-wrld (w state))

(defun replace-arguments (lst replacements) ; replace function arguments in a list of function calls
  (declare (xargs :guard (and (ALISTP replacements))))
  (if (atom lst) lst
    (let* ((x  (car lst))
           (replacement (assoc-equal x replacements)))
      (cons (if replacement (cdr replacement)
              (if (atom x) x (cons (car x) (replace-arguments (cdr x) replacements))))
            (replace-arguments (cdr lst) replacements)))))

; replace the function symbol according to the replacement list r
; that is: (f a b) becomes (g a b) if (f g) is an element of r
; in case the first element of fn is not a first element of r,
; rewrites lambda functions for one step, that is:
; replaces (f a b) for (g c a b) if (f (lambda (d e) (g c d e))) is an element of r
(defun replace-atom (r fn)
  (cond ((or (atom r) (atom fn)) fn)
        (t (if (equal (car fn) (car (car r)))
             (let* ((f (cadr (car r)))
                    (is-lambda (and (consp f) (eql 'lambda (car f))))
                    (values (cdr fn))
                    (val (if is-lambda (car (replace-arguments (list (caddr f)) (pairlis$ (cadr f) values))) (cons f values))))
               val)
             (replace-atom (cdr r) fn)))))

; iterate over the function to do perform this replacement
(defun replacefns (r fn)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section replacefns
; Replace function occurences in an expression.~/
; The function replaces only function occurences. Variables are left as-is.
;
; Example use:
;   :replacefns ((foo bar) (bar foo) (x z)) ((+ (foo x y) (bar x y)))
; Replaces bar with foo and foo with bar, and leaves x untouched
; since it is only used as a variable. Return value:
;   ((+ (BAR X Y) (FOO X Y)))~/
; Assumes there are no macros.
; The function is defined guardless.
; The first argument should be a list of lists of length 2. Less than that gives
; an error, further arguments will be ignored.
; The second argument should be a list of terms.
; Every element will undergo the replacement.
;
; Should handle lambda expressions too:
; :replacefns ((foo bar) (bar foo)) ((+ ((lambda (foo j) (foo foo j)) x y) (bar x y)))
; "
  (cond ((atom fn) fn) ; which is probably NIL, but we stick with the original if not
        (t (cons (if (atom (car fn)) (car fn)
                   (if (consp (caar fn)) ; when a cons is used at the place of a function, it must be a lambda expression
                     (if (and (eq 'lambda (caaar fn))
                              (consp (cdaar fn))
                              (symbol-listp (cadaar fn))
                              (consp (cddaar fn))
                              (null (cdr (cddaar fn))))
                       `((lambda ,(cadaar fn) . ,(replacefns r (cddaar fn))) . ,(replacefns r (cdar fn)))
                       (er hard? 'replacefns "Not a valid term: ~x0. Does your term still include macro's?" (car fn)))
                     ; in other cases: it is a plain function. Replace it.
                     (replace-atom r (cons (caar fn) (replacefns r (cdar fn))))))
                  (replacefns r (cdr fn))))))

; copy a function by looking it up in the world
; we need state to be able to call TRANSLATE1
(defun copyfun-fn (old new-construct replacements state)
  (declare (xargs :mode :program :stobjs (state)))
  (let*
    ((is-lambda (and (consp new-construct) (eql 'lambda (car new-construct))))
     (new (if is-lambda (caaddr new-construct) new-construct))
     (src-defun (get-defun-wrld old (w state)))
     (defun-like (car src-defun))
     (tuple (cddr src-defun)) ; remove 'defun and name
     (original-args (car tuple))
     (args (if is-lambda (cdaddr new-construct) original-args))
     (lambda-args (if is-lambda (cadr new-construct) original-args))
     (tuple-no-body (butlast (cdr tuple) 1))
     (reps (cons (list old new-construct) replacements)))
    (if (and (subsetp original-args args) (equal lambda-args original-args))
      (MV-LET
       (FLG BODYCONS BINDINGS STATE)
       (TRANSLATE1 (car (last tuple)) :STOBJS-OUT ; does roughly the same as :trans
                   '((:STOBJS-OUT . :STOBJS-OUT))
                   T 'TOP-LEVEL
                   (W STATE) STATE)
       (declare (ignore flg bindings))
       ;(mv-let (bodycons erp state) (trans-fn  state)
       (mv nil (append `(,defun-like ,new ,args) tuple-no-body (replacefns reps (list bodycons))) state)
       )
      (if (equal lambda-args original-args)
        (er soft 'copyfun "The arguments provided in the lambda construct ~x0 are ~x1, of which these original arguments should be a subset: ~x2" new-construct args original-args)
        (er soft 'copyfun "The lambda construct ~x0 takes as input ~x1, which should be an exact match of the original arguments of the original function: ~x2" new-construct lambda-args original-args)
      ))
    ))

; took and rewrote the definition of compute-copy-defun+rewrite in hacking/rewrite-code
; since I cannot conveniently work with er-rewrite-form
; note that this function will accept allmost any definition without errors
; it is your responsibility to call it with a function name as first argument
(defmacro copyfun (old new &optional replacements)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section copyfun
; Copy and rename a function.~/
; You may optionally replace function occurences in the old function.
; This should at least be done for recursive functions.
;
; Example use:
;   (copyfun 'true-listp 'vrai-listep '((true-listp vrai-listep)))
;
; This will create a recursive function vrai-listep identical to true-listp.
; Replacements are performed via ~c[replacefns]. See :DOC REPLACEFNS.
; ~/
; This macro is inspired on compute-copy-defun+rewrite in hacking/rewrite-code.
; It uses state information to retrieve the old function, and writes to the state
; by defining a new one. You can use this macro without distroying certifiability.
;
; This function can be used to mimic generic functions, for example, the \"map\":
;
; (encapsulate ((dummy (a) t))
;   (local (defun dummy (a) a))
; )
; (defun map-dummy (as)
; (if (consp as) (cons (dummy (car as)) (map-dummy (cdr as))) nil))
; (copyfun map-dummy map-car ((dummy car)))
; (copyfun map-dummy map-cadr ((dummy cadr)))
; (copyfun map-dummy (lambda (as) (map-cons as b)) ((dummy (lambda (a) (cons a b)))))"
  `(make-event (copyfun-fn ',old ',new ',replacements state)))

(defun used-in (fn search)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section used-in
; Check whether a function is used in one of a list of expressions.~/
; Assumes there are no macros.
; TODO Bug: Does not handle lambda-expressions well.
; ~/
; Examples:
;
; :used-in f ((+ x (f y)))
;   T
; :used-in x ((+ x (f y)))
;   NIL (x is not a function here)
; :used-in + ((+ x (f y)))
;   T   (even though + is a macro, it was not expanded here)
; :used-in + (+ x (f y))
;   NIL (+ is a symbol, it is the first occurence in the list of expressions.)
; :used-in + ((+) (x) (f y))
;   T"
  (DECLARE (XARGS :GUARD (AND (SYMBOLP fn))))
  (cond ((atom search) nil)
        ((atom (car search)) (used-in fn (cdr search)))
        (t (if (equal fn (car (car search))) t
             (or
              (used-in fn (car search))
              (used-in fn (cdr search))
              )))))

(DEFUN get-Derived-funs-From (FUN ignorelist WORLD-ALIST)
  ;(declare (xargs :mode :program))

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section get-Derived-funs-From
; Get all functions depending on a function.~/
;
; get-Derived-funs-From FUN ignorelist (w state)
;
; If you add a function name to the ignorelist, it will not be searched
; for occurences of FUN.~/
; This function will iterate until it has found the definition of FUN.
; After this, the search is terminated. So this function assumes that there
; are no functions defined using FUN when FUN itself was not defined.
; I am not sure about mutual recurrence functions here.. they can probably cause
; this function to return incorrect results.
; See also: get-Derived-funs
; "
  (COND ((ENDP WORLD-ALIST) nil) ;we hit the end of the world. Exit
        ((AND (EQ fun (CAAR WORLD-ALIST))
              (EQ 'ABSOLUTE-EVENT-NUMBER (CADAR WORLD-ALIST)))
         nil) ;we hit the definitional part of the function we're looking for. Exit
        ((and (eq 'def-bodies (CADAR WORLD-ALIST))
              (not (member (CAAR WORLD-ALIST) ignorelist))
              (used-in fun (caar (cddar world-alist))))
         (cons (caar world-alist) (get-Derived-funs-From fun ignorelist (cdr world-alist))))
        (T (get-Derived-funs-From fun ignorelist (CDR WORLD-ALIST)))))

(defun get-Derived-funs (funs derived wrld)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section get-Derived-funs
; Perform get-Derived-funs-From recursively.~/
;
; get-Derived-funs-From FUNS DERIVED (w state)
;
; Returns DERIVED and all functions depending on a function in FUNS,
; possibly in multiple steps. For instance:
; (defun f (x) x)
; (defun g (x) (f x))
; (defun h (x) (g x))
; (get-Derived-funs-From '(h) NIL (w state))
; will return all three functions.
; ~/
; This function will at least return what is listed in DERIVED.
; It is defined using get-Derived-funs-From.
; "
  ; the function terminates, but this is difficult to prove.
  ; the argument used is that the set 'funs - derived' is decreasing.
  ; (where - is the set-minus)
  ;
  ; since this is just a helper function for generating macro's,
  ; we simply don't bother adding it to the logical world.
  ;
  ; we can be more efficient by using the used-in-oneof defuns defined below.
  ; That way we would only have to go through the world once at the cost of
  ; maybe missing some mutually recursive functions.
  (declare (xargs :mode :program
            ))
  (if (atom funs) derived
    (let
      ((newderived (get-Derived-funs-From (car funs) derived wrld)))
      (get-Derived-funs (remove-duplicates (append (cdr funs) newderived))
                        (remove-duplicates (append derived newderived))
                        wrld)
      )))

(defun used-in-oneof (fns search)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section used-in-oneof
; Check whether any of a list of functions is used in any of a list of expressions.~/
; Examples:
;
; :used-in-oneof (f) ((+ x (f y)))
;   T (f is used)
; :used-in-oneof (x) ((+ x (f y)))
;   NIL (x is not a function here)
; :used-in-oneof (f x) ((+ x (f y)))
;   T (x is not used, but f is)~/
; Assumes there are no macro's; TODO: does not handle lambda-expressions well.
; See also: used-in"
  (cond ((atom search) nil)
        ((atom (car search)) (used-in-oneof fns (cdr search)))
        (t (if (member (car (car search)) fns) t
             (or
              (used-in-oneof fns (car search))
              (used-in-oneof fns (cdr search))
              )))))

; repeatedly perform used-in-oneof
(defun used-in-oneof-filter (fns searches)
  (if (atom searches) nil
    (if (used-in-oneof fns (car searches))
      (cons (car searches) (used-in-oneof-filter fns (cdr searches)))
      (used-in-oneof-filter fns (cdr searches)))))

(defun get-Derived-theorems (symbs endcondition world-alist res-with-class
                                   res-without-class)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section get-Derived-theorems
; Get all theorems saying something about some functions.~/
;
; get-Derived-theorems FUNS ENDAT (w state)
;
; Returns a list of lemmas that contain any of FUNS.
; You may use some event label at ENDAT to shorten the search.
; ~/
; Returns the translated theorems as how they are stored in the world.
; "
  (DECLARE (XARGS :measure (len world-alist)))
  (COND ((ENDP WORLD-ALIST) res-with-class)
        ((AND (ENDP SYMBS) (ENDP res-without-class)) res-with-class)
        ((EQ 'ABSOLUTE-EVENT-NUMBER (CADAR WORLD-ALIST))
         (if (EQ endcondition (CAAR WORLD-ALIST)) res-with-class
           (get-Derived-theorems symbs ENDCONDITION (CDR WORLD-ALIST) res-with-class res-without-class)))
        ((EQ 'THEOREM (cadar WORLD-ALIST))
         (get-derived-theorems symbs ENDCONDITION (CDR WORLD-ALIST) res-with-class
                               (if (used-in-oneOf symbs (CDDAR WORLD-ALIST))
                                (cons
                                  `(,(CAAR WORLD-ALIST) ,(CDDAR WORLD-ALIST))
                                  res-without-class)
                                res-without-class)))
        (T
         (LET* ((itm (if (EQ 'CLASSES (cadar WORLD-ALIST)) (ASSOC (CAAR WORLD-ALIST) res-without-class) nil)))
           (if itm
             (get-derived-theorems symbs ENDCONDITION (CDR WORLD-ALIST) (cons `(,(car itm) ,(cadr itm) ,(cddar WORLD-ALIST)) res-with-class)
                                   (remove itm res-without-class))
             (get-derived-theorems symbs endcondition (CDR WORLD-ALIST) res-with-class res-without-class))))))

; pick a substitution (if there is one) for subAll
(defun subAll-pick (name newname changeby)
  (if (atom changeby) (list name newname)
    (if (equal (caar changeby) name)
      (car changeby)
      (subAll-pick name newname (cdr changeby)))))

(defun subAll (names pf ALTERNATIVES)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section subAll
; Create substitution names using a prefix. Does not perform the substitution~/
;
; subAll NAMES PREFIX ALTERNATIVES
;
; Returns a list of lists of length two.
; The first element being an item from NAMES.
; The second is the same, prefixed by PREFIX.
; If the element occurs in ALTERNATIVES, this alternative is used instead.
; ~/
; Example:
;  :subAll (a b c) (x) (b Y)
;  ((A X-A) (B Y) (C X-C))
; "
  (cond ((atom names) nil)
        (t (cons (subAll-pick
                  (car names) (packn (list pf '- (car names)))
                  ALTERNATIVES
                  )
                 (subAll (cdr names) pf ALTERNATIVES)))))

; concatenate copyfun-fn results
(defun map-copyfun (subs repls state)
  (declare (xargs :mode :program :stobjs (state)))
  (cond ((atom subs) (mv nil nil state))
        (t (mv-let (er fn state) (copyfun-fn (caar subs) (cadar subs) repls state)
                   (mv-let (er2 rst state) (map-copyfun (cdr subs) repls state)
                           (mv (append er er2) (cons fn rst) state))))))

; copy a theorem, make sure the hint is such that it never fails
(defun copythm (definstance oldthm oldname newname reps funs rule-classes)
  ;(DECLARE (ignore funs)) ; might be needed if you wish to change the hints
  (let* ((usestmt (cons ':functional-instance (cons oldname reps)))
         (thm (replacefns reps oldthm))
         )
    `(defthm
     ,newname
     ,thm
     :hints (("Goal" :use (,usestmt) :in-theory ',funs)
             '(:use ,definstance :in-theory ',funs))
     :RULE-CLASSES ,(replacefns reps rule-classes)
     )))

; some theorems might be split into parts. For example: (implies (something) (and (prop1) (prop2) (prop3)))
; Instead of putting them back together, we generate new names for other parts.
; first, a helper function:
(defun numerate-name (taken i new)
  (declare (xargs :measure (len taken)))
  (let* ((newname (packn (list new '- i)))
        (newtaken (remove newname taken))
        )
    (if (> (len taken) (len newtaken)) (numerate-name newtaken (+ i 1) new) newname)))
; and perform the disambiguation
(defun disamb-name (newname takennames)
  (if (member newname takennames) (numerate-name takennames 1 newname) newname))
; note that we do not check the world for duplicate names.
; The downside is that the user has to be aware of this, but he should be anyways when defining theorems himself.
; The upside is that in case two identical defspec-reuses are performed, events will be identical and thus redundant.

(defun map-copythm (definstance thms prefix reps funs takennames)
  (if (atom thms) nil
    (let* ((ct (car thms))
           (name (nth 0 ct))
           (rule-classes (nth 2 ct))
           (thm (nth 1 ct))
           (newname (disamb-name (packn (list prefix '- name)) takennames))
           (next (map-copythm definstance (cdr thms) prefix reps funs (cons newname takennames)))
           )
        (cons (copythm definstance
                       thm
                       name
                       newname
                       reps
                       funs
                       rule-classes
                       )
              next
        ))))

; Matt K.: Added the following verify-termination calls, which are necessary
; for find-encapsulate; see the comment there about "Modified by Matt K. to
; use...".

(verify-termination >=-len)
(verify-termination all->=-len)
(verify-termination strip-cadrs)
(verify-termination signature-fns)
(verify-termination access-event-tuple-type)
(verify-termination access-event-tuple-namex)

(defun find-encapsulate (wrld)

; Modified by Matt K. 10/15/2015 to use the abstractions
; access-event-tuple-type and access-event-tuple-namex, whose definitions are
; about to change and could change again in the future.

  (if (endp wrld) nil
    (let*
      ((ev (car wrld)))
      (if (and (eq (car ev) 'EVENT-LANDMARK)
               (eq (cadr ev) 'GLOBAL-VALUE)
               (eq (access-event-tuple-type (cddr ev))
                   'ENCAPSULATE))
        (access-event-tuple-namex (cddr ev))
        (find-encapsulate (cdr wrld))
        ))))

; remove duplicate occurences while ignoring the car of the list.
; Used for theorems, such that only one of two differently named theorems for the same lemma will be used.
; Useful in case one theorems is: (and a b), while the other is: (and b c)
; This ensures the theorem for b is only given once
(defun remove-duplicates-on-cdr (l)
  (DECLARE (XARGS :GUARD (ALISTP L)))
  (COND ((ENDP L) NIL)
        ((MEMBER-EQUAL (cdr (CAR L)) (strip-cdrs (CDR L)))
         (REMOVE-DUPLICATES-on-cdr (CDR L)))
        (T (CONS (CAR L)
                 (REMOVE-DUPLICATES-on-cdr (CDR L))))))

(defun get-fun-names (lst)
  (if (endp lst) nil
    (cons (if (atom (car lst)) (car lst)
            (caar (cddar lst))) (get-fun-names (cdr lst)))))

(defun instanceOf-defspec-fn (specname prefix rename hints otf-flg state)
  (declare (xargs :mode :program :stobjs (state)))
  (LET*
    ((wrld (w state))
     (encapsulated-functions (find-encapsulate (acl2::decode-logical-name specname wrld)))
     (function-substitutions (subAll encapsulated-functions prefix rename))
     (derived-functions (get-Derived-funs encapsulated-functions nil wrld))
     (derived-function-substitutions (subAll derived-functions prefix rename)))
    (mv-let (er defuns state)
            (map-copyfun derived-function-substitutions (append function-substitutions derived-function-substitutions) state)
            (let* ((definstance-name (packn (list prefix '- specname)))
                   (newfuns (get-fun-names (strip-cadrs derived-function-substitutions)))
                   (defthms (map-copythm definstance-name (get-derived-theorems (append encapsulated-functions derived-functions) specname wrld nil nil)
                                         prefix (append function-substitutions derived-function-substitutions) newfuns newfuns))
                   )
              (MV er (cons 'progn (append (cons `(definstance ,specname
                                                   ,definstance-name
                                                   :functional-substitution
                                                   ,function-substitutions
                                                   :otf-flg ,otf-flg
                                                   :hints ,hints
                                                   ) defuns)
                                          defthms
                                   )) state)
              ))))
(defmacro instance-Of-defspec (spec prefix &optional rename &key hints otf-flg)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section instance-Of-defspec
; Reuse what is outside a defspec.~/
; Usage
; (instanceOf-defspec specname prefix)
; or
; (instanceOf-defspec specname prefix rename)
;
; Will use all functions in the defspec specname, prefixed with prefix.
; For example: fun will be instantiated with prefix-fun.
; If you wish to, you can supply the optional rename argument '((fun newfun))
; to instantiate fun with newfun.
;
; All functions and theorems that are currently in scope and depend on the defspec
; will be duplicated (prefixed with prefix or renamed as rename).
; ~/
; For example use, see the file closedMonoid.lisp
; "
  `(make-event (instanceOf-defspec-fn ',spec ',prefix ,rename ',hints ',otf-flg state) :check-expansion nil))

; get all constraints of a set of functions
(defun map-constraint (funs wrld)
  (declare (xargs :mode :program)) ; constraint is a :program
  (if (atom funs) nil
    (cons (constraint (car funs) wrld) (map-constraint (cdr funs) wrld))))
; think up a set of names for unnamed theorems
(defun namethms (thms nm i)
  (if (atom thms) nil
  (cons `(defthm ,(packn (list nm '- i)) ,(car thms)) (namethms (cdr thms) nm (1+ i)))))
; get the specification constraints, see is-a
(defun oldspec (specname thmname prefix rename wrld)
  (declare (xargs :mode :program))
  (LET*
    ((WRLD1 (acl2::decode-logical-name specname WRLD))
     (funs (find-encapsulate wrld1))
     ;(funs (strip-cars (cadddr ls)))
     (function-substitutions (subAll funs prefix rename))
     (constraints (remove-duplicates (map-constraint funs wrld)))
     (namedthms (remove-duplicates (namethms (replacefns function-substitutions constraints) thmname 0)))
     )
     namedthms
  ))
(defmacro is-a (specname prefix thmname &optional rename)

;;; This legacy doc string was replaced Nov. 2014 by the corresponding
;;; auto-generated defxdoc form in the last part of this file.

; ":Doc-Section is-a
; Reuse what is inside a defspec.~/
; Usage
; (isa-spec specname prefix thmname)
; or
; (isa-spec specname prefix thmname rename)
;
; All theorems that are in the defspec will be put in the current scope.
; ~/
; Examples can be found in the file closedMonoid
; "
  `(make-event (cons 'progn
                  (oldspec ',specname ',thmname ',prefix ,rename (w state)))))

; this function was quite useful while debugging. Use it on a function name to see all that is known about the function.
(defmacro symbol-lemmas (name)
  `(get-derived-theorems '(,name) 't (w state) nil nil))

; this is another implementation of firstn, which is such that n-ary can be conveniently defined
; it is copied as-is from data-structures/list-defthms, but we do not want to add this book as a dependency
(DEFUN XFIRSTN (N L)
  (DECLARE (XARGS :GUARD (AND (INTEGERP N) (<= 0 N) (TRUE-LISTP L))))
  (COND ((ZP N) NIL) (T (CONS (CAR L) (XFIRSTN (1- N) (CDR L))))))
;(include-book "data-structures/list-defthms" :dir :system)
; We add some "default" anonymous functions.
; The idea is to get as much sharing as possible:
;  a "map" function, for instance, could map the function "unary-function"
;  a "foldr" could fold the function "binary-function"
; For efficiency reasons, however, we do not provide "map" and "foldr" in this book just yet.
; In fact, we try not use defspec-ed functions in this book too much! (in new function definitions, proofs, or whatsoever)
; If we do, the defspec will become slower to reuse (because of the added function definitions).
; In case of bugs in DefSpeC-reuse, it might even fail to be reused.
; This might then cause people to write their own version again, something we avoid to improve on the amount of sharing.
(defspec n-ary ((n-ary-function (x) t) (function-size () t))
  (local (defun n-ary-function (x) (car x)))
  (local (defun function-size () 1))
  (defthmd n-ary-destructor ; this theorem will probably not be applied, but this is what constitutes an n-ary function
    (equal (n-ary-function (xfirstn (function-size) x))
           (n-ary-function x)
           ))
  (defthm constant-natp ; prevent functions with a negative number of arguments. This causes difficulties defining a good Currying-mechanism.
    (and (natp (function-size))
         (integerp (function-size))
         (<= 0 (function-size))))
  )
(defspec constant ((constant-function () t))
  (local (defun constant-function () t)))
(defun constant-as-n-ary-function (x) (declare (ignore x)) (constant-function))
(instance-Of-defspec n-ary constant-as '((function-size (lambda () 0))))
(defspec unary ((unary-function (x) t))
  (local (defun unary-function (x) x)))
#| ; enable to test lemmas and congruences:
(include-book "perm")
(DEFUN for-all (lst)
  (if (endp lst) t
    (and (unary-function (car lst))
         (for-all (cdr lst)))))
(DEFTHM for-all-HOLDS-FOR-MEMBER
  (IMPLIES (AND (for-all LST)
                (MEMBER-EQUAL V LST))
           (UNARY-FUNCTION V)))
(DEFTHM PERMP-IMPLIES-EQUAL-FOR-ALL-1 ; this theorem is exactly as generated by defcong
  (IMPLIES (PERMP LST LST-EQUIV)
           (EQUAL (FOR-ALL LST)
                  (FOR-ALL LST-EQUIV)))
  :RULE-CLASSES (:CONGRUENCE)
  ) ; |# ; end of test-bit
(defun unary-as-n-ary-function (x) (unary-function (car x)))
(instance-Of-defspec n-ary unary-as '((function-size (lambda () 1))))
(defun n-ary-as-unary-function (x) (unary-function (car x)))
(instance-Of-defspec unary n-ary-as)
(defspec binary ((binary-function (x y) t))
  (local (defun binary-function (x y) (cons x y))))
(defun binary-as-n-ary-function (x) (binary-function (car x) (cadr x)))
(instance-Of-defspec n-ary binary-as '((function-size (lambda () 2))))
(defspec ternary ((ternary-function (x y z) t))
  (local (defun ternary-function (x y z) (list x y z))))
(defun ternary-as-n-ary-function (x) (ternary-function (car x) (cadr x) (caddr x)))
(instance-Of-defspec n-ary ternary-as '((function-size (lambda () 3))))#|ACL2s-ToDo-Line|#

; I think "quartary" sounds odd, plus I cannot think of any natural quartary function ("if" is a ternary one) so I will leave it at this.

; The defxdoc forms below were initially generated automatically from
; legacy documentation strings in this file.

(include-book "xdoc/top" :dir :system)

(defxdoc copyfun
  :parents (copyfun)
  :short "Copy and rename a function."
  :long "<p>You may optionally replace function occurences in the old function.
 This should at least be done for recursive functions.

 Example use:
   (copyfun 'true-listp 'vrai-listep '((true-listp vrai-listep)))

 This will create a recursive function vrai-listep identical to true-listp.
 Replacements are performed via @('replacefns'). See :DOC REPLACEFNS.</p>

 <p>This macro is inspired on compute-copy-defun+rewrite in
 hacking/rewrite-code.  It uses state information to retrieve the old function,
 and writes to the state by defining a new one. You can use this macro without
 distroying certifiability.

 This function can be used to mimic generic functions, for example, the \"map\":

 (encapsulate ((dummy (a) t))
   (local (defun dummy (a) a))
 )
 (defun map-dummy (as)
 (if (consp as) (cons (dummy (car as)) (map-dummy (cdr as))) nil))
 (copyfun map-dummy map-car ((dummy car)))
 (copyfun map-dummy map-cadr ((dummy cadr)))
 (copyfun map-dummy (lambda (as) (map-cons as b)) ((dummy (lambda (a) (cons a
 b)))))</p>")

(defxdoc get-derived-funs
  :parents (get-derived-funs)
  :short "Perform get-Derived-funs-From recursively."
  :long "<p>get-Derived-funs-From FUNS DERIVED (w state)

 Returns DERIVED and all functions depending on a function in FUNS,
 possibly in multiple steps. For instance:
 (defun f (x) x)
 (defun g (x) (f x))
 (defun h (x) (g x))
 (get-Derived-funs-From '(h) NIL (w state))
 will return all three functions.</p>

 <p>This function will at least return what is listed in DERIVED.  It is
 defined using get-Derived-funs-From.</p>")

(defxdoc get-derived-funs-from
  :parents (get-derived-funs-from)
  :short "Get all functions depending on a function."
  :long "<p>get-Derived-funs-From FUN ignorelist (w state)

 If you add a function name to the ignorelist, it will not be searched for
 occurences of FUN.</p>

 <p>This function will iterate until it has found the definition of FUN.  After
 this, the search is terminated. So this function assumes that there are no
 functions defined using FUN when FUN itself was not defined.  I am not sure
 about mutual recurrence functions here.. they can probably cause this function
 to return incorrect results.  See also: get-Derived-funs</p>")

(defxdoc get-derived-theorems
  :parents (get-derived-theorems)
  :short "Get all theorems saying something about some functions."
  :long "<p>get-Derived-theorems FUNS ENDAT (w state)

 Returns a list of lemmas that contain any of FUNS.
 You may use some event label at ENDAT to shorten the search.</p>

 <p>Returns the translated theorems as how they are stored in the world.</p>")

(defxdoc instance-of-defspec
  :parents (instance-of-defspec)
  :short "Reuse what is outside a defspec."
  :long "<p>Usage
 (instanceOf-defspec specname prefix)
 or
 (instanceOf-defspec specname prefix rename)

 Will use all functions in the defspec specname, prefixed with prefix.
 For example: fun will be instantiated with prefix-fun.
 If you wish to, you can supply the optional rename argument '((fun newfun))
 to instantiate fun with newfun.

 All functions and theorems that are currently in scope and depend on the defspec
 will be duplicated (prefixed with prefix or renamed as rename).</p>

 <p>For example use, see the file closedMonoid.lisp</p>")

(defxdoc is-a
  :parents (is-a)
  :short "Reuse what is inside a defspec."
  :long "<p>Usage
 (isa-spec specname prefix thmname)
 or
 (isa-spec specname prefix thmname rename)

 All theorems that are in the defspec will be put in the current scope.</p>

 <p>Examples can be found in the file closedMonoid</p>")

(defxdoc replacefns
  :parents (replacefns)
  :short "Replace function occurences in an expression."
  :long "<p>The function replaces only function occurences. Variables are left
 as-is.

 Example use:
   :replacefns ((foo bar) (bar foo) (x z)) ((+ (foo x y) (bar x y)))
 Replaces bar with foo and foo with bar, and leaves x untouched
 since it is only used as a variable. Return value:
   ((+ (BAR X Y) (FOO X Y)))</p>

 <p>Assumes there are no macros.  The function is defined guardless.  The first
 argument should be a list of lists of length 2. Less than that gives an error,
 further arguments will be ignored.  The second argument should be a list of
 terms.  Every element will undergo the replacement.

 Should handle lambda expressions too:
 :replacefns ((foo bar) (bar foo)) ((+ ((lambda (foo j) (foo foo j)) x y) (bar x y)))</p>")

(defxdoc suball
  :parents (suball)
  :short "Create substitution names using a prefix. Does not perform the substitution"
  :long "<p>subAll NAMES PREFIX ALTERNATIVES

 Returns a list of lists of length two.
 The first element being an item from NAMES.
 The second is the same, prefixed by PREFIX.
 If the element occurs in ALTERNATIVES, this alternative is used instead.</p>

 <p>Example: :subAll (a b c) (x) (b Y) ((A X-A) (B Y) (C X-C))</p>")

(defxdoc used-in
  :parents (used-in)
  :short "Check whether a function is used in one of a list of expressions."
  :long "<p>Assumes there are no macros.  TODO Bug: Does not handle
 lambda-expressions well.</p>

 <p>Examples:

 :used-in f ((+ x (f y)))
   T
 :used-in x ((+ x (f y)))
   NIL (x is not a function here)
 :used-in + ((+ x (f y)))
   T   (even though + is a macro, it was not expanded here)
 :used-in + (+ x (f y))
   NIL (+ is a symbol, it is the first occurence in the list of expressions.)
 :used-in + ((+) (x) (f y)) T</p>")

(defxdoc used-in-oneof
  :parents (used-in-oneof)
  :short "Check whether any of a list of functions is used in any of a list of expressions."
  :long "<p>Examples:

 :used-in-oneof (f) ((+ x (f y)))
   T (f is used)
 :used-in-oneof (x) ((+ x (f y)))
   NIL (x is not a function here)
 :used-in-oneof (f x) ((+ x (f y))) T (x is not used, but f is)</p>

 <p>Assumes there are no macro's; TODO: does not handle lambda-expressions
 well.  See also: used-in</p>")
