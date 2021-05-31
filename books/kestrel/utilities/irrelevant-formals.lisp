; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(program)

(defun translate1-simple-cmp (lst ctx wrld state-vars acc)

; We translate for logic, not execution.

  (cond
   ((endp lst) (value-cmp (reverse acc)))
   (t (mv-let (erp x bindings)
        (translate1-cmp (car lst)
                        t   ; stobjs-out
                        nil ; bindings
                        t   ; known-stobjs
                        ctx wrld state-vars)
        (declare (ignore bindings))
        (cond (erp (mv erp x))
              (t (translate1-simple-cmp (cdr lst) ctx wrld state-vars
                                        (cons x acc))))))))

(defun get-measures-simple-1 (edcls)

; This is a simple, non-checking version of ACL2 source function get-measures1.

  (cond ((null edcls) *no-measure*)
        ((eq (caar edcls) 'xargs)
         (let ((temp (assoc-keyword :MEASURE (cdar edcls))))
           (cond ((null temp)
                  (get-measures-simple-1 (cdr edcls)))
                 (t (cadr temp)))))
        (t (get-measures-simple-1 (cdr edcls)))))

(defun get-measures-simple (fives)

; This is a simple, non-checking version of ACL2 source function get-measures.

  (cond ((endp fives) nil)
        (t (cons (get-measures-simple-1 (fourth (car fives)))
                 (get-measures-simple (cdr fives))))))

(defun irrelevant-formals-msg-from-def-lst (def-lst ctx wrld state-vars rawp)

; This function is modeled after ACL2 source function chk-acceptable-defuns,
; but here we do only minimal checks and return a context-message pair, that
; is, multiple values of the form (mv ctx x).  See the Essay on Context-message
; Pairs (cmp).

; Warning: This function is not affected by set-irrelevant-formals-ok.  See
; chk-irrelevant-formals for how to accommodate the :irrelevant-formals-ok
; entry in the acl2-defaults-table.

  (er-let*-cmp
   ((fives

; As noted in ACL2 source function chk-acceptable-defuns, fives is a list of
; five-tuples each of the form (name args doc edcls body).

     (chk-defuns-tuples-cmp def-lst nil ctx wrld))
    (names (value-cmp (strip-cars fives)))
    (ignore ; just doing a check here
     (chk-no-duplicate-defuns-cmp names ctx)))
   (let* ((measures (get-measures-simple def-lst))
          (arglists (strip-cadrs fives))
          (stobjs-in-lst ; we will be translating for logic, not execution
           (arglists-to-nils arglists))
          (wrld2

; We extend the world for the new names as in chk-acceptable-defuns1.  We treat
; them all as :program mode because that's simplest; for purposes of checking
; irrelevant-formals, there's presumably no need to be concerned about the
; defun-mode (in particular, whether a logic-mode function is calling a
; program-mode function).

           (store-stobjs-ins names stobjs-in-lst
                             (putprop-x-lst2
                              names 'formals arglists
                              (putprop-x-lst1
                               names 'symbol-class :program
                               wrld))))
          (guards (get-guards fives nil nil wrld))
          (ignores (get-ignores fives))
          (ignorables (get-ignorables fives))
          (ubodies (get-bodies fives))
          (irrelevants-alist (get-irrelevants-alist fives)))
     (er-let*-cmp
      ((bodies

; We translate the bodies for logic rather than execution.  We could use
; translate-bodies1 instead, but then we would need to compute non-executablep
; and known-stobjs-lst.  That would likely involve refactoring the basic ACL2
; source utility, get-unambiguous-xargs-flg, so that we can get a
; context-message pair when computing non-executablep; similarly for
; get-stobjs-in-lst.  While that isn't difficult, it also isn't necessary here;
; note that there are many other checks that we are skipping, not merely
; executability of the defun bodies (see chk-acceptable-defuns and its
; supporting functions).  Our goal is just to detect problems with
; irrelevant-formals.

        (translate1-simple-cmp ubodies ctx wrld2 state-vars nil)))
      (value-cmp (chk-irrelevant-formals-msg names arglists guards

; We treat :split-types as nil, since the irrelevant-formals computation is
; seeded the same regardless of the use of :split-types.

                                             nil ; split-types-terms
                                             measures ignores ignorables
                                             irrelevants-alist bodies
                                             rawp))))))

(defconst *defun-macros* '(defun defund defun-nx defund-nx
                                 defun$ defunt
                                 defun-inline defund-inline
                                 defun-notinline defund-notinline))

(defun defuns-p (x)

; Recognize (defun ...) and ((defun ...) (defun ...) ... (defun ...)).

  (declare (xargs :guard t))
  (or (and (true-listp x)
           (member-eq (car x) *defun-macros*))
      (and (true-list-listp x)
           (subsetp-eq (strip-cars x) *defun-macros*))))

(defun def-listp-from-defuns-p (x)

; Convert a defuns-p into a def-lst, i.e., a list of definitions without the
; leading 'defun.

  (declare (xargs :guard (defuns-p x)))
  (cond ((symbolp (car x))
         (list (cdr x)))
        (t (strip-cdrs x))))

(defmacro irrelevant-formals-ok (def-or-defs &key wrld ctx statep action)
  `(let ((def-lst (def-listp-from-defuns-p ,def-or-defs))
         (ctx0 ,(or ctx ''irrelevant-formals-ok))
         (wrld ,(or wrld '(w state)))
         (state-vars ,(if statep
                          '(default-state-vars t)
                        '(default-state-vars nil)))
         (action ,action))
     (prog2$
      (or (member-eq action '(:none nil :raw :error))
          (er hard 'irrelevant-formals-ok
              "The value of :action must be one of ~v0."
              '(:none nil :raw :error)))
      (mv-let (ctx msg)
        (irrelevant-formals-msg-from-def-lst def-lst ctx0 wrld state-vars
                                             (eq action :raw))
        (cond ((eq action :none) (not (or ctx msg)))
              (ctx (er hard ctx "~@0" msg)) ; error before irrelevance check
              ((null msg) t)
              ((null action) nil)
              ((eq action :raw) msg) ; a list of two lists, not a message
              (t (assert$ (eq action :error)
                          (er hard ctx0 "~@0" msg))))))))

(defmacro chk-irrelevant-formals-ok (def-or-defs)
  `(let* ((def-lst (def-listp-from-defuns-p ,def-or-defs))
          (ctx (cons 'chk-irrelevant-formals-ok def-lst)))
     (mv-let (erp msg)
       (irrelevant-formals-msg-from-def-lst def-lst
                                            ctx
                                            (w state)
                                            (default-state-vars t)
                                            nil)
       (if (or erp msg)
           (er soft ctx "~@0" msg)
         (value t)))))

(defxdoc irrelevant-formals-ok
  :parents (irrelevant-formals system-utilities-non-built-in)
  :short "Determine whether @(see irrelevant-formals) are OK in definitions."
  :long "<p>This utility returns a Boolean.  For a related utility that can
 cause an error, see @(see chk-irrelevant-formals-ok).</p>

 @({
 General Form:

 (irrelevant-formals-ok
  def-or-defs ; a definition or a list of definitions
  &key
  wrld   ; ACL2 world; default is (w state)
  ctx    ; a ctxp to use in error messages; default is 'irrelevant-formals-ok
  statep ; take certain defaults from state when statep is true; default is nil
  action ; nil (default) - no error when irrelevance check fails
         ; :none         - no error, ever (even for ill-formed defuns)
         ; :raw          - return lists showing failure (see below)
         ; :error        - cause an error if any check fails
  )
 })

 <p>where all arguments are evaluated and the keyword arguments are as
 described above.  This utility returns @('t') when @(see irrelevant-formals)
 checking passes, and @('nil') when that check fails &mdash; except, as
 discussed in comments above, when keyword @(':action') has a non-@('nil')
 value.  Any keyword argument of @('nil') is treated the same as when that
 keyword is missing.</p>

 @({
 Example Forms:

 ; This returns T, but instead returns NIL if any variables in the
 ; IRRELEVANT declaration are omitted:
 (irrelevant-formals-ok
  '((defun f (x0 x1 x2 x3 x4 x5)
      (declare (irrelevant x1 x3 x5 x4)
               (xargs :guard (natp x2)))
      (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil))))

 ; This returns NIL because y is an irrelevant formal:
 (irrelevant-formals-ok
  '((defun f1 (x y)
      (if (consp x) (f2 (cdr x) y) t))
    (defun f2 (x y)
      (if (consp x) (f1 (cdr x) y) nil))))

 ; This is as just above, but because of the missing argument in the
 ; call of f2 in the body of f1, a translation error occurs:
 (irrelevant-formals-ok
  '((defun f1 (x y)
      (if (consp x) (f2 (cdr x)) t))
    (defun f2 (x y)
      (if (consp x) (f1 (cdr x) y) nil))))

 ; Because of the :action argument below, we get an error from the
 ; irrelevance check even though translation and other checks are
 ; successful:
 (irrelevant-formals-ok
  '((defun f1 (x y)
      (if (consp x) (f2 (cdr x) y) t))
    (defun f2 (x y)
      (if (consp x) (f1 (cdr x) y) nil)))
  :action :error)
 })

 <p>When keyword @(':action') is @(':raw') and the @(see irrelevant-formals)
 check fails, a list of two lists is returned: a list the associates each key,
 a function name, with the of the formals of that function that are declared
 irrelevant but are not; and a list of slots @('(function-name formal-position
 . formal-name)'), where the positions are zero-based, for the formals that are
 irrelevant but not declared so.  Here is an example.</p>

 @({
 ACL2 !>(irrelevant-formals-ok
         '((defun f1 (x y z)
             (declare (irrelevant z))
             (if (consp x) (f2 (cdr x) y z) z))
           (defun f2 (x y z)
             (if (consp x) (f1 (cdr x) y z) nil)))
         :action :raw)
 (((F1 Z)) ((F1 1 . Y) (F2 1 . Y)))
 ACL2 !>
 })

 <p>Remarks.</p>

 <ul>

 <li>The use of @(tsee set-irrelevant-formals-ok) has no effect on the result;
 that is, the value of @(':irrelevant-formals-ok') in the @(tsee
 acl2-defaults-table) does not affect this utility.</li>

 <li>Each definition must be a call of a macro in the following list:
 @(`*defun-macros*`).</li>

 <li>As noted above, an error occurs by default if the given definitions are
 determined to be ill-formed.  However, only some of the usual checks for
 @(tsee defun) events are performed; for example, the bodies are translated
 only for logic, not executability, and only partial checks are made for the
 @(see declare) forms.  The point of this tool is to perform @(see
 irrelevant-formals) checks, not to do complete checks for the given
 forms.</li>

 </ul>")

(defxdoc chk-irrelevant-formals-ok
  :parents (irrelevant-formals system-utilities-non-built-in)
  :short "Determine whether @(see irrelevant-formals) are OK in definitions."
  :long "<p>As discussed below, this variant of the utility @(tsee
  irrelevant-formals-ok) returns an @(see error-triple).</p>

 @({General Form:

 (irrelevant-formals-ok def-or-defs)
 })

 <p>where @('def-or-defs') evaluates to a definition or a list of definitions.
 Each definition must be a call of a macro in the following list:
 @(`*defun-macros*`).</p>

 @({
 Example Form:

 (chk-irrelevant-formals-ok
  '((defun f (x0 x1 x2 x3 x4 x5)
      (declare (irrelevant x1 x3 x5 x4)
               (xargs :guard (natp x2)))
      (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil))))
 })

 <p>See @(see irrelevant-formals-ok) for a utility that makes the same check as
 this one, except that it returns a single value or a hard error.  By contrast,
 @('chk-irrelevant-formals-ok') returns an @(see error-triple), which is @('(mv
 nil t state)') when the @(see irrelevant-formals) check passes for the given
 definition or list of definitions, and otherwise returns a soft error as in
 @('(er soft ...)').</p>")
