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

(defmacro when-allowed (kwd dcls form len default)

; This is just form if kwd is in dcls; otherwise it's a list of len filled
; filled with default.

  `(if (member-eq ,kwd ,dcls)
       ,form
     (make-list ,len :initial-element ,default)))

(defun irrelevant-slots-to-alist-1 (slots alist)
  (cond ((endp slots) alist)
        (t (irrelevant-slots-to-alist-1
            (cdr slots)
            (let ((slot (car slots)))
              (put-assoc-eq (car slot) (cddr slot) alist))))))

(defun irrelevant-slots-to-alist (names slots)
  (irrelevant-slots-to-alist-1 slots (pairlis$ names nil)))

(defun irrelevant-formals-info-from-def-lst (def-lst ctx wrld state-vars result
                                              dcls)

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
   (let* ((len (length fives))
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
          (umeasures (when-allowed :measure dcls (get-measures-simple fives)
                                   len *no-measure*))
          (uguards (when-allowed :guard dcls (get-guards fives nil nil wrld)
                                 len t))
          (ignores (when-allowed :ignore dcls (get-ignores fives)
                                 len nil))
          (ignorables (when-allowed :ignorable dcls (get-ignorables fives)
                                    len nil))
          (ubodies (get-bodies fives))
          (irrelevants-alist (if (member-eq :irrelevant dcls)
                                 (get-irrelevants-alist fives)
                               (pairlis-x2 names nil))))
     (er-let*-cmp

; We translate guards and bodies for logic rather than execution.  For guards
; we could insist on stobjs-out (nil), but we keep it simple as we do for
; bodies; we now explain why we translate bodies for logic.  We could use
; translate-bodies1 instead for the bodies, but then we would need to compute
; non-executablep and known-stobjs-lst.  That would likely involve refactoring
; the basic ACL2 source utility, get-unambiguous-xargs-flg, so that we can get
; a context-message pair when computing non-executablep; similarly for
; get-stobjs-in-lst.  While that isn't difficult, it also isn't necessary here;
; note that there are many other checks that we are skipping, not merely
; executability of the defun bodies (see chk-acceptable-defuns and its
; supporting functions).  Our goal is just to detect problems with
; irrelevant-formals.

      ((guards
        (translate1-simple-cmp uguards ctx wrld2 state-vars nil))
       (measures
        (translate1-simple-cmp umeasures ctx wrld2 state-vars nil))
       (bodies
        (translate1-simple-cmp ubodies ctx wrld2 state-vars nil))
       (val (value-cmp (chk-irrelevant-formals-msg names arglists guards

; We treat :split-types as nil, since the irrelevant-formals computation is
; seeded the same regardless of the use of :split-types.

                                                   nil ; split-types-terms
                                                   measures ignores ignorables
                                                   irrelevants-alist bodies
                                                   (or (eq result :default)
                                                       (eq result :raw))))))
      (value-cmp (if (eq result :default)
                     (if (null (cdr names))
                         (strip-cddrs (cadr val))
                       (irrelevant-slots-to-alist names (cadr val)))
                   val))))))

(defconst *defun-macros* '(defun defund defun-nx defund-nx
                                 defun$ defunt
                                 defun-inline defund-inline
                                 defun-notinline defund-notinline))

(defun defuns-p (x)

; Recognize (defun ...) and ((defun ...) (defun ...) ... (defun ...)).

  (declare (xargs :guard t))
  (or (and (true-listp x)
           (member-eq (car x) *defun-macros*))
      (and (consp x)
           (let ((lst (if (eq (car x) 'mutual-recursion)
                          (cdr x)
                        x)))
; In the mutual-recursion case the cars should all be defun or defund, but we
; don't bother here with that stronger check.
             (subsetp-eq (strip-cars lst) *defun-macros*)))))

(defun def-listp-from-defuns-p (x)

; Convert a defuns-p into a def-lst, i.e., a list of definitions without the
; leading 'defun.

  (declare (xargs :guard (defuns-p x)))
  (cond ((eq (car x) 'mutual-recursion)
         (strip-cdrs (cdr x)))
        ((symbolp (car x))
         (list (cdr x)))
        (t (strip-cdrs x))))

;;; !! Change to irrelevant-formals-info.  Update :doc, especially for dcls and
;;; result :nice.  Point out that :nice doesn't show those declared irrelevant
;;; but are not (so is a bit odd if, contrary to default, :dcls includes
;;; :irrelevant and there are bogus irrelevants declared).
(defmacro irrelevant-formals-info (def-or-defs
                                    &key
                                    wrld ctx statep
                                    (result ':default)
                                    (dcls ''(:measure :guard :ignore
                                                      :ignorable :irrelevant)
                                          dcls-p))
  `(let* ((def-lst (def-listp-from-defuns-p ,def-or-defs))
          (ctx0 ,(or ctx ''irrelevant-formals-info))
          (wrld ,(or wrld '(w state)))
          (state-vars ,(if statep
                           '(default-state-vars t)
                         '(default-state-vars nil)))
          (result ,result)
          (dcls ,(if dcls-p
                     dcls
                   `(if (eq result :default)
                        '(:measure :guard :ignore :ignorable)
                      ,dcls))))
     (progn$
      (or (member-eq result '(:msg :raw :default))
          (er hard ctx0
              "The value of the :result keyword for ~x0 must be one of ~v1."
              'irrelevant-formals-info
              '(:msg :raw :default)))
      (or (and (true-listp dcls)
               (subsetp-eq dcls '(:measure :guard :ignore :ignorable
                                           :irrelevant)))
          (er hard ctx0
              "The value of the :dcls keyword for ~x0 must be a list that is ~
               a subset of the list ~x1."
              'irrelevant-formals-info
              '(:measure :guard :ignore :ignorable :irrelevant)))
      (mv-let (ctx info)
        (irrelevant-formals-info-from-def-lst def-lst ctx0 wrld state-vars
                                              result dcls)
        (cond (ctx ; error before irrelevance check
               (er hard ctx "~@0" info))
              (t info))))))

(defmacro chk-irrelevant-formals-ok (def-or-defs)
  `(let* ((def-lst (def-listp-from-defuns-p ,def-or-defs))
          (ctx 'chk-irrelevant-formals-ok))
     (mv-let (erp msg)
       (irrelevant-formals-info-from-def-lst def-lst
                                             ctx
                                             (w state)
                                             (default-state-vars t)
                                             :msg
                                             '(:measure :guard :ignore
                                                        :ignorable
                                                        :irrelevant))
       (if (or erp msg)
           (er soft ctx "~@0" msg)
         (value t)))))

(defxdoc irrelevant-formals-info
  :parents (std/system system-utilities-non-built-in irrelevant-formals)
  :short "Determine whether @(see irrelevant-formals) are OK in definitions."
  :long "<p>This utility returns a Boolean.  For a related utility that can
 cause an error, see @(see chk-irrelevant-formals-ok).</p>

 @({
 General Form:

 (irrelevant-formals-info
  def-or-defs ; a definition, a list of definitions, or of the form
              ; (mutual-recursion def1 ... defk)
  &key
  wrld   ; ACL2 world; if missing or nil, this is (w state)
  ctx    ; a ctxp to use in error messages; if this is nil or missing,
         ; then ctx is 'irrelevant-formals-info
  statep ; certain defaults come from state when statep is true;
         ; default is nil
  dcls   ; which parts of the given declare forms to use
  result ; the form of the result; default is :default
  )
 })

 <p>where all arguments are evaluated, @('dcls') and @('result') are as
 described below, and the other arguments are as described above.  The case
 that @('def-or-defs') is @('(mutual-recursion def1 ... defk)') is treated
 identically to the case it is @('(def1 ... defk)').</p>

 @({
 Simple Example Form:

 ; This returns the list (X1 X3 X4 X5) of irrelevant formals.
 (irrelevant-formals-info
  '(defun f (x0 x1 x2 x3 x4 x5)
     (declare (xargs :guard (natp x2)))
     (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))
 })

 <p>The keyword arguments have defaults that may suffice for most users.  When
 @(':dcls') and @(':results') are omitted, the computation of irrelevant
 formals ignores ``@('irrelevant')'' declarations.  That key point is probably
 all you need to know unless you use the @(':dcls') or @(':results') keywords;
 here is their documentation.</p>

 <p>The value of @(':dcls') should be a subset of the list
 @('(:measure :guard :ignore :ignorable :irrelevant)'), where these keywords
 mean (respectively) that the @(':measure') and @(':guard') @(tsee xargs)
 declarations as well as the @('ignore'), @('ignorable'), and @('irrelevant')
 declararations are taken into account when computing the irrelevant formals.
 This list is the default unless the value of @(':result') is
 @(':default') (which is its default), in which case @(':dcls') defaults to
 @('(:measure :guard :ignore :ignorable)').  This behavior supports the common
 usage of omitting the @(':dcls') and @(':result') arguments in order to
 compute irrelevant formals, without considering which irrelevant formals may
 be declared.</p>

 <p>The legal values of @(':result') and their meanings are as follows.</p>

 <ul>

 <li>@(':default')<br/>
 If @('def-or-defs') is a single definition (or a list containing just a single
 definition), the return value is a list of the irrelevant formals.  Otherwise
 @('def-or-defs') is a list of two or more definitions.  If it defines function
 symbols @('f1'), ..., @('fk') where k&gt;1, then the result is an association
 list that associates each @('fi') with a list of the formals of of @('fi')
 that are irrelevant.  As noted above, unless @(':dcls') is supplied
 explicitly, the computation of irrelevant formals is done without the use of
 any @('irrelevant') declarations.</li>

 <li>@(':raw')<br/>
 The result is @('nil') if and only if the irrelevant-formals check passes.
 The form of a non-@('nil') result is described below.</li>

 <li>@(':msg')<br/>
 The result is @('nil') if and only if the irrelevant-formals check passes.
 If the result is non-@('nil'), then it is a message (see @(see msgp))
 explaining the failure, which is suitable for printing with the @('~@')
 directive of @(tsee fmt).</li>

 </ul>

 @({
 More Example Forms:

 ; This returns (X1 X3 X4 X5) as in the ``Simple Example Form'' above,
 ; thus illustrating that by default, `irrelevant' declarations are
 ; ignored (as explained earlier above).
 (irrelevant-formals-info
  '(defun f (x0 x1 x2 x3 x4 x5)
     (declare (irrelevant x1 x3 x5 x4)
              (xargs :guard (natp x2)))
     (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))

 ; Same as above.
 (irrelevant-formals-info
  '((defun f (x0 x1 x2 x3 x4 x5)
      (declare (xargs :guard (natp x2)))
      (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil))))

 ; Unlike the examples above, this time X2 is included in the result,
 ; because :guard is not in the list specified by :dcls.
 (irrelevant-formals-info
  '((defun f (x0 x1 x2 x3 x4 x5)
      (declare (xargs :guard (natp x2)))
      (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))
  :dcls nil)

 ; This returns ((F1 . Y) (F2 . Y)) because y is an irrelevant formal
 ; for both f1 and f2.
 (irrelevant-formals-info
  '((defun f1 (x y)
      (if (consp x) (f2 (cdr x) y) t))
    (defun f2 (x y)
      (if (consp x) (f1 (cdr x) y) nil))))

 ; This is handled exactly as just above.
 (irrelevant-formals-info
  '(mutual-recursion
    (defun f1 (x y)
      (if (consp x) (f2 (cdr x) y) t))
    (defun f2 (x y)
      (if (consp x) (f1 (cdr x) y) nil))))

 ; This is as just above, except that the missing argument in the call
 ; of f2 in the body of f1, a hard ACL2 error occurs:
 (irrelevant-formals-info
  '(mutual-recursion
    (defun f1 (x y)
      (if (consp x) (f2 (cdr x)) t))
    (defun f2 (x y)
      (if (consp x) (f1 (cdr x) y) nil))))

 ; Because of the :result argument below, we get a msgp from the
 ; irrelevance check.  Try running (fmx \"~@0\" x) where x is bound
 ; to this result.
 (irrelevant-formals-info
  '(mutual-recursion
    (defun f1 (x y)
      (if (consp x) (f2 (cdr x) y) t))
    (defun f2 (x y)
      (if (consp x) (f1 (cdr x) y) nil)))
  :result :msg)
 })

 <p>When keyword @(':result') is @(':raw') and the @(see irrelevant-formals)
 check fails, a list of two lists is returned: a list the associates each key,
 a function name, with the of the formals of that function that are declared
 irrelevant but are not; and a list of slots @('(function-name formal-position
 . formal-name)'), where the positions are zero-based, for the formals that are
 irrelevant but not declared so.  Here is an example.</p>

 @({
 ACL2 !>(irrelevant-formals-info
         '(mutual-recursion
           (defund f1 (x y z)
             (declare (irrelevant z))
             (if (consp x) (f2 (cdr x) y z) z))
           (defund f2 (x y z)
             (if (consp x) (f1 (cdr x) y z) nil)))
         :result :raw)
 (((F1 Z)) ((F1 1 . Y) (F2 1 . Y)))
 ACL2 !>
 })

 <p>Remarks.</p>

 <ul>

 <li>The use of @(tsee set-irrelevant-formals-ok) has no effect on the result;
 that is, the value of @(':irrelevant-formals-info') in the @(tsee
 acl2-defaults-table) does not affect this utility.</li>

 <li>Each definition must be a call of a macro in the following list:
 @(`*defun-macros*`).</li>

 <li>As noted above, an error occurs by default if the given definitions are
 determined to be ill-formed.  However, only some of the usual checks for
 @(tsee defun) events are performed; for example, translation of measures,
 guards, and bodies is only for logic, not execution, and only partial checks
 are made for the @(see declare) forms.  The point of this tool is to perform
 @(see irrelevant-formals) checks, not to do complete checks for the given
 forms.</li>

 </ul>")

(defxdoc chk-irrelevant-formals-ok
  :parents (std/system system-utilities-non-built-in irrelevant-formals)
  :short "Check @(see irrelevant-formals) in definitions."
  :long "@({General Form:

 (chk-irrelevant-formals-ok def-or-defs)
 })

 <p>where @('def-or-defs') evaluates to a definition, a list of definitions, or
 a list of definitions preceded by @('mutual-recursion').  Each definition must
 be a call of a macro in the following list: @(`*defun-macros*`).</p>

 @({
 Example Forms:

 ; Success: Returns (value t).
 (chk-irrelevant-formals-ok
  '(defun f (x0 x1 x2 x3 x4 x5)
     (declare (irrelevant x1 x3 x5 x4)
              (xargs :guard (natp x2)))
     (if (consp x0) (f (cdr x0) x1 x2 x5 x4 x3) nil)))

 ; Failure: Error message reports y irrelevant for both definitions.
 (chk-irrelevant-formals-ok
  '(mutual-recursion
    (defun f1 (x y)
      (if (consp x) (f2 (cdr x) y) t))
    (defun f2 (x y)
      (if (consp x) (f1 (cdr x) y) nil))))
 })

 <p>See @(see irrelevant-formals-info) for a related utility that returns a
 single value.  By contrast, @('chk-irrelevant-formals-ok') returns an @(see
 error-triple), which is @('(mv nil t state)') when the @(see
 irrelevant-formals) check passes for the given definition or list of
 definitions, and otherwise returns a soft error as in @('(er soft
 ...)').  Note that all relevant @(see declare) forms, including
 ``@('irrelevant')'', are taken into account.  For finer-grained control of the
 use of declarations, see @(see irrelevant-formals-info).</p>")
