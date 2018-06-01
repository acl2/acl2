; Copyright (C) 2018, J Strother Moore
; Written by J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; PLTP(A): An ACL2 Implementation of 
; the Edinburgh Pure Lisp Theorem Prover of 1973

; J Strother Moore

; PLTP(A) is an ACL2 :program mode implementation of the techniques and
; heuristics of the Edinburgh Pure Lisp Theorem Prover, PLTP, as of 14
; September, 1973.  PLTP(A) is NOT a faithful translation of the 1973 code
; because the known bugs and oddities of PLTP's 14 September, 1973 source code
; have been repaired and some of the algorithms have been implemented
; differently while preserving a high-level equivalency to the original code.
; See index.html for an overview of PLTP(A).

; To re-certify this book: 

#||
(defpkg "PLTP"
  (set-difference-eq
   (union-eq '(packn1)
             (union-eq *acl2-exports*
                       *common-lisp-symbols-from-main-lisp-package*))
   '(eval subst args getprop putprop untranslate boolean
          all-vars all-vars-list reduce props induct prove
          *features* set-feature)))
(certify-book "pltpa" 1)
||#

; To play with PLTP(A):  Below is a sample script that illustrates how to
; start PLTP(A), define a function, and prove a theorem.

#||
(include-book ; (Matt K mod) breaking line to fool dependency scanner
  "pltpa") ; Load these sources

(pltpa)                ; Switch from ACL2 package to PLTP package and boot up
                       ; the PLTP logical world

(boot-strap)           ; If already in the PLTP package, re-boot PLTP logical
                       ; world

; Booting PLTP will print the current settings for various :features affecting
; the notation used when formulas are printed.  It will also summarize how to
; change these settings.  For more details on that, see the comment in the
; defun of set-feature below.

(define (append        ; define a PLTP function
         (lambda (x y)
           (if x (cons (car x) (append (cdr x) y)) y))))

(prove assoc-of-append ; name is irrelevant except for io; theorems are not
                       ; stored in the PLTP world

       (equal (append (append a b) c)
              (append a (append b c))))

(props append)         ; print all the stored properties of APPEND

(rbt append)           ; = ``roll-back-through'' rolls back (undoes) the PLTP
                       ; wrld through definition of APPEND

(proveall :standard)   ; re-boot and process all the definitions and theorems
                       ; in the standard 14 September, 1973 Edinburgh
                       ; regression suite

(proveall :jacm)       ; re-boot and process all the definitions and theorems
                       ; in the 1975 Boyer-Moore JACM paper ``Proving Theorems
                       ; about Lisp Functions''
||#

; Convention:  I do not use the ACL2 function ``if'' in this code.  Every
; occurrence of ``if'' in code (not in English comments) refers to the function
; of that name in the PLTP(A) logic.  Furthermore, I have tried to use ALL CAPS
; for every such occurrence of IF.

(in-package "PLTP")


(program)

(defconst *version* "PLTP(A)")

; -----------------------------------------------------------------
; The Property List ``World''

; PLTP(A)'s logical world is stored on a property list, e.g., a list of
; elements of the form (symbol property . value), which itself is
; stored in the ACL2 ``state global'' referred to by (@ WRLD).

(defun getprop (sym prop default wrld)
  (cond ((endp wrld) default)
        ((and (eq sym (car (car wrld)))
              (eq prop (cadr (car wrld))))
         (cddr (car wrld)))
        (t (getprop sym prop default (cdr wrld)))))

(defun putprop (sym prop val wrld)
  (cond ((endp wrld) (cons (list* sym prop val) wrld))
        ((and (eq sym (car (car wrld)))
              (eq prop (cadr (car wrld))))
         (cons (list* sym prop val) (cdr wrld)))
        (t (cons (car wrld) (putprop sym prop val (cdr wrld))))))

(defun putprop* (tuples wrld)
  (cond
   ((endp tuples) wrld)
   (t (putprop* (cdr tuples)
                (putprop (car (car tuples))
                         (cadr (car tuples))
                         (caddr (car tuples))
                         wrld)))))

; Setting up the environment.

(set-state-ok t)

; Boot-strap0, which begins the process of creating a ``completely fresh''
; world actually transfers the :feature settings of the current world, if any,
; to the new world.  This way, it appears that :feature settings are somehow
; out-of-the-world (not affected by re-booting) when in fact they are
; conveniently found in the world.

; The construction of the new world is completed by DEFINing some basic
; functions, but we can't write that code until we've introduced DEFINE.

(defconst *features* '(:untranslate-enabled
                       :untranslate-if-to-cond
                       :untranslate-constants
                       :untranslate-logical-connectives))

(defun collect-features (wrld)
; Rather than look for the specific :feature properties we just get them all.
; But the *features* list above limits what can be set below.
  (cond
   ((endp wrld) nil)
   ((eq (car (car wrld)) :feature)
    (cons (list (car (car wrld))
                (cadr (car wrld))
                (cddr (car wrld)))
          (collect-features (cdr wrld))))
   (t (collect-features (cdr wrld)))))

(defun boot-strap0 (acl2::state)
  (acl2::assign wrld
                (putprop*
                 `((CAR ARITY 1)
                   (CDR ARITY 1)
                   (CONS ARITY 2)
                   (EQUAL ARITY 2)
                   (IF ARITY 3)
                   (CAR BOOLEAN nil)
                   (CAR NUMERIC nil)
                   (CDR BOOLEAN nil)
                   (CDR NUMERIC nil)
                   (CONS BOOLEAN nil)
; We don't store a NUMERIC property for CONS because we don't access it.
                   (EQUAL BOOLEAN t)
                   (EQUAL NUMERIC t)

; We don't store BOOLEAN or NUMERIC properties for IF
; because we never access it.

                   ,@(cond
                      ((acl2::boundp-global 'wrld acl2::state)
; If a boot-strap has been done, preserve the current features
                       (collect-features (@ wrld)))
                      (t '((:feature :untranslate-enabled t)
                           (:feature :untranslate-if-to-cond nil)
                           (:feature :untranslate-constants t)
                           (:feature :untranslate-logical-connectives t)
                           (:feature :help "(set-feature key val) for keys above or
      (set-feature :ALL val) with val being one of
      :defaults, :pltp-notation, or :raw-notation")))))
                 nil)))

; -----------------------------------------------------------------
; Terms -- User Terms and Internal Form and Converting Between Them

; Formally, a term is either a variable symbol, the constant NIL, or the
; application of a function symbol of arity n to n terms.  Any ACL2 symbol with
; an ARITY property in the PLTP(A) logical world is a function symbol and the
; arity of that symbol is as given by the property.  We assume that the
; following symbols have the arities listed:

; CAR     1
; CDR     1
; CONS    2
; EQUAL   2
; IF      3

; We extend this formal notion of term with some abbreviations:
; T abbreviates (CONS NIL NIL)
; 0 abbreviates NIL
; 1 abbreviates (CONS NIL NIL)
; 2 abbreviates (CONS NIL 1)
; etc.

; We will inspect terms with the following:

; (varp x) -- x is a variable symbol

; (null x) -- x is the constant NIL

; else -- x is the application of (fn x) to the n elements of (args x), where n
;         is the arity of the function symbol.  For convenience, (arg1 x) is
;         the 1st (1-based) element of (args x) when the arity of (fn x) is no
;         less than 1, (arg2 x) is the 2nd element of (args x) when the arity
;         of (fn x) is no less than 2, and (arg3 x) is the 3rd element of (args
;         x) when the arity of (fn x) is no less than 3.

; To construct a term we use (cons fn (list arg_1 ... arg_n)).

; We recognize legal user-level terms with this predicate.

(mutual-recursion
 (defun utermp (x wrld)
   (cond
    ((atom x)

; When x is an atom, then it must be a non-keyword variable symbol, a PLTP(A)
; constant symbol (PLTP(A)::NIL or PLTP(A)::T) or a natural number.

     (or (eq x NIL)
         (eq x T)
         (natp x)
         (and (symbolp x)
              (not (equal (symbol-package-name x) "KEYWORD")))))
    (t (and (consp x)
            (true-listp x)
            (symbolp (car x))
            (not (equal (symbol-package-name (car x)) "KEYWORD"))
            (not (member (car x) '(CARARG CDRARG)))
            (equal (getprop (car x) 'arity nil wrld)
                   (length (cdr x)))
            (utermp-list (cdr x) wrld)))))
 (defun utermp-list (x wrld)
   (cond
    ((endp x) t)
    (t (and (utermp (car x) wrld)
            (utermp-list (cdr x) wrld))))))

(defconst *T* '(CONS NIL NIL))

(mutual-recursion
 (defun translate (uterm)
; We know uterm is a utermp.  We expand the abbreviations for T and natural
; numbers.
   (cond
    ((symbolp uterm)
     (cond ((eq uterm T) *T*)
           (t uterm)))
    ((natp uterm)
     (cond ((equal uterm 0)
            NIL)
           (t `(CONS NIL ,(translate (- uterm 1))))))
    (t (cons (car uterm)
             (translate-list (cdr uterm))))))
 (defun translate-list (terms)
   (cond ((endp terms) nil)
         (t (cons (translate (car terms))
                  (translate-list (cdr terms)))))))

; Henceforth, we assume that every object treated as a term is in fact a
; translated utermp.

(defun varp (x)
  (and (symbolp x)
       (not (null x))))

(defun applicationp (x)
; This is equivalent to (and (not (varp x)) (not (null x))).
  (consp x))

(defun fn (x)

; We make no assumption that x is an application!  We return the keyword :UNDEF
; when x is not an application.  :UNDEF cannot be a function symbol because it
; is keyword.  Thus we're free to apply fn to any term and if the result is a
; known function symbol we know the term is an application of that function.

  (cond
   ((varp x) :UNDEF)
   ((null x) :UNDEF)
   (t (car x))))

(defun args (x)
; We assume (applicationp x), or, equivalently, (not (eq (fn x) :UNDEF)). 
 (cdr x))

; These functions should only be used when (fn x) has an appropriate number
; of args.

(defun arg1 (x)
  (cadr x))

(defun arg2 (x)
  (caddr x))

(defun arg3 (x)
  (cadddr x))

; The following concept, that of whether a term is boolean valued, is important
; to the prover and its introduction here is somewhat premature: we are still
; defining basic infrastructure and haven't gotten to substantive theorem
; proving routines yet.  But boolean is involved in the ``untranslation'' of
; terms into back user-familiar terms.  For example, (IF a b (CONS NIL NIL)) is
; presented as (IMPLIES a b) if b is boolean.  So we need this concept now.
; Were it not for its role in untranslation, boolean would be introduced in
; the section on Determining the Type of a Term.

(defun boolean (term wrld)
  (cond
   ((varp term) nil)
   ((null term) t)
   ((equal term *T*) t)
   (t (let ((funsym (fn term)))
        (cond ((or (eq funsym 'IF)
                   (eq funsym 'COND))
               (and (boolean (arg2 term) wrld)
                    (boolean (arg3 term) wrld)))
              (t (getprop funsym 'BOOLEAN NIL wrld)))))))

; Untranslate

; Untranslate converts internal, formal PLTP(A) terms into a user-level terms.
; There are several :features that control untranslate.

; :untranslate-enabled -- when nil, untranslate is the identity function no
;   matter how the other switches are set.  Default: t.

; :untranslate-if-to-cond -- if t, all IFs to be printed are shown as COND.  IF
;   is the standard internal form and COND is actually defined to be IF, so
;   input involving COND will eventually settle down to an internal term
;   involving only IFs.  But untranslation can convert displayed IFs to CONDs.
;   Default: nil.

; :untranslate-constants -- if t, then (CONS NIL NIL) is printed as T, (CONS
;   NIL (CONS NIL NIL)) is printed as 2, etc.  NIL is always printed as NIL,
;   never as 0, and (CONS NIL NIL) is either printed as itself or as T, never
;   as 1.  Default: t.

; :untranslate-logical-connectives -- if t, then IMPLIES, AND, OR, and NOT are
;   printed instead of the equivalent IF expressions.  Default: t.

(mutual-recursion
 (defun untranslate1 (term wrld)
   (cond
    ((varp term) term)
    ((null term) NIL)
    ((equal term *t*)
     (cond ((getprop :feature :untranslate-constants t wrld) T)
           (t term)))
    (t (case (fn term)
         (CAR `(CAR ,(untranslate1 (arg1 term) wrld)))
         (CDR `(CDR ,(untranslate1 (arg1 term) wrld)))
         (CONS (let ((x (untranslate1 (arg1 term) wrld))
                     (y (untranslate1 (arg2 term) wrld)))
                 (cond
; Since T is the root of all numeric output, we don't have to
; check the :untranslate-constants switch.
                  ((and (null x) (eq y T)) 2)
                  ((and (null x) (natp y)) (+ 1 y))
                  (t `(CONS ,x ,y)))))
         (EQUAL (let ((x (untranslate1 (arg1 term) wrld))
                      (y (untranslate1 (arg2 term) wrld)))
                  `(EQUAL ,x ,y)))
         (IF (let ((x (untranslate1 (arg1 term) wrld))
                   (y (untranslate1 (arg2 term) wrld))
                   (z (untranslate1 (arg3 term) wrld)))
               (cond
                ((null (getprop :feature :untranslate-logical-connectives t wrld))
                 `(,(cond ((getprop :feature :untranslate-if-to-cond nil wrld)
                           'COND)
                          (t 'IF))
                   ,x ,y ,z))
                ((and (eq y NIL)
                      (equal (arg3 term) *T*))
                 `(NOT ,x))
                ((and (equal (arg3 term) *T*)
                      (boolean (arg2 term) wrld))
                 `(IMPLIES ,x ,y))
                ((and (eq z NIL)
                      (boolean (arg2 term) wrld))
                 `(AND ,x ,y))
                ((and (equal (arg2 term) *T*)
                      (boolean (arg3 term) wrld))
                 `(OR ,x ,z))
                (t `(,(cond ((getprop :feature :untranslate-if-to-cond nil wrld)
                             'COND)
                            (t 'IF))
                     ,x ,y ,z)))))
         (otherwise
          (cons (fn term)
                (untranslate1-list (args term) wrld)))))))
 (defun untranslate1-list (terms wrld)
   (cond ((endp terms) nil)
         (t (cons (untranslate1 (car terms) wrld)
                  (untranslate1-list (cdr terms) wrld))))))

(defun untranslate (term wrld)
  (cond ((getprop :feature :untranslate-enabled t wrld)
         (untranslate1 term wrld))
        (t term)))

; -----------------------------------------------------------------
; Generating ``New'' Symbols

; The following is low-level ACL2 symbol hacking to generate ``new'' symbols.
; It is all wrapped up in new-vars1 and then in new-vars, the latter of which
; is considered a basic part of the theorem prover's infrastructure.

(defun make-nat-from-digits (digits n)
  (cond ((endp digits) n)
        (t (make-nat-from-digits (cdr digits)
                                 (+ (car digits)
                                    (* 10 n))))))

(defun find-root-and-suffix1 (sym chars digits)
  (cond
   ((endp chars) (mv 0 (make-nat-from-digits digits 0)))
   (t (let ((d (char-code (car chars))))
        (cond
         ((and (<= 48 d) (<= d 57))
          (find-root-and-suffix1 sym (cdr chars) (cons (- d 48) digits)))
         (t (mv (intern-in-package-of-symbol (coerce (reverse chars) 'string) sym)
                (make-nat-from-digits digits 0))))))))

(defun find-root-and-suffix (sym)

; Assuming sym is a symbol ending in a possibly empty sequence of digits we
; return (mv root k), where k is the natural whose decimal representation is
; the maximal sequence of digits at the end of sym and root is the symbol (in
; the same package) formed from the initial part of sym.  Thus, when sym is
; ABC123 then we return (mv 'ABC 123).  When there is no digit at the end of
; sym, k is 0 and root is sym.  When every character in sym's name is a digit,
; root is the non-symbol 0 and k is the obvious natural, e.g., |123| is mapped
; to (mv 0 123).

  (find-root-and-suffix1 sym (reverse (coerce (symbol-name sym) 'list)) nil))

(defun maximal-suffix-alist (vars alist)
  (cond ((endp vars) alist)
        (t (mv-let (root k)
             (find-root-and-suffix (car vars))
             (maximal-suffix-alist (cdr vars)
                                   (put-assoc-eq root
                                                 (max (or (cdr (assoc-eq root alist)) 0)
                                                      k)
                                                 alist))))))

(defun new-vars1 (targets suffix-alist)

; Roughly speaking: generate an alist pairing each target with a new variable
; symbol.  The question is what do we mean by ``new''?  Basic Idea: if the
; target in question is a variable symbol we decompose it into a root and a
; suffix, as when we decompose TEMP21 into TEMP and 21.  Then we map that
; target to the symbol with the same root and a suffix one greater than the max
; of the target's suffix and the maximal suffix on that root as stored in
; suffix-alist.  So, for example, suppose the target is TEMP21 and the
; suffix-alist contains the entry (TEMP . 45).  Then we map TEMP21 to TEMP46.
; But if suffix-alist contained (TEMP . 17) instead, we map TEMP21 to TEMP22.
; If an element of targets is not a symbol, we use G for the root of the new
; symbol.

  (cond
   ((endp targets) nil)
   (t (let ((sym (cond ((symbolp (car targets))
                        (car targets))
                       (t 'GENRL))))
        (mv-let (root k1)
          (find-root-and-suffix sym)
          (let* ((k (cond ((assoc-eq root suffix-alist)
                           (max k1 (cdr (assoc-eq root suffix-alist))))
                          (t k1)))
                 (new-var (intern-in-package-of-symbol
                           (coerce (packn1
                                    (cond ((equal root 0)
                                           (list (+ k 1)))
                                          (t (list root (+ k 1)))))
                                   'string)
                           sym)))
            (cons (cons (car targets) new-var)
                  (new-vars1 (cdr targets)
                             (put-assoc-eq root (+ k 1) suffix-alist)))))))))

; -----------------------------------------------------------------
; All the Output Routines

; From the perspective of understanding the prover heuristics and organization,
; the code in this section can be ignored.  It implements the output printed by
; the prover.

; Here is how we inspect the properties for a symbol:

(defun props1 (fn alist ac)
  (cond
   ((endp alist) (reverse ac))
   ((eq fn (car (car alist)))
    (props1 fn
            (cdr alist)
            (cons (list (cadr (car alist)) (cddr (car alist)))
                  ac)))
   (t (props1 fn (cdr alist) ac))))

; Typing (props fn) will display all the properties that PLTP(A) has for the
; function named fn.  (Props :feature) will list all the features.

(defmacro props (fn)
  `(props1 ',fn (@ wrld) nil))

; And here is how we set :features in wrld:

(defmacro set-feature (name val)

; The supported features are listed below.  They are stored as properties in
; wrld.  For example, to say that :untranslate-enabled is set to nil means that
; the value of the :untranslate-enabled property of :feature in wrld is nil.

; :untranslate-enabled -- when :untranslate-enabled is nil, untranslate is the
;   identity function no matter how the other features are set.  Default: t.

; :untranslate-if-to-cond -- if t, the all IFs in the term are printed as
;   CONDs.  IF is the standard internal form and COND is actually defined to be
;   IF, so input involving COND will eventually settle down to an internal term
;   involving only IFs.  But untranslation can convert displayed IFs to CONDs.
;   Default: nil.

; :untranslate-constants -- if t, then (CONS NIL NIL) is printed as T, (CONS
;   NIL (CONS NIL NIL)) is printed as 2, etc.  NIL is always printed as NIL,
;   never as 0, and (CONS NIL NIL) is either printed as itself or as T, never
;   as 1.  Default: t.

; :untranslate-logical-connectives -- if t, then IMPLIES, AND, OR, and NOT are
;   printed instead of the equivalent IF expressions.  Default: t.

; We implement a shortcut that will set several features at once:

; (set-feature :all :defaults)       - restore default values of all features
; (set-feature :all :pltp-notation)  - mimic PLTP-style notation
; (set-feature :all :raw-notation)   - show internal forms in output

  (declare (xargs
            :guard
            (and (or (eq name :all)
                     (member name *features*))
                 (member val '(t nil
                                 :defaults
                                 :pltp-notation
                                 :raw-notation))
                 (eq (eq name :all)
                     (or (eq val :defaults)
                         (eq val :pltp-notation)
                         (eq val :raw-notation))))))
  `(er-progn
    (assign wrld
            ,(cond
              ((eq name :all)
               (cond
                ((eq val :defaults)
                 '(putprop* '((:feature :untranslate-enabled t)
                              (:feature :untranslate-if-to-cond nil)
                              (:feature :untranslate-constants t)
                              (:feature :untranslate-logical-connectives t))
                            (@ wrld)))
                ((eq val :pltp-notation)
                 '(putprop* '((:feature :untranslate-enabled t)
                              (:feature :untranslate-if-to-cond t)
                              (:feature :untranslate-constants t)
                              (:feature :untranslate-logical-connectives nil))
                            (@ wrld)))
                (t ; (eq val :raw-notation)
                 '(putprop* '((:feature :untranslate-enabled nil) ; this one suffices!
                              (:feature :untranslate-if-to-cond nil)
                              (:feature :untranslate-constants nil)
                              (:feature :untranslate-logical-connectives nil))
                            (@ wrld)))))
              (t
               `(putprop :feature ,name ,val (@ wrld)))))
    (value (props :feature))))


(defun simplify-msg (term1 wrld)
  (cw "WHICH IS EQUIVALENT TO:~%~y0.~%"
      (untranslate term1 wrld)))

(defun do-fertilize1-msg (action term1 flg)

  (declare (ignore action flg))

; We have chosen to ignore the details available as to what fertilization did.
; But, for the record, action is one of XLR, XRL, MLR, MRL and indicates
; whether the substitution is cross-fertilization (X) or massive substitution
; (M), and whether its Left for Right or vice versa.  Flg indicates whether the
; IF-term being manipulated is an IMPLIES or not.  If it is not an IMPLIES,
; PLTP(A) rearranged the false branch to hide the equality.

  (cw "FERTILIZE WITH ~x0.~%~%" term1))

(defun fertilize-msg (term1 wrld)
  (cw "THE THEOREM TO BE PROVED IS NOW:~%~y0.~%"
      (untranslate term1 wrld)))

(defun tilde-*-generalize1-phrase1 (alist)
  (cond ((null alist) nil)
        (t (cons (msg "~p0 BY ~x1"
                      (caar alist)
                      (cdar alist))
                 (tilde-*-generalize1-phrase1 (cdr alist))))))

(defun tilde-*-generalize1-phrase (alist)
    (list* "" "~@*" "~@* AND " "~@*, "
         (tilde-*-generalize1-phrase1 alist)
         nil))

; Note: We print PLTP's ``(WORK ON FIRST CONJUNCT ONLY)'' message when
; PLTP(A)'s generalize uses split-conjunction to split off the first conjunct.
; But we don't print it again when INDUCT uses split-conjunction.  This is ok
; because if generalize gets a conjunction as input it produces a conjunction
; as output for induct and while induct must recognize that its been given a
; conjunction it doesn't have to print the message again because PLTP didn't.

(defun split-conjunction-msg (flg)
  (cond
   (flg
    (cw "(WORK ON FIRST CONJUNCT ONLY)~%~%"))
   (t nil)))

(defun generalize-msg (flg alist term wrld)
; Flg is t if term is the first conjunct of the current goal theorem and
; is nil if term is the whole goal theorem.  Alist is the generalizing
; substitution mapping subterms to new vars.
  (cond
   (alist
    (cw "GENERALIZE COMMON SUBTERM~#0~[S~/~] BY REPLACING ~*1.~%~%~
         THE GENERALIZED ~#2~[~/(first conjunct) ~]TERM IS:~%~x3~%~%"
        (cond ((cdr alist) 0)(t 1))
        (tilde-*-generalize1-phrase alist)
        (if flg 1 0)
        (untranslate term wrld)))
   (t nil)))

(defun tilde-*-induct-phrase (vars)
  (list* "" "~x*" "~x* AND " "~x*, " vars nil))

(defun induct-msg (signal indvars new-goal wrld)
  (cond
   ((eq signal 'STUCK)
    (cw "Stuck with:~%~y0.~%" new-goal))
   ((eq signal 'SIMPLE)
    (cw "MUST TRY INDUCTION.~%~%~
         INDUCT ON ~*0.~%~%~
         THE THEOREM TO BE PROVED IS NOW:~%~y1.~%"
        (tilde-*-induct-phrase indvars)
        (untranslate new-goal wrld)))
   ((or (eq signal 'SPECIAL1)
        (eq signal 'SPECIAL2))
    (cw "MUST TRY INDUCTION.~%~%~
         (SPECIAL CASE REQUIRED)~%~%~
         INDUCT ON ~*0.~%~%~
         THE THEOREM TO BE PROVED IS NOW:~%~y1.~%"
        (tilde-*-induct-phrase indvars)
        (untranslate new-goal wrld)))
   (t (cw "Special case not covered!~%~y0.~%"
          (untranslate new-goal wrld)))))

(defun pre-proveall-msg (key state)
  (prog2$
   (cw "~%~f0 Proveall by ~s1~%"
       key
       *version*)
   (acl2::print-current-idate *standard-co* state)))

(defun post-proveall-msg (key state)
  (prog2$
   (cw "~%Successful ~f0 Proveall by ~s1 completed on~%"
       key
       *version*)
   (pprogn
    (acl2::print-current-idate *standard-co* state)
    (fms "~%~x0~%"(list (cons #\0 (props :feature)))  *standard-co* state nil)
    (value :invisible))))

; -----------------------------------------------------------------
; Basic Theorem Proving Concepts

(mutual-recursion
 (defun term-size (term)
   (cond
    ((varp term) 1)
    ((null term) 1)
    (t (+ 1 (term-size-list (args term))))))
 (defun term-size-list (terms)
   (cond
    ((endp terms) 0)
    (t (+ (term-size (car terms))
          (term-size-list (cdr terms)))))))

(mutual-recursion
 (defun occur (term1 term2)
   (cond
    ((equal term1 term2) t)
    ((or (varp term2)
         (null term2))
     nil)
    (t (occur-list term1 (args term2)))))
 (defun occur-list (term1 term2-list)
   (cond
    ((endp term2-list) nil)
    (t (or (occur term1 (car term2-list))
           (occur-list term1 (cdr term2-list)))))))

(defun occur-cons (term1 term2)
  (or (equal term1 term2)
      (and (applicationp term2)
           (eq (fn term2) 'CONS)
           (or (occur-cons term1 (arg1 term2))
               (occur-cons term1 (arg2 term2))))))

(defun ident (term1 term2)
; Return :EQUAL, :NOT-EQUAL, or :UNKNOWN where PLTP returned, respectively, 1,
; NIL, and 0.
  (let ((size1 (term-size term1))
        (size2 (term-size term2)))
    (cond
     ((equal size1 size2)
      (cond ((equal term1 term2) :EQUAL)
            (t :UNKNOWN)))
     ((and (< size1 size2)
           (applicationp term2)
           (eq (fn term2) 'CONS)
           (or (null term1)
               (occur-cons term1 term2)))
      :NOT-EQUAL)
     ((and (< size2 size1)
           (applicationp term1)
           (eq (fn term1) 'CONS)
           (or (null term2)
               (occur-cons term2 term1)))
      :NOT-EQUAL)
     (t :UNKNOWN))))

(mutual-recursion
 (defun all-vars (term)
   (cond ((varp term) (list term))
         ((null term) nil)
         (t (all-vars-list (args term)))))
 (defun all-vars-list (terms)
   (cond ((endp terms) nil)
         (t (union-eq (all-vars (car terms))
                      (all-vars-list (cdr terms)))))))

(mutual-recursion
 (defun all-fns (term)
   (cond ((varp term) nil)
         ((null term) nil)
         (t (add-to-set (fn term) (all-fns-list (args term))))))
 (defun all-fns-list (terms)
   (cond ((endp terms) nil)
         (t (union-eq (all-fns (car terms))
                      (all-fns-list (cdr terms)))))))

(defun finished (term)
  (subsetp-eq (all-fns term) '(CAR CDR CONS EQUAL)))

(mutual-recursion
 (defun all-calls (fn term)
   (cond ((varp term) nil)
         ((null term) nil)
         (t (let ((rest (all-calls-list fn (args term))))
              (cond
               ((eq (fn term) fn)
                (add-to-set-equal term rest))
               (t rest))))))
 (defun all-calls-list (fn terms)
   (cond ((endp terms) nil)
         (t (union-equal (all-calls fn (car terms))
                         (all-calls-list fn (cdr terms)))))))

(defun new-vars (targets term)

; Targets is a list of terms.  We return an alist that maps each element in
; targets to a variable symbol not used in term.

; Note: When calling new-vars multiple times to get a set of distinct vars one
; must be careful to pass in a ``term'' that contains all the already-generated
; vars.  E.g., if the first call of new-vars produced alist1 and then we want
; an alist2 containing some additional new-vars, we must take the new vars of
; alist1 and put them into a ``term'' to pass to the second call.  My
; convention is to use the ``term'' `(NEW-VAR-GLUE ,@(strip-cdrs alist1)
; ,old-term).

    (new-vars1 targets (maximal-suffix-alist (all-vars term) nil)))

(defun explicit-valuep (term)
  (or (null term)
      (and (eq (fn term) 'CONS)
           (explicit-valuep (arg1 term))
           (explicit-valuep (arg2 term)))))

(defun explicit-value-listp (x)
  (or (endp x)
      (and (explicit-valuep (car x))
           (explicit-value-listp (cdr x)))))

(mutual-recursion
 (defun subst (new-term old-term term)
   (cond
    ((equal old-term term) new-term)
    ((varp term) term)
    ((null term) term)
    (t (cons (fn term)
             (subst-list new-term old-term (args term))))))
 (defun subst-list (new-term old-term terms)
   (cond ((endp terms) nil)
         (t (cons (subst new-term old-term (car terms))
                  (subst-list new-term old-term (cdr terms)))))))

(mutual-recursion
 (defun subst* (alist term)
   (let ((temp (assoc-equal term alist)))
     (cond
      (temp (cdr temp))
      ((varp term) term)
      ((null term) term)
      (t (cons (fn term)
               (subst*-list alist (args term)))))))
 (defun subst*-list (alist terms)
   (cond
    ((endp terms) nil)
    (t (cons (subst* alist (car terms))
             (subst*-list alist (cdr terms)))))))

(defun lispprim (term)
  (or (null term)
      (member-eq (fn term) '(CAR CDR CONS EQUAL IF))))


; -----------------------------------------------------------------
; Symbolic Evaluation

(defun bombedp1 (args)
  (cond ((endp args) nil)
        ((or (eq (fn (car args)) 'CAR)
             (eq (fn (car args)) 'CDR))
         t)
        (t (bombedp1 (cdr args)))))

(mutual-recursion
(defun bombedp (fn val)
  (cond ((varp val) nil)
        ((null val) nil)
        ((and (eq fn (fn val))
              (bombedp1 (args val)))
         t)
        (t (bombedp-list fn (args val)))))
(defun bombedp-list (fn vals)
  (cond ((endp vals) nil)
        (t (or (bombedp fn (car vals))
               (bombedp-list fn (cdr vals)))))))
(mutual-recursion

(defun eval (term alist xfn wrld)

; Term is symbolically evaluated under alist, which binds local variables to
; their symbolic values. Xfn is the nonprimitive function currently being
; expanded or NIL if we're not in an expansion.

; Warning: This function can expand indefinitely.  For example, (DEFINE (FOO
; (LAMBDA (X) (IF X (FOO (APPLY NIL X)) NIL)))) will cause (foo x) to be
; repeatedly expanded because no bombing of top-level arguments to the
; recursive call is detected.  (In this example, by APPLY we mean the undefined
; function introduced in the standard PLTP proveall by (DCL (APPLY (X Y))).)
; For what it is worth, this same behavior is seen in PLTP and that looping in
; both implementations occurs even if the (apply nil x) above is replaced by
; (apply nil (car x)).

  (cond
   ((varp term)
    (let ((temp (assoc-eq term alist)))
      (cond (temp (cdr temp)) (t term))))
   ((explicit-valuep term)
; PLTP doesn't quite do this.  It makes a special case for T and numbers but
; not for explicit constants written as CONS expressions.
    term)
   (t (case (fn term)
        (CAR
         (let ((a (eval (arg1 term) alist xfn wrld)))
           (cond
            ((eq (fn a) 'CONS)
             (arg1 a))
            (t `(CAR ,a)))))
        (CDR
         (let ((a (eval (arg1 term) alist xfn wrld)))
           (cond
            ((null a) NIL)
            ((eq (fn a) 'CONS)
             (arg2 a))
            (t `(CDR ,a)))))
        (CONS
         `(CONS ,(eval (arg1 term) alist xfn wrld)
                ,(eval (arg2 term) alist xfn wrld)))
        (EQUAL
         (let ((a (eval (arg1 term) alist xfn wrld))
               (b (eval (arg2 term) alist xfn wrld)))
           (case (ident a b)
             (:EQUAL *T*)
             (:NOT-EQUAL NIL)
             (otherwise
              (cond
               ((and (eq (fn a) 'CONS)
                     (eq (fn b) 'CONS))
                (eval
                 '(IF (EQUAL (CAR X) (CAR Y))
                      (EQUAL (CDR X) (CDR Y))
                      NIL)
                 (list (cons 'X a)
                       (cons 'Y b))
                 xfn
                 wrld))
               (t `(EQUAL ,a ,b)))))))
        (IF
         (let ((a (eval (arg1 term) alist xfn wrld)))
           (case (ident a NIL)
             (:EQUAL (eval (arg3 term) alist xfn wrld))
             (:NOT-EQUAL (eval (arg2 term) alist xfn wrld))
             (otherwise
              (let ((b (eval (arg2 term) alist xfn wrld))
                    (c (eval (arg3 term) alist xfn wrld)))
                `(IF ,a ,b ,c))))))
        (otherwise
         (eval-fncall (fn term)
                      (eval-list (args term) alist xfn wrld)
                      xfn
                      wrld))))))

(defun eval-list (terms alist xfn wrld)
  (cond ((endp terms) nil)
        (t (cons (eval (car terms) alist xfn wrld)
                 (eval-list (cdr terms) alist xfn wrld)))))

(defun eval-fncall (fn args xfn wrld)
  (cond
   ((and (eq fn xfn)
         (not (explicit-value-listp args)))
    (cons fn args))
   (t (let ((defn (getprop fn 'defn :undef wrld)))
        (cond
         ((eq defn :undef) (cons fn args))
         (t (let* ((formals (cadr defn))
                   (body (caddr defn))
                   (val (eval body (pairlis$ formals args) fn wrld)))
              (cond
               ((bombedp fn val)
                (cons fn args))
               (t val)))))))))
)

(defun evaluate (term wrld)

; This function returns the eval'd term.

  (eval term nil :UNDEF wrld))

; -----------------------------------------------------------------
; Rewriting

(defun find-first-IF (terms)
  (cond
   ((endp terms) nil)
   ((eq (fn (car terms)) 'IF) (car terms))
   (t (find-first-IF (cdr terms)))))

; Renaming: Our function rewrite1 is the analogue of PLTP's REWRITE and our
; rewrite is the analogue of PLTP's NORMALIZE.  We preserve the COMMENTs (with
; COND replaced by IF) from PLTP's rewrite to make sure we implement all and
; only the rewrite rules used by PLTP.

(mutual-recursion

(defun rewrite1 (term wrld)
  (cond
; COMMENT 'IF TERM IS AN EQUALITY`;
   ((eq (fn term) 'EQUAL)
    (rewrite1-equal term wrld))

; COMMENT 'TERM IS AN IF`;
   ((eq (fn term) 'IF)
    (rewrite1-IF term wrld))
   (t (lift-and-rewrite1-IF-arg term wrld))))

(defun rewrite1-equal (term wrld)
  (let ((term1 (arg1 term))
        (term2 (arg2 term)))
    (case (ident term1 term2)
; COMMENT '(EQUAL KNOWN1 KNOWN2) => T OR NIL`;
      (:EQUAL *T*)
      (:NOT-EQUAL NIL)
      (otherwise
; COMMENT '(EQUAL BOOL T) => BOOL`;
       (cond
        ((and (equal term1 *T*)
              (boolean term2 wrld))
         term2)
        ((and (equal term2 *T*)
              (boolean term1 wrld))
         term1)
; COMMENT '(EQUAL (EQUAL A B) C) =>
;          (IF (EQUAL A B) (EQUAL C T) (IF C NIL T))`;

        ((eq (fn term1) 'EQUAL)
         (rewrite1-IF
          `(IF ,term1
               ,(rewrite1 `(EQUAL ,term2 ,*T*) wrld)
               ,(rewrite1 `(IF ,term2 NIL ,*T*) wrld))
          wrld))
        ((eq (fn term2) 'EQUAL)
         (rewrite1-IF
          `(IF ,term2
               ,(rewrite1 `(EQUAL ,term1 ,*T*) wrld)
               ,(rewrite1 `(IF ,term1 NIL ,*T*) wrld))
          wrld))
; COMMENT '(EQUAL X NIL) => (IF X NIL T)`;
        ((equal term1 NIL)
         (rewrite1-IF `(IF ,term2 NIL ,*T*) wrld))
        ((equal term2 NIL)
         (rewrite1-IF `(IF ,term1 NIL ,*T*) wrld))
        (t 
; COMMENT 'GO SEE IF ONE ARG IS A IF`;
         (lift-and-rewrite1-IF-arg term wrld)))))))

(defun rewrite1-IF (term wrld)
  (let ((term1 (arg1 term))
        (term2 (arg2 term))
        (term3 (arg3 term)))
    (case (ident term1 NIL)
; COMMENT'(IF KNOWN X Y) => X OR Y`;
      (:EQUAL term3)
      (:NOT-EQUAL term2)
      (otherwise
       (cond
; COMMENT '(IF X Y Y) => Y`;
        ((equal term2 term3)
         term2)
; COMMENT '(IF X X NIL) => X`;
        ((and (equal term1 term2)
              (equal term3 NIL))
         term1)
; COMMENT '(IF BOOL T NIL ) => BOOL`;
        ((and (boolean term1 wrld)
              (equal term2 *T*)
              (equal term3 NIL))
         term1)
; COMMENT '(IF X T (IF Y NIL T)) => (IF Y (IF X T NIL) T)`;
        ((and (equal term2 *T*)
              (eq (fn term3) 'IF)
              (equal (arg2 term3) NIL)
              (equal (arg3 term3) *T*))
         (let ((term2 (cond ((boolean term1 wrld)
                             term1)
                            (t `(IF ,term1 ,*T* NIL))))
               (term1 (arg1 term3))
               (term3 *T*))
           (rewrite1-IF-IF `(IF ,term1 ,term2 ,term3) wrld)))

        (t (rewrite1-IF-IF term wrld)))))))

(defun rewrite1-IF-IF (term wrld)

; Term is known to be an IF.  If the first argument is an IF we
; may distribute it, but may not.

  (let ((term1 (arg1 term))
        (term2 (arg2 term))
        (term3 (arg3 term)))

; COMMENT '(IF (IF A T2 T3) B C) => (IF A (IF T2 B C)
;         (IF T3 B C)) WHERE T2 OR T3 ISNIL`;

    (cond
     ((and (eq (fn term1) 'IF)
           (or (equal (arg2 term1) NIL)
               (equal (arg3 term1) NIL)))
      (let ((term12 (rewrite1 `(IF ,(arg2 term1) ,term2 ,term3) wrld))
            (term13 (rewrite1 `(IF ,(arg3 term1) ,term2 ,term3) wrld)))
        (rewrite1-IF
         `(IF ,(arg1 term1) ,term12 ,term13)
         wrld)))

; COMMENT '(IF (IF A B C) D E)=> (IF A (IF B C [sic] E) (IF C D E))
;      WHERE D AND E ARE NOT NIL OR D AND E ARE T AND NIL`;

     ((eq (fn term1) 'IF)
      (cond
       ((or (and (equal term2 NIL)
                 (not (equal term3 *T*)))
            (and (equal term3 NIL)
                 (not (equal term2 *T*))))
        term)
       (t (let ((term12 (rewrite1 `(IF ,(arg2 term1) ,term2 ,term3) wrld))
                (term13 (rewrite1 `(IF ,(arg3 term1) ,term2 ,term3) wrld)))
            (rewrite1-IF
             `(IF ,(arg1 term1) ,term12 ,term13)
             wrld)))))
     (t term))))

(defun lift-and-rewrite1-IF-arg (term wrld)

;COMMENT '(FOO X (IF A B C) Y) =>
; (IF A (FOO X B Y) (FOO X C Y))`;

  (let ((term1 (find-first-IF (args term))))
    (cond
     ((null term1) term)
     (t (rewrite1-IF
         `(IF ,(arg1 term1)
              ,(rewrite1 (subst (arg2 term1) term1 term) wrld)
              ,(rewrite1 (subst (arg3 term1) term1 term) wrld))
         wrld)))))
)

; Renaming: Our function rewrite is the analogue of PLTP's NORMALIZE.

(mutual-recursion
 (defun rewrite (term wrld)
   (cond
    ((varp term) term)
    ((null term) term)
    (t (rewrite1 (cons (fn term) (rewrite-list (args term) wrld)) wrld))))
 (defun rewrite-list (terms wrld)
   (cond
    ((endp terms) nil)
    (t (cons (rewrite (car terms) wrld)
             (rewrite-list (cdr terms) wrld))))))

; -----------------------------------------------------------------
; Reduce

(defun reduce (term conslist wrld)
  (cond
   ((not (eq (fn term) 'IF))
    term)
   (t (let ((term1 (arg1 term))
            (term2 (arg2 term))
            (term3 (arg3 term)))
; COMMENT 'IF TERM1 IS NIL OR CONS, EVAL IT`;
        (case (ident term1 NIL)
          (:EQUAL (reduce term3 conslist wrld))
          (:NOT-EQUAL (reduce term2 conslist wrld))
          (otherwise
           (cond
            ((member-equal term1 conslist)
             (reduce term2 conslist wrld))
; COMMENT '(IF ATOM A B) => (IF ATOM R(A(ATOM/CONS)) R(B(ATOM/NIL)))`;
            ((varp term1)
             `(IF ,term1
                  ,(reduce term2 (cons term1 conslist) wrld)
                  ,(reduce (subst nil term1 term3) conslist wrld)))
; COMMENT '(IF (EQUAL A KNOWNLINK) B C) => (IF (EQUAL A KNOWNLINK)
;   R(B(A/KNOWNLINK))
;   R(C((EQUAL A KNOWNLINK)/NIL)))`;
            ((eq (fn term1) 'EQUAL)
             (cond
              ((explicit-valuep (arg1 term1))
               `(IF ,term1
                    ,(reduce (subst (arg1 term1) (arg2 term1) term2)
                             conslist wrld)
                    ,(reduce (subst NIL term1 term3)
                             conslist wrld)))
              ((explicit-valuep (arg2 term1))
               `(IF ,term1
                    ,(reduce (subst (arg2 term1) (arg1 term1) term2)
                             conslist wrld)
                    ,(reduce (subst NIL term1 term3)
                             conslist wrld)))
              (t `(IF ,term1
                      ,(reduce (subst *T* term1 term2)
                               conslist wrld)
                      ,(reduce (subst NIL term1 term3)
                               conslist wrld)))))
; COMMENT '(IF (IF ...) A B) => (IF R(IF) R(A) R(B))`;
            ((eq (fn term1) 'IF)
             (let ((term1 (reduce term1 conslist wrld))
                   (term2 (reduce term2 conslist wrld))
                   (term3 (reduce term3 conslist wrld)))
               (cond ((equal term3 NIL)
; COMMENT '(IF BOOL A B) => (IF BOOL R(A(BOOL/T)) R(B(BOOL/NIL)))`;
                      (cond ((boolean term1 wrld)
                             `(IF ,term1
                                  ,(reduce (subst *T* term1 term2)
                                           conslist wrld)
                                  ,(reduce (subst NIL term1 term3)
                                           conslist wrld)))
                            (t
; COMMENT '(IF RANDOM A B) => (IF RANDOM R(A(RANDOM/CONS))
;                                       R(B(RANDOM/NIL)))`;
                             `(IF ,term1
                                  ,(reduce term2
                                           (cons term1 conslist) wrld)
                                  ,(reduce (subst NIL term1 term3)
                                           conslist wrld)))))
                     (t `(IF ,term1 ,term2 ,term3)))))
            ((boolean term1 wrld)
             `(IF ,term1
                  ,(reduce (subst *T* term1 term2)
                           conslist wrld)
                  ,(reduce (subst NIL term1 term3)
                           conslist wrld)))
            (t
; COMMENT '(IF RANDOM A B) => (IF RANDOM R(A(RANDOM/CONS))
;                                       R(B(RANDOM/NIL)))`;
             `(IF ,term1
                  ,(reduce term2 (cons term1 conslist) wrld)
                  ,(reduce (subst NIL term1 term3)
                           conslist wrld))))))))))

; -----------------------------------------------------------------
; Simplification

; Renaming: Our simplify1 is PLTP's NORMALATE.

(defun simplify1 (term0 wrld)
  (let ((term1
         (reduce (rewrite (evaluate term0 wrld) wrld) nil wrld)))
    (cond
     ((equal term1 term0)
      term0)
     (t (simplify1 term1 wrld)))))

; The only difference between simplify1 and simplify is that the latter prints the
; result if it's different from the input.

(defun simplify (term wrld)
  (let ((term1 (simplify1 term wrld)))
    (cond
     ((equal term term1)
      term)
     (t (prog2$
         (simplify-msg term1 wrld)
         term1)))))

; -----------------------------------------------------------------
; Determining the Type of a Term

; Every time a new function is introduced with DEFINE we will determine its
; ``type'' and store that in the world.  PLTP did not do this.  It had
; ``on-demand'' typing: when the prover asked for the type of an expression it
; would look on the property lists of the relevant functions (as here) and if a
; function had not yet been typed it did so then and stored the result (as
; here) before continuing.  Doing it all at DEFINE time simplifies the prover
; routines because they don't have to side-effect the world.  And PLTP and PLTP(A)
; probably store the same type information.  But that is not guaranteed!

; PLTP's on-demand typing, for example, would recursively type any untyped,
; defined subroutine before typing its caller and typing was context free (with
; no sensitivity to actuals).  Since our DEFINE requires all subroutines to be
; already defined (and thus typed) we should see no change here on functions
; whose subroutines were already defined.  But PLTP did not care about the
; order of definitions.  Imagine that [/ DEFS] introduced f, g, and h in that
; order and that h is used in f and f is used in g.  Then during the
; normalation pass, g would be simplified, perhaps causing f and h to be typed
; before h is simplified.  That ``premature'' typing of f and h would persist
; after h is simplified because PLTP did not re-type at re-DEFINE time.  We
; don't investigate whether this changes behavior of any functions in [/ DEFS]
; but admit the possibility.

; The definition of boolean should be here but we moved it up so we could
; define untranslate above.

(defun put-boolean-property (fn wrld)
; Note that if fn is boolean it is also numeric.  So we may set that property
; too.
  (cond
   ((not (eq (getprop fn 'BOOLEAN :UNDEF wrld) :UNDEF))
    wrld)
   (t
    (let ((def (getprop fn 'DEFN :UNDEF wrld)))
      (cond
       ((eq def :UNDEF) wrld)
       (t (let* ((body (caddr def))
                 (wrld1 (putprop fn 'BOOLEAN T wrld)))
            (cond
             ((boolean body wrld1)
; Leave the BOOLEAN property set to T and add a NUMERIC property.
              (putprop fn 'NUMERIC T wrld1))
             (t
; Revert to a NIL BOOLEAN property for the function.
              (putprop fn 'BOOLEAN NIL wrld))))))))))

(defun numeric (term wrld)
  (cond
   ((varp term)
    nil)
   ((null term) t)
   (t (let ((funsym (fn term)))
        (case funsym
          (CONS
           (and (equal (arg1 term) nil)
                (numeric (arg2 term) wrld)))
          ((IF COND)
           (and (numeric (arg2 term) wrld)
                (numeric (arg3 term) wrld)))
          (otherwise
           (getprop funsym 'NUMERIC nil wrld)))))))

(defun put-numeric-property (fn wrld)
  (cond
   ((not (eq (getprop fn 'NUMERIC :UNDEF wrld) :UNDEF))
    wrld)
   (t
    (let ((def (getprop fn 'DEFN :UNDEF wrld)))
      (cond
       ((eq def :UNDEF) wrld)
       (t (let* ((body (caddr def))
                 (wrld1 (putprop fn 'NUMERIC T wrld)))
            (cond
             ((numeric body wrld1)
; Leave the NUMERIC property set to T.
              wrld1)
             (t
; Revert to a NIL NUMERIC property for the function.
              (putprop fn 'NUMERIC NIL wrld))))))))))

(defun typeexpr (term wrld)
  (cond
   ((varp term)
    *T*)
   ((explicit-valuep term)
    `(EQUAL X ,term))
   (t (case (fn term)
        ((CAR CDR)
         *T*)
        (CONS
         (cond ((and (explicit-valuep term)
                     (numeric term wrld))
                `(EQUAL X ,term))
               (t
                `(IF X
                     (IF ,(subst '(CAR X) 'X (typeexpr (arg1 term) wrld))
                         ,(subst '(CDR X) 'X (typeexpr (arg2 term) wrld))
                         NIL)
                     NIL))))
        (EQUAL
         `(IF X (EQUAL X ,*T*) ,*T*))
        ((IF COND)
         `(IF ,(typeexpr (arg3 term) wrld)
                ,*T*
                ,(typeexpr (arg2 term) wrld)))
        (otherwise
         (cond
          ((boolean term wrld)
           '(BOOLEAN X))
          ((numeric term wrld)
           '(NUMBERP X))
          (t (let ((typefn (getprop (fn term) 'TYPEFN 'CONSTTRUE wrld)))
               `(,typefn X)))))))))

(defun put-typefn-property (fn wrld)
  (cond
   ((not (eq (getprop fn 'TYPEFN :UNDEF wrld) :UNDEF))
    wrld)
   (t
    (let ((def (getprop fn 'DEFN :UNDEF wrld)))
      (cond
       ((eq def :UNDEF) wrld)
       (t (let ((body (caddr def))
; We always intern the type function name in the PLTP package.  Some PLTP functions,
; e.g., NUMBERP are in the ACL2 package.
                (typefn (intern-in-package-of-symbol
                         (coerce (packn1 (list fn 'TYPE)) 'string)
                         'put-typefn-property)))
            (let* ((wrld1 (putprop fn 'TYPEFN typefn wrld))
                   (wrld2 (putprop typefn 'arity 1 wrld1))
                   (type-body (subst NIL `(,typefn X) (typeexpr body wrld2)))
                   (simplified-type-body (simplify1 type-body wrld2)))
              (cond
               ((and (or (equal simplified-type-body *T*)
                         (equal simplified-type-body '(CONSTTRUE X)))
                     (not (eq (getprop fn 'TYPEFN :UNDEF wrld2) 'CONSTTRUE)))
                (let ((wrld3 (putprop fn 'TYPEFN 'CONSTTRUE wrld2)))
                  wrld3))
               (t (let* ((wrld3 (putprop typefn 'DEFN
                                         `(LAMBDA (X) ,simplified-type-body)
                                         wrld2))
                         (wrld4 (putprop typefn 'BOOLEAN t wrld3))
                         (wrld5 (putprop typefn 'NUMERIC t wrld4)))

; Note that we do not put a TYPEFN property on an auto-generated type function
; name.  For example, if the user defines FOO, FOO will have a TYPEFN property
; and that might be some auto-generated function name like FOOTYPE.  But
; FOOTYPE won't have a TYPEFN property.  If (FOO a b c) gets generalized to V
; we may generate a new hyp (FOOTYPE V).  That, in turn, might get generalized
; later and its type will be BOOLEAN because we've stored a BOOLEAN property
; for FOOTYPE.  But by NOT storing a TYPEFN for auto-generated names we can
; distinguish them from other names.  The only names that do not have TYPEFNs
; are the five primitives (CAR, CDR, CONS, EQUAL, IF) and the auto-generated
; names.

                    wrld5)))))))))))

; -----------------------------------------------------------------
; Introducing New Function Symbols and Finishing the Boot-Strap Process

; PLTP(A) checks various preconditions on definitions.  PLTP did not!  See the
; comments in unacceptable-define for a complete list of the conditions checked
; by PLTP(A).  None of these were checked by PLTP!  What you typed was what you got!

(defun legal-pltp-variable-names (lst)
  (cond ((endp lst) t)
        ((and (symbolp (car lst))
              (not (equal (symbol-package-name (car lst)) "KEYWORD")))
         (legal-pltp-variable-names (cdr lst)))
        (t nil)))

(defun negate-test (test)

; If test is of the form (NOT a) we return a.  Else we return (NOT a).  Except:
; We recognize (NOT a), (IF a NIL T), (COND a NIL T), (EQUAL a NIL), (NULL a),
; and (ZEROP A) as idioms for (NOT a), and when we say we return (NOT a) we
; actually mean (IF a NIL T).

  (cond
   ((or (eq (fn test) 'NOT)
        (eq (fn test) 'NULL)
        (and (or (eq (fn test) 'IF)
                 (eq (fn test) 'COND))
             (eq (arg2 test) NIL)
             (equal (arg3 test) *T*))
        (and (eq (fn test) 'EQUAL)
             (eq (arg2 test) NIL))
        (eq (fn test) 'ZEROP))
    (arg1 test))
   (t `(IF ,test NIL ,*T*))))

; Renaming: Our car/cdr-var is PLTP's carcdrsko.
(defun car/cdr-var (term)

; Return (mv flg var), where flg indicates whether term is a possibly empty
; car/cdr nest around a variable and var is that variable when flg=t.  We
; actually recognize SUB1 as a synonym for CDR because when we apply this
; function to determine if a newly proposed definition terminates we may
; encounter SUB1 calls.  They are eventually expanded away in DEFINE by the
; simplification step.

  (cond ((varp term)
         (mv t term))
        ((or (eq (fn term) 'CAR)
             (eq (fn term) 'CDR)
             (eq (fn term) 'SUB1))
         (car/cdr-var (arg1 term)))
        (t (mv nil nil))))

(mutual-recursion
 (defun controllerp (fn i var path term)

; The ith formal of fn, var, is a controller iff the ith actual of every
; recursive call of fn in term (which is initially the body of fn) is a car/cdr
; nest on var and var is tested against NIL on the path to each call.  This
; concept is not involved in PLTP.  As a courtesy, PLTP(A) issues a warning if a
; DEFINE introduces a function definition with no controller.  Some functions
; in the proveall, e.g., BINADD, provoke this warning.

   (cond
    ((eq fn 'COND)
; COND is primitive defined as IF and when we check its definition we
; can get fooled into thinking it's recursive! 
     t)
    ((varp term) t)
    ((null term) t)
    ((eq (fn term) fn)
     (cond
      ((and (member-eq var path)
            (mv-let (flg var1)
              (car/cdr-var (nth (+ i 1) term))
              (and flg
                   (eq var1 var))))
       (controllerp-list fn i var path (args term)))
      (t nil)))
    ((or (eq (fn term) 'IF)
         (eq (fn term) 'COND))
     (and (controllerp fn i var path (arg1 term))
          (controllerp fn i var
                       (cons (arg1 term) path)
                       (arg2 term))
          (controllerp fn i var
                       (cons (negate-test (arg1 term)) path)
                       (arg3 term))))
    (t (controllerp-list fn i var path (args term)))))

 (defun controllerp-list (fn i var path terms)
   (cond
    ((endp terms) t)
    (t (and (controllerp fn i var path (car terms))
            (controllerp-list fn i var path (cdr terms)))))))

(defun find-controllerp1 (fn i formals body)
  (cond
   ((endp formals) nil)
   ((controllerp fn i (car formals) nil body) t)
   (t (find-controllerp1 fn (+ 1 i) (cdr formals) body))))

(defun find-controllerp (fn formals body)
  (find-controllerp1 fn 0 formals body))

(defun unacceptable-define (doublet wrld)
  (cond
   ((not (and (true-listp doublet)
              (equal (length doublet) 2)))
; Doublet must be of the form (x y).
    'NOT-A-DOUBLET)
   ((not (symbolp (car doublet))) 'FN-NOT-A-SYMBOL)
; Function symbol must be a symbol.
   ((equal (symbol-package-name (car doublet)) "KEYWORD")
; Function symbol must not be a keyword.
    'FN-IS-A-KEYWORD)
   ((member-eq (car doublet) '(CARARG CDRARG))
; The user cannot define CARARG or CDRARG which are used as undefined symbols
; in our rename-car/cdr (aka, PLTP's RIDCARCDR).
    'FN-IS-A-PROTECTED-SYMBOL)
   ((assoc-eq (car doublet) wrld)
; The proposed function name is completely new.
    'NOT-NEW-FN-SYMBOL)
   ((assoc-eq (intern-in-package-of-symbol
               (coerce (packn1 (list (car doublet) 'TYPE)) 'string)
               (car doublet))
              wrld)
; The function's typefunction name is new.
    'NOT-NEW-TYPEFN-SYMBOL)
   ((not (and (true-listp (cadr doublet))
              (equal (length (cadr doublet)) 3)
              (eq (car (cadr doublet)) 'LAMBDA)))
; The purported lambda expession has the right basic shape.
    'NOT-A-LAMBDA)
   ((not (true-listp (cadr (cadr doublet))))
; The list of formals is a true-list.
    'FORMALS-NOT-TRUE-LIST)
   ((not (legal-pltp-variable-names (cadr (cadr doublet))))
; The list of formals are legal variable names.
    'ILLEGAL-FORMAL-VARIABLE-NAME)
   ((not (no-duplicatesp (cadr (cadr doublet))))
; There are no duplicate formals.
    'DUPLICATE-FORMAL)
   ((not (let ((wrld1 (putprop (car doublet)
                               'arity
                               (length (cadr (cadr doublet)))
                               wrld)))
           (utermp (caddr (cadr doublet)) wrld1)))
; The body is a term provided the new symbol has the appropriate arity.  This
; check guarantees that all subfunctions used in the definition have already been
; introduced and are called with the correct number of arguments.
    'BODY-NOT-A-TERM)
   (t (let ((tbody (translate (caddr (cadr doublet)))))
        (cond
         ((not (subsetp-eq (all-vars tbody)
                           (cadr (cadr doublet))))
; There are no free variables in the body.
          'FREE-VARS-IN-BODY)
         ((not (find-controllerp (car doublet)
                                 (cadr (cadr doublet))
                                 tbody))
; The function has at least one controller (or else a warning is
; issued).
          (prog2$
           (cw "~x0 may not terminate.~%" (car doublet))
           nil))
         (t nil))))))

(defun define-immediate (fn formals body wrld)

; Store the DEFN property of fn along with the other properties maintained by
; PLTP(A).  See the comment after define-simplified for an extended comparison with
; september-core.txt.

  (let* ((wrld1 (putprop fn
                         'ARITY
                         (length formals)
                         wrld))
         (wrld2 (putprop fn
                         'DEFN
                         (list 'LAMBDA formals body)
                         wrld1))
         (wrld3 (put-boolean-property fn wrld2))
         (wrld4 (put-numeric-property fn wrld3))
         (wrld5 (put-typefn-property fn wrld4)))
    wrld5))

(defun define-simplified (fn formals body wrld)
; Store the DEFN of fn, simplify it, and re-store it.  See the following
; comment.
  (let* ((wrld1 (define-immediate fn formals body wrld))
         (wrld2 (putprop* `((,fn BOOLEAN :UNDEF)
                            (,fn NUMERIC :UNDEF)
                            (,fn TYPEFN :UNDEF))
                          wrld1)))
    (define-immediate fn formals
      (simplify1 body wrld2)
      wrld2)))

; Discrepancy with September-Core.txt

; In Listing-F, file [/ INPUT] pg 3, we see a relatively straightforward
; FUNCTION DEFINE which just stores the DEFN property and adds the function
; name to ALLFNS.  Below that is FUNCTION NORMDEF which simplifies an existing
; definition and DEFINEs it again.  Then, in Listing-H, file [/] pg 2, we see
; how PLTP was initialized: all the source code was loaded and then [/ DEFS]
; (Listing-I, pg 8) was loaded and then APPLIST(ALLFNS,NORMDEF) was performed.
; Thus, when PLTP was fired up as of September, 1973, it automatically included
; all the definitions in [/ DEFS] and then re-defined all the definitions with
; simplified bodies.  However, if the user of that system then did an
; interactive DEFINE, the body was not simplified unless the user explicitly
; invoked NORMDEF.

; Here we sort of simulate that but only roughly.  We define DEFINE so that it
; stores the unsimplified definition and then simplifies the body and redefines
; it.  So for definitions in [/ DEFS] this gives us the same definitions as
; PLTP used.  However, it gives us possibly different (simplified) definitions
; for anything done interactively in our session.

(defun define1 (doublet state)
  (let* ((wrld (@ wrld))
         (reason (unacceptable-define doublet wrld)))
    (cond
     (reason
      (er soft 'PLTP
          "~x0 is an unacceptable PLTP(A) definition.  Reason: ~x1!"
          doublet
          reason))
     (t
      (let ((wrld1
             (define-simplified
               (car doublet)
               (cadr (cadr doublet))
               (translate (caddr (cadr doublet)))
               wrld)))
        (er-progn
         (assign wrld wrld1)
         (value (car doublet))))))))

(defmacro define (doublet)
  `(define1 (quote ,doublet) state))

; The requirement that all functions used in a DEFINE (except the one being
; defined) already have arities in wrld means that we must have a way to
; declare permanently undefined symbols.  So we introduce DCL.  PLTP did not
; have DCL.

(defun unacceptable-dcl (doublet wrld)
  (cond
   ((not (and (true-listp doublet)
              (equal (length doublet) 2)))
    'NOT-A-DOUBLET)
   ((not (symbolp (car doublet))) 'FN-NOT-A-SYMBOL)
   ((equal (symbol-package-name (car doublet)) "KEYWORD")
    'FN-IS-A-KEYWORD)
   ((member-eq (car doublet) '(CARARG CDRARG))
    'FN-IS-A-PROTECTED-SYMBOL)
   ((assoc-eq (car doublet) wrld)
; The proposed function name is completely new.
    'NOT-NEW-FN-SYMBOL)
   ((not (true-listp (cadr doublet)))
    'FORMALS-NOT-TRUE-LIST)
   ((not (legal-pltp-variable-names (cadr doublet)))
    'ILLEGAL-FORMAL-VARIABLE-NAME)
   ((not (no-duplicatesp (cadr doublet)))
    'DUPLICATE-FORMAL)
   (t nil)))

(defun dcl1 (doublet state)
  (let* ((wrld (@ wrld))
         (reason (unacceptable-dcl doublet wrld)))
    (cond
     (reason
      (er soft 'PLTP
          "~x0 is an unacceptable PLTP(A) declaration.  Reason: ~x1!"
          doublet
          reason))
     (t
      (let* ((wrld1 (putprop (car doublet) 'arity (length (cadr doublet)) wrld))
             (wrld2 (putprop (car doublet) 'defn :undef wrld1))
             (wrld3 (putprop (car doublet) 'boolean nil wrld2))
             (wrld4 (putprop (car doublet) 'numeric nil  wrld3))
             (wrld5 (putprop (car doublet) 'TYPEFN 'CONSTTRUE wrld4)))
        (er-progn
         (assign wrld wrld5)
         (value (car doublet))))))))

(defmacro dcl (doublet)
  `(dcl1 (quote ,doublet) state))

(defun boot-strap1 (acl2::state)
; These functions are used by parts of the prover and so must
; be defined as part of the boot process.
  (er-progn
   (boot-strap0 acl2::state)
   (define (COND (LAMBDA (X Y Z) (IF X Y Z))))
   (define (AND (LAMBDA (X Y) (IF X (IF Y T NIL) NIL))))
   (define (ADD1 (LAMBDA (X) (CONS NIL X))))
   (define (SUB1 (LAMBDA (X) (CDR X))))
   (define (IMPLIES (LAMBDA (X Y) (IF X (IF Y T NIL) T))))
   (define (NOT (LAMBDA (X) (IF X NIL T))))
   (define (OR (LAMBDA (X Y) (IF X T (IF Y T NIL)))))
   (define (BOOLEAN (LAMBDA (X) (IF X (EQUAL X T) T))))
   (define (NUMBERP (LAMBDA (X) (IF X (IF (CAR X) NIL (NUMBERP (CDR X))) T))))
   (define (CONSTTRUE (LAMBDA (X) T)))
   (define (ZEROP (LAMBDA (X) (EQUAL X 0))))

; We always end the boot-strap with a special mark so we don't undo into
; the boot-strap world:

   (assign wrld (putprop 'BOOT-STRAP 'DONE T (@ wrld)))
   (value `(((length (@ wrld)) ,(length (@ wrld)))
            ((props :feature) ,(props :feature))))))

(defmacro boot-strap nil '(boot-strap1 acl2::state))

(defun roll-back-through1 (name rwrld)
  (cond
   ((or (endp rwrld)
        (eq (car (car rwrld)) 'BOOT-STRAP))
    nil)
   ((and (eq (car (car rwrld)) name)
         (eq (cadr (car rwrld)) 'arity))
    (cdr rwrld))
   (t (roll-back-through1 name (cdr rwrld)))))

(defun last-user-fn1 (rwrld wrld)
; Rwrld is a reversed initial segment of wrld and is known to include the full
; boot-strap block of properties.  We find the first name in rwrld that has an
; ARITY but no TYPEFN property in wrld.  We return BOOT-STRAP if we get to the
; marker in rwrld that indicates the end of the boot-strap.
  (cond
   ((or (endp rwrld)
        (eq (car (car rwrld)) 'BOOT-STRAP))
    'BOOT-STRAP)
   ((and (eq (cadr (car rwrld)) 'arity)
         (eq (getprop (car (car rwrld)) 'typefn :undef wrld) :undef))
    (car (car rwrld)))
   (t (last-user-fn1 (cdr rwrld) wrld))))

(defun roll-back-through (name wrld state)
  (let* ((rwrld1 (revappend wrld nil))
         (rwrld2 (roll-back-through1 name rwrld1)))
    (cond
     ((null rwrld2)
      (er soft "PLTP(A)"
          "~x0 is either an unknown PLTP function name or else a PLTP ~
           primitive that may not be undone."
          name))
     (t (er-progn
         (assign wrld (revappend rwrld2 nil))
         (value (last-user-fn1 rwrld2 wrld)))))))

(defmacro rbt (name)
  `(roll-back-through ',name (@ wrld) state))

; -----------------------------------------------------------------
; Fertilization

; PLTP(A)'s fertilization is different from PLTP's.  When PLTP fertilized 
; (IF (EQUAL a b) (P a) (Q a b)) it ``defined'' (*1) to be (NOT (EQUAL a b)) and
; then produced

; (IF (IF (P b) T (*1))
;     (IF (Q a b) T (EQUAL a b))
;     NIL)

; which is actually propositionally equivalent to the input if one can use the
; definition of *1.  The trouble with this argument is that *1 is not really a
; defineable function since it contains free variables.  But ignoring that, the
; advantage of this approach is that PLTP could then recur root-and-branch
; through the propositional structure of the conjecture and do fertilizations
; anywhere it found an opportunity.  However, it only did the first one it
; found.

; In PLTP(A) we don't want to define functions on the fly during proofs and we
; don't want to ``define'' things like *1.  So we accept that fertilization
; does not return an equivalent term.  It is possibly a generalization: it must
; return a term that, if valid, entails the validity of the input.  But if that
; is the specification, it cannot recur root-and-branch because the new terms
; are not equivalent to the ones they replace.  Our fertilization must confine
; itself to top-level conjunctions, looking for opportunities to fertilize in
; chains of implications.  E.g.,
; (IF (IF t1 (IF (equal a b) (P a) T) T)
;     (R a b)
;     NIL)
; can be fertilized (generalized) to
;  (IF (IF t1 (P b) T)
;      (R a b)
;      NIL)
; but if the NIL in the input is replaced by a non-NIL term, fertilization will
; not apply.  We discuss this further below but this is offered as a
; foreshadowing of what's coming, which is more complicated than PLTP's
; algorithm.  And remember:  the point of this new complexity is just to
; repair a suspicious step in PLTP, not to improve its heuristics.

; One last point: Issues like this drove us to a major design change when we
; developed the next prover, THM and then NQTHM.  We abandoned PLTP's
; commitment to keeping the entire problem expressed as a single formula and
; went to the ``pool'' of subgoals, each a clause and implicitly conjoined.  By
; splitting conjuncts apart we don't repeatedly parse the IF-structure looking
; for them, and we don't risk cross-multiplying the cases from one conjunct
; with those of another via full IF-normalization.  (PLTP's REWRITE has a very
; complicated (inadequate) set of rules to avoid normalization across
; conjuncts.)  Furthermore, by going to clauses fertilization no longer has to
; worry about literals that intervene between the equality in the
; ``hypothesis'' and the equality in the ``conclusion.''  For example,
; (IF t1 (IF (EQUAL a b) (IF t2 (EQUAL (f a) (g b)) T) T) T)
; doesn't give PLTP an opportunity for cross-fertilization:  that can
; only happen on goals in which the equality hypothesis and conclusion are
; adjacent in the same IF (IF (EQUAL a b) (EQUAL (f a) (f b)) T).

; In fact, PLTP(A) does improve upon PLTP in this regard and looks for a
; cross-fertilizable EQUAL deeper in the ``conclusion.''

(defun fertilization-possiblep (term)
  (let ((term1 (arg1 term))
        (term2 (arg2 term))
        (term3 (arg3 term)))
    (cond ((and (eq (fn term1) 'EQUAL)
                (not (equal term3 NIL)))
           (let ((lhs1 (arg1 term1))
                 (rhs1 (arg2 term1)))
             (and (or (and (not (explicit-valuep lhs1))
                           (occur lhs1 term2))
                      (and (not (explicit-valuep rhs1))
                           (occur rhs1 term2))))))
          (t nil))))

(mutual-recursion
 (defun cross-fertilization-possiblep (code lhs rhs term)

; Code is XRL or XLR meaning cross-fertilize rhs-for-lhs, or vice versa.  Let's
; call lhs the target if code is XRL and rhs the target otherwise.  The target
; must not be an explicit value -- that check should be made before calling
; this function.  We determine whether there is an EQUALity in term such that
; the target occurs on the corresponding side.

   (cond
    ((or (varp term)
         (null term))
     nil)
    ((eq (fn term) 'EQUAL)
     (cond ((eq code 'XRL)
            (occur lhs (arg1 term)))
           (t (occur rhs (arg2 term)))))
    (t (cross-fertilization-possiblep-list code lhs rhs (args term)))))
 (defun cross-fertilization-possiblep-list (code lhs rhs terms)
   (cond
    ((endp terms) nil)
    (t (or (cross-fertilization-possiblep code lhs rhs (car terms))
           (cross-fertilization-possiblep-list code lhs rhs (cdr terms)))))))

(mutual-recursion
 (defun do-cross-fertilize (code lhs rhs term)

; Code is XRL or XLR meaning cross-fertilize rhs-for-lhs, or vice versa.  Let's
; call lhs the ``target'' if code is XRL and rhs the ``target'' otherwise.  We
; assume that the target is not an explicit value.  We cross fertilize into
; every EQUALity for which cross-fertilization is possible.  Otherwise we
; substitute left-for-right or right-for-left as per code everywhere outside
; the EQUALs.  This is a generalization of cross-fertilization in PLTP, where
; we only cross-fertilize when term itself is an EQUAL, but we have to allow
; cross-fertilization into terms containing IFs because of the fact that we
; don't do induction on numbers and some of PLTP's EQUALs become (IF A1 T
; (EQUAL lhs' rhs')).

   (cond
    ((equal term (cond ((eq code 'XRL) lhs) (t rhs)))
     (cond ((eq code 'XRL) rhs) (t lhs)))
    ((or (varp term)
         (null term))
     term)
    ((eq (fn term) 'EQUAL)
     (cond ((eq code 'XRL)
            (cond ((occur lhs (arg1 term))
                   `(EQUAL ,(subst rhs lhs (arg1 term)) ,(arg2 term)))
                  (t (subst rhs lhs term))))
           (t
            (cond ((occur rhs (arg2 term))
                   `(equal ,(arg1 term) ,(subst lhs rhs (arg2 term))))
                  (t (subst lhs rhs term))))))
    (t (cons (fn term)
             (do-cross-fertilize-list code lhs rhs (args term))))))
 (defun do-cross-fertilize-list (code lhs rhs terms)
   (cond
    ((endp terms) nil)
    (t (cons (do-cross-fertilize code lhs rhs (car terms))
             (do-cross-fertilize-list code lhs rhs (cdr terms)))))))

(defun do-fertilize1 (action term1 term2 term3)

; Our caller created term2 from the true branch of an IF whose test and false
; branch were term1 and term3 respectively.  It did so by performing action,
; which is one of XRL, XLR, MRL, or MLR, where the X indicates cross
; fertilization, the M massive substitution, and the `rl' sequences mean
; ``substitute r for l.''  Our caller has already determined the action and
; carried it out; we just report it and form the final IF-term from the three
; pieces.  We would be justified in creating (IF term1 term2 term3) except that
; would cause the prover to loop when the next fertilization undoes the one
; just done.  So we have to delete the equality (term1) governing term2 while
; insuring that the caller's input is proveable if our answer is.

; (IF term1 term2 term3)
; <-->
; (term1 --> term2) & ((NOT term1) --> term3)
; <--
; term2 & ((NOT term1) --> term3)
; <-->
; term2 & (term3 v term1)
; <-->
; (IF term2 (IF term3 T term1) NIL)

; Note that if term3 is definitely non-NIL then this reduces to term2.  Note
; also that fertilization does not maintain equivalence!  It merely insures
; that the output is sufficient to prove the input.

  (prog2$
   (do-fertilize1-msg action term1 (eq (ident term3 NIL) :NOT-EQUAL))
   (cond
    ((eq (ident term3 NIL) :NOT-EQUAL)
     term2)
    (t `(IF ,term2 (IF ,term3 ,*T* ,term1) NIL)))))


(defun do-fertilize (term)

; We assume that (fertilization-possiblep term) is true.  Among other things
; this means that term is an IF whose test is an EQUAL.  We have to decide
; whether we can do cross fertilization or just massive substitution and have
; to decide which side of the equality to substitute for which.  The result is
; a term' that, if proveable under some additional hyps, means that term is
; proveable under those same additional hyps.

  (let* ((term1 (arg1 term))
         (term2 (arg2 term))
         (term3 (arg3 term))
         (lhs1 (arg1 term1))
         (rhs1 (arg2 term1)))

; To make the code simpler we will first determine if any cross-fertilization
; is possible and then repeat a lot of the work to decide which one to do.  If
; we were dealing with larger terms this code would have to be optimized.

    (cond
     ((or (and (not (explicit-valuep rhs1))
               (cross-fertilization-possiblep 'XLR lhs1 rhs1 term2))
          (and (not (explicit-valuep lhs1))
               (cross-fertilization-possiblep 'XRL lhs1 rhs1 term2)))
; Cross-fertilization is possible.
; Note:  We intentionally make the xfert and noxfert code symmetric, unlike PLTP.
      (cond
       ((and (not (explicit-valuep rhs1))
             (cross-fertilization-possiblep 'XLR lhs1 rhs1 term2))
        (cond
         ((and (not (explicit-valuep lhs1))
               (cross-fertilization-possiblep 'XRL lhs1 rhs1 term2))
          (cond
           ((< (term-size rhs1) (term-size lhs1))
            (do-fertilize1 'XRL term1
                           (do-cross-fertilize 'XRL lhs1 rhs1 term2)
                           term3))
           (t (do-fertilize1 'XLR term1
                             (do-cross-fertilize 'XLR lhs1 rhs1 term2)
                             term3))))
         (t (do-fertilize1 'XLR term1
                           (do-cross-fertilize 'XLR lhs1 rhs1 term2)
                           term3))))
       (t (do-fertilize1 'XRL term1
                         (do-cross-fertilize 'XRL lhs1 rhs1 term2)
                         term3))))
; We'll do a massive substitution.
     ((and (not (explicit-valuep rhs1))
           (occur rhs1 term2))
      (cond
       ((and (not (explicit-valuep lhs1))
             (occur lhs1 term2))
        (cond
         ((< (term-size rhs1) (term-size lhs1))
          (do-fertilize1 'MRL term1 (subst rhs1 lhs1 term2) term3))
         (t (do-fertilize1 'MLR term1 (subst lhs1 rhs1 term2) term3))))
       (t (do-fertilize1 'MLR term1 (subst lhs1 rhs1 term2) term3))))
     (t (do-fertilize1 'MRL term1 (subst rhs1 lhs1 term2) term3)))))

(defun fertilize-through (term)

; As long as term is a chain of implications, e.g., (hyp1 --> (hyp2 --> ... -->
; ((a=b) --> concl)...))  we dive through it looking for the first fertilizable
; hyp.  We also dive through conjunctions in the conclusion.  Thus, for example,
; (IF test1
;     (IF (IF test2 (IF (equal A B) (CAR B) (cdr a)) t)
;         (IF test3 (IF test4 (IF (equal c d) (car d) (cdr d)) t) t)
;         nil)
;     t)
; fertilizes to
; (IF test1
;     (IF (IF test2 (IF (CAR A) (IF (cdr a) t (equal A B)) nil) t)
;         (IF test3 (IF test4 (IF (equal c d) (car d) (cdr d)) t) t)
;         nil)
;     t)
; where t denotes (cons nil nil).

; (thm (implies
;       (IF test1
;           (IF (IF test2 (IF (car a) (IF (cdr a) t (equal a b)) nil) t)
;               (IF test3 (IF test4 (IF (equal c d) (car d) (cdr d)) t) t)
;               nil)
;           t)
;       (IF test1
;           (IF (IF test2 (IF (equal a b) (car b) (cdr a)) t)
;               (IF test3 (IF test4 (IF (equal c d) (car d) (cdr d)) t) t)
;               nil)
;           t)))

  (cond
   ((eq (fn term) 'IF)
    (cond ((fertilization-possiblep term)
           (do-fertilize term))
          ((equal (arg3 term) *T*)
           (let ((term2 (fertilize-through (arg2 term))))
             (cond
              ((equal term2 (arg2 term))
               term)
              (t `(IF ,(arg1 term) ,term2 ,*T*)))))
          ((equal (arg2 term) *T*)
; Note that (IF hyp T concl) is equal to (IF (NOT hyp) concl T), so
; this case is just another form of implication.
           (let ((term3 (fertilize-through (arg3 term))))
             (cond
              ((equal term3 (arg3 term))
               term)
              (t `(IF ,(arg1 term) ,*T* ,term3)))))
          ((equal (arg3 term) NIL)
           (let ((term1 (fertilize-through (arg1 term))))
             (cond
              ((equal term1 (arg1 term))
               (let ((term2 (fertilize-through (arg2 term))))
                 (cond ((equal term2 (arg2 term))
                        term)
                       (t `(IF ,(arg1 term) ,term2 NIL)))))
              (t `(IF ,term1 ,(arg2 term) NIL)))))
          (t term)))
   (t term)))

(defun fertilize (term wrld)
  (let ((term1 (fertilize-through term)))
    (cond
     ((equal term term1) term)
     (t (prog2$
         (fertilize-msg term1 wrld)
         term1)))))


; -----------------------------------------------------------------
; Generalization

(mutual-recursion
 (defun all-non-trivial-subterms (term ans)
   (cond ((varp term) ans)
         ((explicit-valuep term) ans)
         (t (all-non-trivial-subterms-list (args term)
                                           (cond
                                            ((or (lispprim term)
                                                 (member-equal term ans))
                                             ans)
                                            (t (cons term ans)))))))
 (defun all-non-trivial-subterms-list (terms ans)
   (cond
    ((endp terms) ans)
    (t (all-non-trivial-subterms-list
        (cdr terms)
        (all-non-trivial-subterms (car terms) ans))))))

(defun keeperp (term terms)
; We return nil if term occurs in any element of terms except itself.
  (cond ((endp terms) t)
        ((equal term (car terms)) (keeperp term (cdr terms)))
        ((occur term (car terms)) nil)
        (t (keeperp term (cdr terms)))))

(defun collect-largest1 (tail terms)
  (cond ((endp tail) nil)
        ((keeperp (car tail) terms)
         (cons (car tail) (collect-largest1 (cdr tail) terms)))
        (t (collect-largest1 (cdr tail) terms))))

(defun collect-largest (terms)
  (collect-largest1 terms terms))

(defun largest-common-subterms (hyp-flg term1 term2)
  (collect-largest
   (intersection-equal
    (cond (hyp-flg
           (all-non-trivial-subterms-list
            (cond ((applicationp term1) (args term1))
                  (t nil))
            nil))
          (t (all-non-trivial-subterms term1 nil)))
    (all-non-trivial-subterms term2 nil))))

; Renaming: Our generalizable-subterms is PLTP's GENRLT1.
(mutual-recursion
 (defun generalizable-subterms (term)
   (cond
    ((varp term) nil)
    ((null term) nil)
    ((eq (fn term) 'EQUAL)
     (union-equal (largest-common-subterms nil (arg1 term) (arg2 term))
                  (generalizable-subterms-list (args term))))
    ((and (eq (fn term) 'IF)
          (equal (arg3 term) *T*))
     (union-equal (largest-common-subterms t (arg1 term) (arg2 term))
                  (generalizable-subterms-list (args term))))
    (t (generalizable-subterms-list (args term)))))

 (defun generalizable-subterms-list (terms)
   (cond
    ((endp terms) nil)
    (t (union-equal (generalizable-subterms (car terms))
                    (generalizable-subterms-list (cdr terms))))))
 )

; Renaming: Our add-type-restrictions is PLTP's addtypestmts.
(defun add-type-restrictions (pairs term wrld)
  (cond
   ((endp pairs) term)
   ((occur (cdr (car pairs)) term)
    (let ((x (typeexpr (car (car pairs)) wrld)))
      (cond
       ((not (eq (fn x) 'consttrue))
        `(IMPLIES ,(subst (cdr (car pairs)) 'X x)
                  ,(add-type-restrictions (cdr pairs) term wrld)))
       (t (add-type-restrictions (cdr pairs) term wrld)))))
   (t (add-type-restrictions (cdr pairs) term wrld))))

(defun split-conjunction (term)

; If term is a conjunction, return (mv t a b) where a and b are the two
; conjuncts.  In this case, term is equivalent to (IF a b NIL) but may have
; actually been (IF a' NIL b).  Else return (mv nil term nil).

  (cond
   ((eq (fn term) 'IF)
    (cond
     ((eq (arg2 term) NIL)
      (mv t `(NOT ,(arg1 term)) (arg3 term)))
     ((eq (arg3 term) NIL)
      (mv t (arg1 term) (arg2 term)))
     (t (mv nil term nil))))
   (t (mv nil term nil))))

(defun reassemble-conjunction (flg a b)
  (cond
   (flg `(IF ,a ,b NIL))
   (t a)))

; Renaming: Our generalize is PLTP's GENRLIZE.
(defun generalize (term wrld)
  (mv-let (flg a b)
    (split-conjunction term)
    (prog2$
     (split-conjunction-msg flg)
     (let* ((substlist (new-vars (generalizable-subterms a) term))
            (a1 (add-type-restrictions substlist (subst* substlist a) wrld)))
       (prog2$
        (generalize-msg flg substlist a1 wrld)
        (reassemble-conjunction flg a1 b))))))

; -----------------------------------------------------------------
; Induction

; Renaming: PLTP called the second component below the ARGLIST.
(defrec candrec (score indvars bombbay failures) nil)

(defun collect-indvars1 (pocket args)

; Loop through pocket collecting into args the var of every car/cdr nest around
; a var.  Return the accumulated vars or t if we encounter a non-car/cdr-var
; term.

  (cond
   ((endp pocket)
    args)
   (t (mv-let (flg var)
        (car/cdr-var (car pocket))
        (cond (flg
               (collect-indvars1 (cdr pocket) (add-to-set-eq var args)))
              (t t))))))

(defun collect-indvars (bomblist args bombs)
  (cond
   ((endp bomblist)
    (mv t args bombs))
   (t (let* ((pocket (car bomblist))
             (args (collect-indvars1 pocket args)))
        (cond
         ((eq args t)
          (mv nil nil nil))
         (t (collect-indvars (cdr bomblist)
                             args
                             (append pocket bombs))))))))

(defun getcands (analysis)
; Each element of analysis is of the form: (*** fn pockets others fn ***)
  (cond
   ((endp analysis)
    nil)
   (t (mv-let (flg indvars bombs)
        (collect-indvars (caddr (car analysis)) nil nil)
        (cond (flg
               (cons (make candrec
                           :score 1
                           :indvars indvars
                           :bombbay bombs
                           :failures (cadddr (car analysis)))
                     (getcands (cdr analysis))))
              (t (getcands (cdr analysis))))))))

(defun merge2 (cand1 cand2)
  (cond ((intersectp-eq (access candrec cand1 :indvars)
                        (access candrec cand2 :indvars))
         (make candrec
               :score (+ 1 (access candrec cand2 :score))
               :indvars (union-eq (access candrec cand1 :indvars)
                                  (access candrec cand2 :indvars))
               :bombbay (union-equal (access candrec cand1 :bombbay)
                                     (access candrec cand2 :bombbay))
               :failures (union-equal (access candrec cand1 :failures)
                                      (access candrec cand2 :failures))))
        (t nil)))

(defun do-first-merge (cand1 candlist)
  (cond ((endp candlist) nil)
        (t (let ((merged-cand (merge2 cand1 (car candlist))))
             (cond
              (merged-cand
               (cons merged-cand (cdr candlist)))
              (t (cons (car candlist)
                       (do-first-merge cand1 (cdr candlist)))))))))

(defun merge-cands (candlist)
  (cond
   ((endp (cdr candlist)) candlist)
   (t (let ((candlist1 (do-first-merge (car candlist) (cdr candlist))))
        (cond
         ((equal candlist1 (cdr candlist))
; We failed to put (car candlist) anywhere into (cdr candlist).  So
; we skip over (car candlist) and merge the rest.  Since merge2 is
; commutative, this works.
          (cons (car candlist)
                (merge-cands (cdr candlist))))
         (t (merge-cands candlist1)))))))

(defun choose-high (candlist)
  (cond
   ((endp candlist) nil)
   (t (let ((high-cands (choose-high (cdr candlist))))
        (cond
         ((null high-cands) (list (car candlist)))
         ((equal (access candrec (car candlist) :score)
                 (access candrec (car high-cands) :score))
          (cons (car candlist) high-cands))
         ((< (access candrec (car candlist) :score)
             (access candrec (car high-cands) :score))
          high-cands)
         (t (list (car candlist))))))))

; Note: PLTP broke some induction ties by counting how many steps a CONS for
; the induction variable allowed EVAL to take.  This was called RATECANDS.
; This requires augmenting EVAL to count steps which makes it ugly.  We decided
; to abandon this heuristic and use one that is actually more appropriate: we
; implement the notion of flawed inductions as used in NQTHM and ACL2. An
; induction is flawed if it modifies variables that some functions hold
; constant in recursion.  In PLTP(A), rate-cands below, instead of counting steps,
; counts such flaws.

(defun unchangedp (i var calls)
  (cond ((endp calls) t)
        ((eq var (nth i (args (car calls))))
         (unchangedp i var (cdr calls)))
        (t nil)))

(defun collect-unchanged1 (i formals actuals calls)

; When i is 0, formals is the list of formal variables for some function fn,
; calls is a list of all the recursive calls of fn in the definition of fn.
; Actuals is the list of actuals in some (other) call of fn.  For every formal
; that appears unchanged in every call in calls, we collect the corresponding
; actual (provided that actual is a variable symbol).

  (cond ((endp formals) nil)
        ((and (varp (car actuals))
              (unchangedp i (car formals) calls))
         (add-to-set-eq (car actuals)
                        (collect-unchanged1 (+ 1 i)
                                            (cdr formals)
                                            (cdr actuals)
                                            calls)))
        (t (collect-unchanged1 (+ 1 i) (cdr formals) (cdr actuals) calls))))

(mutual-recursion
 (defun collect-unchanged (term wrld)
   (cond
    ((varp term) nil)
    ((null term) nil)
    (t (let* ((fn (fn term))
              (actuals (args term))
              (ans (collect-unchanged-list actuals wrld))
              (defn (getprop fn 'defn :undef wrld)))
         (cond
          ((or (lispprim fn)
               (eq defn :undef))
           ans)
          (t (let ((formals (cadr defn))
                   (body (caddr defn)))
               (union-eq
                (collect-unchanged1 0 formals actuals (all-calls fn body))
                ans))))))))

 (defun collect-unchanged-list (terms wrld)
   (cond ((endp terms) nil)
         (t (union-eq (collect-unchanged (car terms) wrld)
                      (collect-unchanged-list (cdr terms) wrld)))))
 )

(defun rate-cand (cand unchanged)

; Suppose cand suggests induction on A, B, C, but that some terms in the
; conjecture suggest keeping B and C unchanged. Then cand's new score will be
; -2.  That is, we set the score of cand to the negative of the cardinality of
; the intersection of cand's indvars variables with the unchanged variables in
; the term.  We use the negation so that the candidate with the highest score,
; i.e., fewest disagreements with other inductions, is chosen.  As noted above,
; PLTP did not use this heuristic; it counted EVAL steps.

  (change candrec cand
          :score (- (length
                     (intersection-eq
                      (access candrec cand :indvars)
                      unchanged)))))

(defun rate-cands1 (candlist unchanged)
  (cond
   ((endp candlist) nil)
   (t (cons (rate-cand (car candlist) unchanged)
            (rate-cands1 (cdr candlist) candlist)))))

(defun rate-cands (candlist indterm wrld)
  (rate-cands1 candlist (collect-unchanged indterm wrld)))

(defun choose-new (candlist indvarlist)
  (cond
   ((endp candlist) nil)
   (t (cons (change candrec (car candlist)
                    :score (length
                            (set-difference-eq
                             (access candrec (car candlist) :indvars)
                             indvarlist)))
            (choose-new (cdr candlist) indvarlist)))))

; Renaming: Our rename-car/cdr is PLTP's RIDCARCDR.
(mutual-recursion
 (defun rename-car/cdr (term)

; We eliminate all CAR and CDR calls in term by replacing them with calls to
; undefined functions.  See the discussion of FUNCTION APPSUB1 in
; september-core.txt to see why we don't do it the way PLTP did.

   (cond
    ((varp term) term)
    ((explicit-valuep term) term)
    ((eq (fn term) 'CAR) `(CARARG ,(rename-car/cdr (arg1 term))))
    ((eq (fn term) 'CDR) `(CDRARG ,(rename-car/cdr (arg1 term))))
    (t (cons (fn term)
             (rename-car/cdr-list (args term))))))
 (defun rename-car/cdr-list (terms)
   (cond
    ((endp terms) nil)
    (t (cons (rename-car/cdr (car terms))
             (rename-car/cdr-list (cdr terms))))))
 )

(mutual-recursion
 (defun collect-car-cdr-calls-outside (fn term)
   (cond ((varp term) nil)
         ((null term) nil)
         ((eq (fn term) fn) nil)
         (t (let ((ans (collect-car-cdr-calls-outside-list fn (args term))))
              (cond ((or (eq (fn term) 'CAR)
                         (eq (fn term) 'CDR))
                     (cons term ans))
                    (t ans))))))
 (defun collect-car-cdr-calls-outside-list (fn terms)
   (cond ((endp terms) nil)
         (t (union-equal (collect-car-cdr-calls-outside fn (car terms))
                         (collect-car-cdr-calls-outside-list fn (cdr terms)))))))

(mutual-recursion
 (defun collect-pockets (fn term)
   (cond
    ((varp term) nil)
    ((null term) nil)
    ((eq (fn term) fn)
     (cons (collect-car-cdr-calls-outside-list fn (args term))
           (collect-pockets-list fn (args term))))
    (t (collect-pockets-list fn (args term)))))
 (defun collect-pockets-list (fn terms)
   (cond
    ((endp terms) nil)
    (t (append (collect-pockets fn (car terms))
               (collect-pockets-list fn (cdr terms)))))))

(mutual-recursion
 (defun collect-others (fn term)
   (cond
    ((varp term) nil)
    ((null term) nil)
    ((or (eq (fn term) 'CAR)
         (eq (fn term) 'CDR))
     (cons term (collect-others fn (arg1 term))))
    ((eq (fn term) fn) nil)
    (t (collect-others-list fn (args term)))))

 (defun collect-others-list (fn terms)
   (cond
    ((endp terms) nil)
    (t (append (collect-others fn (car terms))
               (collect-others-list fn (cdr terms)))))))

(mutual-recursion
 (defun induction-analysis (term wrld)

; PLTP's induction analysis used EVALUATE which accumulated ``bomb''
; information as a side-effect.  Our evaluate does not.  So we sweep term, eval
; the body of every function call, and collect ``bomb'' information from the
; expanded bodies.  We return an almost-PLTP-style ``analysis.''  The returned
; analysis is a list of tuples, each of the form

; (*** fn (... pocket_i ...) (... other_i ...) fn ***)

; For comparison, PLTP's ANALYSIS had same components but the elements were in
; possibly different orders.

; Here, fn is the recursive function that was expanded, each pocket_i
; corresponds to one recursive call of fn and lists car/cdr calls appearing
; among the actuals of the recursive call.  Each other_i is a car/cdr call
; appearing in the expanded body but outside any recursive call.

   (cond
    ((varp term) nil)
    ((null term) nil)
    (t (let* ((fn (fn term))
              (actuals (args term))
              (analysis (induction-analysis-list actuals wrld)))
         (cond
          ((lispprim fn) analysis)
          (t (let ((defn (getprop fn 'DEFN :undef wrld)))
               (cond
                ((eq defn :undef) analysis)
                (t (let* ((formals (cadr defn))
                          (body (caddr defn))
                          (xbody
                           (eval body
                                 (pairlis$ formals
                                           (rename-car/cdr-list actuals))
                                 fn
                                 wrld))
                          (pockets
                           (collect-pockets fn xbody))
                          (others
                           (collect-others fn xbody)))
                     (cond
                      ((null pockets) analysis)
                      (t (cons `(*** ,fn ,pockets ,others ,fn ***)
                               analysis)))))))))))))

 (defun induction-analysis-list (terms wrld)
   (cond
    ((endp terms) nil)
    (t (append (induction-analysis (car terms) wrld)
               (induction-analysis-list (cdr terms) wrld))))))

; Renaming: Our pick-induction-cand is PLTP's PICKINDVARS except we rate
; candidates wrt unchanged variables whereas PLTP did step counting.
 
(defun pick-induction-cand (indterm indvarlist wrld)
  (let ((candlist (getcands (induction-analysis indterm wrld))))
    (cond
     ((null candlist) nil)
     (t (let ((candlist (choose-high (merge-cands candlist))))
          (cond
           ((cdr candlist)
            (let ((candlist (choose-high (rate-cands candlist indterm wrld))))
              (cond
               ((cdr candlist)
                (let ((candlist
                       (choose-high
                        (choose-new candlist indvarlist))))
                  (car candlist)))
               (t (car candlist)))))
           (t (car candlist))))))))

(defun carcdrinfo (terms carcdrinfo)

; Terms is a list of car/cdr-vars, i.e., CAR or CDR applied to a variable.  We
; build an alist mapping each variable to CAR, CDR, or BOTH, depending on which
; symbols are applied to var.

  (cond
   ((endp terms) carcdrinfo)
   (t (let* ((term (car terms))
             (fn (fn term)) ; CAR or CDR
             (var (arg1 term))
             (y (assoc-equal var carcdrinfo)))
        (carcdrinfo (cdr terms)
                    (cond (y
                           (cond ((eq fn (cdr y))
                                  carcdrinfo)
                                 (t (put-assoc-eq var 'both carcdrinfo))))
                          (t (cons (cons var fn) carcdrinfo))))))))

(defun carsubsts (alist carconsts)

; Given an alist mapping variables to CAR, CDR, or BOTH, we build and return
; two substitutions.  The first, called the carsubst, maps each variable to its
; car constant.  The second maps, called the justcarsubst, maps just those
; variables that are never CDR'd to their car constants.  Thus, the second is a
; subset of the first.

  (cond
   ((endp alist) (mv nil nil))
   ((eq (cdr (car alist)) 'CDR)
    (carsubsts (cdr alist) carconsts))
   (t (mv-let (carsubst justcarsubst)
        (carsubsts (cdr alist) carconsts)
        (let ((y (cons (car (car alist))
                       (cdr (assoc-eq (car (car alist)) carconsts)))))
          (cond ((equal (cdr (car alist)) 'CAR)
                 (mv (cons y carsubst) (cons y justcarsubst)))
                (t (mv (cons y carsubst) justcarsubst))))))))

; (justcarsubst '((A . CAR) (B . CDR) (C . CAR) (C . CDR))
;               '((A . A1) (B . B1) (C . C1)))

(defun setupsubst (cand carconsts)
; Return (mv carsubst justcarsubst) as described in carsubsts.
  (carsubsts (carcdrinfo (access candrec cand :bombbay) nil)
             carconsts))

(defun conjoin (terms)
  (cond ((endp (cdr terms))
         (car terms))
        (t `(AND ,(car terms)
                 ,(conjoin (cdr terms))))))


(defun nilcase (indvars indterm)
  (cond
   ((endp (cdr indvars)) (subst nil (car indvars) indterm))
   (t `(AND ,(subst nil (car indvars) indterm)
            ,(nilcase (cdr indvars) indterm)))))


(defun indhyp (carsubst justcarsubst indterm)
  (cond
   (carsubst
    (cond
     ((equal (length carsubst) (length justcarsubst))
      (subst* carsubst indterm))
     (t `(AND ,(subst* carsubst indterm)
              ,(subst* justcarsubst indterm)))))
   (t indterm)))

(defun cons-subst (indvars carconsts)
  (cond
   ((endp indvars) nil)
   (t (cons (cons (car indvars)
                  `(CONS ,(cdr (assoc-eq (car indvars) carconsts)) ,(car indvars)))
            (cons-subst (cdr indvars) carconsts)))))

(defun indconcl (indvars carconsts indterm)
  (subst* (cons-subst indvars carconsts)
            indterm))

(defun simple-car/cdr-vars (list)

; We know that every element of list is a car/cdr nest around a variable.  We
; check additionally that every nest is just 1 deep.

  (cond ((endp list) t)
        (t (and (varp (arg1 (car list)))
                (simple-car/cdr-vars (cdr list))))))

(defun simple-inductive-failures (indvars list)

; List is the :failures list of an induction candidate.  It is thus a list of
; car/cdr terms that were not involved in a recursive call.  We make sure that
; none of the variables in those the nests (that are more than 1 deep) are
; being inducted upon.  Thus, if X is in indvars and (CAR (CDR X)) is in list,
; we fail.  But if only (CAR X) is in list we wouldn't fail.

  (cond
   ((endp list) t)
   ((applicationp (arg1 (car list)))
    (mv-let (flg var)
      (car/cdr-var (arg1 (car list)))
      (cond ((and flg (member-eq var indvars))
             nil)
            (t (simple-inductive-failures indvars (cdr list))))))
   (t (simple-inductive-failures indvars (cdr list)))))

(defun simpleind (indvars cand)
  (and (simple-car/cdr-vars (access candrec cand :bombbay))
       (simple-inductive-failures indvars (access candrec cand :failures))))

(defun collect-car/cdr-nests (const list)
  (cond ((endp list) nil)
        (t (mv-let (flg var)
             (car/cdr-var (car list))
             (cond
              ((and flg (eq var const))
               (cons (car list)
                     (collect-car/cdr-nests const (cdr list))))
              (t (collect-car/cdr-nests const (cdr list))))))))

(defun special1 (const indvars cand)

; We are in the first special case (see page 169 of Moore's thesis) when
; there is only one induction variable, const, (which is known to be the first
; element of indvars), every recursive failure (i.e., every term in the
; :bombbay of cand) is in fact `(CDR ,const), but there are non-recursive
; failures (in :failures) on const, all of which are car/cdr nests at most 2
; deep around const.

  (and (null (cdr indvars))
       (set-equalp-equal (access candrec cand :bombbay)
                         `((CDR ,const)))
       (let ((const-failures
              (collect-car/cdr-nests const
                                     (access candrec cand :failures))))
         (and const-failures
              (subsetp-equal const-failures
                             `((CAR ,const)
                               (CDR ,const)
                               (CAR (CDR ,const))
                               (CDR (CDR ,const))))))))


(defun special2 (const indvars cand)
  (and (null (cdr indvars))
       (or (member-equal `(CDR (CDR ,const)) (access candrec cand :bombbay))
           (member-equal `(CAR (CDR ,const)) (access candrec cand :bombbay)))))

(defun spec2hyp (const carcon1 carcon2 indterm cand)
  (let ((bomblist (access candrec cand :bombbay)))
    (conjoin
     `(,@(cond ((member-equal `(CAR ,const) bomblist)
                `(,(subst carcon1 const indterm)))
               (t nil))
       ,@(cond ((member-equal `(CAR (CDR ,const)) bomblist)
                `(,(subst carcon2 const indterm)))
               (t nil))
       ,@(cond ((member-equal `(CDR (CDR ,const)) bomblist)
                `(,indterm))
               (t nil))))))

(defun specialmode (indvars carconsts cand indterm goal indvarlist)
; Indvarlist is passed in and back out just so that induct, below, can
; return it.
  (let* ((const (car indvars))
         (carcon1 (cdr (assoc-eq const carconsts))))
    (let ((carcon2 (cdr (car (new-vars (list const) goal)))))
      (cond
       ((special1 const indvars cand)
        (mv 'special1
            indvars
            `(AND ,(nilcase indvars indterm)
                  (AND ,(subst `(CONS ,carcon1 NIL) const indterm)
                       (IMPLIES ,(subst `(CONS ,carcon2 ,const)
                                        const
                                        indterm)
                                ,(subst `(CONS ,carcon1 (CONS ,carcon2 ,const))
                                        const
                                        indterm))))
            indvarlist))
       ((special2 const indvars cand)
        (mv 'special2
            indvars
            `(AND ,(nilcase indvars indterm)
                  (AND ,(subst `(CONS ,carcon1 NIL) const indterm)
                       (IMPLIES ,(spec2hyp const carcon1 carcon2 indterm cand)
                                ,(subst `(CONS ,carcon1 (CONS ,carcon2 ,const))
                                        const
                                        indterm))))
            indvarlist))
       (t (mv 'special-case-not-covered nil indterm indvarlist))))))

; Rename INDUCT to induct1 for easier output.

(defun rename-apart (indvars new-a b)

; Replace in b every indvar with a new variable that doesn't occur either in
; new-a or in b.

  (subst* (new-vars indvars `(CONS ,new-a ,b)) b))

(defun induct1 (goal indvarlist wrld)
  (mv-let (flg a b)
    (split-conjunction goal)
    (let ((cand (pick-induction-cand a indvarlist wrld)))
      (cond
       ((null cand)
        (mv 'STUCK nil goal))
       (t (let* ((indvars (access candrec cand :indvars))
                 (const (car indvars))
                 (carconsts (new-vars indvars goal)))
            (cond
             ((simpleind indvars cand)
              (mv-let (carsubst justcarsubst)
                (setupsubst cand carconsts)
                (let* ((new-a `(AND ,(nilcase indvars a)
                                    (IMPLIES ,(indhyp carsubst justcarsubst a)
                                             ,(indconcl indvars carconsts a))))
                       (new-b (rename-apart indvars new-a b)))
                  (mv 'SIMPLE
                      indvars
                      (reassemble-conjunction flg new-a new-b)))))
             ((special1 const indvars cand)
              (let* ((carcon1 (cdr (assoc-eq const carconsts)))
                     (carcon2 (cdr (car (new-vars (list const)
                                                  `(NEW-VAR-GLUE
                                                    ,@(strip-cdrs carconsts)
                                                    ,goal)))))
                     (new-a `(AND ,(nilcase indvars a)
                                  (AND ,(subst `(CONS ,carcon1 NIL) const a)
                                       (IMPLIES ,(subst `(CONS ,carcon2 ,const)
                                                        const
                                                        a)
                                                ,(subst `(CONS ,carcon1 (CONS ,carcon2 ,const))
                                                        const
                                                        a)))))
                     (new-b (rename-apart indvars new-a b)))
                (mv 'SPECIAL1
                    indvars
                    (reassemble-conjunction flg new-a new-b))))
             ((special2 const indvars cand)
              (let* ((carcon1 (cdr (assoc-eq const carconsts)))
                     (carcon2 (cdr (car (new-vars (list const)
                                                  `(NEW-VAR-GLUE
                                                    ,@(strip-cdrs carconsts)
                                                    ,goal)))))
                     (new-a `(AND ,(nilcase indvars a)
                                  (AND ,(subst `(CONS ,carcon1 NIL) const a)
                                       (IMPLIES ,(spec2hyp const carcon1 carcon2 a cand)
                                                ,(subst `(CONS ,carcon1 (CONS ,carcon2 ,const))
                                                        const
                                                        a)))))
                     (new-b (rename-apart indvars new-a b)))
                (mv 'SPECIAL2
                    indvars
                    (reassemble-conjunction flg new-a new-b))))
             (t (mv 'special-case-not-covered nil goal)))))))))

(defun induct (goal indvarlist wrld)
  (mv-let (signal indvars new-goal)
    (induct1 goal indvarlist wrld)
    (prog2$
     (induct-msg signal indvars new-goal wrld)
     (mv signal indvars new-goal))))

; -----------------------------------------------------------------
; The Theorem Prover

; COMMENT 'THIS IS THE THEOREM PROVER.  ASTOUNDING IN ITS SIMPLICITY.
; THE OUTPUT FUNCTIONS HAVE BEEN MOVED TO THE SIDE TO REVEAL THE
; ESSENCE OF THE SYSTEM:  BEAT THE THEOREM TO DEATH WITH
; EVALUATION, NORMALIZE AND REDUCE.  IF THAT FAILS, TRY A LITTLE
; AI AND THEN MORE VIOLENCE.`;

; While PLTP's PROVE1 called evaluate, normalize (aka our rewrite), and reduce
; repeatedly, we just call PLTP's NORMALATE (aka our simplify) to make our
; output easier to implement.

; PLTP wrapped fertilize, generalize, and induct into a single routine called
; ARTIFINTEL.  A comment before the definition reads:

; COMMENT 'THIS FUNCTION APPLIES FERTILIZATION AND IF THAT FAILS
; TRIES GENERALIZING AND INDUCTING.  IT IS CAREFUL TO WORK ONLY
; ON THE FIRST CONJUNCT IF THE THEOREM IS A CONJUNCT.  FOR THIS
; IT GETS THE NAME "ARTIFICIAL INTELLIGENCE", BEING ABOUT THE
; SMARTEST PROGRAM IN THE THEOREM PROVER.`;

; However, we have moved the functions out into the main prove1 loop to
; foreshadow the development of Nqthm's and ACL2's ``waterfall''.

(defun prove1 (goal indvarlist wrld)
  (let ((goal1 (simplify goal wrld)))
    (cond
     ((finished goal1)
      (cond ((eq (fn goal1) 'CONS)
             'QED)
            (t 'STOP)))
     (t (let ((goal2 (fertilize goal1 wrld)))
          (cond
           ((not (equal goal2 goal1))
            (prove1 goal2 indvarlist wrld))
           (t (let* ((goal3 (generalize goal2 wrld)))

; If simplify or fertilization treated variables specially (as ACL2's use of
; eliminable equalities and destructor elimination do) then after
; generalization we should go back to the top of prove1.  But here there is no
; point and we go straight to induction.

                (mv-let (signal indvars goal4)
                  (induct goal3 indvarlist wrld)
                  (cond
                   ((or (eq signal 'STUCK)
                        (eq signal 'SPECIAL-CASE-NOT-COVERED))
                    'STOP)
                   (t (prove1 goal4
                              (append indvars indvarlist)
                              wrld))))))))))))

(defmacro prove (name uterm)
  `(let ((name ',name)
         (uterm ',uterm)
         (wrld (@ wrld)))
     (cond
      ((utermp uterm wrld)
       (let ((val (prove1 (translate uterm) nil wrld)))
         (cond ((eq val 'STOP)
                (er soft 'PLTP "Proof of ~x0 failed!" name))
               (t (value val)))))
      (t (er soft 'PLTP
             "The conjecture named ~x0,~%~y1,~%is not legal input to PROVE. ~
              Reason: NOT-A-TERM!" name uterm)))))

(defmacro proveall (key)
; Key must be one of the known keywords signifying a proveall file.
  (declare (xargs :guard (member-eq key '(:standard :jacm))))
  `(pprogn
    (pre-proveall-msg ',key state)
    (er-progn
     (ld (case ',key
           (:STANDARD "standard-proveall.lsp")
           (otherwise ; = :JACM
            "jacm-proveall.lsp"))
         :ld-pre-eval-print t
         :ld-error-action :error
         :ld-user-stobjs-modified-warning t)
     (post-proveall-msg ',key state))))

(defmacro acl2::pltpa nil
  `(er-progn (in-package "PLTP")
             (boot-strap)
             (set-feature :all :pltp-notation)))

