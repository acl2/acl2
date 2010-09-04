(in-package "ACL2")

;; Here we copy the translate function from ACL2 and remove the check
;; for function existence.  This is really useful when you want to do
;; macro expansion but don't really care (yet) about the underlying
;; functions.

;; The changes were quite minor and are marked by "CHANGE".  We
;; renamed all of the functions, of course, but the only substantial
;; changes were to remove the call to "(ev ..)" and to replace the
;; undefined function call check with a recursive call to translate.

(set-state-ok t)

(MUTUAL-RECURSION

 (DEFUN TRANSLATE11X-FLETX-ALISTX (FIVES STOBJS-OUT BINDINGS 
				      KNOWN-STOBJS FLET-ALIST CTX W STATE)
  (declare (xargs :mode :program))
   (COND
    ((ENDP FIVES) (TRANS-VALUE NIL))
    (T
     (TRANS-ER-LET*
      ((FLET-ENTRY (TRANSLATE11X-FLETX-ALISTX1
		    (CAR FIVES)
		    STOBJS-OUT BINDINGS
		    KNOWN-STOBJS FLET-ALIST CTX W STATE))
       (FLET-ENTRIES (TRANSLATE11X-FLETX-ALISTX
		      (CDR FIVES)
		      STOBJS-OUT BINDINGS
		      KNOWN-STOBJS FLET-ALIST CTX W STATE)))
      (TRANS-VALUE (CONS FLET-ENTRY FLET-ENTRIES))))))

 (DEFUN TRANSLATE11X-FLETX-ALISTX1
   (FIVE STOBJS-OUT BINDINGS
	 KNOWN-STOBJS FLET-ALIST CTX W STATE)
  (declare (xargs :mode :program))
   (LET
    ((NAME (CAR FIVE))
     (BOUND-VARS (CADR FIVE))
     (EDCLS (FOURTH FIVE))
     (BODY (FIFTH FIVE))
     (STOBJS-OUT (IF (EQ STOBJS-OUT T) T :LOCAL)))
    (COND
     ((MEMBER-EQ NAME
		 '(FLET WITH-LOCAL-STOBJ THROW-RAW-EV-FNCALL
			UNTRACE$-FN-GENERAL))
      (TRANS-ER
       SOFT CTX
       "An FLET form has attempted to bind ~x0.  However, this ~
                 symbol must not be FLET-bound."
       NAME))
     ((GETPROP NAME 'PREDEFINED
	       NIL 'CURRENT-ACL2-WORLD
	       W)
      (TRANS-ER
       SOFT CTX
       "An FLET form has attempted to bind ~x0, which is predefined ~
                 in ACL2 hence may not be FLET-bound."
       NAME))
     (T
      (TRANS-ER-LET*
       ((TDCLS
	 (TRANSLATE11X-LST (TRANSLATE-DCL-LST EDCLS W)
			  NIL BINDINGS NIL KNOWN-STOBJS
			  "in a DECLARE form in an FLET binding"
			  FLET-ALIST CTX W STATE))
	(TBODY
	 (TRANSLATE11X
	  BODY STOBJS-OUT
	  (IF (EQ STOBJS-OUT T)
	      BINDINGS
	      (TRANSLATE-BIND STOBJS-OUT STOBJS-OUT BINDINGS))
	  NIL
	  KNOWN-STOBJS FLET-ALIST CTX W STATE)))
       (LET
	((STOBJS-BOUND
	  (COLLECT-NON-X
	   NIL
	   (COMPUTE-STOBJ-FLAGS BOUND-VARS KNOWN-STOBJS W)))
	 (USED-VARS (UNION-EQ (ALL-VARS TBODY)
			      (ALL-VARS1-LST TDCLS NIL)))
	 (IGNORE-VARS (IGNORE-VARS EDCLS))
	 (IGNORABLE-VARS (IGNORABLE-VARS EDCLS))
	 (STOBJS-OUT (TRANSLATE-DEREF STOBJS-OUT BINDINGS)))
	(COND
	 ((AND (NOT (EQ STOBJS-OUT T))
	       (NOT (CONSP STOBJS-OUT)))
	  (TRANS-ER
	   SOFT CTX
	   "We are unable to determine the output signature for an ~
                      FLET-binding of ~x0.  You may be able to remedy the ~
                      situation by rearranging the order of the branches of ~
                      an IF and/or rearranging the order of the presentation ~
                      of a clique of mutually recursive functions.  If you ~
                      believe you have found an example on which you believe ~
                      ACL2 should be able to complete this translation, ~
                      please send such an example to the ACL2 implementors."
	   NAME))
	 ((AND (NOT (EQ STOBJS-OUT T))
	       STOBJS-BOUND
	       (NOT (SUBSETP-EQ STOBJS-BOUND
				(COLLECT-NON-X NIL STOBJS-OUT))))
	  (LET
	   ((STOBJS-RETURNED (COLLECT-NON-X NIL STOBJS-OUT)))
	   (TRANS-ER
	    SOFT CTX
	    "The single-threaded object~#0~[ ~&0 is a formal~/s ~
                        ~&0 are formals~] of an FLET-binding of ~x3.  It is a ~
                        requirement that ~#0~[this object~/these objects~] be ~
                        among the outputs of the body of that binding, but ~
                        ~#0~[it is~/they are~] not.  That body returns ~
                        ~#1~[no single-threaded objects~/the single-threaded ~
                        object ~&2~/the single-threaded objects ~&2~]."
	    (SET-DIFFERENCE-EQ STOBJS-BOUND STOBJS-RETURNED)
	    (ZERO-ONE-OR-MORE STOBJS-RETURNED)
	    STOBJS-RETURNED NAME)))
	 ((INTERSECTP-EQ USED-VARS IGNORE-VARS)
	  (TRANS-ER
	   SOFT CTX
	   "Contrary to the declaration that ~#0~[it is~/they are~] ~
                      IGNOREd, the variable~#0~[ ~&0 is~/s ~&0 are~] used in ~
                      the body of an FLET-binding of ~x1, whose formal ~
                      parameter list includes ~&2."
	   (INTERSECTION-EQ USED-VARS IGNORE-VARS)
	   NAME BOUND-VARS))
	 (T
	  (LET*
	   ((DIFF
	     (SET-DIFFERENCE-EQ
	      BOUND-VARS
	      (UNION-EQ USED-VARS
			(UNION-EQ IGNORABLE-VARS IGNORE-VARS))))
	    (IGNORE-OK
	     (IF
	      (NULL DIFF)
	      T
	      (CDR
	       (ASSOC-EQ
		:IGNORE-OK (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
					W))))))
	   (COND
	    ((NULL IGNORE-OK)
	     (TRANS-ER
	      SOFT CTX
	      "The variable~#0~[ ~&0 is~/s ~&0 are~] not used in ~
                          the body of the LET expression that binds ~&1.  But ~
                          ~&0 ~#0~[is~/are~] not declared IGNOREd or ~
                          IGNORABLE.  See :DOC set-ignore-ok."
	      DIFF BOUND-VARS))
	    (T
	     (PPROGN
	      (COND
	       ((EQ IGNORE-OK :WARN)
		(WARNING$
		 CTX "Ignored-variables"
		 "The variable~#0~[ ~&0 is~/s ~&0 are~] not used ~
                             in the body of an FLET-binding of ~x1 that binds ~
                             ~&2.  But ~&0 ~#0~[is~/are~] not declared ~
                             IGNOREd or IGNORABLE.  See :DOC set-ignore-ok."
		 DIFF NAME BOUND-VARS))
	       (T STATE))
	      (LET*
	       ((TBODY
		 (COND
		  (TDCLS
		   (LET
		    ((GUARDIAN (DCL-GUARDIAN TDCLS)))
		    (COND
		     ((EQUAL GUARDIAN *T*) TBODY)
		     (T (FCONS-TERM* 'PROG2$ GUARDIAN TBODY)))))
		  (T TBODY)))
		(BODY-VARS (ALL-VARS TBODY))
		(EXTRA-BODY-VARS
		 (SET-DIFFERENCE-EQ BODY-VARS BOUND-VARS)))
	       (COND
		(EXTRA-BODY-VARS
		 (TRANS-ER
		  SOFT CTX
		  "The variable~#0~[ ~&0 is~/s ~&0 are~] used in ~
                               the body of an FLET-binding of ~x1 that only ~
                               binds ~&2.  In ACL2, every variable occurring ~
                               in the body of an FLET-binding, (fn vars ~
                               body), must be in vars, i.e., a formal ~
                               parameter of that binding.  The ACL2 ~
                               implementors may be able to remove this ~
                               restriction, with some effort, if you ask."
		  EXTRA-BODY-VARS NAME BOUND-VARS))
		(T (MV NIL
		       (LIST* NAME (MAKE-LAMBDA BOUND-VARS TBODY)
			      STOBJS-OUT)
		       (IF (EQ STOBJS-OUT T)
			   BINDINGS
			   (DELETE-ASSOC-EQ :LOCAL BINDINGS))
		       STATE))))))))))))))))

 (DEFUN TRANSLATE11X-FLETX
   (X STOBJS-OUT BINDINGS INCLP
      KNOWN-STOBJS FLET-ALIST CTX W STATE)
  (declare (xargs :mode :program))
   (COND
    ((NOT (EQL (LENGTH X) 3))
     (TRANS-ER
      SOFT CTX
      "An FLET form must have the form (flet bindings body), where ~
               bindings is a list of local function definitions, but ~x0 does ~
               not have this form.  See :DOC flet."
      X))
    (T
     (LET
      ((ERR-STRING
	"The above error indicates a problem with the form ~p0."))
      (MV-LET
       (ERP FIVES STATE)
       (CHK-DEFUNS-TUPLES (CADR X)
			  T CTX W STATE)
       (MV-LET
	(ERP IGNORED-VAL STATE)
	(IF ERP (SILENT-ERROR STATE)
	    (CHK-NO-DUPLICATE-DEFUNS (STRIP-CARS FIVES)
				     CTX STATE))
	(DECLARE (IGNORE IGNORED-VAL))
	(COND
	 (ERP (TRANS-ER SOFT CTX ERR-STRING X))
	 (T
	  (TRANS-ER-LET*
	   ((FLET-ALIST
	     (TRANSLATE11X-FLETX-ALISTX
	      FIVES STOBJS-OUT BINDINGS
	      KNOWN-STOBJS FLET-ALIST CTX W STATE)))
	   (TRANSLATE11X (CAR (LAST X))
			STOBJS-OUT BINDINGS INCLP KNOWN-STOBJS
			FLET-ALIST CTX W STATE))))))))))

 (DEFUN TRANSLATE11X-MV-LETX
   (X STOBJS-OUT BINDINGS INCLP KNOWN-STOBJS
      LOCAL-STOBJ LOCAL-STOBJ-CREATOR
      FLET-ALIST CTX W STATE)
  (declare (xargs :mode :program))
   (COND
    ((NOT (AND (TRUE-LISTP (CADR X))
	       (> (LENGTH (CADR X)) 1)))
     (TRANS-ER
      SOFT CTX
      "The first form in an MV-LET expression must be a true list of ~
               length 2 or more.  ~x0 does not meet these conditions."
      (CADR X)))
    ((NOT (ARGLISTP (CADR X)))
     (MV-LET
      (CULPRIT EXPLAN)
      (FIND-FIRST-BAD-ARG (CADR X))
      (TRANS-ER
       SOFT CTX
       "The first form in an MV-LET expression must be a list ~
                       of distinct variables of length 2 or more, but ~x0 ~
                       does not meet these conditions.  The element ~x1 ~@2."
       X CULPRIT EXPLAN)))
    ((NOT (>= (LENGTH X) 4))
     (TRANS-ER
      SOFT CTX
      "An MV-LET expression has the form (mv-let (var var var*) form ~
               dcl* form) but ~x0 does not have sufficient length to meet ~
               this condition."
      X))
    (T
     (LET*
      ((BOUND-VARS (CADR X))
       (PRODUCER-KNOWN-STOBJS
	(IF (AND LOCAL-STOBJ (NOT (EQ KNOWN-STOBJS T)))
	    (ADD-TO-SET-EQ LOCAL-STOBJ KNOWN-STOBJS)
	    KNOWN-STOBJS))
       (BOUND-STOBJS-OUT
	(COMPUTE-STOBJ-FLAGS BOUND-VARS PRODUCER-KNOWN-STOBJS W))
       (STOBJS-BOUND0 (COLLECT-NON-X NIL BOUND-STOBJS-OUT))
       (STOBJS-BOUND (IF LOCAL-STOBJ
			 (REMOVE1-EQ LOCAL-STOBJ STOBJS-BOUND0)
			 STOBJS-BOUND0))
       (BODY (CAR (LAST X))))
      (MV-LET
       (ERP EDCLS STATE)
       (COLLECT-DECLARATIONS (BUTLAST (CDDDR X) 1)
			     (CADR X)
			     'MV-LET
			     STATE CTX)
       (COND
	(ERP (MV T NIL BINDINGS STATE))
	(T
	 (TRANS-ER-LET*
	  ((TCALL
	    (TRANSLATE11X (CADDR X)
			 BOUND-STOBJS-OUT
			 BINDINGS INCLP PRODUCER-KNOWN-STOBJS
			 FLET-ALIST CTX W STATE))
	   (TDCLS
	    (TRANSLATE11X-LST (TRANSLATE-DCL-LST EDCLS W)
			     NIL BINDINGS INCLP KNOWN-STOBJS
			     "in a DECLARE form in an MV-LET"
			     FLET-ALIST CTX W STATE))
	   (TBODY
	    (TRANSLATE11X BODY STOBJS-OUT BINDINGS INCLP
			 KNOWN-STOBJS FLET-ALIST CTX W STATE)))
	  (LET
	   ((USED-VARS (UNION-EQ (ALL-VARS TBODY)
				 (ALL-VARS1-LST TDCLS NIL)))
	    (IGNORE-VARS
	     (IF LOCAL-STOBJ
		 (CONS LOCAL-STOBJ (IGNORE-VARS EDCLS))
		 (IGNORE-VARS EDCLS)))
	    (IGNORABLE-VARS (IGNORABLE-VARS EDCLS))
	    (STOBJS-OUT (TRANSLATE-DEREF STOBJS-OUT BINDINGS)))
	   (COND
	    ((AND LOCAL-STOBJ
		  (NOT (MEMBER-EQ LOCAL-STOBJ IGNORE-VARS)))
	     (TRANS-ER
	      SOFT CTX
	      "A local-stobj must be declared ignored, but ~x0 is ~
                         not.  See :DOC with-local-stobj."
	      LOCAL-STOBJ))
	    ((AND STOBJS-BOUND (NOT (CONSP STOBJS-OUT)))
	     (TRANS-ER
	      SOFT CTX "~@0"
	      (UNKNOWN-BINDING-MSG
	       STOBJS-BOUND
	       "an MV-LET" "the MV-LET" "the MV-LET")))
	    ((AND STOBJS-BOUND
		  (NOT (SUBSETP STOBJS-BOUND
				(COLLECT-NON-X NIL STOBJS-OUT))))
	     (LET
	      ((STOBJS-RETURNED (COLLECT-NON-X NIL STOBJS-OUT)))
	      (TRANS-ER
	       SOFT CTX
	       "The single-threaded object~#0~[ ~&0 has~/s ~&0 ~
                           have~] been bound in an MV-LET.  It is a ~
                           requirement that ~#0~[this object~/these objects~] ~
                           be among the outputs of the MV-LET, but ~#0~[it ~
                           is~/they are~] not.  The MV-LET returns ~#1~[no ~
                           single-threaded objects~/the single-threaded ~
                           object ~&2~/the single-threaded objects ~&2~]."
	       (SET-DIFFERENCE-EQ STOBJS-BOUND STOBJS-RETURNED)
	       (ZERO-ONE-OR-MORE STOBJS-RETURNED)
	       STOBJS-RETURNED)))
	    ((INTERSECTP-EQ USED-VARS IGNORE-VARS)
	     (TRANS-ER
	      SOFT CTX
	      "Contrary to the declaration that ~#0~[it is~/they ~
                         are~] IGNOREd, the variable~#0~[ ~&0 is~/s ~&0 are~] ~
                         used in the MV-LET expression that binds ~&1."
	      (INTERSECTION-EQ USED-VARS IGNORE-VARS)
	      BOUND-VARS))
	    (T
	     (LET*
	      ((DIFF
		(SET-DIFFERENCE-EQ
		 BOUND-VARS
		 (UNION-EQ
		  USED-VARS
		  (UNION-EQ IGNORABLE-VARS IGNORE-VARS))))
	       (IGNORE-OK
		(IF
		 (NULL DIFF)
		 T
		 (CDR
		  (ASSOC-EQ
		   :IGNORE-OK (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
					   W))))))
	      (COND
	       ((NULL IGNORE-OK)
		(TRANS-ER
		 SOFT CTX
		 "The variable~#0~[ ~&0 is~/s ~&0 are~] not used ~
                             in the body of the MV-LET expression that binds ~
                             ~&1.  But ~&0 ~#0~[is~/are~] not declared ~
                             IGNOREd or IGNORABLE.  See :DOC set-ignore-ok."
		 DIFF BOUND-VARS))
	       (T
		(PPROGN
		 (COND
		  ((EQ IGNORE-OK :WARN)
		   (WARNING$
		    CTX "Ignored-variables"
		    "The variable~#0~[ ~&0 is~/s ~&0 are~] not used ~
                                in the body of the MV-LET expression that ~
                                binds ~&1. But ~&0 ~#0~[is~/are~] not declared ~
                                IGNOREd or IGNORABLE.  See :DOC set-ignore-ok."
		    DIFF BOUND-VARS))
		  (T STATE))
		 (LET*
		  ((TBODY
		    (COND
		     (TDCLS
		      (LET
		       ((GUARDIAN (DCL-GUARDIAN TDCLS)))
		       (COND
			((EQUAL GUARDIAN *T*) TBODY)
			(T
			 (FCONS-TERM* 'PROG2$ GUARDIAN TBODY)))))
		     (T TBODY)))
		   (BODY-VARS (ALL-VARS TBODY))
		   (EXTRA-BODY-VARS
		    (SET-DIFFERENCE-EQ BODY-VARS (CADR X)))
		   (VARS (ALL-VARS1 TCALL EXTRA-BODY-VARS))
		   (MV-VAR (GENVAR 'GENVAR "MV" NIL VARS)))
		  (TRANS-VALUE
		   (LIST*
		    (MAKE-LAMBDA
		     (CONS MV-VAR EXTRA-BODY-VARS)
		     (CONS
		      (MAKE-LAMBDA
		       (APPEND (CADR X) EXTRA-BODY-VARS)
		       TBODY)
		      (APPEND
		       (HIDE-IGNORED-ACTUALS
			IGNORE-VARS (CADR X)
			(MV-NTH-LIST MV-VAR 0 (LENGTH (CADR X))))
		       EXTRA-BODY-VARS)))
		    (IF
		     LOCAL-STOBJ
		     (LET
		      ((TCALL-VARS
			(REMOVE1-EQ
			 LOCAL-STOBJ (ALL-VARS TCALL))))
		      (CONS
		       (MAKE-LAMBDA (CONS LOCAL-STOBJ TCALL-VARS)
				    TCALL)
		       (CONS (LIST LOCAL-STOBJ-CREATOR)
			     TCALL-VARS)))
		     TCALL)
		    EXTRA-BODY-VARS))))))))))))))))))

 (DEFUN TRANSLATE11X-CALLX
   (FN ARGS
       STOBJS-OUT STOBJS-OUT2 BINDINGS INCLP
       KNOWN-STOBJS MSG FLET-ALIST CTX W STATE)
  (declare (xargs :mode :program))
   (LET
    ((STOBJS-IN (IF (CONSP FN)
		    (COMPUTE-STOBJ-FLAGS (LAMBDA-FORMALS FN)
					 KNOWN-STOBJS W)
		    (STOBJS-IN FN W))))
    (COND
     ((CONSP STOBJS-OUT)
      (COND
       ((CONSP STOBJS-OUT2)
	(COND
	 ((NOT (EQUAL STOBJS-OUT STOBJS-OUT2))
	  (TRANS-ER
	   SOFT CTX
	   "It is illegal to invoke ~@0 here because of a signature ~
                     mismatch.  ~x1 returns a result of shape ~x2 where a ~
                     result of shape ~x3 is required."
	   (IF (CONSP FN) MSG (MSG "~x0" FN))
	   FN (PRETTYIFY-STOBJS-OUT STOBJS-OUT2)
	   (PRETTYIFY-STOBJS-OUT STOBJS-OUT)))
	 (T
	  (TRANS-ER-LET*
	   ((ARGS (TRANSLATE11X-LST
		   ARGS STOBJS-IN BINDINGS
		   (COMPUTE-INCLP-LST STOBJS-IN STOBJS-OUT)
		   KNOWN-STOBJS
		   MSG FLET-ALIST CTX W STATE)))
	   (TRANS-VALUE (FCONS-TERM FN ARGS))))))
       (T
	(LET
	 ((BINDINGS
	   (TRANSLATE-BIND STOBJS-OUT2 STOBJS-OUT BINDINGS)))
	 (TRANS-ER-LET*
	  ((ARGS (TRANSLATE11X-LST
		  ARGS
		  STOBJS-IN BINDINGS INCLP KNOWN-STOBJS
		  MSG FLET-ALIST CTX W STATE)))
	  (TRANS-VALUE (FCONS-TERM FN ARGS)))))))
     ((CONSP STOBJS-OUT2)
      (LET
       ((BINDINGS
	 (TRANSLATE-BIND STOBJS-OUT STOBJS-OUT2 BINDINGS)))
       (TRANS-ER-LET*
	((ARGS
	  (TRANSLATE11X-LST ARGS
			   STOBJS-IN BINDINGS INCLP KNOWN-STOBJS
			   MSG FLET-ALIST CTX W STATE)))
	(TRANS-VALUE (FCONS-TERM FN ARGS)))))
     (T
      (LET
       ((BINDINGS
	 (TRANSLATE-BIND STOBJS-OUT2 STOBJS-OUT BINDINGS)))
       (TRANS-ER-LET*
	((ARGS
	  (TRANSLATE11X-LST ARGS
			   STOBJS-IN BINDINGS INCLP KNOWN-STOBJS
			   MSG FLET-ALIST CTX W STATE)))
	(TRANS-VALUE (FCONS-TERM FN ARGS))))))))

 (DEFUN TRANSLATE11X
   (X STOBJS-OUT BINDINGS INCLP
      KNOWN-STOBJS FLET-ALIST CTX W STATE)
  (declare (xargs :mode :program))
   (COND
    ((F-BIG-CLOCK-NEGATIVE-P STATE)
     (TRANS-ER
      SOFT CTX
      "Translate ran out of time!  This is almost certainly ~
               caused by a loop in macro expansion."))
    ((OR (ATOM X) (EQ (CAR X) 'QUOTE))
     (LET*
      ((STOBJS-OUT (TRANSLATE-DEREF STOBJS-OUT BINDINGS))
       (VC (LEGAL-VARIABLE-OR-CONSTANT-NAMEP X))
       (CONST (AND (EQ VC 'CONSTANT)
		   (DEFINED-CONSTANT X W))))
      (COND
       ((AND (SYMBOLP X)
	     (NOT (KEYWORDP X))
	     (NOT VC))
	(TRANS-ER
	 SOFT CTX
	 "The symbol ~x0 is being used as a variable ~
                   or constant symbol but does not have the proper ~
                   syntax.  Such names must ~@1.  See :DOC name."
	 X
	 (TILDE-@-ILLEGAL-VARIABLE-OR-CONSTANT-NAME-PHRASE X)))
       ((AND (EQ VC 'CONSTANT) (NOT CONST))
	(TRANS-ER
	 SOFT CTX
	 "The symbol ~x0 (in package ~x1) has the syntax of ~
                   a constant, but has not been defined."
	 X (SYMBOL-PACKAGE-NAME X)))
       ((AND (NOT (ATOM X)) (NOT (TERMP X W)))
	(TRANS-ER
	 SOFT CTX
	 "The proper form of a quoted constant is (quote x), ~
                   but ~x0 is not of this form."
	 X))
       (T
	(LET
	 ((TRANSX (COND ((KEYWORDP X) (KWOTE X))
			((SYMBOLP X)
			 (COND ((EQ VC 'CONSTANT) CONST) (T X)))
			((ATOM X) (KWOTE X))
			(T X))))
	 (COND
	  ((EQ STOBJS-OUT T) (TRANS-VALUE TRANSX))
	  ((CONSP STOBJS-OUT)
	   (COND
	    ((CDR STOBJS-OUT)
	     (TRANS-ER
	      SOFT CTX
	      "One value, ~x0, is being returned where ~
                           ~x1 values were expected."
	      X (LENGTH STOBJS-OUT)))
	    ((AND (NULL (CAR STOBJS-OUT))
		  (STOBJP TRANSX KNOWN-STOBJS W))
	     (TRANS-ER
	      SOFT CTX
	      "A single-threaded object, namely ~x0, is ~
                           being used where an ordinary object is ~
                           expected."
	      TRANSX))
	    ((AND (CAR STOBJS-OUT)
		  (NOT (OR INCLP (EQ (CAR STOBJS-OUT) TRANSX))))
	     (COND
	      ((STOBJP TRANSX KNOWN-STOBJS W)
	       (TRANS-ER
		SOFT CTX
		"The single-threaded object ~x0 is being ~
                             used where the single-threaded ~
                             object ~x1 was expected."
		TRANSX (CAR STOBJS-OUT)))
	      (T
	       (TRANS-ER
		SOFT CTX
		"The ordinary object ~x0 is being ~
                             used where the single-threaded ~
                             object ~x1 was expected."
		TRANSX (CAR STOBJS-OUT)))))
	    (T (TRANS-VALUE TRANSX))))
	  (T
	   (LET
	    ((BINDINGS
	      (TRANSLATE-BIND
	       STOBJS-OUT
	       (LIST (IF (STOBJP TRANSX KNOWN-STOBJS W)
			 TRANSX NIL))
	       BINDINGS)))
	    (TRANS-VALUE TRANSX)))))))))
    ((NOT (TRUE-LISTP (CDR X)))
     (TRANS-ER
      SOFT CTX
      "Function applications in ACL2 must end in NIL.  ~x0 is ~
               not of this form."
      X))
    ((NOT (SYMBOLP (CAR X)))
     (COND
      ((OR (NOT (CONSP (CAR X)))
	   (NOT (EQ (CAAR X) 'LAMBDA)))
       (TRANS-ER
	SOFT CTX
	"Function applications in ACL2 must begin with a ~
                      symbol or LAMBDA expression.  ~x0 is not of ~
                      this form."
	X))
      ((OR (NOT (TRUE-LISTP (CAR X)))
	   (NOT (>= (LENGTH (CAR X)) 3))
	   (NOT (TRUE-LISTP (CADR (CAR X)))))
       (TRANS-ER SOFT CTX
		 "Illegal LAMBDA expression: ~x0." X))
      ((NOT (= (LENGTH (CADR (CAR X)))
	       (LENGTH (CDR X))))
       (TRANS-ER
	SOFT CTX
	"The LAMBDA expression ~x0 takes ~#1~[no ~
                      arguments~/1 argument~/~x2 arguments~] and is ~
                      being passed ~#3~[no arguments~/1 argument~/~x4 ~
                      arguments~]."
	(CAR X)
	(ZERO-ONE-OR-MORE (LENGTH (CADR (CAR X))))
	(LENGTH (CADR (CAR X)))
	(ZERO-ONE-OR-MORE (LENGTH (CDR X)))
	(LENGTH (CDR X))))
      (T (TRANSLATE11X (LIST* 'LET
			     (LISTLIS (CADR (CAR X)) (CDR X))
			     (CDDR (CAR X)))
		      STOBJS-OUT BINDINGS INCLP
		      KNOWN-STOBJS FLET-ALIST CTX W STATE))))
    ((AND (NOT (EQ STOBJS-OUT T))
	  (EQ (CAR X) 'MV))
     (LET
      ((STOBJS-OUT (TRANSLATE-DEREF STOBJS-OUT BINDINGS)))
      (COND
       ((LET ((LEN (LENGTH (CDR X))))
	     (OR (< LEN 2) (> LEN 32)))
	(COND
	 ((< (LENGTH (CDR X)) 2)
	  (TRANS-ER
	   SOFT CTX
	   "MV must be given at least two arguments, but ~x0 has ~
                          fewer than two arguments."
	   X))
	 (T
	  (TRANS-ER
	   SOFT CTX
	   "MV must be given no more than 32 arguments; thus ~x0 ~
                          has too many arguments."
	   X))))
       ((CONSP STOBJS-OUT)
	(COND
	 ((NOT (INT= (LENGTH STOBJS-OUT)
		     (LENGTH (CDR X))))
	  (TRANS-ER
	   SOFT CTX
	   "The expected number of return values for ~x0 is ~x1 but ~
                     the actual number of return values is ~x2."
	   X (LENGTH STOBJS-OUT)
	   (LENGTH (CDR X))))
	 (T
	  (TRANS-ER-LET*
	   ((ARGS
	     (TRANSLATE11X-LST (CDR X)
			      STOBJS-OUT
			      BINDINGS INCLP KNOWN-STOBJS 'MV
			      FLET-ALIST CTX W STATE)))
	   (TRANS-VALUE (LISTIFY ARGS))))))
       (T
	(LET*
	 ((NEW-STOBJS-OUT (COMPUTE-STOBJ-FLAGS (CDR X)
					       KNOWN-STOBJS W))
	  (BINDINGS
	   (TRANSLATE-BIND STOBJS-OUT NEW-STOBJS-OUT BINDINGS)))
	 (COND
	  ((NOT
	    (NO-DUPLICATESP (COLLECT-NON-X NIL NEW-STOBJS-OUT)))
	   (TRANS-ER
	    SOFT CTX
	    "It is illegal to return more than one ~
                         reference to a given single-threaded object ~
                         in an MV form.  The form ~x0 is thus illegal."
	    X))
	  (T
	   (TRANS-ER-LET*
	    ((ARGS
	      (TRANSLATE11X-LST (CDR X)
			       NEW-STOBJS-OUT
			       BINDINGS INCLP KNOWN-STOBJS 'MV
			       FLET-ALIST CTX W STATE)))
	    (TRANS-VALUE (LISTIFY ARGS))))))))))
    ((AND (NOT (EQ STOBJS-OUT T))
	  (EQ (CAR X) 'MV-LET))
     (TRANSLATE11X-MV-LETX X STOBJS-OUT BINDINGS INCLP KNOWN-STOBJS
			 NIL NIL FLET-ALIST CTX W STATE))
    ((ASSOC-EQ (CAR X) FLET-ALIST)
     (LET*
      ((ENTRY (ASSOC-EQ (CAR X) FLET-ALIST))
       (LAMBDA-FN (CADR ENTRY))
       (FORMALS (LAMBDA-FORMALS LAMBDA-FN))
       (STOBJS-OUT2 (TRANSLATE-DEREF (CDDR ENTRY)
				     BINDINGS)))
      (COND
       ((NOT (EQL (LENGTH FORMALS) (LENGTH (CDR X))))
	(TRANS-ER
	 SOFT CTX
	 "FLET-bound local function ~x0 takes ~#1~[no ~
                        arguments~/1 argument~/~x2 arguments~] but in the ~
                        call ~x3 it is given ~#4~[no arguments~/1 ~
                        argument~/~x5 arguments~].   The formal parameters ~
                        list for the applicable FLET-binding of ~x0 is ~X67."
	 (CAR X)
	 (ZERO-ONE-OR-MORE (LENGTH FORMALS))
	 (LENGTH FORMALS)
	 X (ZERO-ONE-OR-MORE (LENGTH (CDR X)))
	 (LENGTH (CDR X))
	 FORMALS NIL))
       (T (TRANSLATE11X-CALLX
	   LAMBDA-FN (CDR X)
	   STOBJS-OUT
	   STOBJS-OUT2 BINDINGS INCLP KNOWN-STOBJS
	   (MSG "a call of FLET-bound function ~x0"
		(CAR X))
	   FLET-ALIST CTX W STATE)))))
    ((AND BINDINGS
	  (NOT (EQ (CAAR BINDINGS) :STOBJS-OUT))
	  (MEMBER-EQ (CAR X)
		     '(DEFUN DEFMACRO IN-PACKAGE PROGN)))
     (TRANS-ER
      SOFT CTX
      "We do not permit the use of ~x0 inside of code to be ~
               executed by Common Lisp because its Common Lisp ~
               meaning differs from its ACL2 meaning."
      (CAR X)))
    ((AND
      BINDINGS
      (NOT (EQ (CAAR BINDINGS) :STOBJS-OUT))
      (MEMBER-EQ (CAR X)
		 '(DEFPKG DEFCONST
		    DEFSTOBJ DEFTHM DEFAXIOM DEFLABEL
		    DEFDOC DEFTHEORY VERIFY-TERMINATION
		    VERIFY-GUARDS IN-THEORY
		    IN-ARITHMETIC-THEORY PUSH-UNTOUCHABLE
		    REMOVE-UNTOUCHABLE RESET-PREHISTORY
		    SET-BODY TABLE THEORY-INVARIANT
		    INCLUDE-BOOK CERTIFY-BOOK VALUE-TRIPLE
		    LOCAL MAKE-EVENT WITH-OUTPUT PROGN!)))
     (TRANS-ER
      SOFT CTX
      "We do not permit the use of ~x0 inside of code to be ~
               executed by Common Lisp because its Common Lisp ~
               runtime value and effect differs from its ACL2 meaning."
      (CAR X)))
    ((AND (EQ (CAR X) 'PARGS)
	  (TRUE-LISTP X)
	  (MEMBER (LENGTH X) '(2 3))
	  (LET ((FORM (CAR (LAST X))))
	       (OR FLET-ALIST
		   (NOT (AND (CONSP FORM)
			     (SYMBOLP (CAR FORM))
			     (FUNCTION-SYMBOLP (CAR FORM) W))))))
     (COND
      (FLET-ALIST
       (TRANS-ER
	SOFT CTX
	"Pargs may not be called in the scope of an flet.  If you ~
                 want support for that capability, please contact the ACL2 ~
                 implementors."))
      (T
       (LET
	((FORM (CAR (LAST X))))
	(TRANS-ER
	 SOFT CTX
	 "Pargs may only be used when its form argument is a ~
                   function call, unlike the argument ~x0.~@1  See :DOC pargs."
	 FORM
	 (IF
	  (AND (CONSP FORM)
	       (SYMBOLP (CAR FORM))
	       (GETPROP (CAR FORM)
			'MACRO-BODY
			NIL 'CURRENT-ACL2-WORLD
			W))
	  (LIST
	   "  Note that ~x0 is a macro, not a function symbol."
	   (CONS #\0 (CAR FORM)))
	  ""))))))
    ((EQ (CAR X) 'TRANSLATE-AND-TEST)
     (COND
      ((NOT (EQUAL (LENGTH X) 3))
       (TRANS-ER
	SOFT CTX
	"TRANSLATE-AND-TEST requires exactly two ~
                      arguments: ~x0 ."
	X))
      (T
       (TRANS-ER-LET*
	((ANS (TRANSLATE11X (CADDR X)
			   STOBJS-OUT BINDINGS INCLP
			   KNOWN-STOBJS FLET-ALIST CTX W STATE)))
	(MV-LET
	 (TEST-ERP TEST-TERM TEST-BINDINGS STATE)
	 (TRANSLATE11X (LIST (CADR X) 'FORM)
		      '(NIL)
		      NIL INCLP
		      KNOWN-STOBJS FLET-ALIST CTX W STATE)
	 (DECLARE (IGNORE TEST-BINDINGS))
	 (COND
	  (TEST-ERP (MV TEST-ERP TEST-TERM BINDINGS STATE))
	  (T
	   (MV-LET
	    (ERP MSG LATCHES) ;; CHANGE :: Just stub this (ev ..) call right out ..
	    (mv nil nil nil)
	    (DECLARE (IGNORE LATCHES))
	    (COND
	     (ERP
	      (TRANS-ER
	       SOFT CTX
	       "The attempt to evaluate the ~
                                      TRANSLATE-AND-TEST test, ~X01, ~
                                      when FORM is ~X21, failed with ~
                                      the evaluation error:~%~%``~@3''"
	       (CADR X)
	       NIL ANS MSG))
	     ((OR (CONSP MSG) (STRINGP MSG))
	      (TRANS-ER SOFT CTX "~@0" MSG))
	     (T (TRANS-VALUE ANS)))))))))))
    ((EQ (CAR X) 'WITH-LOCAL-STOBJ)
     (MV-LET
      (ERP ST MV-LET-FORM CREATOR)
      (PARSE-WITH-LOCAL-STOBJ (CDR X))
      (COND
       (ERP
	(TRANS-ER
	 SOFT CTX
	 "Ill-formed with-local-stobj form, ~x0.  ~
                         See :DOC with-local-stobj."
	 X))
       ((NOT (AND ST (EQ ST (STOBJ-CREATORP CREATOR W))))
	(TRANS-ER
	 SOFT CTX
	 "Illegal with-local-stobj form, ~x0.  The first ~
                         argument must be the name of a stobj other than ~
                         STATE and the third, if supplied, must be its ~
                         creator function.  See :DOC with-local-stobj."
	 X))
       ((EQ STOBJS-OUT :STOBJS-OUT)
	(TRANS-ER
	 SOFT CTX
	 "Calls of with-local-stobj, such as ~x0, cannot be ~
                         evaluated directly in the top-level loop.  ~
                         See :DOC with-local-stobj."
	 X))
       (T (TRANSLATE11X-MV-LETX
	   MV-LET-FORM
	   STOBJS-OUT BINDINGS INCLP KNOWN-STOBJS
	   ST CREATOR FLET-ALIST CTX W STATE)))))
    ((AND (ASSOC-EQ (CAR X) *TTAG-FNS-AND-MACROS*)
	  (NOT (TTAG W)))
     (TRANS-ER
      SOFT CTX
      "The ~x0 ~s1 cannot be called unless a trust tag is in effect.  ~
               See :DOC defttag.~@2"
      (CAR X)
      (IF (GETPROP (CAR X)
		   'MACRO-BODY
		   NIL 'CURRENT-ACL2-WORLD
		   W)
	  "macro" "function")
      (OR (CDR (ASSOC-EQ (CAR X)
			 *TTAG-FNS-AND-MACROS*))
	  "")))
    ((GETPROP (CAR X)
	      'MACRO-BODY
	      NIL 'CURRENT-ACL2-WORLD
	      W)
     (COND
      ((AND (EQ STOBJS-OUT :STOBJS-OUT)
	    (MEMBER-EQ (CAR X)
		       '(PAND POR PARGS PLET))
	    (EQ (F-GET-GLOBAL 'PARALLEL-EVALUATION-ENABLED
			      STATE)
		T))
       (TRANS-ER
	SOFT CTX
	"Parallel evaluation is enabled, but is not implemented for ~
                 calls of parallelism primitives (~&0) made directly in the ~
                 ACL2 top-level loop, as opposed to being made inside a ~
                 function definition.  The call ~P12 is thus illegal.  To ~
                 allow such calls to be evaluated (but without parallelism), ~
                 evaluate ~x3.  See :DOC parallelism-at-the-top-level and ~
                 :DOC set-parallel-evaluation."
	'(PAND POR PARGS PLET)
	X (TERM-EVISC-TUPLE T STATE)
	'(SET-PARALLEL-EVALUATION :BOGUS-PARALLELISM-OK)))
      ((AND (MEMBER-EQ (CAR X)
		       (GLOBAL-VAL 'UNTOUCHABLE-FNS W))
	    (NOT (EQ (F-GET-GLOBAL 'TEMP-TOUCHABLE-FNS STATE)
		     T))
	    (NOT (MEMBER-EQ (CAR X)
			    (F-GET-GLOBAL 'TEMP-TOUCHABLE-FNS
					  STATE))))
       (TRANS-ER
	SOFT CTX
	"It is illegal to call ~x0 because it has been placed ~
                 on untouchable-fns."
	(CAR X)))
      (T
       (MV-LET
	(ERP EXPANSION STATE)
	(MACROEXPAND1 X CTX STATE)
	(COND
	 (ERP (MV T NIL BINDINGS STATE))
	 (T (TRANSLATE11X EXPANSION STOBJS-OUT BINDINGS
			 INCLP KNOWN-STOBJS FLET-ALIST CTX
			 W (F-DECREMENT-BIG-CLOCK STATE))))))))
    ((EQ (CAR X) 'LET)
     (COND
      ((NOT (AND (>= (LENGTH X) 3)
		 (DOUBLETON-LIST-P (CADR X))))
       (TRANS-ER
	SOFT CTX
	"The proper form of a let is (let bindings dcl ... ~
                 dcl body), where bindings has the form ((v1 term) ~
                 ... (vn term)) and the vi are distinct variables, ~
                 not constants, and do not begin with an asterisk, ~
                 but ~x0 does not have this form."
	X))
      ((NOT (ARGLISTP (STRIP-CARS (CADR X))))
       (MV-LET
	(CULPRIT EXPLAN)
	(FIND-FIRST-BAD-ARG (STRIP-CARS (CADR X)))
	(TRANS-ER
	 SOFT CTX
	 "The form ~x0 is an improper let expression ~
                         because it attempts to bind ~x1, which ~@2."
	 X CULPRIT EXPLAN)))
      ((AND
	(NOT (EQ STOBJS-OUT T))
	(NOT (EQUAL 1 (LENGTH (CADR X))))
	(NOT (ALL-NILS (COMPUTE-STOBJ-FLAGS (STRIP-CARS (CADR X))
					    KNOWN-STOBJS W))))
       (TRANS-ER
	SOFT CTX
	"A single-threaded object name, such as ~x0, may be ~
                 LET-bound only when it is the only binding in the ~
                 LET, but ~x1 binds more than one variable."
	(CAR (COLLECT-NON-X
	      NIL
	      (COMPUTE-STOBJ-FLAGS (STRIP-CARS (CADR X))
				   KNOWN-STOBJS W)))
	X))
      (T
       (LET*
	((BOUND-VARS (STRIP-CARS (CADR X)))
	 (STOBJS-BOUND
	  (COLLECT-NON-X
	   NIL
	   (COMPUTE-STOBJ-FLAGS BOUND-VARS KNOWN-STOBJS W)))
	 (BODY (CAR (LAST X))))
	(MV-LET
	 (ERP EDCLS STATE)
	 (COLLECT-DECLARATIONS (BUTLAST (CDDR X) 1)
			       BOUND-VARS 'LET
			       STATE CTX)
	 (COND
	  (ERP (MV T NIL BINDINGS STATE))
	  (T
	   (TRANS-ER-LET*
	    ((VALUE-FORMS
	      (COND
	       ((AND (NOT (EQ STOBJS-OUT T))
		     STOBJS-BOUND)
		(TRANS-ER-LET*
		 ((VAL
		   (TRANSLATE11X
		    (CADR (CAR (CADR X)))
		    (LIST (CAR BOUND-VARS))
		    BINDINGS INCLP
		    KNOWN-STOBJS FLET-ALIST CTX W STATE)))
		 (TRANS-VALUE (LIST VAL))))
	       (T
		(TRANSLATE11X-LST
		 (STRIP-CADRS (CADR X))
		 (IF (EQ STOBJS-OUT T) T NIL)
		 BINDINGS INCLP KNOWN-STOBJS
		 "in a LET binding (or ~
                                           LAMBDA application)"
		 FLET-ALIST CTX W STATE))))
	     (TBODY
	      (TRANSLATE11X BODY STOBJS-OUT BINDINGS INCLP
			   KNOWN-STOBJS FLET-ALIST CTX W STATE))
	     (TDCLS (TRANSLATE11X-LST
		     (TRANSLATE-DCL-LST EDCLS W)
		     (IF (EQ STOBJS-OUT T) T NIL)
		     BINDINGS INCLP KNOWN-STOBJS
		     "in a DECLARE form in a LET (or LAMBDA)"
		     FLET-ALIST CTX W STATE)))
	    (LET
	     ((USED-VARS (UNION-EQ (ALL-VARS TBODY)
				   (ALL-VARS1-LST TDCLS NIL)))
	      (IGNORE-VARS (IGNORE-VARS EDCLS))
	      (IGNORABLE-VARS (IGNORABLE-VARS EDCLS))
	      (STOBJS-OUT (TRANSLATE-DEREF STOBJS-OUT BINDINGS)))
	     (COND
	      ((AND (NOT (EQ STOBJS-OUT T))
		    STOBJS-BOUND (NOT (CONSP STOBJS-OUT)))
	       (TRANS-ER SOFT CTX "~@0"
			 (UNKNOWN-BINDING-MSG
			  STOBJS-BOUND
			  "a LET" "the LET" "the LET")))
	      ((AND
		(NOT (EQ STOBJS-OUT T))
		STOBJS-BOUND
		(NOT
		 (SUBSETP-EQ STOBJS-BOUND
			     (COLLECT-NON-X NIL STOBJS-OUT))))
	       (LET
		((STOBJS-RETURNED
		  (COLLECT-NON-X NIL STOBJS-OUT)))
		(TRANS-ER
		 SOFT CTX
		 "The single-threaded object~#0~[ ~&0 ~
                               has~/s ~&0 have~] been bound in a ~
                               LET.  It is a requirement that ~
                               ~#0~[this object~/these objects~] be ~
                               among the outputs of the LET, but ~
                               ~#0~[it is~/they are~] not.  The LET ~
                               returns ~#1~[no single-threaded ~
                               objects~/the single-threaded object ~
                               ~&2~/the single-threaded objects ~&2~]."
		 (SET-DIFFERENCE-EQ STOBJS-BOUND STOBJS-RETURNED)
		 (ZERO-ONE-OR-MORE STOBJS-RETURNED)
		 STOBJS-RETURNED)))
	      ((INTERSECTP-EQ USED-VARS IGNORE-VARS)
	       (TRANS-ER
		SOFT CTX
		"Contrary to the declaration that ~#0~[it is~/they ~
                             are~] IGNOREd, the variable~#0~[ ~&0 is~/s ~&0 ~
                             are~] used in the body of the LET expression that ~
                             binds ~&1."
		(INTERSECTION-EQ USED-VARS IGNORE-VARS)
		BOUND-VARS))
	      (T
	       (LET*
		((IGNORE-VARS
		  (AUGMENT-IGNORE-VARS
		   BOUND-VARS VALUE-FORMS IGNORE-VARS))
		 (DIFF
		  (SET-DIFFERENCE-EQ
		   BOUND-VARS
		   (UNION-EQ
		    USED-VARS
		    (UNION-EQ IGNORABLE-VARS IGNORE-VARS))))
		 (IGNORE-OK
		  (IF
		   (NULL DIFF)
		   T
		   (CDR
		    (ASSOC-EQ
		     :IGNORE-OK (TABLE-ALIST 'ACL2-DEFAULTS-TABLE
					     W))))))
		(COND
		 ((NULL IGNORE-OK)
		  (TRANS-ER
		   SOFT CTX
		   "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                 used in the body of the LET expression that ~
                                 binds ~&1.  But ~&0 ~#0~[is~/are~] not ~
                                 declared IGNOREd or IGNORABLE.  See :DOC ~
                                 set-ignore-ok."
		   DIFF BOUND-VARS))
		 (T
		  (PPROGN
		   (COND
		    ((EQ IGNORE-OK :WARN)
		     (WARNING$
		      CTX "Ignored-variables"
		      "The variable~#0~[ ~&0 is~/s ~&0 are~] not ~
                                    used in the body of the LET expression ~
                                    that binds ~&1.  But ~&0 ~#0~[is~/are~] ~
                                    not declared IGNOREd or IGNORABLE.  See ~
                                    :DOC set-ignore-ok."
		      DIFF BOUND-VARS))
		    (T STATE))
		   (LET*
		    ((TBODY
		      (COND
		       (TDCLS
			(LET
			 ((GUARDIAN (DCL-GUARDIAN TDCLS)))
			 (COND
			  ((EQUAL GUARDIAN *T*) TBODY)
			  (T (FCONS-TERM* 'PROG2$
					  GUARDIAN TBODY)))))
		       (T TBODY)))
		     (BODY-VARS (ALL-VARS TBODY))
		     (EXTRA-BODY-VARS
		      (SET-DIFFERENCE-EQ BODY-VARS BOUND-VARS)))
		    (TRANS-VALUE
		     (CONS
		      (MAKE-LAMBDA
		       (APPEND BOUND-VARS EXTRA-BODY-VARS)
		       TBODY)
		      (APPEND
		       (HIDE-IGNORED-ACTUALS
			IGNORE-VARS BOUND-VARS VALUE-FORMS)
		       EXTRA-BODY-VARS)))))))))))))))))))
    ((EQ (CAR X) 'FLET)
     (TRANSLATE11X-FLETX X STOBJS-OUT BINDINGS INCLP
		       KNOWN-STOBJS FLET-ALIST CTX W STATE))
    ((AND (NOT (EQ STOBJS-OUT T))
	  (NULL (CDR X))
	  (STOBJ-CREATORP (CAR X) W))
     (TRANS-ER
      SOFT CTX
      "It is illegal to call ~x0 in this context because it is a stobj ~
               creator.  Stobj creators cannot be called directly except in ~
               theorems.  If you did not explicitly call a stobj creator, then ~
               this error is probably due to an attempt to evaluate a ~
               with-local-stobj form directly in the top-level loop.  Such ~
               forms are only allowed in the bodies of functions and in ~
               theorems.  Also see :DOC with-local-stobj."
      (CAR X)))
    ((EQUAL (ARITY (CAR X) W)
	    (LENGTH (CDR X)))
     (COND
      ((AND (MEMBER-EQ (CAR X)
		       (GLOBAL-VAL 'UNTOUCHABLE-FNS W))
	    (NOT (EQ (F-GET-GLOBAL 'TEMP-TOUCHABLE-FNS STATE)
		     T))
	    (NOT (MEMBER-EQ (CAR X)
			    (F-GET-GLOBAL 'TEMP-TOUCHABLE-FNS
					  STATE))))
       (TRANS-ER
	SOFT CTX
	"It is illegal to call ~x0 because it has been ~
                      placed on untouchable-fns."
	(CAR X)))
      ((EQ (CAR X) 'IF)
       (COND
	((STOBJP (CADR X) KNOWN-STOBJS W)
	 (TRANS-ER
	  SOFT CTX
	  "It is illegal to test on a ~
                             single-threaded object such as ~x0."
	  (CADR X)))
	(T
	 (TRANS-ER-LET*
	  ((ARG1
	    (TRANSLATE11X (CADR X)
			 (IF (EQ STOBJS-OUT T) T '(NIL))
			 BINDINGS INCLP
			 KNOWN-STOBJS FLET-ALIST CTX W STATE))
	   (ARG2
	    (TRANSLATE11X (CADDR X)
			 STOBJS-OUT BINDINGS INCLP
			 KNOWN-STOBJS FLET-ALIST CTX W STATE))
	   (ARG3
	    (TRANSLATE11X (CADDDR X)
			 STOBJS-OUT BINDINGS INCLP
			 KNOWN-STOBJS FLET-ALIST CTX W STATE)))
	  (TRANS-VALUE (FCONS-TERM* 'IF ARG1 ARG2 ARG3))))))
      ((EQ (CAR X) 'SYNP)
       (COND
	((NOT (EQ STOBJS-OUT T))
	 (TRANS-ER
	  SOFT CTX
	  "A call to synp is not allowed here.  This ~
                             call may have come from the use of syntaxp ~
                             or bind-free within a function definition ~
                             since these two macros expand into calls to ~
                             synp.  The form we were translating when we ~
                             encountered this problem is ~x0.  If you ~
                             believe this error message is itself in error ~
                             or that we have been too restrictive, please ~
                             contact the maintainers of ACL2."
	  X))
	((EQL (LENGTH X) 4)
	 (TRANS-ER-LET*
	  ((QUOTED-VARS (TRANSLATE11X (CADR X)
				     '(NIL)
				     BINDINGS INCLP '(STATE)
				     FLET-ALIST CTX W STATE))
	   (QUOTED-USER-FORM
	    (TRANSLATE11X (CADDR X)
			 '(NIL)
			 BINDINGS INCLP '(STATE)
			 FLET-ALIST CTX W STATE))
	   (QUOTED-TERM (TRANSLATE11X (CADDDR X)
				     '(NIL)
				     BINDINGS INCLP '(STATE)
				     FLET-ALIST CTX W STATE)))
	  (LET
	   ((QUOTED-TERM (IF (QUOTEP QUOTED-TERM)
			     QUOTED-TERM
			     (SUBLIS-VAR NIL QUOTED-TERM))))
	   (COND
	    ((QUOTEP QUOTED-TERM)
	     (TRANS-ER-LET*
	      ((TERM-TO-BE-EVALUATED
		(TRANSLATE11X (CADR QUOTED-TERM)
			     '(NIL)
			     BINDINGS INCLP '(STATE)
			     FLET-ALIST CTX W STATE)))
	      (LET
	       ((QUOTED-VARS (IF (QUOTEP QUOTED-VARS)
				 QUOTED-VARS
				 (SUBLIS-VAR NIL QUOTED-VARS)))
		(QUOTED-USER-FORM
		 (IF (QUOTEP QUOTED-USER-FORM)
		     QUOTED-USER-FORM
		     (SUBLIS-VAR NIL QUOTED-USER-FORM))))
	       (COND
		((AND (QUOTEP QUOTED-VARS)
		      (QUOTEP QUOTED-USER-FORM))
		 (TRANS-VALUE
		  (FCONS-TERM* 'SYNP
			       QUOTED-VARS QUOTED-USER-FORM
			       (KWOTE TERM-TO-BE-EVALUATED))))
		(T (TRANS-ER
		    SOFT CTX *SYNP-TRANS-ERR-STRING* X))))))
	    (T (TRANS-ER SOFT CTX *SYNP-TRANS-ERR-STRING* X))))))
	(T (TRANS-ER SOFT CTX *SYNP-TRANS-ERR-STRING* X))))
      ((EQ (CAR X) 'PROG2$)
       (TRANS-ER-LET*
	((ARG1 (TRANSLATE11X (CADR X)
			    (IF (EQ STOBJS-OUT T) T '(NIL))
			    BINDINGS INCLP
			    KNOWN-STOBJS FLET-ALIST CTX W STATE))
	 (ARG2
	  (TRANSLATE11X (CADDR X)
		       STOBJS-OUT BINDINGS INCLP
		       KNOWN-STOBJS FLET-ALIST CTX W STATE)))
	(TRANS-VALUE (FCONS-TERM* 'PROG2$ ARG1 ARG2))))
      ((EQ (CAR X) 'MUST-BE-EQUAL)
       (COND
	((AND (NOT (EQ (F-GET-GLOBAL 'LD-SKIP-PROOFSP STATE)
		       'INCLUDE-BOOK))
	      (NON-TRIVIAL-ENCAPSULATE-EE-ENTRIES
	       (GLOBAL-VAL 'EMBEDDED-EVENT-LST W)))
	 (TRANS-ER
	  SOFT CTX
	  "It is illegal to call ~x0 (~x1) under an ~
                        encapsulate event with a non-empty signature."
	  'MUST-BE-EQUAL
	  'MBE))
	(T
	 (TRANS-ER-LET*
	  ((ARG1
	    (TRANSLATE11X (CADR X)
			 STOBJS-OUT BINDINGS INCLP
			 KNOWN-STOBJS FLET-ALIST CTX W STATE))
	   (ARG2
	    (TRANSLATE11X (CADDR X)
			 STOBJS-OUT BINDINGS INCLP
			 KNOWN-STOBJS FLET-ALIST CTX W STATE)))
	  (TRANS-VALUE (FCONS-TERM* 'MUST-BE-EQUAL
				    ARG1 ARG2))))))
      ((OR (EQ (CAR X) 'TIME$)
	   (EQ (CAR X) 'EC-CALL))
       (COND
	((AND
	  (EQ (CAR X) 'EC-CALL)
	  (NOT
	   (AND (CONSP (CDR X))
		(CONSP (CADR X))
		(LET ((FN (CAR (CADR X))))
		     (AND (SYMBOLP FN)
			  (NOT (MEMBER-EQ FN *EC-CALL-BAD-OPS*))
			  (FUNCTION-SYMBOLP FN W))))))
	 (TRANS-ER
	  SOFT CTX
	  "A call of ~x0 must only be made on an argument of the ~
                        form (FN ARG1 ... ARGK), where FN is a known function ~
                        in the current ACL2 world other than ~v1. The call ~
                        ~x2 is thus illegal."
	  'EC-CALL
	  *EC-CALL-BAD-OPS* X))
	(T
	 (TRANS-ER-LET*
	  ((ARG1
	    (TRANSLATE11X (CADR X)
			 STOBJS-OUT BINDINGS INCLP
			 KNOWN-STOBJS FLET-ALIST CTX W STATE)))
	  (TRANS-VALUE (FCONS-TERM* (CAR X) ARG1))))))
      ((MEMBER-EQ (CAR X)
		  '(WITH-PROVER-TIME-LIMIT))
       (TRANS-ER-LET*
	((ARG1 (TRANSLATE11X (CADR X)
			    (IF (EQ STOBJS-OUT T) T '(NIL))
			    BINDINGS INCLP
			    KNOWN-STOBJS FLET-ALIST CTX W STATE))
	 (ARG2
	  (TRANSLATE11X (CADDR X)
		       STOBJS-OUT BINDINGS INCLP
		       KNOWN-STOBJS FLET-ALIST CTX W STATE)))
	(TRANS-VALUE (FCONS-TERM* (CAR X) ARG1 ARG2))))
      ((EQ STOBJS-OUT T)
       (TRANS-ER-LET*
	((ARGS (TRANSLATE11X-LST (CDR X)
				T BINDINGS INCLP KNOWN-STOBJS
				NIL FLET-ALIST CTX W STATE)))
	(TRANS-VALUE (FCONS-TERM (CAR X) ARGS))))
      ((AND
	(MEMBER-EQ (CAR X)
		   '(MAKUNBOUND-GLOBAL PUT-GLOBAL))
	(NOT (EQ (F-GET-GLOBAL 'TEMP-TOUCHABLE-VARS
			       STATE)
		 T))
	(OR
	 (NOT (AND (CONSP (CADR X))
		   (EQ (CAR (CADR X)) 'QUOTE)
		   (NULL (CDDR (CADR X)))
		   (SYMBOLP (CADR (CADR X)))))
	 (AND (MEMBER-EQ (CADR (CADR X))
			 (GLOBAL-VAL 'UNTOUCHABLE-VARS W))
	      (NOT (MEMBER-EQ (CADR (CADR X))
			      (F-GET-GLOBAL 'TEMP-TOUCHABLE-VARS
					    STATE))))
	 (AND (EQ (CAR X) 'MAKUNBOUND-GLOBAL)
	      (ALWAYS-BOUNDP-GLOBAL (CADR (CADR X))))))
       (COND
	((NOT (AND (CONSP (CADR X))
		   (EQ (CAR (CADR X)) 'QUOTE)
		   (NULL (CDDR (CADR X)))
		   (SYMBOLP (CADR (CADR X)))))
	 (TRANS-ER
	  SOFT CTX
	  "The first arg of ~x0 must be a quoted symbol, ~
                             unlike ~x1.  We make this requirement in support ~
                             of untouchable-vars."
	  (CAR X)
	  (CADR X)))
	((AND (MEMBER-EQ (CADR (CADR X))
			 (GLOBAL-VAL 'UNTOUCHABLE-VARS W))
	      (NOT (MEMBER-EQ (CADR (CADR X))
			      (F-GET-GLOBAL 'TEMP-TOUCHABLE-VARS
					    STATE))))
	 (TRANS-ER
	  SOFT CTX
	  "State global variable ~x0 has been rendered ~
                             untouchable and thus may not be directly ~
                             altered, as in ~x1.~@2"
	  (CADR (CADR X))
	  X
	  (LET
	   ((SET-FN
	     (INTERN-IN-PACKAGE-OF-SYMBOL
	      (CONCATENATE 'STRING
			   "SET-" (SYMBOL-NAME (CADR (CADR X))))
	      (CADR (CADR X)))))
	   (COND
	    ((FUNCTION-SYMBOLP SET-FN W)
	     (MSG
	      "~|There is a function ~x0, which ~
                                           (from the name) may provide the ~
                                           functionality you desire."
	      SET-FN))
	    (T "")))))
	(T
	 (TRANS-ER
	  SOFT CTX
	  "Built-in state global variables may not be made ~
                             unbound, as in ~x1."
	  (CADR (CADR X))
	  X))))
      (T
       (LET
	((STOBJS-OUT (TRANSLATE-DEREF STOBJS-OUT BINDINGS))
	 (STOBJS-OUT2
	  (LET ((TEMP (TRANSLATE-DEREF (CAR X) BINDINGS)))
	       (COND (TEMP TEMP)
		     (T (STOBJS-OUT (CAR X) W))))))
	(TRANSLATE11X-CALLX (CAR X)
			  (CDR X)
			  STOBJS-OUT STOBJS-OUT2
			  BINDINGS INCLP KNOWN-STOBJS (CAR X)
			  FLET-ALIST CTX W STATE)))))
    ((ARITY (CAR X) W)
     (TRANS-ER
      SOFT CTX
      "~x0 takes ~#1~[no arguments~/1 argument~/~x2 ~
               arguments~] but in the call ~x3 it is given ~#4~[no ~
               arguments~/1 argument~/~x5 arguments~].   The formal ~
               parameters list for ~x0 is ~X67."
      (CAR X)
      (ZERO-ONE-OR-MORE (ARITY (CAR X) W))
      (ARITY (CAR X) W)
      X (ZERO-ONE-OR-MORE (LENGTH (CDR X)))
      (LENGTH (CDR X))
      (FORMALS (CAR X) W)
      NIL))
    ((EQ (CAR X) 'DECLARE)
     (TRANS-ER
      SOFT CTX
      "It is illegal to use DECLARE as a function symbol, as ~
               in ~x0.  DECLARE forms are permitted only in very ~
               special places, e.g., before the bodies of function ~
               definitions, LETs, and MV-LETs.  DECLARE forms are ~
               never permitted in places in which their ``values'' ~
               are relevant.  If you already knew this, it is likely ~
               you have made a typographical mistake, e.g., including ~
               the body in the DECLARE form or closing the superior ~
               form before typing the body."
      X))
    (T  
     ;; CHANGE : Replace the non-existing function failure with this code ..
     ;;
     (trans-er-let*
      ((args (translate11x-lst (cdr x) 
			       nil BINDINGS INCLP KNOWN-STOBJS
			       "Unknown Function" FLET-ALIST CTX W STATE)))
      (trans-value (fcons-term (car x) args))))))

 (DEFUN TRANSLATE11X-LST
   (LST STOBJS-OUT BINDINGS INCLP-LST
	KNOWN-STOBJS MSG FLET-ALIST CTX W STATE)
  (declare (xargs :mode :program))
   (COND
    ((ATOM LST) (TRANS-VALUE NIL))
    ((EQ STOBJS-OUT T)
     (TRANS-ER-LET*
      ((X (TRANSLATE11X (CAR LST)
		       T BINDINGS
		       (IF (EQ INCLP-LST T) T (CAR INCLP-LST))
		       KNOWN-STOBJS FLET-ALIST CTX W STATE))
       (Y
	(TRANSLATE11X-LST (CDR LST)
			 T BINDINGS
			 (IF (EQ INCLP-LST T) T (CDR INCLP-LST))
			 KNOWN-STOBJS
			 MSG FLET-ALIST CTX W STATE)))
      (TRANS-VALUE (CONS X Y))))
    ((CAR STOBJS-OUT)
     (TRANS-ER-LET*
      ((X
	(COND
	 ((EQ (IF (OR (EQ KNOWN-STOBJS T)
		      (MEMBER-EQ (CAR LST) KNOWN-STOBJS))
		  (CAR LST)
		  NIL)
	      (CAR STOBJS-OUT))
	  (TRANS-VALUE (CAR LST)))
	 ((AND (EQ (CAR STOBJS-OUT) 'STATE)
	       (OR (EQUAL (CAR LST)
			  '(DECREMENT-BIG-CLOCK STATE))
		   (EQUAL (CAR LST)
			  '(F-DECREMENT-BIG-CLOCK STATE))))
	  (TRANS-VALUE '(DECREMENT-BIG-CLOCK STATE)))
	 ((EQ (CAR LST) (CAR STOBJS-OUT))
	  (LET
	   ((KNOWN-STOBJS (COLLECT-NON-X NIL KNOWN-STOBJS)))
	   (TRANS-ER
	    SOFT CTX
	    "The form ~x0 is being used~#1~[ ~/, as ~
                             an argument to a call of ~x2,~/, ~@2,~] ~
                             where the single-threaded object of that ~
                             name is required.  But in the current ~
                             context, ~#3~[there are no declared ~
                             stobj names~/the only declared stobj ~
                             name is ~&4~/the only declared stobj ~
                             names are ~&4~]."
	    (CAR LST)
	    (IF (NULL MSG) 0 (IF (SYMBOLP MSG) 1 2))
	    MSG
	    (COND ((NULL KNOWN-STOBJS) 0)
		  ((NULL (CDR KNOWN-STOBJS)) 1)
		  (T 2))
	    KNOWN-STOBJS)))
	 (T
	  (TRANS-ER
	   SOFT CTX
	   "The form ~x0 is being used~#1~[ ~/, as an ~
                             argument to a call of ~x2,~/, ~@2,~] where the ~
                             single-threaded object ~x3 is required.  Note ~
                             that the variable ~x3 is required, not merely a ~
                             term that returns such a single-threaded object, ~
                             so you may need to bind ~x3 with LET; see :DOC ~
                             stobj."
	   (CAR LST)
	   (IF (NULL MSG) 0 (IF (SYMBOLP MSG) 1 2))
	   MSG (CAR STOBJS-OUT)))))
       (Y
	(TRANSLATE11X-LST (CDR LST)
			 (CDR STOBJS-OUT)
			 BINDINGS
			 (IF (EQ INCLP-LST T) T (CDR INCLP-LST))
			 KNOWN-STOBJS
			 MSG FLET-ALIST CTX W STATE)))
      (TRANS-VALUE (CONS X Y))))
    (T
     (TRANS-ER-LET*
      ((X (TRANSLATE11X (CAR LST)
		       '(NIL)
		       BINDINGS
		       (IF (EQ INCLP-LST T) T (CAR INCLP-LST))
		       KNOWN-STOBJS FLET-ALIST CTX W STATE))
       (Y
	(TRANSLATE11X-LST (CDR LST)
			 (CDR STOBJS-OUT)
			 BINDINGS
			 (IF (EQ INCLP-LST T) T (CDR INCLP-LST))
			 KNOWN-STOBJS
			 MSG FLET-ALIST CTX W STATE)))
      (TRANS-VALUE (CONS X Y)))))))

(DEFUN TRANSLATE1x (X STOBJS-OUT BINDINGS KNOWN-STOBJS CTX W STATE)
  (declare (xargs :mode :program))
  (MV-LET
   (ERP VAL-BINDINGS STATE)
   (MV-LET (ERP VAL BINDINGS STATE)
           (TRANSLATE11X X STOBJS-OUT BINDINGS NIL KNOWN-STOBJS NIL CTX W STATE)
           (MV ERP (CONS VAL BINDINGS) STATE))
   (MV ERP (CAR VAL-BINDINGS)
       (CDR VAL-BINDINGS)
       STATE)))

(DEFUN pseudo-translate (FORM STATE)
  (declare (xargs :mode :program))
  (LET
   ((WRLD (W STATE)))
   (MV-LET
    (FLG VAL BINDINGS STATE)
    (TRANSLATE1x FORM :STOBJS-OUT
		 '((:STOBJS-OUT . :STOBJS-OUT))
		 T 'TOP-LEVEL
		 WRLD STATE)
    (declare (ignore bindings))
    (mv flg val state))))
