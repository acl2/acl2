; ACL2 Version 4.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic
; NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; memoize-raw.lisp -- Raw lisp definitions for memoization functions, only to
; be included in the experimental HONS version of ACL2.

; The original version of this file was contributed by Bob Boyer and
; Warren A. Hunt, Jr.  The design of this system of Hash CONS,
; function memoization, and fast association lists (applicative hash
; tables) was initially implemented by Boyer and Hunt.

(in-package "ACL2")



; [Jared]: Thread safety note -- I am getting rid of all of the locking stuff
; that was here before.  None of it was in use (because it was #+parallel and
; that was never enabled).  Today, memoize is definitely not thread safe, and
; making it thread safe will require a lot of time and careful thought.  The
; locking stuff that was here is just muddying the waters and making things
; harder to understand, so I want to just get rid of it for now and then do it
; right later.

(eval-when
 (:execute :compile-toplevel :load-toplevel)

 #-hons
 ;; [Jared] This restriction makes some sense since we need at least things
 ;; like the hons addressing scheme for ponsing to work.  It also makes sense
 ;; for things like compact-print-file that shouldn't really be part of
 ;; memoize.
 (error "memoize-raw.lisp should only be included when #+hons is set."))



; MFIXNUM.  We use the type mfixnum for counting things that are best counted
; in the trillions or more.  Mfixnums just so happen to coincide with regular
; fixnums on 64-bit CCL and SBCL.

(defconstant most-positive-mfixnum (1- (expt 2 60)))

(deftype mfixnum ()
  `(integer ,(- -1 most-positive-mfixnum)
            ,most-positive-mfixnum))



; [Jared]: We probably should generally work toward getting rid of defg/defv's
; in favor of regular parameters, for better thread safety, etc.

(defmacro defg (&rest r)

  "DEFG is a short name for DEFPARAMETER.  However, in Clozure Common
  Lisp (CCL) its use includes two promises: (1) never to locally bind
  the variable, e.g., with LET or LAMBDA, and (2) never to call
  MAKUNBOUND on the variable.  CCL uses fewer machine instructions to
  reference such a variable than an ordinary special, which may have a
  per-thread binding that needs to be locked up."

  #-Clozure
  `(defparameter ,@r)
  #+Clozure
  `(ccl::defstatic ,@r))


(defmacro defv (&rest r)

  "DEFV is a short name for DEFVAR.  However, in Clozure Common Lisp
  (CCL) its use includes two promises: (1) never to locally bind the
  variable, e.g., with LET or LAMBDA, and (2) never to call MAKUNBOUND
  on the variable.  CCL uses fewer machine instructions to reference
  such a variable than an ordinary special, which may have a
  per-thread binding that needs to be locked up.  Unlike for DEFVAR,
  the second argument of DEFV is not optional."

  #-Clozure
  `(defparameter ,@r)
  #+Clozure
  `(ccl::defstaticvar ,@r))


; [Jared]: We should probably get rid of mht and use hl-mht instead.

(defv *mht-default-size*
  ;; BOZO defined as a defconst in memoize.lisp
  60)

(defv *mht-default-rehash-size*      1.5)
(defv *mht-default-rehash-threshold* 0.7)
(defv *mht-default-shared*           nil)

(declaim (type fixnum *mht-default-size*))
(declaim (float *mht-default-rehash-size*))
(declaim (float *mht-default-rehash-threshold*))

(defn mht (&key (test             'eql)
                (size             *mht-default-size*)
                (shared           *mht-default-shared*)
                (rehash-size      *mht-default-rehash-size*)
                (rehash-threshold *mht-default-rehash-threshold*)
                (weak             nil))
  (declare (ignorable shared weak))
  (make-hash-table :test             test
                   :size             size
                   :rehash-size      rehash-size
                   :rehash-threshold rehash-threshold
                   #+Clozure :weak   #+Clozure weak
                   #+Clozure :shared #+Clozure *mht-default-shared*))



; MACROS FOR PROFILING -------------------------------------------------------
;
; We use PROFILER-IF to avoid monitoring of code that we have introduced into
; the user's code for the purpose of profiling.
;
; Semantically, PROFILER-IF is the same as IF.  However, the execution of the
; PROFILER-IF macro also puts the IF form into *IGNORE-FORM-HT* so that the
; compiler macro for IF will not consider 'fixing' it with code to monitor
; which branch of the IF is taken.

#+Clozure
(progn
  (defg *ignore-form-ht* (make-hash-table :test 'eq))
  (declaim (hash-table *ignore-form-ht*)))

(defmacro profiler-if (test true &optional false)
  (let ((val `(if ,test ,true ,false)))
    #+Clozure
    (setf (gethash val *ignore-form-ht*) t)
    val))

(defmacro profiler-cond (&rest r)
  (cond ((null r) nil)
        (t `(profiler-if ,(caar r)
                     (progn ,@(cdar r))
                     (profiler-cond ,@(cdr r))))))

(defmacro profiler-and (&rest r)
  (cond ((null r) t)
        ((null (cdr r)) (car r))
        (t `(profiler-if ,(car r)
                         (profiler-and ,@(cdr r))
                         nil))))

(defmacro profiler-or (&rest r)
  (cond ((null r) nil)
        ((null (cdr r)) (car r))
        (t (let ((temp (make-symbol "TEMP")))
             `(let ((,temp ,(car r)))
                (profiler-if ,temp
                             ,temp
                             (profiler-or ,@(cdr r))))))))

(defmacro profiler-when (test &rest r)
  `(profiler-if ,test (progn ,@r)))





; NUMBER OF ARGUMENTS AND RETURN VALUES --------------------------------------
;
; A trivial but critical part of memoizing functions is knowing how many
; arguments they take and how many return values they produce.
;
; Interface:
;
;    (number-of-arguments fn)
;      - Tries to detect how many arguments fn takes
;      - Returns NIL on failure
;
;    (number-of-return-values fn)
;      - Tries to detect how many return values fn has
;      - Returns NIL on failure
;
;    (set-number-of-arguments-and-values fn nargs nvals)
;      - Explicitly asserts that FN has NARGS arguments and NVALS return values
;      - This takes precedence over the introspection code in
;        number-of-arguments and number-of-values.
;      - You'd better be right for soundness.

(defv *number-of-arguments-and-values-ht*

  ;; BOZO probably don't care about defv for this, could just use a
  ;; defparameter.

  (let ((ht (make-hash-table)))
    (declare (hash-table ht))
    ;; [Jared]: I don't understand the motivation for these... it might be best
    ;; to eliminate anything we don't absolutely need from this list.
    (loop for pair in
      '((bad-lisp-objectp . (1 . 1))
        (apropos . (nil . 0))
        (aref . (nil . 1))
        (array-displacement . (1 . 2))
        (decode-float . (1 . 3))
        (expansion-alist-pkg-names-memoize . (1 . 1))
        (fchecksum-obj . (1 . 1))
        (worse-than . (2 . 1))
        (find-symbol . (nil . 2))
        (function . (nil . 1))
        (get-properties . (2 . 3))
        (gethash . (nil . 2))
        (integer-decode-float (1 . 3))
        (intern . (nil . 2))
        ;; [Jared]: this looks weird but makes sense; (lambda (x y z) (mv x y z))
        ;; returns a single argument, viz. an anonymous function.
        (lambda . (nil . 1))
        (list . (nil . 1))
        (list* . (nil . 1))
        (macroexpand . (nil . 2))
        (macroexpand-1 . (nil . 2))
        (pprint-dispatch  . (nil . 2))
        (prog1 . (nil . 1))
        (prog2 . (nil . 1))
        (quote . (1 . 1))) do
      (setf (gethash (car pair) ht)
            (cdr pair)))
    (loop for sym in
          '(car cdr caar cadr cdar cddr caaar cadar cdaar
            cddar caadr caddr cdadr cdddr caaaar cadaar cdaaar cddaar
            caadar caddar cdadar cdddar caaadr cadadr cdaadr cddadr
            caaddr cadddr cdaddr cddddr) do
            (setf (gethash sym ht) '(1 . 1)))
    ht)

  "The hash table *NUMBER-OF-ARGUMENTS-AND-VALUES-HT* maps a symbol fn
  to a cons pair (a . d), where a is the number of inputs and d is the
  number of outputs of fn.  NIL for a or d indicates 'don't know'.")

(declaim (hash-table *number-of-arguments-and-values-ht*))

(defun set-number-of-arguments-and-values (fn nargs nvals)
  (setf (gethash fn *number-of-arguments-and-values-ht*)
        (cons nargs nvals)))


; [Jared]: I don't understand the motivation behind the defn* macros.
;
; Q: Defun-one-output seems to be some kind of ACL2 thing for adding ftype
; proclaims to Common Lisp functions, but defn1 already does a ftype
; declamation, so is there some point to having defn1-one-output?
;
; Q: If these are just for raw lisp functions, why do we care about guards?

(defmacro defn1 (f a &rest r)
  (when (intersection a lambda-list-keywords)
    (error "DEFN1: In the defintion of ~s, the argument list ~s contains a ~
            member of lambda-list-keywords." f a))
  `(progn
     (set-number-of-arguments-and-values ',f ,(length a) 1)
     (declaim (ftype (function ,(make-list (len a) :initial-element t)
                               (values t))
                     ,f))
     (defun ,f ,a
       (declare (xargs :guard t))
       ,@r)))

(defmacro defn1-one-output (f a &rest r)
  (when (intersection a lambda-list-keywords)
    (error "DEFN1-ONE-OUTPUT: In the definition of ~s, the argument list ~s ~
            contains a member of lambda-list-keywords." f a))
  `(progn
     (set-number-of-arguments-and-values ',f ,(length a) 1)
     (declaim (ftype (function ,(make-list (len a) :initial-element t)
                               (values t))
                     ,f))
     (defun-one-output ,f ,a
       (declare (xargs :guard t))
       ,@r)))

(defmacro defn2 (f a &rest r)
  (when (intersection a lambda-list-keywords)
    (error "DEFN2: In the definition of ~s, the argument list ~s contains a ~
            member of lambda-list-keywords." f a))
  `(progn
     (set-number-of-arguments-and-values ',f ,(length a) 2)
     (declaim (ftype (function ,(make-list (len a) :initial-element t)
                               (values t t)) ,f))
     (defun ,f ,a (declare (xargs :guard t)) ,@r)))


(defn1 number-of-arguments (fn)
  (let* ((state *the-live-state*)
         (w (w state))
         (pair (gethash fn *number-of-arguments-and-values-ht*)))
    (cond ((not (symbolp fn))
           ;; This should probably be an error instead.
           nil)

          ((and (consp pair) (integerp (car pair)))
           ;; Table takes precedence
           (car pair))

          ;; Magic code that works for proper ACL2 functions.
          ((let ((formals (getprop fn 'formals t 'current-acl2-world w)))
             (and (not (eq t formals))
                  (length formals))))

          ((or (not (fboundp fn))
               (macro-function fn)
               (special-operator-p fn))
           nil)

          #+Clozure
          ;; Magic code that works for raw Lisp functions on CCL.
          ((multiple-value-bind (req opt restp keys)
                                (ccl::function-args (symbol-function fn))
                                (and (null restp)
                                     (null keys)
                                     (integerp req)
                                     (eql opt 0)
                                     req)))

          (t nil))))

(defn1 number-of-return-values (fn)
  (let* ((state *the-live-state*)
         (w (w state))
         (pair (gethash fn *number-of-arguments-and-values-ht*)))
    (cond ((not (symbolp fn))
           ;; This should probably be an error instead.
           nil)

          ((and (consp pair) (integerp (cdr pair)))
           ;; Table takes precedence
           (cdr pair))

          ((member fn '(let let* mv-let progn if return-last))
           ;; [Jared]: BOZO why cause an error here instead of returning NIL
           ;; like we do in all other cases?
           (error "number-of-return-values: It is curious to ask about 'the' ~
                   number of return values of ~a because the answer is that ~
                   it depends." fn))

          ((let ((formals (getprop fn 'formals t 'current-acl2-world w)))
             ;; Figures out the number of return values for ACL2 functions.
             (and (not (eq t formals))
                  (len (stobjs-out fn w)))))

          (t nil))))




; PONSING --------------------------------------------------------------------
;
; PONS is the critical function for generating memoization keys.  To a rough
; approximation, here is how we memoize (F arg1 arg2 ... argN):
;
;     PONS := (PIST* arg1 ... argN)
;     LOOK := F-MemoTable[PONS]
;     if (LOOK exists)
;        return LOOK
;     else
;        RESULT := (F arg1 arg2 ... argN)
;        F-MemoTable[PONS] = RESULT
;        return RESULT
;
; In other words, we use (PIST* arg1 ... argN) to create the hash key for the
; arguments arg1 ... argN.  And PIST* is defined in terms of PONS.
;
;    (PIST*)          = NIL
;    (PIST* X1)       = X1
;    (PIST* X1 X2)    = (PONS X1 X2)
;    (PIST* X1 X2 X3) = (PONS X1 (PONS X2 X3))
;      ...                ...
;
; As its name suggests, PONS is similar to a HONS.  The main difference is that
; whereas (HONS X Y) requires us to recursively generate a "canonical" version
; of X and Y, (PONS X Y) does not descend into its arguments.
;
; It is worth noting that in the 0 and 1-ary cases of PIST*, no PONSing is
; necessary!  Because of this it can be considerably cheaper to memoize unary
; and zero-ary functions than higher-arity functions.  Note also that as the
; arity of the function increases, the amount of ponsing (and hence its cost)
; increases.
;
; The soundness requirement on PIST* is that two argument lists should produce
; an EQL keys only if they are pairwise EQUAL.  This follows from a stronger
; property of PONS:
;
;     (EQL (PONS A B) (PONS C D))  --->  (EQL A C) && (EQL B D).
;
; Why is this property sufficient?  The 0-2 argument cases are trivial.  Here
; is an sketch of the 3-ary case, which generalizes easily to the N-ary case:
;
;    Our goal is to ensure:
;
;       If   (EQL (PIST* A1 B1 C1) (PIST* A2 B2 C2))
;       Then (EQUAL A1 A2) && (EQUAL B1 B2) && (EQUAL C2 C2)
;
;    Assume the hypothesis:
;
;       (EQL (PONS A1 (PONS B1 C1)) (PONS A2 (PONS B2 C2)))
;
;    Then from our PONS property it follows immediately that
;
;      1. (EQL A1 A2), and hence (EQUAL A1 A2) since EQL implies EQUAL.
;      2. (EQL (PONS B1 C1) (PONS B2 C2)).
;
;    From 2, again from our PONS property it follows that
;
;      1. (EQL B1 B2), and hence (EQUAL B1 B2) since EQL implies EQUAL.
;      2. (EQL C1 C2), and hence (EQUAL C1 C2) since EQL implies EQUAL.
;
;    Which is what we wanted to show.
;
; For our memoization scheme to be effective, it is desirable for PIST* to
; produce EQL keys when given pairwise-EQL argument lists.  This follows easily
; if our PONS property holds in both directions, that is:
;
;     (EQL (PONS A B) (PONS C D))  <--->  (EQL A C) && (EQL B D).
;
; Okay, so how does PONS actually work?  First we will introduce a "slow"
; ponsing scheme, and then explain an optimization that avoids slow ponsing in
; many cases.
;
;
; Slow Ponsing.
;
; The above discussion hides the fact that PONS and PIST* take an additional
; argument, called the Pons Table.  This table is essentially a scheme for
; remembering which keys we have produced for argument lists that have been
; encountered thus far.  Note that the act of PONSing implicitly modifies the
; Pons Table.
;
; The Pons Table is similar to the CDR-HT-EQL in the Classic Honsing scheme;
; see the Essay on Classic Honsing.  That is, it is an EQL hash table that
; binds each
;
;    Y ->  { key : key is the key for (PONS X Y) }
;
; As in classic honsing, these sets are represented as Flex Alists.  The basic
; implementation of (PONS X Y), then, is as follows:
;
;     Y_KEYS := PonsTable[Y]
;     XY_KEY := FlexAssoc(X, Y_KEYS)
;     If (XY_KEY was found)
;        return XY_KEY
;     Else
;        NewKey = (CONS X Y)
;        Y_KEYS := FlexAcons(NewKey, Y_KEYS)
;        PonsTable[Y] := Y_KEYS
;        return NewKey
;
; In other words, we build a new (X . Y) cons and use it as the key, unless we
; had previously seen these same arguments and such a key is already available.
;
;
; Avoiding Slow Ponsing.
;
; When static honsing is enabled, we activate an improvement to slow ponsing.
;
; In particular, if X and Y can be assigned addresses (see the discussion of
; Static Hons Addressing from hons-raw.lisp) without the use of an OTHER-HT or
; STR-HT, then we can just combine their addresses with hl-addr-combine (which
; is one-to-one) and use the resulting integer as our key.  In many cases this
; allows us to avoid the hash table lookups required in Slow Ponsing.
;
; The basic ideas here are:
;
;   - Some ACL2 objects (any static conses, symbol, or small fixnum) have
;     addresses, but other objects (larger numbers, characters, strings, and
;     ordinary conses) do not.
;
;   - If (PONS X Y) is given X and Y that both had addresses, we basically just
;     hash their addresses with hl-addr-combine.  The resulting integer is used
;     as the key.
;
;   - Otherwise, we fall back to Slow Ponsing.  Since slow ponsing always
;     creates a cons instead of an integer, there's no possibility of confusion
;     between the keys from the two schemes.

#+static-hons
(defun pons-addr-of-argument (x)

; See hl-addr-of.  This is similar, except without the STR-HT or OTHER-HT we
; can simply fail to assign addresses to strings, large numbers, rationals, and
; so forth.

; NOTE: Keep this in sync with hl-addr-of and hl-addr-of-unusual-atom.

  (cond ((eq x nil) 256)
        ((eq x t)   257)

        ((symbolp x)
         (hl-symbol-addr x))

        ((and (typep x 'fixnum)
              (<= hl-minimum-static-int (the fixnum x))
              (<= (the fixnum x) hl-maximum-static-int))
         (the fixnum
           (+ hl-static-int-shift (the fixnum x))))

        ((characterp x)
         (char-code x))

        (t
         nil)))

(defabbrev pons-addr-hash (x y)

; We try to compute the addresses of X and Y and hash them together.  If either
; doesn't have an address, we just return NIL.

  #+static-hons
  (let ((xaddr (pons-addr-of-argument x)))
    (if (not xaddr)
        nil
      (let ((yaddr (pons-addr-of-argument y)))
        (if (not yaddr)
            nil
          (hl-addr-combine* xaddr yaddr)))))

  #-static-hons
  ;; We don't try to avoid ponsing here.
  nil)

(defn1 pons (x y ht)
  (declare (hash-table ht))

  #+static-hons
  (let ((addr (pons-addr-hash x y)))
    (when addr (return-from pons addr)))

  (let* ((flex-alist (gethash y ht))
         (entry      (hl-flex-assoc x flex-alist)))
    (or entry
        (let* ((was-alistp (listp flex-alist))
               ;; BOZO think about maybe using static cons here... ??
               (new-cons       (cons x y))
               (new-flex-alist (hl-flex-acons new-cons flex-alist)))
          ;; Ctrl+C safety is subtle.  If was-alistp, then the above
          ;; was applicative.  We now install the flex alist, which
          ;; occurs as a single update to the hash table.
          (when was-alistp
            (setf (gethash y ht) new-flex-alist))
          ;; Otherwise, the flex-acons was non-applicative and the table
          ;; was already extended, so there's nothing more we need to do.
          new-cons))))

(defmacro pist* (table &rest x)
  (cond ((atom x) x)
        ((atom (cdr x)) (car x))
        (t (list 'pons (car x)
                 (cons 'pist* (cons table (cdr x))) table))))







; MEMOIZATION TABLES ---------------------------------------------------------

(defg *memoize-info-ht*
  ;; This is the main memoize database, and it is actually two maps in one:
  ;;   - It binds each currently-memoized function symbol FN to its entry
  ;;   - It binds the number for each memoized function back to the symbol FN
  (mht))

(declaim (hash-table *memoize-info-ht*))

;; [Jared]: but.... isn't it NOT special, since it's defined with defg?
;;
;; (declaim (special *memoize-info-ht*))



(defrec memoize-info-ht-entry
  ;; Main data structure for a particular memoized function.  The fields are
  ;; vaguely ordered by most frequently referenced first.
  (
   ;; this apparently has something to do with attachment tracking...
   ;; extended ancestors with attachments or some such?
   ext-anc-attachments

   ;; start-time is a symbol whose val is the start time of the current,
   ;; outermost call of fn, or -1 if no call of fn is in progress.
   start-time

   num            ;; an integer that is unique to this function
   tablename      ;; a symbol whose value is the memoize table for fn
   ponstablename  ;; a symbol whose value is the pons table for fn
   condition      ;; T or NIL. :condition arg as passed to memoize-fn
   inline         ;; T or NIL. :inline arg as passed to memoize-fn
   memoized-fn    ;; the new value of (symbol-function fn)
   old-fn         ;; the old value of (symbol-function fn), or nil.
   fn             ;; a symbol, the name of the function being memoized
   sts            ;; the stobj memotable lists for fn
   trace          ;; T or NIL. :trace arg as passed to memoize-fn
   before         ;; form to evaluate first

   ;; cl-defun is the function body actually used, in the inline=t case, as
   ;; supplied (or as computed, if not supplied)
   cl-defun

   formals        ;; as supplied (or as computed, if not supplied)
   commutative    ;; asserts this is a binary commutative function

   ;; (advanced, for raw lisp memoization only) specials are any special
   ;; variables read by the function, and are treated like extra, implicit
   ;; arguments.  for real ACL2 functions the specials should always be NIL.
   specials

   stobjs-in      ;; as supplied (or as computed, if not supplied)
   stobjs-out     ;; as supplied (or as computed, if not supplied)

   watch-ifs      ;; Boolean, whether to monitor each IF
   forget         ;; Boolean, clears memo when outermost call exits.

   ;; memo-table-init-size is an integer that says how big the memo
   ;; table should be when it is first created, default *mht-default-size*
   memo-table-init-size
   )
  t)



(defn1 memoized-functions ()
  ;; Get the names of all memoized functions as a list.
  (let (ans)
    (maphash (lambda (fn info)
               (declare (ignore info))
               (when (symbolp fn)
                 (push fn ans)))
             *memoize-info-ht*)
    ans))

(defn1 memoizedp-raw (fn)
  (and (symbolp fn)
       (values (gethash fn *memoize-info-ht*))))

(defn1 memoize-condition (fn)
  ;; Get the condition for a memoized function.
  (let ((x (gethash fn *memoize-info-ht*)))
    (if x
        ;; BOZO should probably check that fn is a symbol.
        (access memoize-info-ht-entry x :condition)
      ;; BOZO should probably cause an error.
      nil)))





; [Jared]: the memoize call array seems really overly complicated.  It's not
; just that it has a strange format, but also we seem to need all this stuff to
; grow it, rememoize functions, etc.  It seems like it might be a lot nicer to
; just make the metering stuff part of the dynamic data associated with the
; memoized function, i.e., instead of having a separate pons table and memoize
; table associated with these various symbols, why not just link to a structure
; that has the pons table, the memo table, the metering stuff, etc., and have
; it all in one place.
;
; [Jared]: Man, this seems worse and worse the more I look into it.  To try to
; avoid indexing into the memoize-call-array at runtime we're doing a lot of
; the index computations at macroexpansion time when functions are memoized,
; which is probably why (or part of the reason) that growing the array requires
; us to rememoize everything.

(defg *memoize-call-array*
  (make-array 1 :element-type 'mfixnum :initial-element 0)

  "*MEMOIZE-CALL-ARRAY*, 'ma' for short, is used for storage of the monitoring
  information for memoized functions.  ma has as its length 4 times the square
  of the maximum number of memoized functions.

  ma is initialized in MEMOIZE-INIT.  Think of ma as a two dimensional array
  with dimensions

     (twice the max number of memoized functions) x
     (twice the max number of memoized functions).

  Each 'column' corresponds to info about a memoized function, but the first
  five columns are 'special'.  We count rows and columns starting at 0.

      Column 0 is used as scratch space by COMPUTE-CALLS-AND-TIMES for sums
      across all functions.

      Columns 1, 2, and 3 are not currently used at all.

      Column 4 is for the anonymous 'outside caller'.

      Column 5 is for the first memoized function.

      In columns 5 and greater,
         - row 0 is used to count 'bytes',
         - row 1 for 'hits',
         - row 2 for MHT calls,
         - row 3 for 3 HONS calls (defunct), and
         - row 4 for PONS calls (defunct).

  The elements of an ma column starting at row 10 are for counting and timing
  info.  Suppose column 7 corresponds to the memoized function FOO and column
  12 corresponds to the memoized function BAR.  Whenever FOO calls BAR, element
  2*12 of column 7 will be incremented by 1, and the total elapsed time for the
  call will be added to element 2*12+1 of column 7.

  Though ma may 'grow', it may not grow while any memoized function is running,
  and here is why: every memoized function has a cached opinion about the size
  of ma.  To avoid an abort during a call of MEMOIZE one may
  call (MEMOIZE-HERE-COME n) to assure that ma has room for at least n more
  memoized functions.")

(declaim (type (simple-array mfixnum (*)) *memoize-call-array*))




(defv *initial-max-memoize-fns* 500)

(defg *2max-memoize-fns* (* 2 *initial-max-memoize-fns*))
(declaim (type fixnum *2max-memoize-fns*))

(defconstant *ma-bytes-index*       0)
(defconstant *ma-hits-index*        1)
(defconstant *ma-mht-index*         2)
(defconstant *ma-hons-index*        3)
(defconstant *ma-pons-index*        4)

(defconstant *ma-initial-max-symbol-to-fixnum* 4)

(defg *max-symbol-to-fixnum* *ma-initial-max-symbol-to-fixnum*)
(declaim (type fixnum *max-symbol-to-fixnum*))


(defn clear-memoize-call-array ()

  "(CLEAR-MEMOIZE-CALL-ARRAY) zeros out all records of function calls as far as
  reporting by MEMOIZE-SUMMARY, etc. is concerned."

  (let ((m *memoize-call-array*))
    (declare (type (simple-array mfixnum (*)) m))
    (loop for i fixnum below (length m)
          do (setf (aref m i) 0))))

(defn clear-memoize-statistics ()
  ;; User-level.  See memoize.lisp.
  (clear-memoize-call-array)
  nil)



(defmacro heap-bytes-allocated ()

  #+Clozure
  '(the mfixnum (ccl::%heap-bytes-allocated))

  ;; Might be easy to add this sort of thing for some other Lisps, but
  ;; for now we'll just say 0.
  #-Clozure
  0)


(defn1 bytes-allocated (x)

; BOZO why are we caring about performance here?
  "For a memoized function X, (BYTES-ALLOCATED x) is the number of
  heap bytes X has caused to be allocated on the heap."

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (the mfixnum (+ *ma-bytes-index*
                        (the mfixnum (* *2max-memoize-fns* (the mfixnum x)))))))

; It would be nice to pull out the updating code into a coherent thing, but
; it's very tricky with the memoize-call-array complications...
;; (defabbrev update-bytes-allocated (memoize-call-array 2mfnn start-bytes)
;;   `(safe-incf (aref memoize-call-array
;;                     ,(+ *ma-bytes-index* 2mfnn))
;;                              (the mfixnum (- (heap-bytes-allocated) ,*mf-start-bytes*))
;;                              ,fn)


(defn1 number-of-hits (x)

; BOZO why are we caring about performance here?

  "For a memoized function X, (NUMBER-OF-HITS x) is the number of
  times that a call of X returned a remembered answer."

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (the mfixnum (+ *ma-hits-index*
                        (the mfixnum (* *2max-memoize-fns* (the mfixnum x)))))))






;; BOZO ??!? what are these??
(defg *compute-array* (make-array 0)

  "*COMPUTE-ARRAY*, ca for short, is an array of proper lists.  At the
  end of a call of COMPUTE-CALLS-AND-TIMES, which is called by
  MEMOIZE-SUMMARY, (aref ca n) will contain the numbers of the
  functions that have called the function numbered n.")

(declaim (type (simple-array t (*)) *compute-array*))


;; BOZO ??!? what are these??
(defg *caller* (* *ma-initial-max-symbol-to-fixnum* *2max-memoize-fns*)
  "When memoized functions are executing in parallel, the value of
  *CALLER* and of statistics derived therefrom may be meaningless and
  random.")

(declaim (type fixnum *caller*))




(defn memoize-here-come (n)
  (let ((m (ceiling
            (+ 100 (* 1.1 (- n (- (/ *2max-memoize-fns* 2)
                                  (floor
                                   (/ (hash-table-count *memoize-info-ht*) 2)))))))))
    (when (posp m) (memoize-call-array-grow (* 2 m)))))

(defn sync-memoize-call-array ()

  ; To be called only by MEMOIZE-INIT, MEMOIZE-CALL-ARRAY-GROW, or
  ; SAVE-MEMOIZE-CALL-ARRAY.

  (let ((n1 (the fixnum (* *2max-memoize-fns* *2max-memoize-fns*)))
        (n2 (1+ *max-symbol-to-fixnum*)))
    (declare (type fixnum n1 n2))
    (unless (eql n1 (length *memoize-call-array*))
      (unless (eql 1 (length *memoize-call-array*))
        (setq *memoize-call-array*
              (make-array 1 :element-type 'mfixnum :initial-element 0))
        ;; [Jared]: What the hell?  Why are we gc'ing?
        (gc$))
      (setq *memoize-call-array*
            (make-array n1 :element-type 'mfixnum :initial-element 0)))
    (unless (eql n2 (length *compute-array*))
      (setq *compute-array* (make-array n2 :initial-element nil)))
    (setq *caller* (* *ma-initial-max-symbol-to-fixnum* *2max-memoize-fns*))))

(defun memoize-call-array-grow
  (&optional (2nmax (* 2 (ceiling (* 3/2 (/ *2max-memoize-fns* 2))))))
  (unless (integerp 2nmax)
    (error "(memoize-call-array-grow ~s).  Arg must be an integer." 2nmax))
  (unless (evenp 2nmax)
    (error "(memoize-call-array-grow ~s).  Arg must be even." 2nmax))
  (unless (> 2nmax 100)
    (error "(memoize-call-array-grow ~s).  Arg must be > 100." 2nmax))
  (when (<= 2nmax *2max-memoize-fns*)
    (error "memoize-call-array-grow: *memoize-call-array* already big enough.")
    (return-from memoize-call-array-grow))
  (unless (<= (* 2nmax 2nmax) most-positive-fixnum)
    (error "memoize-call-array-grow: most-positive-fixnum exceeded.  Too many ~
            memoized functions."))
  (unless (< (* 2nmax 2nmax) array-total-size-limit)
    (error "memoize-call-array-grow: ARRAY-TOTAL-SIZE-LIMIT exceeded.  Too ~
            many memoized functions."))
  (unless (eql *caller* (* *ma-initial-max-symbol-to-fixnum* *2max-memoize-fns*))
    (ofv "MEMOIZE-CALL-ARRAY-GROW was called while a memoized-function~% was ~
          executing, so call reports may be quite inaccurate."))

  (setq *memoize-call-array*
        (make-array 1 :element-type 'mfixnum :initial-element 0))
  (setq *2max-memoize-fns* 2nmax)
  (sync-memoize-call-array)
  (rememoize-all)
  nil)





;; --------------- THE TERRIBLE LINE -------------------------------------
;; --------------- THE TERRIBLE LINE -------------------------------------
;; --------------- THE TERRIBLE LINE -------------------------------------



; ----------------------------------------------------------------------------
; SAFE-INCF

;; [Jared]: this seems kind of awful.

(defmacro safe-incf (x inc &optional where)

  "SAFE-INCF is essentially like a MFIXNUM version of INCF, but:
     - it always returns NIL instead of the sum
     - it does nothing when the increment amount is zero
     - it causes an error if the addition overflows

  In a call of (SAFE-INCF X INC),
     - X must be a place that holds an MFIXNUM
     - INC must evaluate to an MFIXNUM
     - Both X and INC must evaluate without side effects.

  An optional third parameter is merely to help with error location
  identification.

  In (SAFE-INCF (AREF A (FOO)) INC), (FOO) is only evaluted once.  Same for
  SVREF."

  (cond ((integerp inc)
         (if (<= inc 0)
             nil
           `(safe-incf-aux ,x ,inc ,where)))

        ((symbolp inc)
         `(profiler-if (>= 0 (the mfixnum ,inc))
                       nil
                       (safe-incf-aux ,x ,inc ,where)))

        (t (let ((incv (make-symbol "INCV")))
             `(let ((,incv (the mfixnum ,inc)))
                (declare (type mfixnum ,incv))
                (profiler-if (>= 0 ,incv)
                             nil
                             (safe-incf-aux ,x ,incv ,where)))))))

(defn1 safe-incf-aux-error (x inc where)
  (error "~%; SAFE-INCF-AUX: ** Error: ~a."
         (list :x x :inc inc :where where)))

(defmacro safe-incf-aux (x inc where)
  (profiler-cond
   ((not (or (symbolp inc)
             (profiler-and (< inc most-positive-mfixnum)
                           (> inc 0))))
    (safe-incf-aux-error x inc where))

   ((profiler-and (true-listp x)
                  (equal (len x) 3)
                  (member (car x) '(aref svref))
                  (symbolp (nth 1 x))
                  (consp (nth 2 x)))
    (let ((idx (make-symbol "IDX")))
      `(let ((,idx (the fixnum ,(nth 2 x))))
         (declare (type fixnum ,idx))
         (safe-incf (,(nth 0 x) ,(nth 1 x) ,idx)
                    ,inc
                    ',where))))

   (t
    (let ((v (make-symbol "V")))
      `(let ((,v (the mfixnum ,x)))
         (declare (type mfixnum ,v))
         (profiler-cond
          ((<= ,v (the mfixnum (- most-positive-mfixnum (the mfixnum ,inc))))
           (setf (the mfixnum ,x)
                 (the mfixnum (+ ,v (the mfixnum ,inc))))
           nil)
          (t
           (safe-incf-aux-error ',x ',inc ',where))))))))







;  OUR-SYNTAX

(defmacro our-syntax (&rest args)

  "OUR-SYNTAX is similar to Common Lisp's WITH-STANDARD-IO-SYNTAX.
  The settings in OUR-SYNTAX are oriented towards reliable, standard, vanilla,
  mechanical reading and printing, and less towards human readability.

  Please, before changing the following, consider existing uses of this macro
  insofar as the changes might impact reliable, standard, vanilla, mechanical
  printing.  Especially consider COMPACT-PRINT-FILE.  Consider using
  OUR-SYNTAX-NICE."

; We use the *ACL2-PACKAGE* and the *ACL2-READTABLE* because we use
; them almost all the time in our code.

; Keep in sync with COMPACT-PRINT-STREAM.

  `(with-standard-io-syntax
    (setq *package*   *acl2-package*)
    (setq *readtable* *acl2-readtable*)
    ,@args))

(defmacro our-syntax-nice (&rest args)

; OUR-SYNTAX-NICE offers slightly more pleasant human readabilty.

  `(our-syntax
    (setq *print-case*                 :downcase)
    (setq *print-pretty*               t)
    (setq *print-readably*             nil)
    (setq *print-right-margin*         70)
    (setq *print-miser-width*          100)
    ,@args))


(defv *hons-verbose* t)
(defg *ofv-note-printed* nil)
(defg *ofv-msg-list* nil)


(defun ofv (&rest r) ; For verbose but helpful info.
  (our-syntax-nice
   (when *hons-verbose*
     (format *debug-io* "~%; Aside:  ")
     (let ((*print-level* 3)
           (*print-length* 5)
           (*print-lines* 5))
       (let ((ab (loop for x in r collect (abbrev x))))
         (apply #'format *debug-io* ab)
         (when (loop for x in ab as y in r thereis (not (eq x y)))
           (push (cons 'ofv r) *ofv-msg-list*)
           (format *debug-io* "~%; See *ofv-msg-list*."))
         (unless *ofv-note-printed*
           (format *debug-io*
                   "~%; Aside:  (setq acl2::*hons-verbose* nil) to ~
                    suppress asides.")
           (setq *ofv-note-printed* t))))
     (force-output *debug-io*))))


(defmacro ofn (&rest r) ; For forming strings.
  `(our-syntax (format nil ,@r)))

(defn1 ofnum (n) ; For forming numbers.
  (check-type n number)
  (if (= n 0) (setq n 0))
  (our-syntax
   (cond ((typep n '(integer -99 999))
          (format nil "~8d" n))
         ((or (< -1000 n -1/100)
              (< 1/100 n 1000))
          (format nil "~8,2f" n))
         (t (format nil "~8,2e" n)))))

(defmacro ofni (&rest r) ; For forming symbols in package ACL2.
  `(our-syntax (intern (format nil ,@r) *acl2-package*)))

(defmacro ofnm (&rest r) ; For forming uninterned symbols.
  `(our-syntax (make-symbol (format nil ,@r))))

(defmacro oft (&rest r) ; For writing to *standard-output*.
  `(progn (format t ,@r) (force-output *standard-output*)))

(defmacro oftr (&rest r) ; For writing to *trace-output*.
  `(progn (format *trace-output* ,@r) (force-output *trace-output*)))

(defn1 suffix (str sym)
  (check-type str string)
  (check-type sym symbol)
  (let ((spkn (package-name (symbol-package sym)))
        (sn (symbol-name sym)))
    (format nil "~s,~s,~s" str spkn sn)))










;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;; MEMOIZE ;;;;;;;;;;

; for initialization

(defg *memoize-init-done* nil)

; locals used in memoize-on and memoize-off





; locals used in functions generated by memoize-fn

(defconstant *mf-old-caller*  (make-symbol "OLD-CALLER"))
(defconstant *mf-start-bytes* (make-symbol "START-BYTES"))
(defconstant *mf-ans*         (make-symbol "ANS"))
(defconstant *mf-ans-p*       (make-symbol "ANS-P"))
(defconstant *mf-ma*          (make-symbol "MA"))
(defconstant *mf-args*        (make-symbol "ARGS"))
(defconstant *mf-2mmf*        (make-symbol "MF-2MMF"))
(defconstant *mf-2mmf-fnn*    (make-symbol "MF-2MMF-FNN"))
(defconstant *mf-count-loc*   (make-symbol "MF-COUNT-LOC"))


(defv *never-profile-ht* (make-hash-table :test 'eq))
(declaim (hash-table *never-profile-ht*))


(defn1 st-lst (st)

; ST-LST returns a symbol whose value is a list in which are saved the names of
; the memoize tables that will be set to nil whenever the stobj st is changed.

  (check-type st symbol)
  (multiple-value-bind (symbol status)
      (intern (format nil "HONS-S-~s,~s"
                      (package-name (symbol-package st))
                      (symbol-name st))
              (find-package "ACL2_INVISIBLE"))
    (or status (eval `(defg ,symbol nil)))
    symbol))

(defmacro memoize-flush (st)

; MEMOIZE-FLUSH 'forgets' all that was remembered for certain functions that
; use certain stobjs.  We must keep memoize-flush very fast in execution so as
; not to slow down stobj update or resize operations in general.  We 'forget'
; the pons table later.

  (let ((s (st-lst st)))
    `(when (boundp ',s)
       (loop for sym in (symbol-value ',s) do
             (when (boundp sym) ; Is this test needed?
               (let ((old (symbol-value sym)))
                 (unless (or (null old)
                             ;; don't clear empty hts?  probably silly
                             (and (hash-table-p old)
                                  (eql 0 (hash-table-count old))))
                   (setf (symbol-value sym) nil))))))))





(defparameter *memo-max-sizes*
  ;; Binds function names to memo-max-sizes-entry structures.
  ;;
  ;; Jared originally added this table because he wanted to know how big
  ;; memoization tables were getting (so that he could set up appropriate
  ;; initial sizes), but when tables are cleared they are thrown away, so for
  ;; tables that are frequently cleared it wasn't possible to see how large the
  ;; table had become.
  ;;
  ;; After seeing the information, we thought it might be a good idea to use it
  ;; to infer what a good table size might be when we recreate the memo table.
  ;; See the function predict-good-memoize-table-size for details.
  (make-hash-table))

; BOZO should we use this information to try to guess better sizes and
; rehash thresholds for memoize tables?

(defrec memo-max-sizes-entry
  ;; A single entry in the *memo-table-max-sizes* table.
  (num-clears   ; how many times has this table been cleared (nat)
   max-pt-size  ; maximum size of the pons table before any clear (nat)
   max-mt-size  ; maximum size of the memo table before any clear (nat)
   avg-pt-size  ; average size of pons table before any clear (float)
   avg-mt-size  ; average size of memo table before any clear (float)
   )
  t)

(defun make-initial-memoize-hash-table (fn init-size)

; FN is the name of a function.  INIT-SIZE is the initial size that the user
; says we should use.  We want to come create and return a new hash table for
; this function's memoization table.  One possible implementation of this
; function would just be:
;
;    (mht :size init-size)
;
; But we hope to do better.  Our idea is to look at how large the table has
; been in the past, and use that size to make a good prediction of how large
; the table will be this time.
;
; The idea here is to build a table that's just slightly bigger than the
; average size we've seen so far.  We arbitrarily say that "slightly bigger"
; means 1.2x the previous average.
;
; By itself this would be scary.  Big hash tables can use a lot of memory: a
; rule of thumb in CCL is that 1 MB of space buys you 44,000 entries.  I want
; to avoid creating a hundred-megabyte memo tables for a function just because
; it was used heavily for a short while and then cleared once before.  On the
; other hand, if a memo table truly does get large on a regular basis, then we
; do want to guess a big size for it.
;
; So in this code, I enforce an artificial maximum on our guess, but I allow
; this maximum to grow with the number of times we've cleared the table.
; Basically I allow the maximum guess to grow at a rate of 1 MB per clear.  If
; a table has been cleared 100 times, I think we have a pretty good sense of
; its average usage and we can be comfortable allocating up to 100 MB for it.
; If it's been cleared more than 1000 times, the cap is a gigabyte.  But of
; course, to actually reach such a large guess, you'd have to be repeatedly
; filling up the table to contain millions of entries and then clearing it.

  (let* ((max-sizes
          ;; The previously recorded sizes of this table, if any exist.
          (gethash fn *memo-max-sizes*))
         (size-to-use
          (if (not max-sizes)
              ;; We never cleared this memoize table before, so we don't have
              ;; anything to go on besides what the user says.  Do what they
              ;; say.
              init-size
            (let* ((nclears       (access memo-max-sizes-entry max-sizes :num-clears))
                   (avg-mt-size   (access memo-max-sizes-entry max-sizes :avg-mt-size))
                   (our-guess     (ceiling (* 1.20 avg-mt-size)))
                   (capped-guess  (min our-guess (* nclears 44000)))
                   (final-guess   (max 60 init-size capped-guess)))
              final-guess))))
    ;; BOZO also try to guess a better rehash-size?
    (mht :size size-to-use)))

(defun make-initial-memoize-pons-table (fn init-size)

; This is just like make-initial-memoize-hash-table, but for the pons table.

  (let* ((max-sizes (gethash fn *memo-max-sizes*))
         (size-to-use
          (if (not max-sizes)
              init-size
            (let* ((nclears       (access memo-max-sizes-entry max-sizes :num-clears))
                   (avg-pt-size   (access memo-max-sizes-entry max-sizes :avg-pt-size))
                   (our-guess     (ceiling (* 1.20 avg-pt-size)))
                   (capped-guess  (min our-guess (* nclears 44000)))
                   (final-guess   (max 60 init-size capped-guess)))
              final-guess))))
    ;; BOZO also try to guess a better rehash-size?
    (mht :size size-to-use)))

(defun update-memo-max-sizes (fn pt-size mt-size)
  ;; Called during clear-one-memo-and-pons-hash when the tables existed.
  ;; When called, pt-size and mt-size are nonzero.
  (let ((old (gethash fn *memo-max-sizes*)))
    (if (not old)
        (setf (gethash fn *memo-max-sizes*)
              (make memo-max-sizes-entry
                    :num-clears 1
                    :max-pt-size pt-size
                    :max-mt-size mt-size
                    :avg-pt-size (coerce pt-size 'float)
                    :avg-mt-size (coerce mt-size 'float)))
      (let* ((old.num-clears  (access memo-max-sizes-entry old :num-clears))
             (old.max-pt-size (access memo-max-sizes-entry old :max-pt-size))
             (old.max-mt-size (access memo-max-sizes-entry old :max-mt-size))
             (old.avg-pt-size (access memo-max-sizes-entry old :avg-pt-size))
             (old.avg-mt-size (access memo-max-sizes-entry old :avg-mt-size))
             (new.num-clears  (+ 1 old.num-clears)))
        (setf (gethash fn *memo-max-sizes*)
              (make memo-max-sizes-entry
                    :num-clears  new.num-clears
                    :max-pt-size (max pt-size old.max-pt-size)
                    :max-mt-size (max mt-size old.max-mt-size)
                    :avg-pt-size (/ (+ pt-size (* old.avg-pt-size old.num-clears))
                                    new.num-clears)
                    :avg-mt-size (/ (+ mt-size (* old.avg-mt-size old.num-clears))
                                    new.num-clears))))))
  nil)

(defun print-memo-max-sizes ()
  (when (equal (hash-table-count *memo-max-sizes*) 0)
    (return-from print-memo-max-sizes nil))
  (format t "Memo table statistics gathered at each from when they were cleared:~%~%")
  (let ((indent 8) ;; length of "Function"
        (indent-str nil))
    (maphash (lambda (fn entry)
               (declare (ignore entry))
               (setq indent (max indent (length (symbol-name fn)))))
             *memo-max-sizes*)
    (setq indent-str (format nil "~a" (+ 2 indent)))
    (format t (concatenate 'string "~" indent-str ":@a") "Function")
    (format t " ~10:@a | ~15:@a ~15:@a | ~15:@a ~15:@a~%"
            "Clears" "PT Max" "PT Avg" "MT Max" "MT Avg")
    (maphash
     (lambda (fn entry)
       (let* ((num-clears  (access memo-max-sizes-entry entry :num-clears))
              (max-pt-size (access memo-max-sizes-entry entry :max-pt-size))
              (max-mt-size (access memo-max-sizes-entry entry :max-mt-size))
              (avg-pt-size (access memo-max-sizes-entry entry :avg-pt-size))
              (avg-mt-size (access memo-max-sizes-entry entry :avg-mt-size)))
         (format t (concatenate 'string "~" indent-str ":@a ~10:D | ~15:D ~15:D | ~15:D ~15:D~%")
                 fn num-clears
                 max-pt-size (floor avg-pt-size)
                 max-mt-size (floor avg-mt-size))))
     *memo-max-sizes*)
    (format t "~%"))
  nil)









(defn1 symbol-to-fixnum-create (s)
  (check-type s symbol)
  (let ((g (gethash s *memoize-info-ht*)))
    (if g
        (access memoize-info-ht-entry g :num)
      (let (new)
        (loop for i fixnum from
              (if (eql *caller* (* *ma-initial-max-symbol-to-fixnum*
                                   *2max-memoize-fns*))
                  (1+ *ma-initial-max-symbol-to-fixnum*)
                (1+ *max-symbol-to-fixnum*))
              below (the fixnum (floor *2max-memoize-fns* 2))
              do (unless (gethash i *memoize-info-ht*)
                   (setq new i)
                   (return)))
        (cond (new
               (setq *max-symbol-to-fixnum* (max *max-symbol-to-fixnum* new))
               new)
              (t (memoize-call-array-grow)
                 (safe-incf *max-symbol-to-fixnum* 1 symbol-to-fixnum-create)
                 *max-symbol-to-fixnum*))))))

(defn1 symbol-to-fixnum (s)
  (check-type s symbol)
  (let ((g (gethash s *memoize-info-ht*)))
    (if g (access memoize-info-ht-entry g :num)
      (error "(symbol-to-fixnum ~s).  Illegal symbol." s))))

(defn1 fixnum-to-symbol (n)
  (check-type n fixnum)
  (or (gethash n *memoize-info-ht*)
      (error "(fixnum-to-symbol ~s). Illegal number." n)))

(defn1 coerce-index (x)
  (if (and (typep x 'fixnum)
           (>= x 0)
           (< x (length *memoize-call-array*)))
      x
    (symbol-to-fixnum x)))







; We use DEFVAR for *UNSMASHED-IF* and *UNSMASHED-OR* so we don't set
; them; that could accidentally pick up the wrong value if this file
; were loaded twice.

(defvar *unsmashed-if* (compiler-macro-function 'if))
(defvar *unsmashed-or* (compiler-macro-function 'or))

(defg *smashed-if* nil)
(defg *smashed-or* nil)

(defn1 memoize-eval-compile (def watch-ifs)
  (unless (and (consp def)
               (eq 'defun (car def))
               (consp (cdr def))
               (symbolp (cadr def)))
    (error "MEMOIZE-EVAL-COMPILE:  Bad input:~%~s." def))
  (cond
   #+Clozure
   ((and watch-ifs *smashed-if* *unsmashed-if*)
    (cond ((and (eql ccl::*nx-speed* 3)
                (eql ccl::*nx-safety* 0))
           (unwind-protect
               (progn
                 (setf (compiler-macro-function 'if) *smashed-if*)
                 (setf (compiler-macro-function 'or) *smashed-or*)
                 (compile (eval def)))
             (setf (compiler-macro-function 'if) *unsmashed-if*)
             (setf (compiler-macro-function 'or) *unsmashed-or*)))
          (t (format t "~%; MEMOIZE-EVAL-COMPILE: ~a.  WATCH-IF does not work ~
                        unless SAFETY=0 and SPEED=3."
                     (cadr def))
             (compile (eval def)))))
   (t
    (compile (eval def))))
  nil)




(defg *hons-gentemp-counter* 0)
(declaim (type fixnum *hons-gentemp-counter*))

(defn1-one-output hons-gentemp (root)
  (check-type root string)
  (loop
   (safe-incf *hons-gentemp-counter* 1 hons-gentemp)
   (let ((name (format nil "HONS-G-~s,~s" root *hons-gentemp-counter*)))
     (multiple-value-bind (sym status)
         (intern name (find-package "ACL2_INVISIBLE"))
       (if (null status) (return sym))))))


(defn1 dcls (l)
     (loop for dec in l nconc
           (let ((temp
                  (if (consp dec)
                      (loop for d in (cdr dec) nconc
                            (if (and (consp d) (eq (car d) 'ignore))
                                nil
                              (cons d nil))))))
             (if temp (cons (cons 'declare temp) nil)))))


; PRINE  - princ eviscerated

(defg *assoc-eq-hack-ht* (mht :test 'eql))
(declaim (hash-table *assoc-eq-hack-ht*))

(defn assoc-eq-hack (x y)
  (cond ((atom y) nil)
        (t (let ((h (gethash y *assoc-eq-hack-ht*)))
             (cond (h (gethash x h))
                   (t (setq h (mht :test 'eq))
                      (setf (gethash y *assoc-eq-hack-ht*) h)
                      (loop for pair in y do
                            (setf (gethash (car pair) h) pair))
                      (gethash x h)))))))

(defun abbrev (x &optional
                (level *print-level*)
                (length *print-length*))
  (cond ((atom x) x)
        ((eql level 0) '?)
        ((eql length 0) '?)
        (t (let ((pair (assoc-eq-hack
                        x (table-alist 'evisc-table
                                       (w *the-live-state*)))))
             (cond (pair (cdr pair))
                   (t (let ((a (abbrev (car x)
                                       (and level (1- level))
                                       length))
                            (d (abbrev (cdr x)
                                       level
                                       (and length (1- length)))))
                        (cond ((and (eq a (car x))
                                    (eq d (cdr x)))
                               x)
                              ((and (eq a '?)
                                    (eq d '?))
                               '?)
                              (t (cons a d))))))))))

(defun prine (obj &optional stream)
  (let ((*print-pretty* nil))
    (princ (abbrev obj *print-level* *print-length*) stream)))


(defun prine-alist (obj &optional stream)

  ; Does not print the last atom.
  ; Prints "=" between pairs.

  (let ((*print-pretty* t))
    (let ((max 6))
      (cond
       ((loop for tail on obj always
              (and
               (consp (car tail))
               (atom (caar tail))
               (setq max (max max
                              (if (symbolp (caar tail))
                                  (length (symbol-name (caar tail)))
                                0)))))
        (loop for tail on obj do
              (cond ((eq obj tail) (write-char #\Space stream))
                    (t (format t "~&    ")))
              (princ (caar tail) stream)
              (loop for i fixnum below
                    (- max
                       (if (symbolp (caar tail))
                           (length (symbol-name (caar tail)))
                         0))
                    do (write-char #\Space stream))
              (princ " = ")
              (prine (cdar tail) stream)))
       (t (prine obj stream))))))

; MEMOIZE-FN


; [Jared]: it seems like we don't care about memoize tracing, whatever that is,
; but maybe this sort of thing is meant for debugging the memoization code.

(defn1 mf-trace-exit (fn nrv ans)
  (oftr "~%< ~s " fn)
  (cond ((> nrv 1)
         (oftr "returned ~@r values:" nrv)
         (loop for i fixnum from 1 to nrv do
               (format t "~%~@r.~8t  " i)
               (prine (car ans) *trace-output*)))
        (t (prine ans *trace-output*)))
  (oftr ")~%"))


(defn fle (x)

  "FLE is akin to the ANSI Common Lisp function FUNCTION-LAMBDA-EXPRESSION.
  'FLE' is shorter.  (FLE 'foo) may return, among other things, the defining
  body of the function FOO.  In Clozure Common Lisp, definition saving is
  controlled by the settings of the variables CCL::*SAVE-DEFINITIONS* and
  CCL::*FASL-SAVE-DEFINITIONS*.  Under Closure Common Lisp, we may also first
  print the name of the file in which FOO was defined."

  #+Clozure
  (let ((loc (ccl::find-definition-sources x)))
    (let ((*print-pretty* nil))
      (when loc (format t "~%; source: ~s" loc))))
  (cond ((functionp x)
         (function-lambda-expression x))
        ((symbolp x)
         (let ((fn (symbol-function x)))
           (cond ((functionp fn)
                  (function-lambda-expression fn))
                 #+Clozure
                 ((and (arrayp fn) (functionp (aref fn 1)))
                  (function-lambda-expression (aref fn 1)))
                 (t (error "Can't figure out ~a as a function." x)))))))


(defconstant *attached-fn-temp* (make-symbol "ATTACHED-FN-TEMP"))

(defvar *memoize-use-attachment-warning-p* t)

(defun memoize-use-attachment-warning (fn at-fn)
  (when *memoize-use-attachment-warning-p*
    (with-live-state
     (warning$ 'top-level "Attachment"
               "Although the function ~x0 is memoized, a result is not being ~
                stored because ~@1.  Warnings such as this one, about not ~
                storing results, will remain off for all functions for the ~
                remainder of the session unless the variable ~x2 is set to a ~
                non-nil value in raw Lisp."
               fn
               (mv-let (lookup-p at-fn)
                       (if (consp at-fn)
                           (assert$ (eq (car at-fn) :lookup)
                                    (mv t (cdr at-fn)))
                         (mv nil at-fn))
                       (cond (lookup-p
                              (msg "a stored result was used from a call of ~
                                    memoized function ~x0, which may have been ~
                                    computed using attachments"
                                   at-fn))
                             (t
                              (msg "an attachment to function ~x0 was used ~
                                    during evaluation of one of its calls"
                                   at-fn))))
               '*memoize-use-attachment-warning-p*))
    (setq *memoize-use-attachment-warning-p* nil)))


#+Clozure
(defn1 mis-ordered-commutative-args (x y)

; [Jared]: I haven't really spent the time to grok this function yet, but it
; looks like it fails to commute non-static conses.  We might at least put
; things into canonical order per their machine addresses.  Sure a GC could
; invalidate this by relocating them, but it still might be better than nothing
; most of the time.

  (cond ((eql x y) nil)
        (t (let ((idx (or (ccl::%staticp x)
                          (and (typep x 'fixnum) x))))
             (cond (idx
                    (let ((idy (or (ccl::%staticp y)
                                   (and (typep y 'fixnum) y))))
                      (cond (idy (< (the fixnum idy)
                                    (the fixnum idx)))
                            ((rationalp y)
                             (< y (the fixnum idx))))))
                   ((rationalp x)
                    (let ((idy (or (ccl::%staticp y)
                                   (and (typep y 'fixnum) y))))
                      (cond (idy (< (the fixnum idy)
                                    x))
                            ((rationalp y)
                             (< y x))))))))))



(defun memoize-fn (fn &key (condition t) (inline t) (trace nil)
                      (cl-defun :default)
                      (formals :default)
                      (stobjs-in :default)
                      (stobjs-out :default)
                      (commutative nil)
                      (specials nil)
                      (watch-ifs nil)
                      (forget nil)
                      (memo-table-init-size *mht-default-size*)
                      (aokp nil)
                      &aux (wrld (w *the-live-state*)))

; [Jared] comment rescued from far above...

; The :CONDITION parameter of MEMOIZE-FN can either be T, or a
; function symbol defined by the user within the ACL2 loop, or a LISTP
; (CONSP or NIL).  In the last case we think of the condition as an
; expression in the formals of FN.  If the :INLINE parameter T, then
; the body of FN is placed inline in the memoized definition;
; otherwise, a funcall of the original function is placed there.


; [Jared]: stray comment rescued from somewhere...

; This code has the 'feature' that if the condition causes an error,
; so will the memoized function.


  "The documentation for MEMOIZE-FN is very incomplete.  One may
  invoke (MEMOIZE-FN fn) on the name of a Common Lisp function FN from
  outside the ACL2 loop to get results of possible interest in terms
  of memoization activity and profiling information.  MEMOIZE-FN
  already has a dozen parameters.

  MEMOIZE-FN replaces the SYMBOL-FUNCTION for the symmbol FN with
  'enhanced' raw Common Lisp code that, supposedly, does not affect
  the value returned by FN but may make some notes and may even obtain
  some return values by remembering them from a previous call.

  If the CONDITION parameter is not NIL, then whenever FN is called,
  and there is not as yet any value remembered for a call of FN on the
  given arguments, then if the evaluation of the CONDITION parameter
  is not NIL, the values that are computed for FN on the given
  arguments will be saved under the given arguments.  If the CONDITION
  parameter is the name of an ACL2 function, the body of that function
  is used as the condition.

  If the INLINE parameter is T, then when MEMOIZE-FN creates a new
  body for FN, we place the old body of FN within the new body, i.e.,
  'in line'.  However, if the INLINE parameter is NIL, then we place
  code that calls the existing SYMBOL-FUNCTION for FN within the new
  body.  One might well argue that our parity for the INLINE parameter
  to MEMOIZE-fn is backwards, but we don't think so.

  The TRACE parameter to MEMOIZE-FN may be T, NIL, :INLINE, or
  :NOTINLINE.

  One may lie to MEMOIZE-FN to force the memoization of a function
  that has ACL2's state as an explicit parameter by using fraudulent
  FORMALS, STOBJS-IN, and STOBJS-OUT parameters to MEMOIZE-FN.

  If the COMMUTATIVE parameter is not NIL, then the two arguments may
  be swapped before further processing.  We hope/presume that ACL2
  will have been used first to prove that commutativity.

  If the CL-DEFN parameter is not NIL, we pretend that the current
  body of FN is that parameter, and similarly for FORMALS, STOBJS-IN,
  and STOBJS-OUT.

  If FN is a raw Common Lisp function and not an ACL2-approved
  function, it may make reference to a variable, say S, that has a
  SPECIAL binding, in which case one needs to consider what in the
  world the meaning is for memoizing such a function at all.  If S is
  a member of the SPECIALS parameter, then it is assumed that FN does
  not alter but only refers to S.  MEMOIZE-FN acts as though FN had S
  as an extra argument for purposes of memoization.

  The WATCH-IFS parameter to MEMOIZE-FN has meaning only when using
  Clozure Common Lisp (CCL).  Under CCL, if the WATCH-IFS parameter is
  not NIL, then every branch of every IF (including OR, AND, COND, and
  CASE) expression in the source code for FN is inflicted with an
  emendation that monitors how many times the true or false branch is
  taken.  This information is printed both by (MEMOIZE-SUMMARY) and in
  more detail by (IF-REPORT).

  If the FORGET parameter is not NIL, the pons and memo tables of FN
  are cleared at the end of every outermost call of FN."

; MIS-ORDERED-COMMUTATIVE-ARGS apparently, but only apparently,
; introduces nondeterminism into the values returned by ACL2 functions
; redefined with MEMOIZE-FN, something highly suspicious because it
; can so easily lead to a contradition.

; We believe that the use of the nondeterministic function
; MIS-ORDERED-COMMUTATIVE-ARGS in the memoization of an ACL2 function
; of two arguments that has been proven commutative is justified by
; the fact that the memoized function will return, modulo EQUAL, the
; same result regardless of what MIS-ORDERED-COMMUTATIVE-ARGS returns,
; and hence the nondeterminism cannot be detected by the ACL2 logic.

; WATCH-IFS forces INLINE.

  (when watch-ifs (setq inline t))

  (when (equal condition *nil*)
    (setq condition nil))

  (maybe-untrace! fn) ; See the comment about Memoization in trace$-def.
  (with-warnings-suppressed

; Big old bunch of error checking...


   (unless *memoize-init-done*
     (error "Memoize-fn:  *MEMOIZE-INIT-DONE* is still nil."))

   (unless (symbolp fn)
     (error "Memoize-fn: ~a is not a symbol." fn))

   (unless (or (fboundp fn) (not (eq cl-defun :default)))
     (error "Memoize-fn: ~s is not fboundp." fn))

   (when (or (macro-function fn)
             (special-operator-p fn)
             (compiler-macro-function fn))
     (error "Memoize-fn: ~s is a macro or a special operator or has ~
            a compiler macro." fn))

   (when (gethash fn *never-profile-ht*)
     (error "Memoize-fn: ~s is in *NEVER-PROFILE-HT*"
            fn))

   (when (memoizedp-raw fn)
     (format t "~%; Memoize-fn: ** Warning: ~s is currently memoized. ~%; So ~
                first we unmemoize it and then memoize it again."
             fn)
     (unmemoize-fn fn))

   (when (member fn (eval '(trace)))
     (format t "~%; Memoize-fn:  Untracing ~s before memoizing it." fn)
     (eval `(untrace ,fn)))

; TRACE, UNTRACE, OLD-TRACE, and OLD-UNTRACE are macros that get
; redefined sometimes.  So we use EVAL in calling them.

   #+Clozure
   (when (ccl::%advised-p fn)
     (error "~%; Memoize-fn: Please unadvise ~s before calling memoize-fn on ~
             it." fn))

   (when (and (fboundp 'old-trace)
              (member fn (eval '(old-trace))))
     (format t "~%; Memoize-fn:  Old-untracing ~s before memoizing it." fn)
     (eval `(old-untrace ,fn)))

   (when (eq fn 'return-last)
     (error "Memoize-fn: RETURN-LAST may not be memoized."))

   (when (getprop fn 'constrainedp nil 'current-acl2-world wrld)
     (error "Memoize-fn: ~s is constrained; you may instead wish ~%~
            to memoize a caller or to memoize its attachment (see ~%~
            :DOC defattach)."
            fn))

   ;; Doesn't this get checked below?  See the lambda-list intersection thing
   #+Clozure
   (when (multiple-value-bind (req opt restp keys)
                              (ccl::function-args (symbol-function fn))
                              (or restp
                                  keys
                                  (not (integerp req))
                                  (not (eql opt 0))))
     (error "Memoize-fn: ~a has non-simple arguments." fn))


   (let*
       ((cl-defun
         ;; Magic code to try to look up the Common Lisp definition for this function.
         (if (eq cl-defun :default)
             (if inline
                 (cond

                  ((not (fboundp fn))
                   (error "MEMOIZE-FN: ** ~a is undefined."
                          fn))

                  ((cltl-def-from-name fn nil wrld))

                  ((function-lambda-expression
                    (symbol-function fn)))

                  (t
                   #+Clozure
                   (unless (and ccl::*save-source-locations*
                                ccl::*fasl-save-definitions*)
                     (format t "~&; Check the settings of ~
                                   CCL::*SAVE-SOURCE-LOCATIONS* ~
                                   and ~
                                   CCL::*FASL-SAVE-DEFINITIONS*."))
                   (error "MEMOIZE-FN: ** Cannot find a ~
                                      definition for ~a via ACL2 ~
                                      or ~
                                      FUNCTION-LAMBDA-EXPRESSION."
                          fn))) nil)
           cl-defun))

        (formals
         ;; Magic code to try to figure out what the formals of the function are.
         ;; For ACL2 functions this works via looking up the 'formals property
         ;; For raw Lips functions we may be able to extract the formals from the
         ;; cl-defun above, or we may generate a list (X1 ... XN) in some cases?
         (if (eq formals :default)
             (let ((fo (getprop fn 'formals t 'current-acl2-world wrld)))
               (if (eq fo t)
                   (if (consp cl-defun)
                       (cadr cl-defun)
                     (let ((n (number-of-arguments fn)))
                       (if n
                           (loop for i fixnum below n
                                 collect (ofni "X~a" i))
                         (error "Memoize-fn: can't determine the number of ~
                                 inputs and outputs of ~a.  To assert that ~a ~
                                 takes, say, 2 inputs and returns 1 output, ~
                                 do:~%~a.~%"
                                fn fn `(set-number-of-arguments-and-values ',fn 2 1)))))
                 fo))
           formals))

        (stobjs-in
         ;; Either the ACL2 stobjs-in property or (T T T T ...) for the number
         ;; of formals that we inferred the function has.
         (if (eq stobjs-in :default)
             (let ((s (getprop fn 'stobjs-in t 'current-acl2-world
                               wrld)))
               (if (eq s t) (make-list (len formals)) s))
           stobjs-in))

        (stobjs-out
         ;; Either the ACL2 stobjs-out property or (T T T T ...) for the number
         ;; of return values that we inferred the function has.
         (if (eq stobjs-out :default)
             (let ((s (getprop fn 'stobjs-out t 'current-acl2-world wrld)))
               (if (eq s t)
                   (let ((n (number-of-return-values fn)))
                     (cond (n (make-list n))
                           ((and (null condition)
                                 (null trace))
                            (list nil nil))
                           (t (error
                               "Memoize-fn: cannot determine the ~
                               number of return values of ~a.~%~
                               You may put a cons of ~
                               two numbers in the hash-table~%~
                               *NUMBER-OF-ARGUMENTS-AND-VALUES-HT* ~
                               under ~a. ~%For example, do (setf ~
                               (gethash '~a ~
                               *NUMBER-OF-ARGUMENTS-AND-VALUES-HT*) ~
                               '(~a . 1))"
                               fn fn fn (len stobjs-in)))))
                 s))
           stobjs-out)))

     ;; Not sure why this check is necessary or useful
     (unless (and (symbol-listp formals)
                  (no-duplicatesp formals)
                  (loop for x in formals never (constantp x)))
       (error "Memoize-fn: FORMALS, ~a, must be a true list of ~
              distinct, nonconstant symbols." formals))

     (when (intersection lambda-list-keywords formals)
       (error "Memoize-fn: FORMALS, ~a, may not intersect ~
              LAMBDA-LIST-KEYWORDS." formals))

     ;; Don't memoize functions involving state.  Fair enough.
     ;; Can you memoize functions with other stobjs??
     (when (and condition (or (member 'state stobjs-in)
                              (member 'state stobjs-out)))
       (error "Memoize-fn:  ~s uses STATE." fn))


     (let*
         ((fnn (symbol-to-fixnum-create fn))
          (2mfnn (* *2max-memoize-fns* fnn))

          (*acl2-unwind-protect-stack*
           (or *acl2-unwind-protect-stack*
               (cons nil *acl2-unwind-protect-stack*)))

          (old-fn (if (fboundp fn) (symbol-function fn)))

          (body (if (or inline (null old-fn))
                    (car (last cl-defun))
                  `(funcall ,old-fn ,@formals)))


          (body-name (make-symbol "BODY-NAME"))
          (body-call (list body-name))

          (condition-body
           (cond ((booleanp condition) condition)
                 ((symbolp condition)
                  ;; Bizarre thing where the condition can be just the name of an ACL2 function,
                  ;; see the documentation above
                  (car (last (cltl-def-from-name condition nil wrld))))
                 (t condition)))

          (dcls (dcls (cdddr (butlast cl-defun))))
          (start-time (let ((v (hons-gentemp
                                (suffix "START-TIME-" fn))))
                        (eval `(prog1 (defg ,v -1)
                                 (declaim (type integer ,v))))))
          (tablename
           ;; Submits the defg form and returns the crazy name that gets generated.
           (eval `(defg
                    ,(hons-gentemp (suffix "MEMOIZE-HT-FOR-" fn))
                    nil)))
          (ponstablename
           ;; Submits the defg form and returns the crazy name that gets generated.
           (eval `(defg
                    ,(hons-gentemp (suffix "PONS-HT-FOR-" fn))
                    nil)))

          (localtablename (make-symbol "TABLENAME"))
          (localponstablename (make-symbol "PONSTABLENAME"))

          ;; When these user-level stobjs change the memo table will need to be cleared, I guess...
          (sts (loop for x in (union stobjs-in stobjs-out)
                     when x collect (st-lst x)))

          ;; Number of arguments.  Specials only matter for common lisp functions, see the notes above in memoize-fn.
          ;; Basically if the function reads from specials we want to count them as args.
          (nra (+ (len formals) (len specials)))

          def
          success)
       (let*
           ((mf-trace-exit
             ;; Ignore this, just some kind of tracing...
             (and trace `((mf-trace-exit ',fn ,(length stobjs-out)
                                         ,*mf-ans*))))
            (mf-record-mht
             ;; performance counting, see memoize-call-array
             `((safe-incf (aref ,*mf-ma* ,2mfnn) 1 ,fn)))
            (mf-record-hit
             ;; performance counting, see memoize-call-array
             (and condition-body
                  `((safe-incf (aref ,*mf-ma* ,(+ 2mfnn *ma-hits-index*)) 1 ,fn))))
            (lookup-marker (cons :lookup fn))



            (body3
             ;; Main part of the new function definition...

             `(let (,*mf-ans* ,*mf-args* ,*mf-ans-p*)
                (declare (ignorable ,*mf-ans* ,*mf-args* ,*mf-ans-p*))

                (profiler-cond
                 ((not ,condition-body)
                  ,@mf-record-hit ; sort of a hit
                  ,(if (not trace)
                       body-call
                     (if (cdr stobjs-out)
                         `(progn
                            (setq ,*mf-ans*
                                  (multiple-value-list ,body-call))
                            ,@mf-trace-exit
                            (values-list ,*mf-ans*))
                       `(progn (setq ,*mf-ans* ,body-call)
                               ,@mf-trace-exit
                               ,*mf-ans*))))


                 ,@(and
                    condition-body
                    `((t

                       ;; reinitialize tables if they don't exist...
                       (profiler-when
                        (null ,tablename)
                        ,@mf-record-mht
                        (setq ,tablename (make-initial-memoize-hash-table ',fn ,memo-table-init-size))

                        ,@(if (> nra 1) ; number of arguments
                              `((setq ,ponstablename
                                      (make-initial-memoize-pons-table ',fn ,memo-table-init-size)))))


                       ;; To avoid a remotely possible parallelism gethash error.  (jared: what?!?)
                       ,@(if (> nra 1)
                             `((setq ,localponstablename
                                     (profiler-or ,ponstablename
                                                  ;; BOZO should this be a make-initial-memoize-pons-table?
                                                  (mht)))))


                       ;; Generate the pons key... if there's just one arg, pist* just returns the arg and
                       ;; doesn't do any ponsing.

                       #+parallel ,@(if (> nra 1) `((ccl::lock-hash-table ,localponstablename)))
                       (setq ,*mf-args* (pist* ,localponstablename ,@formals ,@specials))
                       #+parallel ,@(if (> nra 1) `((ccl::unlock-hash-table ,localponstablename)))


                       ;; dunno what this is for... maybe we're binding a localtablename variable to avoid
                       ;; doing special lookups or some such?

                       (setq ,localtablename
                             ;; BOZO should this be a make-initial-memoize-hash-table?
                             (profiler-or ,tablename (mht)))


                       ;; this is the lookup of the memoized result.

                       (multiple-value-setq
                        (,*mf-ans* ,*mf-ans-p*)
                        ,(let ((gethash-form
                                `(gethash ,*mf-args* ,localtablename)))
                           (cond (aokp `(profiler-cond
                                         (*aokp* ,gethash-form)
                                         (t (mv nil nil))))
                                 (t gethash-form))))



                       (profiler-cond
                        (,*mf-ans-p*

                         ;; Memoized lookup succeeds.  Do profiling things, return answer...

                         ,@(when aokp `((update-attached-fn-called ',lookup-marker)))
                         ,@(if trace `((oftr "~% ~s remembered." ',fn)))
                         ,@mf-record-hit
                         ,@(cond ((null (cdr stobjs-out))
                                  `(,@mf-trace-exit ,*mf-ans*))
                                 (t
                                  ;; No idea what this is doing...
                                  (let ((len-1 (1- (length stobjs-out))))
                                    `(,@(and trace
                                             `(progn
                                                (let* ((,*mf-ans* (append (take ,len-1 ,*mf-ans*)
                                                                          (list (nthcdr ,len-1 ,*mf-ans*)))))
                                                  ,@mf-trace-exit)))
                                      ,(cons
                                        'mv
                                        (nconc (loop for i fixnum below len-1 collect `(pop ,*mf-ans*))
                                               (list *mf-ans*))))))))


                        (t

                         ;; Memoized lookup failed.  Need to run the function and get its results...

                         ,(let* ((vars
                                  ;; Make variables (O0 O1 ... 0N) for the outputs?  Don't really understand what stobjs-out is
                                  ;; for here...
                                  (loop for i fixnum below (if (cdr stobjs-out) (length stobjs-out) 1) collect (ofni "O~a" i)))

                                 (prog1-fn (if (cdr stobjs-out) 'multiple-value-prog1 'prog1))
                                 (mf-trace-exit+
                                  (and mf-trace-exit
                                       `((let ((,*mf-ans* ,(if stobjs-out `(list* ,@vars) (car vars))))
                                           ,@mf-trace-exit)))))

                            `(let (,*attached-fn-temp*)
                               (mv?-let
                                ,vars
                                (let (*attached-fn-called*)
                                  ;; This is where the actual function is being run.  The 01...0N vars are being bound to
                                  ;; the results...
                                  (,prog1-fn
                                   ,body-call
                                   (setq ,*attached-fn-temp* *attached-fn-called*)))
                                (progn
                                  (cond
                                   ,@(and (not aokp)
                                          `((,*attached-fn-temp*
                                             (memoize-use-attachment-warning ',fn ,*attached-fn-temp*))))
                                   (t
                                    ;; Actually install the results
                                    (setf (gethash ,*mf-args* ,localtablename)
                                          (list* ,@vars))))
                                  (update-attached-fn-called ,*attached-fn-temp*)
                                  ,@mf-trace-exit+
                                  (mv? ,@vars)))))))))))))


            (body2
             ;; Bunch of extra profiling stuff wrapped around body3.

             `(let ((,*mf-old-caller* *caller*)
                    (,*mf-start-bytes* (heap-bytes-allocated)))
                (declare (type fixnum ,*mf-old-caller* ,*mf-start-bytes*))
                (unwind-protect
                    (progn (setq ,start-time (acl2h-ticks))
                           (setq *caller* ,2mfnn)
                           ,body3)
                  (safe-incf (aref ,*mf-ma* ,(+ *ma-bytes-index* 2mfnn))
                             (the mfixnum (- (heap-bytes-allocated) ,*mf-start-bytes*))
                             ,fn)
                  (safe-incf (aref ,*mf-ma* (the mfixnum (1+ ,*mf-count-loc*)))
                             (mod (the integer (- (acl2h-ticks) ,start-time))
                                  most-positive-mfixnum)
                             ,fn)
                  ,@(and forget
                         `((setq ,tablename nil)
                           (setq ,ponstablename nil)))
                  (setq ,start-time -1)
                  (setq *caller* ,*mf-old-caller*)))))

         (setq def
               `(defun ,fn ,formals ,@dcls
                  ,@(if trace
                        (if (member trace '(notinline inline))
                            `((declare (,trace ,fn)))
                          `((declare (notinline ,fn)))))
                  (declare (ignorable ,@formals ,@specials))
                  ,@(and commutative
                         `((cond ((mis-ordered-commutative-args
                                   ,(car formals)
                                   ,(cadr formals))
                                  (rotatef ,(car formals)
                                           ,(cadr formals))))))
                  ,@(and trace
                         `((oftr "~%(> ~s (" ',fn)
                           ,@(loop for v in (append formals specials)
                                   append
                                   `((oftr "~& ~s = " ',v)
                                     (prine ,v *trace-output*)))
                           (oftr "~& )")))
                  (let* ((,*mf-count-loc* (the fixnum (+ *caller* (* 2 ,fnn))))
                         (,*mf-ma* *memoize-call-array*)
                         ,localtablename ,localponstablename)
                    (declare (type fixnum ,*mf-count-loc*)
                             (ignorable ,*mf-count-loc* ,*mf-ma*
                                        ,localponstablename
                                        ,localtablename)
                             (type (simple-array mfixnum (*))
                                   ,*mf-ma*))
                    (safe-incf (aref ,*mf-ma* ,*mf-count-loc*) 1 ,fn)
                    (flet ((,body-name () ,body))
                          (profiler-if (eql -1 ,start-time)
                                       ,body2
                                       ,body3))))))
       ;; why the hell is this here
       (setf (gethash fn *number-of-arguments-and-values-ht*)
             (cons (length stobjs-in) (length stobjs-out)))
       (unwind-protect
           (progn
             (let ((ma *memoize-call-array*))
               (declare (type (simple-array mfixnum (*)) ma))
               (loop for i fixnum from 2mfnn
                     below (the fixnum (+ 2mfnn *2max-memoize-fns*))
                     unless (eql (aref ma i) 0)
                     do (setf (aref ma i) 0)))
             (memoize-eval-compile def watch-ifs)
             (setf (gethash fn *memoize-info-ht*)
                   (make memoize-info-ht-entry
                         :fn fn
                         :ext-anc-attachments
                         (and aokp (extended-ancestors fn wrld))
                         :tablename tablename
                         :ponstablename ponstablename
                         :old-fn old-fn
                         :memoized-fn (symbol-function fn)
                         :condition condition
                         :inline inline
                         :num fnn
                         :sts sts
                         :trace trace
                         :start-time start-time
                         :cl-defun cl-defun
                         :formals formals
                         :commutative commutative
                         :specials specials
                         :stobjs-in stobjs-in
                         :stobjs-out stobjs-out
                         :watch-ifs         watch-ifs
                         :forget            forget
                         :memo-table-init-size memo-table-init-size))
             (setf (gethash fnn *memoize-info-ht*) fn)
             (and condition (loop for s in sts do
                                  (push tablename
                                        (symbol-value s))))
             (setq success t))
         (unless success
           (setf (symbol-function fn) old-fn)
           (remhash fn *memoize-info-ht*)
           (remhash fnn *memoize-info-ht*)
           (maphash (lambda (k v)
                      (when (eq fn (cadr v))
                        (remhash k *form-ht*)))
                    *form-ht*)
           (and condition
                (loop for s in sts
                      when (eq tablename (car (symbol-value s)))
                      do (pop (symbol-value s))))
           ;; BOZO should this be an error?
           (format t "~&; Memoize-fn:  Failed to memoize ~s." fn)
           (setq fn nil))))))

  fn)




(defn1 unmemoize-fn (fn)
  (maybe-untrace! fn) ; See the comment about Memoization in trace$-def.
  (let* ((ma *memoize-call-array*)
         (l (memoizedp-raw fn)))
    (declare (type (simple-array mfixnum (*)) ma))
    (unless l (error "Unmemoize-fn: ~s is not memoized." fn))
    (let* ((num       (access memoize-info-ht-entry l :num))
           (tablename (and l (access memoize-info-ht-entry l :tablename)))
           (n2        (* num *2max-memoize-fns*))
           (w         (access memoize-info-ht-entry l :watch-ifs)))

      #+Clozure
      (when w
        (maphash (lambda (k v)
                   (when (eq fn (cadr v))
                     (remhash k *form-ht*)))
                 *form-ht*))

; Note: condition is a first-class ACL2 function, not to be messed
; with here.

      (let (#+Clozure (ccl:*warn-if-redefine-kernel* nil))
        (let ((old-fn (access memoize-info-ht-entry l :old-fn)))
          (if old-fn
              (setf (symbol-function fn) old-fn)
            (fmakunbound fn))))
      (loop for i fixnum from n2
            below (+ n2 *2max-memoize-fns*)
            unless (eql (aref ma i) 0)
            do (setf (aref ma i) 0))
      (remhash fn *memoize-info-ht*)
      (remhash num *memoize-info-ht*)
      (setf (symbol-value tablename) nil)
      (setf (symbol-value (access memoize-info-ht-entry l :ponstablename)) nil)
      (loop for s in (access memoize-info-ht-entry l :sts) do
            (when (boundp s)
              (setf (symbol-value s)
                    (remove tablename (symbol-value s)))))))
  fn)

(defn1 maybe-unmemoize (fn)

; We rely on the normal undoing mechanism (for :ubt etc.) to take care of
; unmemoization.  However, as a courtesy to users who memoize using raw Lisp,
; we provide and call this utility for unmemoizing functions that are not known
; to ACL2 (via the memoize-table) as being memoized.

  (when (and (memoizedp-raw fn)
             (not (cdr (assoc-eq fn (table-alist
                                     'memoize-table (w *the-live-state*))))))
    (unmemoize-fn fn)))



(defn1 unmemoize-all ()

  "(UNMEMOIZE-ALL) unmemoizes all currently memoized functions,
  including all profiled functions."

  ;; Note: can't use maphash because it's undefined to change/remove entries
  ;; except the one you're traversing, and unmemoize-fn has to remove both the
  ;; function and its num.

  (loop for x in (memoized-functions) do (unmemoize-fn x)))

(defn1 memoize-info (k)

  "(MEMOIZE-INFO k) returns the settings of the various arguments to
  MEMOIZE-FN and the settings of the special variables that influence
  MEMOIZE-FN during the memoization of K."

  (let ((v (gethash k *memoize-info-ht*)))
    (and v
         (list (list (access memoize-info-ht-entry v :fn)
                     :condition   (access memoize-info-ht-entry v :condition)
                     :inline      (access memoize-info-ht-entry v :inline)
                     :trace       (access memoize-info-ht-entry v :trace)
                     :cl-defun    (access memoize-info-ht-entry v :cl-defun)
                     :formals     (access memoize-info-ht-entry v :formals)
                     :stobjs-in   (access memoize-info-ht-entry v :stobjs-in)
                     :specials    (access memoize-info-ht-entry v :specials)
                     :commutative (access memoize-info-ht-entry v :commutative)
                     :stobjs-out  (access memoize-info-ht-entry v :stobjs-out)
                     :watch-ifs   (access memoize-info-ht-entry v :watch-ifs)
                     :forget      (access memoize-info-ht-entry v :forget)
                     :memo-table-init-size
                     (access memoize-info-ht-entry v :memo-table-init-size))))))

(defn1 rememoize-all ()
  (let (l)
    (maphash
     (lambda (k v)
       (declare (ignore v))
       (when (symbolp k) (push (memoize-info k) l)))
     *memoize-info-ht*)
    (loop for x in l do (unmemoize-fn (caar x)))
    (gc$)
    (clrhash *form-ht*)
    (setq *max-symbol-to-fixnum* *ma-initial-max-symbol-to-fixnum*)
    (loop for x in l do
          (apply 'memoize-fn (car x)))))




; MEMOIZE-ON AND MEMOIZE-OFF

(defconstant *mo-f* (make-symbol "F"))
(defconstant *mo-o* (make-symbol "O"))
(defconstant *mo-h* (make-symbol "H"))

(defn1 not-memoized-error (f)
  (error "NOT-MEMOIZED-ERROR:  ~s is not memoized." f))

(defmacro memoize-on-raw (fn x)
  `(let* ((,*mo-f* ,fn)
          (,*mo-h* (memoizedp-raw ,*mo-f*)))
     (unless ,*mo-h*
       (not-memoized-error ,*mo-f*))
     (let ((,*mo-o* (symbol-function ,*mo-f*)))
       (unwind-protect
           (progn (setf (symbol-function ,*mo-f*)
                        (access memoize-info-ht-entry ,*mo-h* :memoized-fn))
                  ,x)
         (setf (symbol-function ,*mo-f*) ,*mo-o*)))))

(defmacro memoize-off-raw (fn x)
  `(let* ((,*mo-f* ,fn)
          (,*mo-h* (memoizedp-raw ,*mo-f*)))
     (unless ,*mo-h*
       (not-memoized-error ,*mo-f*))
     (let ((,*mo-o* (symbol-function ,*mo-f*)))
       (unwind-protect
           (progn (setf (symbol-function ,*mo-f*)
                        (access memoize-info-ht-entry ,*mo-h* :old-fn))
                  ,x)
         (setf (symbol-function ,*mo-f*) ,*mo-o*)))))


(defn global-restore-memoize ()
  (maphash (lambda (k l)
             (when (symbolp k)
               (setf (symbol-function k)
                     (access memoize-info-ht-entry l :memoized-fn))))
           *memoize-info-ht*))


; STATISTICS GATHERING AND PRINTING ROUTINES

(defg *memoize-summary-limit* 20

  "*MEMOIZE-SUMMARY-LIMIT* is a raw Lisp variable whose value is the
  maximum number of functions upon which MEMOIZE-SUMMARY reports.  A
  NIL value means report on all.")

(defg *shorten-ht* (mht :test 'eql))

(defn shorten (x n)
  (cond ((and (stringp x) (<= (length x) n))
         x)
        (t
         (let ((x
                ;; Jared -- ugh, this was using maybe-str-hash directly.  It
                ;; looks like X is supposed to be a string or symbol.  Here's
                ;; a dumb approximation of the previous behavior:
                (if (stringp x)
                    (hons-copy x)
                  x)))
           (cond ((gethash x *shorten-ht*))
                 (t (let ((*print-pretty* nil)
                          (*print-length* 10)
                          (*print-level* 5)
                          (*print-lines* 2))
                      (let ((str
                             (with-output-to-string
                               (s)
                               (cond ((stringp x) (princ x s))
                                     (t (prin1 x s))))))
                        (setf (gethash x *shorten-ht*)
                              (cond ((<= (length str) n) str)
                                    ((setf (gethash x *shorten-ht*)
                                           (concatenate
                                            'string
                                            (subseq str 0 (max 0 n))
                                            "...")))))))))))))


(defg *print-alist-width* 45)

(defn1 print-alist (alist separation)
  (check-type separation (integer 0))
  (setq alist
        (loop for x in alist collect
              (progn
                (check-type x
                            (cons (or string symbol)
                                  (cons (or string (integer 0))
                                        null)))
                (list (shorten (car x) *print-alist-width*)
                      (if (integerp (cadr x))
                          (ofnum (cadr x))
                        (cadr x))))))
  (let* ((max1 (loop for x in alist maximize (length (car x))))
         (max2 (loop for x in alist maximize (length (cadr x))))
         (width (max (or *print-right-margin* 70)
                     (+ separation max1 max2))))
    (loop for x in alist do
          (fresh-line)
          (princ (car x))
          (loop for i
                below (- width (+ (length (car x))
                                  (length (cadr x))))
                do (write-char #\Space))
          (princ (cadr x))))
  nil)


; VERY-UNSAFE-INCF

(defmacro very-unsafe-incf (x inc &rest r)

; returns NIL !

  (declare (ignore r))

  (unless (symbolp x)
    ;; Compile-time sanity check
    (error "very-unsafe-incf should only be used on symbols, not ~a" x))

  `(locally (declare (type mfixnum ,x))
            (setq ,x (the mfixnum (+ ,x (the mfixnum ,inc))))
            nil))



(defn1 pons-summary ()
  (our-syntax-nice
   (let ((sssub 0) (nponses 0) (nsubs 0) (nponstab 0))
     (declare (type mfixnum sssub nponses nsubs))
   (format t "(defun pons-summary~%")
   (maphash
    (lambda (k v)
      (cond ((symbolp k)
             (let ((tab (symbol-value (access memoize-info-ht-entry v
                                              :ponstablename))))
               (when tab
                 (very-unsafe-incf nponstab 1 pons-summary)
                 (maphash
                  (lambda (k v) (declare (ignore k))
                    (cond
                     ((not (listp v))
                      (very-unsafe-incf sssub (hash-table-size v)
                                        pons-summary)
                      (very-unsafe-incf nponses (hash-table-count v)
                                        pons-summary)
                      (very-unsafe-incf nsubs 1 pons-summary))
                     (t (very-unsafe-incf nponses (length v)
                                          pons-summary))))
                  tab))))))
    *memoize-info-ht*)
   (print-alist
    `((" Number of pons tables" ,(ofnum nponstab))
      (" Number of pons sub tables" ,(ofnum nsubs))
      (" Sum of pons sub table sizes" ,(ofnum sssub))
      (" Number of ponses" ,(ofnum nponses)))
    5)
   (format t ")")
   nil)))

(defun memoized-values (&optional (fn (memoized-functions)))

  "(MEMOIZED-VALUES fn) prints all the currently memoized values for FN."

  (cond ((listp fn) (mapc #'memoized-values fn))
        ((not (memoizedp-raw fn))
         (format t "~%; Memoized-values:  ~s is not memoized." fn))
        (t (let ((tb (symbol-value
                      (access memoize-info-ht-entry
                              (gethash fn *memoize-info-ht*)
                              :tablename))))
             (cond ((and tb (not (eql 0 (hash-table-count tb))))
                    (format t "~%; Memoized values for ~s." fn)
                    (maphash (lambda (key v)
                               (format t "~%~s~%=>~%~s" key v))
                             tb))))))
  nil)






(defn1 number-of-memoized-entries (x)

  "For a memoized function X, (NUMBER-OF-MEMOIZED-ENTRIES x) is the
  number of entries currently stored for X."

  (let ((h (gethash x *memoize-info-ht*)))
    (unless h (error "~a is not memoized." x))
    (let* ((sym (access memoize-info-ht-entry
                        h
                        :tablename))
           (val (symbol-value sym)))
      (if (hash-table-p val)
          (hash-table-count val)
        0))))

(defn1 number-of-mht-calls (x)

  "For a memoized function X, (NUMBER-OF-MHT-CALLS x) is the number
  of times that the memoize hash-table for X was created."

  (setq x (coerce-index x))
  (aref *memoize-call-array*
        (the mfixnum (+ *ma-mht-index*
                       (the mfixnum
                         (* *2max-memoize-fns*
                            (the mfixnum x)))))))

(defn1 time-for-non-hits/call (x)
  (setq x (coerce-index x))
  (let ((n (- (number-of-calls x) (number-of-hits x))))
    (if (zerop n) 0 (/ (total-time x) n))))

(defn1 time/call (x)
  (setq x (coerce-index x))
  (let ((n (number-of-calls x)))
    (if (zerop n) 0 (/ (total-time x) n))))

(defn1 hits/calls (x)
  (setq x (coerce-index x))
  (let ((n (number-of-calls x)))
    (if (zerop n) 0 (/ (number-of-hits x) (float n)))))

(defn1 bytes-allocated/call (x)
  (setq x (coerce-index x))
  (let ((n (number-of-calls x)))
    (if (eql n 0)
        0
      (/ (bytes-allocated x) n))))










(defn clear-one-memo-and-pons-hash (info)

; INFO is a memoize-info-ht-entry.  Throw away its memoization table and its
; pons table.

; It is debatable whether one should use the CLRHASH approach or the set-to-NIL
; approach in CLEAR-ONE-MEMO-AND-PONS-HASH.  The CLRHASH approach, in addition
; to reducing the number of MAKE-HASH-TABLE calls necessary, has the effect of
; immediately clearing a hash-table even if some other function is holding on
; to it, so more garbage may get garbage collected sooner than otherwise.  The
; set-to-NIL approach has the advantage of costing very few instructions and
; very little paging.

; [Jared]: I don't really understand the comment above; how could another
; function be holding onto a memoize or pons table?  Maybe the answer is that
; if multiple threads are executing a memoized function and we try to clear its
; table, there might be some other thread that happens to have locally bound
; the tables and hence they are still reachable?

  (let* ((fn (access memoize-info-ht-entry info :fn))
         (mt (symbol-value (access memoize-info-ht-entry info :tablename)))
         (pt (symbol-value (access memoize-info-ht-entry info :ponstablename)))
         (mt-count (and mt (hash-table-count mt)))
         (pt-count (and pt (hash-table-count pt))))
    (when mt
      (setf (symbol-value (access memoize-info-ht-entry info :tablename)) nil))
    (when pt
      (setf (symbol-value (access memoize-info-ht-entry info :ponstablename)) nil))
    (when (or mt-count pt-count)
      (update-memo-max-sizes fn (or pt-count 1) (or mt-count 1)))
    nil))

(defn1 clear-memoize-table (fn)
  ;; User-level.  See memoize.lisp.
  (when (symbolp fn)
    (let ((info (gethash fn *memoize-info-ht*)))
      (when info
        (clear-one-memo-and-pons-hash info)))))

(defn1 clear-memoize-tables ()
  ;; User-level.  See memoize.lisp.
  (maphash (lambda (key info)
             (when (symbolp key)
               (clear-one-memo-and-pons-hash info)))
           *memoize-info-ht*))



; MEMOIZE INIT

(defn1 memoize-init ()

  (when *memoize-init-done*
    ;; Already done.
    (return-from memoize-init nil))

  (initialize-never-profile-ht)
  (initialize-profile-reject-ht)

  (unless (eql *caller* (the fixnum
                             (* *ma-initial-max-symbol-to-fixnum*
                                *2max-memoize-fns*)))
    (error "memoize-init:  A memoized function is running."))
  (let (success)
    (unwind-protect
        (progn
          #+Clozure (setup-smashed-if)
          (setq *memoize-info-ht* (mht))
          (setf (gethash *ma-initial-max-symbol-to-fixnum* *memoize-info-ht*)
                "outside-caller")
          (setq *max-symbol-to-fixnum* *ma-initial-max-symbol-to-fixnum*)
          (setq *2max-memoize-fns* (* 2 *initial-max-memoize-fns*))
          (sync-memoize-call-array)
          (clrhash *form-ht*)
          (setq success t))
      (if success (setq *memoize-init-done* t)
        ;; BOZO should this be an error?
        ;; BOZO what are we protecting against?
        (format t "~%; memoize init: Error **"))))
  nil)








(defg *hons-init-hook*
  '(progn

     (set-gag-mode t)

     "If the ACL2 global PRINT-CIRCLE is not t,
      then .cert files may be huge."

     (f-put-global 'print-circle t *the-live-state*)
     (f-put-global 'print-circle-files t *the-live-state*)

     "Tell the user how to shut off asides."

     (hons-init-hook-set '*ofv-note-printed* nil)

     (when (boundp '*help*)
       (ofv "Type *HELP* outside the ACL2 loop for some ~
             documentation tips."))

     (hons-init-hook-set '*print-pretty* t)

     (when (not (memoizedp-raw 'bad-lisp-objectp))
       (memoize-fn 'bad-lisp-objectp :forget t))

     (when (not (memoizedp-raw 'worse-than-builtin))
       ;; If this memoization is removed, update comments in worse-than-builtin.
       (memoize-fn 'worse-than-builtin
                   :condition ; Sol Swords suggestion
                   '(and (nvariablep term1)
                         (not (fquotep term1))
                         (nvariablep term2)
                         (not (fquotep term2)))))

     (when (not (memoizedp-raw 'fchecksum-obj))
       ;; If this memoization is removed, update comments in fchecksum-obj
       (memoize-fn 'fchecksum-obj :forget t))

     (when (not (memoizedp-raw 'expansion-alist-pkg-names-memoize))
       ;; If this memoization is removed, update comments in expansion-alist-pkg-names
       (memoize-fn 'expansion-alist-pkg-names-memoize :forget t))

     (when (not (memoizedp-raw 'physical-memory))
       ;; [Jared]: merged in from e4/memoize-raw.lsp
       (memoize-fn 'physical-memory :inline nil))

     #+Clozure
     (progn

       (hons-init-hook-set 'ccl::*long-site-name*
                           (ignore-errors (ccl::getenv "HOSTNAME")))

       (hons-init-hook-set 'ccl::*short-site-name*
         (subseq ccl::*long-site-name*
                 0 (search "." ccl::*long-site-name*)))

       (hons-init-hook-set '*print-right-margin*
        (ignore-errors (read-from-string (ccl::getenv "COLUMNS"))))

       "Permit FUNCTION-LAMBDA-EXPRESSION to return the form
        used in the DEFUN of a function symbol."

       (hons-init-hook-set 'ccl::*save-definitions* t)
       (hons-init-hook-set 'ccl::*save-source-locations* t)
       (hons-init-hook-set 'ccl::*fasl-save-definitions* t)
       (hons-init-hook-set 'ccl::*record-source-file* t)

       "Allow control-d to exit from CCL."

       (hons-init-hook-set 'ccl::*quit-on-eof* t)

       ;; With *print-array* turned on, we end up sometimes seeing the SBITS
       ;; array in backtraces, etc, which can effectively kill your session.
       (setq *print-array* nil)

;   This might be a good idea, but we do not understand about
;   ccl::advise being called twice, e.g., via *hons-init-hook*.
;
;    "Before an image is saved or we otherwise quit, we kill any WATCH
;     process and delete any /tmp file created by the csh/sh facility."
;
;     (ccl::advise ccl::quit
;                 (progn (watch-kill) (csh-stop) (sh-stop))
;                 :when :before)

       )

     (acl2h-initialize-gc)


     )

  "*HONS-INIT-HOOK* is EVALed by HONS-INIT.  *HONS-INIT-HOOK* may be
  EVALed several times because HONS-INIT may be called several times.
  *HONS-INIT-HOOK* is supposed to set some options that a user might
  want to set in a ccl-init.lisp or an acl2-init.lsp file but might
  not know to set.")

(defn hons-init-hook-set (var val)
  (unless (symbolp var)
    (error "HONS-INIT-HOOK-SET works for symbols, not ~a." var))
  (when (not (equal val (symbol-value var)))
    (ofv "*hons-init-hook*:  Setting ~a to ~a." var val)
    (setf (symbol-value var) val)))


(defn1 hons-init ()

; We assume ACL2-DEFAULT-RESTART will be called at least once.  We
; suspect it will be called whenever an ACL2H CCL saved image is
; started up.  We know that ACL2-DEFAULT-RESTART calls HONS-INIT.  We
; are unsure how many times ACL2-DEFAULT-RESTART might be called, and
; so we code HONS-INIT so that it may be called multiple times.

  (in-package "ACL2")
  (hons-readtable-init)
  (acl2h-ticks-init)
  (memoize-init)
  (eval *hons-init-hook*))


;;; SHORTER, OLDER NAMES

; Note: memsum is defined in memoize.lisp.

(defun memstat (&rest r)
  (apply #'memoized-values r))

(defmacro memo-on (&rest r)
  `(memoize-on ,@r))

(defmacro memo-off (&rest r)
  `(memoize-off ,@r))

(defun clear-memo-tables (&rest r)
;  (setq *pons-call-counter* 0)
;  (setq *pons-misses-counter* 0)
  (apply #'clear-memoize-tables r))








(defun update-memo-entry-for-attachments (fns entry wrld)

; We return (mv changed-p new-entry), where if changed-p is not t or nil then
; it is a function symbol whose attachment has changed, which requires clearing
; of the corresponding memo table.

  (let* ((ext-anc-attachments
          (access memoize-info-ht-entry entry :ext-anc-attachments))
         (valid-p
          (if (eq fns :clear)
              :clear
            (or (null ext-anc-attachments)
                (ext-anc-attachments-valid-p fns ext-anc-attachments wrld t)))))
    (cond ((eq valid-p t) (mv nil entry))
          (t
           (mv (if (eq valid-p nil) t valid-p)
               (change memoize-info-ht-entry entry
                       :ext-anc-attachments
                       (extended-ancestors (access memoize-info-ht-entry entry
                                                   :fn)
                                           wrld)))))))

(defun update-memo-entries-for-attachments (fns wrld state)
  (let ((ctx 'top-level)
        (fns (if (eq fns :clear)
                 fns
               (strict-merge-sort-symbol-<
                (loop for fn in fns
                      collect (canonical-sibling fn wrld))))))
    (when (eq fns :clear)
      (observation ctx
                   "Memoization tables for functions memoized with :AOKP T ~
                    are being cleared."))
    (when fns ; optimization
      (maphash (lambda (k entry)
                 (when (symbolp k)
                   (mv-let (changedp new-entry)
                           (update-memo-entry-for-attachments fns entry wrld)
                           (when changedp
                             (when (not (or (eq changedp t)
                                            (eq fns :clear)))
                               (observation ctx
                                            "Memoization table for function ~x0 ~
                                           is being cleared because ~
                                           attachment to function ~x1 has ~
                                           changed."
                                            k changedp)
                               (clear-one-memo-and-pons-hash entry))
                             (setf (gethash k *memoize-info-ht*)
                                   new-entry)))))
               *memoize-info-ht*))))





; -----------------------------------------------------------------------------

(defun initialize-never-profile-ht ()

; [Jared]: Ugh. These kinds of big lists seem really bad.  There might be
; important reasons that some functions must never be memoized, for instance:
;
;   - It might not be legitimate for functions used in the memoize code itself
;     (e.g., +) to be memoized.  We may also want to make sure we never memoize
;     things like Common Lisp primitives.  I'm not very worried about things
;     like Lisp kernel code; for that you'd have to be in raw Lisp anyway.
;
;   - Certain functions may operate destructively, e.g., strip-cars is
;     implemented as (nreverse (reverse-strip-cars x nil)), so if we memoize
;     reverse-strip-cars we could get into trouble.  In fact this was a
;     soundness bug with ACL2(h) as of ACL2 4.2.  So, we need to be sure not to
;     memoize these.
;
; But there is probably no reason we can't memoize some of the other functions
; here, like string< and remove-duplicates.  Of course it's probably a bad idea
; to memoize these for performance reasons, but really the whole question of
; "how to memoize intelligently" should stay firmly beyond the scope of the
; memoize code.  In these cases, we should probably move the functions into the
; profile-reject-ht instead of making it outright illegal to memoize them.
;
; This list also has a lot of other functions that aren't even defined in ACL2
; and might not even be defined in STP anymore.  We should probably never put
; function names here that aren't defined for regular ACL2(h) users.

  (loop for x in
        '(bytes-used
          memoize-summary
          memoize-summary-after-compute-calls-and-times
          watch-dump
          #+rdtsc ccl::rdtsc
          *
          +
          -
          <
          <=
          =
          >
          >=
          abort
          adjoin
          adjust-array
          allocate-instance
          append
          apply
          apropos
          apropos-list
          aref
          arrayp
          assoc
          assoc-if
          assoc-if-not
          atan
          atom
          bit
          bit-and
          bit-andc1
          bit-andc2
          bit-eqv
          bit-ior
          bit-nand
          bit-nor
          bit-not
          bit-orc1
          bit-orc2
          bit-xor
          break
          butlast
          car
          cdr
          ceiling
          cerror
          change-class
          char-equal
          char-greaterp
          char-lessp
          char-not-equal
          char-not-greaterp
          char-not-lessp
          char/=
          char<
          char<=
          char=
          char>
          char>=
          clear-input
          clear-memoize-tables
          clear-output
          compile
          compile-file
          compile-file-pathname
          compiler-macro-function
          complex
          compute-restarts
          concatenate
          continue
          copy-pprint-dispatch
          copy-readtable
          copy-symbol
          count
          count-if
          count-if-not
          decode-universal-time
          delete
          delete-duplicates
          delete-if
          delete-if-not
          describe
          digit-char
          digit-char-p
          directory
          dribble
          ed
          encode-universal-time
          enough-namestring
          ensure-directories-exist
          ensure-generic-function
          eq
          eql
          error
          eval
          every
          export
          fboundp
          fceiling
          ffloor
          file-position
          fill
          find
          find-class
          find-if
          find-if-not
          find-method
          find-restart
          find-symbol
          finish-output
          fixnum-to-symbol
          float
          float-sign
          floor
          force-output
          format
          fresh-line
          fround
          ftruncate
          funcall
          gensym
          gentemp
          get
          get-dispatch-macro-character
          get-internal-real-time
          get-internal-run-time
          get-macro-character
          get-properties
          get-setf-expansion
          getf
          gethash
          if
          import
          initialize-instance
          intern
          intersection
          invalid-method-error
          invoke-restart
          last
          ld-fn
          len
          len1
          length
          lisp-implementation-type
          list
          list*
          listen
          load
          log
          macro-function
          macroexpand
          macroexpand-1
          make-array
          make-broadcast-stream
          make-concatenated-stream
          make-condition
          make-dispatch-macro-character
          make-hash-table
          make-instance
          make-list
          make-load-form
          make-load-form-saving-slots
          make-package
          make-pathname
          make-random-state
          make-sequence
          make-string
          make-string-input-stream
          make-string-output-stream
          map
          map-into
          mapc
          mapcan
          mapcar
          mapcon
          mapl
          maplist
          max
          member
          member-if
          member-if-not
          memoize-call-array-grow
          memoize-eval-compile
          memoize-fn
          merge
          merge-pathnames
          method-combination-error
          mf-1st-warnings
          mf-2nd-warnings
          mf-warnings
          mismatch
          muffle-warning
          nbutlast
          nconc
          nintersection
          no-applicable-method
          no-next-method
          not
          notany
          notevery
          nset-difference
          nset-exclusive-or
          nstring-capitalize
          nstring-downcase
          nstring-upcase
          nsublis
          nsubst
          nsubst-if
          nsubst-if-not
          nsubstitute
          nsubstitute-if
          nsubstitute-if-not
          null
          nunion
          open
          pairlis
          parse-integer
          parse-namestring
          pathname-device
          pathname-directory
          pathname-host
          pathname-name
          pathname-type
          peek-char
          position
          position-if
          position-if-not
          pprint
          pprint-dispatch
          pprint-fill
          pprint-indent
          pprint-linear
          pprint-newline
          pprint-tab
          pprint-tabular
          prin1
          princ
          princ-to-string
          print
          print-object
          profile-fn
          profile-acl2
          profile-all
          random
          rassoc
          rassoc-if
          rassoc-if-not
          read
          read-byte
          read-char
          read-char-no-hang
          read-delimited-list
          read-from-string
          read-line
          read-preserving-whitespace
          read-sequence
          reduce
          reinitialize-instance
          remove
          remove-duplicates
          remove-if
          remove-if-not
          rename-file
          rename-package
          replace
          require
          room
          round
          sbit
          search
          set-difference
          set-dispatch-macro-character
          set-exclusive-or
          set-macro-character
          set-pprint-dispatch
          set-syntax-from-char
          shadow
          shadowing-import
          shared-initialize
          signal
          signum
          slot-missing
          some
          sort
          stable-sort
          store-value
          string-capitalize
          string-downcase
          string-equal
          string-greaterp
          string-lessp
          string-not-equal
          string-not-greaterp
          string-not-lessp
          string-upcase
          string/=
          string<
          string<=
          string=
          string>
          string>=
          stringp
          sublis
          subseq
          subsetp
          subst
          subst-if
          subst-if-not
          substitute
          substitute-if
          substitute-if-not
          subtypep
          svref
          symbol-to-fixnum
          symbol-to-fixnum-create
          symbolp
          sync-memoize-call-array
          sync-watch-array
          terpri
          time-of-last-watch-update
          time-since-watch-start
          translate-logical-pathname
          translate-pathname
          tree-equal
          true-listp
          truncate
          typep
          unexport
          unintern
          union
          unread-char
          unuse-package
          update-instance-for-different-class
          update-instance-for-redefined-class
          upgraded-array-element-type
          upgraded-complex-part-type
          use-package
          use-value
          user-homedir-pathname
          values
          vector-push-extend
          warn
          watch-array-grow
          wild-pathname-p
          write
          write-byte
          write-char
          write-line
          write-sequence
          write-string
          write-to-string
          y-or-n-p
          yes-or-no-p)
        do (setf (gethash x *never-profile-ht*) t)))




