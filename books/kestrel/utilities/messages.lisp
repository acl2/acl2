; Messages
;
; Copyright (C) 2018-2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)
; Supporting author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(local (in-theory (disable (tau-system))))
(set-induction-depth-limit 0)

(local (include-book "kestrel/alists-light/acons" :dir :system))
(local (include-book "kestrel/alists-light/assoc-equal" :dir :system))
(local (include-book "kestrel/strings-light/char" :dir :system))
(local (include-book "kestrel/utilities/acl2-count" :dir :system))
(local (include-book "kestrel/utilities/msgp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::make-define-config
  :no-function t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc message-utilities
  :parents (kestrel-utilities)
  :short "Utilities for <see topic='@(url msgp)'>messages</see>.")

(defxdoc msg$
  :parents (msg message-utilities)
  :short "A variant of @('msg') which is easier to reason about."
  :long
  (xdoc::topstring
    (xdoc::p
      "@('msg$') is a macro which will rewrite to a call of @('msg$-logic').
       @('msg$-logic') is kept disabled and is known to produce a
       @('msgp'). For execution, @('msg$') expands to something which is
       inlined for efficiency.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maybe-msgp (x)
  :returns (yes/no booleanp)
  :parents (message-utilities)
  :short "Recognize @('nil') and messages."
  (or (msgp x)
      (null x))
  ///

  (defrule maybe-msgp-compound-recognizer
    (if (maybe-msgp x)
        (or (equal x nil)
            (stringp x)
            (and (consp x)
                 (true-listp x)))
      (and (not (equal x nil))
           (not (stringp x))))
    :rule-classes :compound-recognizer)

  (defrule maybe-msgp-when-msgp
    (implies (msgp x)
             (maybe-msgp x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist msg-listp (x)
  (msgp x)
  :parents (message-utilities)
  :short "Recognize true lists of messages."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define msg-fix ((msg msgp))
  :returns (msg$ msgp)
  (mbe :logic (if (msgp msg)
                  msg
                "")
       :exec (the (or string cons) msg))
  :inline t)

;; Subsumed by msg-fix-type-prescription
(in-theory (disable (:t msg-fix)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule msg-fix-type-prescription
  (or (stringp (msg-fix msg))
      (and (consp (msg-fix msg))
           (true-listp (msg-fix msg))))
  :rule-classes :type-prescription
  :enable msg-fix)

(defrule msg-fix-when-msgp
  (implies (msgp msg)
           (equal (msg-fix msg)
                  msg))
  :enable msg-fix)

(defruled msg-fix-when-not-msgp
  (implies (not (msgp msg))
           (equal (msg-fix msg)
                  ""))
  :enable msg-fix)

(defrule msg-fix-when-not-msgp-cheap
  (implies (not (msgp msg))
           (equal (msg-fix msg)
                  ""))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :by msg-fix-when-not-msgp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule stringp-of-car-of-msg-fix
  (equal (stringp (car (msg-fix msg)))
         (not (stringp (msg-fix msg))))
  :enable msg-fix)

(defrule character-alistp-of-cdr-of-msg-fix
  (character-alistp (cdr (msg-fix msg)))
  :enable (msg-fix
           msgp
           character-alistp))

(defrule alistp-of-cdr-of-msg-fix
  (alistp (cdr (msg-fix msg)))
  :enable (msg-fix
           msgp
           alistp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define msg$0 ((str stringp))
  (mbe :logic (if (stringp str) str "")
       :exec str)
  :inline t)

(define msg$1 ((str stringp) arg0)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0)
  :inline t)

(define msg$2 ((str stringp) arg0 arg1)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0 arg1)
  :inline t)

(define msg$3 ((str stringp) arg0 arg1 arg2)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0 arg1 arg2)
  :inline t)

(define msg$4 ((str stringp) arg0 arg1 arg2 arg3)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0 arg1 arg2 arg3)
  :inline t)

(define msg$5 ((str stringp) arg0 arg1 arg2 arg3 arg4)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0 arg1 arg2 arg3 arg4)
  :inline t)

(define msg$6 ((str stringp) arg0 arg1 arg2 arg3 arg4 arg5)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0 arg1 arg2 arg3 arg4 arg5)
  :inline t)

(define msg$7 ((str stringp) arg0 arg1 arg2 arg3 arg4 arg5 arg6)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0 arg1 arg2 arg3 arg4 arg5 arg6)
  :inline t)

(define msg$8 ((str stringp) arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7)
  :inline t)

(define msg$9 ((str stringp) arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8)
  :inline t)

(define msg$10 ((str stringp) arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9)
  (msg (mbe :logic (if (stringp str) str "")
            :exec str)
       arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9)
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define msg$-logic (str args)
  (declare (xargs :type-prescription
                  (or (stringp (msg$-logic str args))
                      (and (consp (msg$-logic str args))
                           (true-listp (msg$-logic str args))))
                  :guard (hide (comment "msg$-logic is not intended to be used in code. Use msg$ instead."
                                        (true-listp args)))
                  :guard-hints (("Goal" :expand ((:free (x) (hide x)))))))
  :returns (msg msgp
                :hints (("Goal" :in-theory (enable msgp))))
  (if (consp args)
      (cons (if (stringp str) str "")
            (if (<= (len args) 10)
                (pairlis$ (take (len args) *base-10-chars*) args)
              nil))
    (if (stringp str) str ""))

  :prepwork
  ((defrulel character-alistp-of-pairlis$
     (implies (and (character-listp x)
                   (equal (len x) (len y)))
              (character-alistp (pairlis$ x y)))
     :induct t
     :enable (pairlis$
              character-alistp
              character-listp
              len))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule msg$0-becomes-msg$-logic
  (equal (msg$0 str)
         (msg$-logic str nil))
  :enable (msg$0 msg$-logic))

(defrule msg$1-becomes-msg$-logic
  (equal (msg$1 str arg0)
         (msg$-logic str (list arg0)))
  :enable (msg$1 msg$-logic len pairlis$))

(defrule msg$2-becomes-msg$-logic
  (equal (msg$2 str arg0 arg1)
         (msg$-logic str (list arg0 arg1)))
  :enable (msg$2 msg$-logic len pairlis$))

(defrule msg$3-becomes-msg$-logic
  (equal (msg$3 str arg0 arg1 arg2)
         (msg$-logic str (list arg0 arg1 arg2)))
  :enable (msg$3 msg$-logic len pairlis$))

(defrule msg$4-becomes-msg$-logic
  (equal (msg$4 str arg0 arg1 arg2 arg3)
         (msg$-logic str (list arg0 arg1 arg2 arg3)))
  :enable (msg$4 msg$-logic len pairlis$))

(defrule msg$5-becomes-msg$-logic
  (equal (msg$5 str arg0 arg1 arg2 arg3 arg4)
         (msg$-logic str (list arg0 arg1 arg2 arg3 arg4)))
  :enable (msg$5 msg$-logic len pairlis$))

(defrule msg$6-becomes-msg$-logic
  (equal (msg$6 str arg0 arg1 arg2 arg3 arg4 arg5)
         (msg$-logic str (list arg0 arg1 arg2 arg3 arg4 arg5)))
  :enable (msg$6 msg$-logic len pairlis$))

(defrule msg$7-becomes-msg$-logic
  (equal (msg$7 str arg0 arg1 arg2 arg3 arg4 arg5 arg6)
         (msg$-logic str (list arg0 arg1 arg2 arg3 arg4 arg5 arg6)))
  :enable (msg$7 msg$-logic len pairlis$))

(defrule msg$8-becomes-msg$-logic
  (equal (msg$8 str arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7)
         (msg$-logic str (list arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7)))
  :enable (msg$8 msg$-logic len pairlis$))

(defrule msg$9-becomes-msg$-logic
  (equal (msg$9 str arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8)
         (msg$-logic str (list arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8)))
  :enable (msg$9 msg$-logic len pairlis$))

(defrule msg$10-becomes-msg$-logic
  (equal (msg$10 str arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9)
         (msg$-logic str
                     (list arg0 arg1 arg2 arg3 arg4 arg5 arg6 arg7 arg8 arg9)))
  :enable (msg$10 msg$-logic len pairlis$))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro msg$ (str &rest args)
  (declare (xargs :guard (<= (len args) 10)))
  (case (len args)
    (0 (list 'msg$0 str))
    (1 (list 'msg$1 str (first args)))
    (2 (list 'msg$2 str (first args) (second args)))
    (3 (list 'msg$3 str (first args) (second args) (third args)))
    (4 (list 'msg$4 str (first args) (second args) (third args) (fourth args)))
    (5 (list 'msg$5 str (first args) (second args) (third args) (fourth args)
             (fifth args)))
    (6 (list 'msg$6 str (first args) (second args) (third args) (fourth args)
             (fifth args) (sixth args)))
    (7 (list 'msg$7 str (first args) (second args) (third args) (fourth args)
             (fifth args) (sixth args) (seventh args)))
    (8 (list 'msg$8 str (first args) (second args) (third args) (fourth args)
             (fifth args) (sixth args) (seventh args) (eighth args)))
    (9 (list 'msg$9 str (first args) (second args) (third args) (fourth args)
             (fifth args) (sixth args) (seventh args) (eighth args)
             (ninth args)))
    (10 (list 'msg$10 str (first args) (second args) (third args) (fourth args)
              (fifth args) (sixth args) (seventh args) (eighth args)
              (ninth args) (tenth args)))
    (otherwise nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro retmsg$ (str &rest args)
  (declare (xargs :guard (<= (len args) 10)))
  `(reterr (msg$ ,str ,@args)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define msg-downcase-first ((msg msgp))
  :returns (new-msg msgp
                    :hints (("Goal" :induct t
                                    :in-theory (enable character-alistp))))
  :parents (message-utilities)
  :short "Convert the first character
          of a <see topic='@(url msg)'>structured message</see>
          to lower case."
  :long
  "<p>
   If the message is a string,
   we use @(tsee str::downcase-first) on the string.
   </p>
   <p>
   Otherwise, if the format string of the message
   does not start with a tilde-directive (see @(tsee fmt)),
   we use @(tsee str::downcase-first) on the format string.
   </p>
   <p>
   Otherwise, we need to look at the tilde-directive
   that starts the format string of the message,
   and possibly modify the tilde-directive
   and the corresponding value in the alist,
   in order to suitably convert the first character
   of the resulting formatted string to lower case.
   This is done as follows:
   </p>
   <ul>
     <li>
     If the command character of the tilde-directive is
     @('x'), @('y'), @('X'), @('Y'), @('f'), or @('F'),
     we leave the message unchanged because
     these directives prints all the ACL2 values in a way that
     capitalization does not really apply:
     numbers are not words,
     symbols are in all caps or start with @('|'),
     characters start with @('#'),
     strings start with @('\"'),
     and @(tsee cons) pairs start with @('(').
     </li>
     <li>
     If the command character of the tilde-directive is
     @('t'), @('c'), space, @('_'), newline, @('%'), @('|'), @('~'), or @('-'),
     we leave the message unchanged because
     these directives do not print words.
     </li>
     <li>
     If the command character of the tilde-directive is @('n'),
     we leave the message unchanged because that directive
     already prints words that start with lower case characters.
     </li>
     <li>
     If the command character of the tilde-directive is @('N'),
     we replace it with @('n').
     </li>
     <li>
     If the command character of the tilde-directive is @('@'),
     we find the corresponding message in the alist
     and we recursively process it with this function.
     </li>
     <li>
     If the command character of the tilde-directive is @('s') or @('S'),
     we find the corresponding string or symbol in the alist,
     and if it is a string we use @(tsee str::downcase-first) on it.
     If instead it is a symbol, we leave the message unchanged
     because symbols are in all caps or start with @('|')
     (as in the case of the @('x') and other command characters above).
     </li>
     <li>
     If the command character of the tilde-directive is
     @('#'), @('*'), @('&'), or @('v'),
     we stop with an error:
     these directives are currently not supported by the implementation.
     </li>
   </ul>
   <p>
   Since @(tsee msgp) is a weak recognizer for messages,
   there is no guarantee that the format string is followed by an alist,
   and that the values in the alist have the appropriate types.
   This function leaves the message unchanged
   if some of these properties do not hold.
   </p>"
  (b* ((msg (msg-fix msg))
       ((when (stringp msg)) (str::downcase-first msg))
       ((cons string alist) msg)
       ((unless (and (> (length string) 0)
                     (eql (char string 0) #\~)))
        (cons (str::downcase-first string) alist))
       ((unless (and (>= (length string) 3)
                     (member (char string 1)
                             (list #\@ #\# #\* #\& #\v #\N #\s #\S))))
        msg))
    (case (char string 1)
      (#\@ (b* (((unless (alistp alist)) msg)
                (value (cdr (assoc (char string 2) alist)))
                ((unless (msgp value)) msg)
                (new-alist (acons (char string 2)
                                  (msg-downcase-first value)
                                  alist)))
             (cons string new-alist)))
      (#\N (b* ((new-string (concatenate 'string
                                         "~n"
                                         (subseq string 2 nil))))
             (cons new-string alist)))
      ((#\s #\S) (b* (((unless (alistp alist)) msg)
                      (value (cdr (assoc (char string 2) alist)))
                      ((unless (stringp value)) msg)
                      (new-alist (acons (char string 2)
                                        (str::downcase-first value)
                                        alist)))
                   (cons string new-alist)))
      (otherwise (prog2$ (raise "Message not supported: ~x0" msg)
                         msg))))
  :no-function nil
  :measure (acl2-count (msg-fix msg)))

(define msg-upcase-first ((msg msgp))
  :returns (new-msg msgp
                    :hints (("Goal" :induct t
                                    :in-theory (enable character-alistp))))
  :parents (message-utilities)
  :short "Convert the first character
          of a <see topic='@(url msg)'>structured message</see>
          to upper case."
  :long
  "<p>
   This is analogous to @(tsee msg-downcase-first),
   but we use @(tsee str::upcase-first) instead of @(tsee str::downcase-first)
   on the strings,
   and the roles of the @('n') and @('N') command characters
   of the tilde-directives are swapped.
   See the documentation of @(tsee msg-downcase-first).
   </p>"
  (b* ((msg (msg-fix msg))
       ((when (stringp msg)) (str::upcase-first msg))
       ((cons string alist) msg)
       ((unless (and (> (length string) 0)
                     (eql (char string 0) #\~)))
        (cons (str::upcase-first string) alist))
       ((unless (and (>= (length string) 3)
                     (member (char string 1)
                             (list #\@ #\# #\* #\& #\v #\n #\s #\S))))
        msg))
    (case (char string 1)
      (#\@ (b* (((unless (alistp alist)) msg)
                (value (cdr (assoc (char string 2) alist)))
                ((unless (msgp value)) msg)
                (new-alist (acons (char string 2)
                                  (msg-upcase-first value)
                                  alist)))
             (cons string new-alist)))
      (#\n (b* ((new-string (concatenate 'string
                                         "~N"
                                         (subseq string 2 nil))))
             (cons new-string alist)))
      ((#\s #\S) (b* (((unless (alistp alist)) msg)
                      (value (cdr (assoc (char string 2) alist)))
                      ((unless (stringp value)) msg)
                      (new-alist (acons (char string 2)
                                        (str::upcase-first value)
                                        alist)))
                   (cons string new-alist)))
      (otherwise (prog2$ (raise "Message not supported: ~x0" msg)
                         msg))))
  :no-function nil
  :measure (acl2-count (msg-fix msg)))
