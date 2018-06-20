; String Utilities
;
; Copyright (C) 2018 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/strings/case-conversion" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "system/kestrel" :dir :system)
(include-book "characters")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc string-utilities
  :parents (kestrel-utilities)
  :short "Utilities for @(see strings).")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nonempty-stringp (x)
  :returns (yes/no booleanp)
  :parents (string-utilities)
  :short "Recognize non-empty strings."
  (not (equal (str-fix x) ""))
  ///

  (defrule stringp-when-nonempty-stringp
    (implies (nonempty-stringp x)
             (stringp x))))

(std::deflist nonempty-string-listp (x)
  (nonempty-stringp x)
  :parents (string-utilities)
  :short "Recognize true lists of nonempty strings."
  :true-listp t
  :elementp-of-nil nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define nats=>string ((nats (unsigned-byte-listp 8 nats)))
  :returns (string stringp)
  :parents (string-utilities)
  :short "Convert a true list of natural numbers below 256
          to the corresponding string."
  (implode (nats=>chars nats)))

(define string=>nats ((string stringp))
  :returns (nats (unsigned-byte-listp 8 nats))
  :parents (string-utilities)
  :short "Convert a string
          to the corresponding true list of natural numbers below 256."
  (chars=>nats (explode string))
  ///

  (more-returns
   (nats nat-listp
         :name nat-listp-of-string=>nats))

  (defrule len-of-string=>nats
    (implies (stringp string)
             (equal (len (string=>nats string))
                    (length string)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define msg-downcase-first ((msg msgp))
  :returns (new-msg msgp :hyp :guard)
  :parents (string-utilities)
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
  (b* (((when (stringp msg)) (str::downcase-first msg))
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
                         msg)))))

(define msg-upcase-first ((msg msgp))
  :returns (new-msg msgp :hyp :guard)
  :parents (string-utilities)
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
  (b* (((when (stringp msg)) (str::upcase-first msg))
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
                         msg)))))
