; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)
(include-book "std/util/error-value-tuples" :dir :system)

(include-book "kestrel/utilities/er-soft-plus" :dir :system)
(include-book "kestrel/utilities/extend-pathname-dollar" :dir :system)
(include-book "kestrel/utilities/messages" :dir :system)
(include-book "std/strings/decimal" :dir :system)
(include-book "std/system/pseudo-event-formp" :dir :system)

(include-book "centaur/misc/tshell" :dir :system)
(include-book "oslib/rmtree" :dir :system)
(include-book "oslib/tempfile" :dir :system)

(include-book "implementation-environments")

(include-book "std/basic/controlled-configuration" :dir :system)
(acl2::controlled-configuration :hooks nil)

(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/string-listp" :dir :system))
(local (include-book "kestrel/utilities/ordinals" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compile-run-read-ienv-c
  ((cc stringp)
   (args string-listp)
   state)
  :returns (mv (er? maybe-msgp)
               (lines string-listp)
               state)
  (b* (((reterr) nil state)
       (compiled-ienv-base "ienv")
       ((erp compiled-ienv state)
        (b* (((reterr) nil state)
             ((mv temp state)
              (oslib::tempfile compiled-ienv-base))
             ((unless temp)
              (retmsg$ "Could not create temporary file for ~x0"
                       compiled-ienv-base)))
          (retok temp state)))
       (- (acl2::tshell-ensure))
       (ienv-c-path (ec-call (extend-pathname :system "kestrel/c/syntax/ienv.c" state)))
       (compile-cmd
         (str::join (list* cc
                           ienv-c-path
                           "-o"
                           compiled-ienv
                           args)
                    " "))
       ((mv exit-status lines state)
        (acl2::tshell-call compile-cmd :print nil))
       ((unless (int= exit-status 0))
        (retmsg$ "Failed to compile ienv.c.~%Exit code: ~x0~%~x1"
                 exit-status
                 (str::join lines (string #\Newline))))
       ((mv exit-status lines state)
        (acl2::tshell-call compiled-ienv :print nil))
       ((unless (int= exit-status 0))
        (retmsg$ "Failed to run ~x0.~%Exit code: ~x1~%~x2"
                 compiled-ienv
                 exit-status
                 (str::join lines (string #\Newline))))
       ((erp state)
        (b* (((reterr) state)
             ((mv success state)
              (oslib::rmtree compiled-ienv))
             ((unless success)
              (retmsg$ "Could not remove temporary file: ~x0"
                       compiled-ienv)))
          (retok state))))
    (retok lines state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ienv-c-out-to-ienv ((lines string-listp))
  :returns (mv (er? maybe-msgp)
               (ienv ienvp))
  (b* (((reterr) (irr-ienv))
       ((unless (= (len lines) 7))
        (retmsg$ "Ill-formed ienv.c output"))
       ((list std-c-str
              gcc-extensions-str
              short-bytes-str
              int-bytes-str
              long-bytes-str
              llong-bytes-str
              plain-char-signedp-str)
        lines)
       ((erp std-c)
        (b* (((reterr) nil))
          (cond ((equal std-c-str "201710")
                 (retok 17))
                ((equal std-c-str "202311")
                 (retok 23))
                (t
                 (retmsg$ "Unrecognized or unsupported standard: ~x0"
                          std-c-str)))))
       (gcc-extensions (not (equal gcc-extensions-str "0")))
       (version (if gcc-extensions
                    (if (= std-c 17)
                        (c::version-c17+gcc)
                      (c::version-c23+gcc))
                  (if (= std-c 17)
                      (c::version-c17)
                    (c::version-c23))))
       (short-bytes? (str::strval short-bytes-str))
       ((unless short-bytes?)
        (retmsg$ "Could not parse a natural number from short-bytes: ~x0"
                 short-bytes-str))
       (int-bytes? (str::strval int-bytes-str))
       ((unless int-bytes?)
        (retmsg$ "Could not parse a natural number from int-bytes: ~x0"
                 int-bytes-str))
       (long-bytes? (str::strval long-bytes-str))
       ((unless long-bytes?)
        (retmsg$ "Could not parse a natural number from long-bytes: ~x0"
                 long-bytes-str))
       (llong-bytes? (str::strval llong-bytes-str))
       ((unless llong-bytes?)
        (retmsg$ "Could not parse a natural number from llong-bytes: ~x0"
                 llong-bytes-str))
       (plain-char-signedp (not (equal plain-char-signedp-str "0")))
       ((unless (<= short-bytes? int-bytes?))
        (retmsg$ "short-bytes exceeds int-bytes: ~x0, ~x1."
                 short-bytes?
                 int-bytes?))
       ((unless (<= 2 short-bytes?))
        (retmsg$ "short-bytes is less than 2: ~x0"
                 short-bytes?))
       ((unless (<= int-bytes? long-bytes?))
        (retmsg$ "int-bytes exceeds long-bytes: ~x0, ~x1."
                 int-bytes?
                 long-bytes?))
       ((unless (<= 2 int-bytes?))
        (retmsg$ "int-bytes is less than 2: ~x0"
                 int-bytes?))
       ((unless (<= long-bytes? llong-bytes?))
        (retmsg$ "long-bytes exceeds llong-bytes: ~x0, ~x1."
                 long-bytes?
                 llong-bytes?))
       ((unless (<= 4 long-bytes?))
        (retmsg$ "long-bytes is less than 4: ~x0"
                 long-bytes?))
       ((unless (<= 8 llong-bytes?))
        (retmsg$ "llong-bytes is less than 8: ~x0"
                 llong-bytes?)))
    (retok (make-ienv
             :version version
             :short-bytes short-bytes?
             :int-bytes int-bytes?
             :long-bytes long-bytes?
             :llong-bytes llong-bytes?
             :plain-char-signedp plain-char-signedp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define infer-ienv-prog
  ((cc stringp)
   (args string-listp)
   state)
  :returns (mv (er? maybe-msgp)
               (ienv ienvp)
               state)
  (b* (((reterr) (irr-ienv) state)
       ((erp lines state) (compile-run-read-ienv-c cc args state))
       ((erp ienv) (ienv-c-out-to-ienv lines)))
    (retok ienv state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define infer-ienv-process-inputs-and-gen-event (name cc args state)
  :returns (mv (er? maybe-msgp)
               (event pseudo-event-formp)
               state)
  (b* (((reterr) '(_) state)
       ((erp name)
        (b* (((reterr) nil))
          (if (symbolp name)
              (retok name)
            (retmsg$ "The NAME input must be a symbol, ~
                      but it is ~x0 instead."
                     name))))
       ((erp cc)
        (b* (((reterr) nil))
          (cond ((stringp cc)
                 (retok cc))
                ((not cc)
                 (retok "gcc"))
                (t
                 (retmsg$ "The :CC input must be a string or NIL, ~
                           but it is ~x0 instead."
                          cc)))))
       ((erp args)
        (b* (((reterr) nil))
          (if (string-listp args)
              (retok args)
            (retmsg$ "The :ARGS input must be a string list, ~
                      but it is ~x0 instead."
                     args))))
       ((erp ienv state) (infer-ienv-prog cc args state))
       (event `(defconst ,name ',ienv)))
    (retok event state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define infer-ienv-fn (name cc args ctx state)
  :returns (mv erp
               (event pseudo-event-formp)
               state)
  (b* (((mv er? event state)
        (infer-ienv-process-inputs-and-gen-event name cc args state))
       ((when er?) (er-soft+ ctx t '(_) "~@0" er?)))
    (value event)))

(defmacro infer-ienv
  (name
   &key
   (cc 'nil)
   (args 'nil))
  `(make-event (infer-ienv-fn ',name ',cc ',args 'infer-ienv state)))
