; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; Because of the last form in this file, this file should not be loaded as part
; of an executable ACL2 image.

; Warning: This file should not be compiled.  The intention is to load the
; .lisp file each time we build ACL2, regardless of the host Lisp.

(in-package "ACL2")

; See section "CHECKS" of acl2.lisp for more checks.

; We begin with a basic test related to the CR/NL character pairs that can
; occur in some systems, but which ACL2 assumes are not routinely present.

(or (equal (length "ab
cd")
           5)
    (error "We have tested that the string ab\\ncd (where \\n denotes
a Newline character) has length 5, but it does not.  Perhaps your system
is using two characters to indicate a new line?"))

; We put the following check here to be sure that the function
; legal-variable-or-constant-namep checks for all possible lambda list
; keywords.

(dolist (name lambda-list-keywords)
        (cond

; The check from legal-variable-or-constant-namep is here.

         ((let ((s (symbol-name name)))
            (or (= (length s) 0)
                (not (eql (char s 0) #\&))))
          (error "We assume that all lambda-list-keywords start with the ~
                  character #\&.~%However, ~s does not.  ACL2 will not work in ~
                  this Common Lisp."
                 name))))

(or (and (integerp char-code-limit)
         (<= 256 char-code-limit)
         (typep 256 'fixnum))
    (error "We assume that 256 is a fixnum not exceeding char-code-limit, for ~
            purposes of~%character manipulation.  ACL2 will not work in this ~
            Common Lisp."))

; Essay on Fixnum Declarations

; To the best of our knowledge, the values of most-positive-fixnum in various
; 32-bit lisps are as follows, so we feel safe in using (signed-byte 30) and
; hence (unsigned-byte 29) to represent fixnums.  At worst, if a lisp is used
; for which (signed-byte 30) is not a subtype of fixnum, a compiler may simply
; fail to create efficient code.  Note:

; (the (signed-byte 30) 536870911) ; succeeds
; (the (signed-byte 30) 536870912) ; fails
; (the (unsigned-byte 29) 536870911) ; succeeds
; (the (unsigned-byte 29) 536870912) ; fails

; Values of most-positive-fixnum in 32-bit Lisps:
; AKCL, GCL: 2147483647
; Allegro:    536870911
; Lucid:      536870911
; CMUCL:      536870911
; SBCL:       536870911
; CCL:        536870911
; MCL:        268435455 ; not supported after ACL2 Version_3.1
; CLISP:       16777215
; Lispworks:  536870911 [version 6.0.1; but observed 8388607 in versions 4.2.0
;                        and 4.4.6]

; We have made many type declarations in the sources of (signed-byte 30).
; Performance could be seriously degraded if these were not fixnum
; declarations.  If the following check fails, then we should consider lowering
; 30.  However, clisp has 24-bit fixnums.  Clisp maintainer Sam Steingold has
; assured us that "CLISP has a very efficient bignum implementation."  Lispworks
; Version 4.2.0 on Linux, 32-bit, had most-positive-fixnum = 8388607 and
; most-negative-fixnum = -8388608; and we have been informed (email 10/22/02)
; that "this is an architectural limit on this platform and the LispWorks fixnum
; size cannot be reconfigured."  But Lispworks 6 is back to supporting larger
; fixnums.

; As of July 2018, 64-bit computers have been available for many years, and it
; may be appropriate soon to make changes based on that fact since ACL2 is only
; rarely run on 32-bit Lisps these days.  Below are values of the largest
; fixnums in 64-bit Lisps.

; Values of most-positive-fixnum in 64-bit Lisps:
; GCL:       9223372036854775807 ; (1- (expt 2 63))
; Allegro:   1152921504606846975 ; (1- (expt 2 60))
; CMUCL:     [apparently available only in 32-bit Lisp]
; SBCL:      4611686018427387903 ; (1- (expt 2 62))
; CCL:       1152921504606846975 ; (1- (expt 2 60))
; Lispworks: 1152921504606846975 ; (1- (expt 2 60))

#-(or clisp (and lispworks (not lispworks-64bit)))
(or (and (<= (1- (ash 1 29)) most-positive-fixnum)
         (<= most-negative-fixnum (- (ash 1 29))))
    (error "We assume for performance reasons that numbers from
(- (ash 1 29)) to (1- (ash 1 29)) are fixnums in Common Lisp
implementations.  If you see this error, then please contact the ACL2
implementors and tell them which Common Lisp implementation you are
using, and that in that Lisp, most-positive-fixnum = ~s and
most-negative-fixnum = ~s."
           most-positive-fixnum
           most-negative-fixnum))

; Now we deal with the existence of case-sensitive images in Allegro.

#+(and allegro allegro-version>= (version>= 6 0))
(when (not (eq excl::*current-case-mode*
               :case-insensitive-upper))
  (error " This Allegro Common Lisp image is not compatible with ACL2
 because *current-case-mode* has the value
  ~s
 rather than the value
  ~s.
 You can try executing the form
  (set-case-mode :case-insensitive-upper)
 before building ACL2 and that should solve the problem, although the
 Allegro 6.0 documentation claims:  \"... it is much better to use an
 image with the desired case mode rather than changing the case mode
 after the image has started.\""
         *current-case-mode*
         :case-insensitive-upper))

(or (equal (symbol-name 'a) "A")
    (error "This Common Lisp image appears to be case-sensitive:~%~
            (equal (symbol-name 'a) \"A\") evaluates to NIL.~%~
            It is therefore not suitable for ACL2."))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                           ACL2 CHARACTERS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; It is difficult or impossible to ensure that #\c is read in as the same
; character in different ACL2 sessions, for any ACL2 character c.  (Even
; #\Newline is potentially problematic, as its char-code is 10 in most Common
; Lisps but is 13 in [now-obsolete] MCL!)  Thus, the soundness of ACL2 rests on
; a caveat that all books are certified using the same Lisp image.  When we say
; ``same lisp image'' we don't mean the same exact process necessarily, but
; rather, an invocation of the same saved image.  Another reason for such a
; caveat, independent of the character-reading issue, is that different saved
; images may be tied into different compilers, thus making the object files of
; the books incompatible.

; Nevertheless, it would of course be nice if all host Lisp implementations of
; ACL2 actually do agree on character and string constants provided by the Lisp
; reader (based on *acl2-readtable*).  Our first check is intended to address
; this point, by providing some confidence that the host Lisp has an ASCII
; character set.  As explained above, we only intend soundness in the case that
; all books are certified from scratch using the same host Lisp, and we do not
; actually assume ASCII characters -- more precisely, we do not assume any
; particular values for code-char and code-char -- so this check is not really
; necessary, except for a claim about ASCII characters in "Precise Description
; of the ACL2 Logic", which should perhaps be removed.  However, as of January
; 2012 we seem to be able to make the following check in all supported Lisps,
; at least on our Linux and Mac OS platforms.  It should be sound for users to
; comment out this check, but with the understanding that ACL2 is taking
; whatever the Lisp reader (using *acl2-readtable*) gives it.

(let ((filename "acl2-characters"))

; Why do we read from a separate file, rather than just saving the relevant
; characters in the present file?  For example, it may seem reasonable to use a
; trusted host Lisp to obtain an alist by evaluating the following expression.

; (loop for i from 0 to 255 do (princ (cons i (code-char i))))

; Could the resulting the alist be placed into this file and used for the check
; below?

; We run into a problem right away with that approach because of Control-D.
; For example, try this

; (princ (cons 4 (code-char 4)))

; and then try quoting the output and reading it back in.  Or,
; try evaluating the following.

; (read-from-string (format nil "~a" (code-char 4)))

; We have seen an error in both cases.

; So instead, we originally generated the file acl2-characters as follows,
; using an ACL2 image based on CCL.

; (with-open-file (str "acl2-characters" :direction :output)
;                 (loop for i from 0 to 255
;                       do (write-char (code-char i) str)))

; We explicitly specify the :external-format in the case of host Lisps for
; which we set the character encoding after the build, on the command line
; written by save-acl2.

  (with-open-file
   (str filename :direction :input)
   (loop for i from 0 to 255

; The function legal-acl2-character-p, called in bad-lisp-objectp for
; characters and strings, checks that the char-code of any character that is
; read must be between 0 and 255.

         do (let ((temp (read-char str)))
              (when #-clisp (not (eql (char-code temp) i))

; In CLISP we find character 10 (Newline) at position 13 (expected Return).
; Perhaps this has something to do CLISP's attempt to comply with the CL
; HyperSpec Section 13.1.8, "Treatment of Newline during Input and Output".
; But something is amiss.  Consider for example the following log (with some
; output edited in the case of the first two forms, but no editing of output
; for the third form).

; ACL2 [RAW LISP]> (with-open-file (str "tmp" :direction :output)
;                                  (write-char (code-char 13) str))
; #\Return
; ACL2 [RAW LISP]> (with-open-file (str "tmp" :direction :input)
;                                  (equal (read-char str) (code-char 10)))
; T
; ACL2 [RAW LISP]> (format nil "~a" (code-char 13))
; "
; ACL2 [RAW LISP]>

; So our check for CLISP is incomplete, but as explained in the comment just
; above this check, we can live with that.

                    #+clisp
                    (and (not (eql (char-code temp) i))
                         (not (eql i 13)))
                (error "Bad character in file ~s: character ~s at position ~s."
                       filename (char-code temp) i))))))

; The check just above does not say anything about the five character names
; that we support (see acl2-read-character-string), as described in :doc
; characters; so we add suitable checks on these here.

(loop for pair in (pairlis '(#\Space #\Tab #\Newline #\Page #\Rubout #\Return)
                           '(32 9 10 12 127 13))
      do (let* ((ch (car pair))
                (code (cdr pair))
                (val (char-code ch)))
           (or (eql val code)
               (error "(char-code ~s) evaluated to ~s (expected ~s)."
                      ch val code))))

; Test that all purportedly standard characters are standard, and vice versa.

(dotimes (i 256)
         (let ((ch (code-char i)))
           (or (equal (standard-char-p ch)
                      (or #+(and mcl (not ccl))
                          (= i 13)
                          #-(and mcl (not ccl))
                          (= i 10)
                          (and (>= i 32)
                               (<= i 126))))
               (error "This Common Lisp is unsuitable for ACL2 because the ~
                       character~%with char-code ~d ~a standard in this ~
                       Common Lisp but should~%~abe."
                      i
                      (if (standard-char-p ch) "is" "is not")
                      (if (standard-char-p ch) "not " "")))))

; Check that char-upcase and char-downcase have the same values in all lisps,
; and in particular, keep us in the realm of ACL2 characters.  Starting with
; Version_2.6 we limit our check to the standard characters (and we no longer
; avoid the check for mcl) because the guard to char-upcase and char-downcase
; limits the use of these functions to standard characters.

(dotimes (i 256)
         (let ((ch (code-char i)))
           (or (not (standard-char-p ch))
               (eql (char-downcase ch)
                    (if (and (>= i 65)
                             (<= i 90))
                        (code-char (+ i 32))
                      ch))
               (error "This Common Lisp is unsuitable for ACL2 because ~
                      (char-downcase ~s)~%is ~s but should be ~s."
                      ch
                      (char-downcase ch)
                      (if (and (>= i 65)
                               (<= i 90))
                          (code-char (+ i 32))
                        ch)))))

(dotimes (i 256)
         (let ((ch (code-char i)))
           (or (not (standard-char-p ch))
               (eql (char-upcase ch)
                    (if (and (>= i 97)
                             (<= i 122))
                        (code-char (- (char-code ch) 32))
                      ch))
               (error "This Common Lisp is unsuitable for ACL2 because ~
                      (char-upcase ~s)~%is ~s but should be ~s."
                      ch
                      (char-upcase ch)
                      (if (and (>= i 65)
                               (<= i 90))
                          (code-char (- (char-code ch) 32))
                        ch)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                           FEATURES, MISC.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The conditional reader macro doesn't care about the package when it looks for
; the symbol.  In fact, :UNIX is not a member of *features* in gcl; LISP:UNIX
; is.

#-(or unix mswindows)
(error "This Common Lisp is unsuitable for ACL2 because~%~
        neither :UNIX nor :MSWINDOWS is a member of *features*.")

(or (typep array-dimension-limit 'fixnum)

; We assume this explicitly in the various copy-array functions.

    (error "We assume that ARRAY-DIMENSION-LIMIT is a fixnum.  CLTL2 ~
            requires this.  ACL2 will not work in this Common Lisp."))

(or (>= multiple-values-limit *number-of-return-values*)
    (error "We assume that multiple-values-limit is at least ~s, but in this ~
            Common Lisp its value is ~s.  Please contact the ACL2 implementors ~
            about lowering the value of ACL2 constant ~
            *NUMBER-OF-RETURN-VALUES*."
           multiple-values-limit
           *number-of-return-values*))

; The following check must be put last in this file, since we don't entirely
; trust that it won't corrupt the current image.  We collect all symbols in
; *common-lisp-symbols-from-main-lisp-package*, other than those that have the
; syntax of a lambda list keyword, that are special.

(let ((badvars nil))
  (dolist (var *copy-of-common-lisp-symbols-from-main-lisp-package*)
          (or (member var *copy-of-common-lisp-specials-and-constants*
                      :test #'eq)
              (if (and (let ((s (symbol-name var)))
                         (or (= (length s) 0)
                             (not (eql (char s 0) #\&))))
                       (eval `(let ((,var (gensym)))

; We are not aware of any predicate, defined in all Common Lisp
; implementations, for checking that a variable is special; so we write our own
; behavioral test here.  If var is special, then the above binding will make it
; boundp and update its symbol-value.  Conversely, if var is not special, then
; there are two cases: either it is not boundp before the binding above in
; which case it remains not boundp, or else its global value is not the above
; gensym value.

                                (and (boundp ',var)
                                     (eq ,var (symbol-value ',var))))))
                  (setq badvars (cons var badvars)))))
  (if badvars
      (error "The following constants or special variables in the main~%~
              Lisp package needs to be included in the list~%~
              *common-lisp-specials-and-constants*:~%~
              ~s."
             badvars)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(format t "Check completed.~%")

; Do not put any forms below!  See comment above.
