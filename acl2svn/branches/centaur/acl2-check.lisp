; ACL2 Version 4.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

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

; Because of the last form in this file, this file should not be loaded as part
; of an executable ACL2 image.

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
; lisps are as follows, so we feel safe in using (signed-byte 30) and hence
; (unsigned-byte 29) to represent fixnums.  At worst, if a lisp is used for
; which (signed-byte 30) is not a subtype of fixnum, a compiler may simply fail
; to create efficient code.  Note:

; (the (signed-byte 30) 536870911) ; succeeds
; (the (signed-byte 30) 536870912) ; fails
; (the (unsigned-byte 29) 536870911) ; succeeds
; (the (unsigned-byte 29) 536870912) ; fails

; Values of most-positive-fixnum.
; AKCL, GCL: 2147483647
; Allegro:    536870911
; Lucid:      536870911
; cmulisp:    536870911
; SBCL:       536870911
; CCL:        536870911
; MCL:        268435455 ; not supported after ACL2 Version_3.1
; CLISP:       16777215
; Lispworks:    8388607 [version 4.2.0 and probably all later versions
;                        (also checked for 4.4.6);
;                        value was 536870911 for an earlier version]

; We have made many type declarations in the sources of (signed-byte 30).
; Performance could be seriously degraded if these were not fixnum
; declarations.  If the following check fails, then we should consider lowering
; 30.  However, clisp has 24-bit fixnums.  Clisp maintainer Sam Steingold has
; assured us that "CLISP has a very efficient bignum implementation."  Lispworks
; Version 4.2.0 on Linux has most-positive-fixnum = 8388607 and
; most-negative-fixnum = -8388608, and we have been informed (email 10/22/02)
; that "this is an architectural limit on this platform and the LispWorks fixnum
; size cannot be reconfigured."

#-(or clisp lispworks)
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

; Now trying to fix this problem, so commenting it out for now.

; #+hons
; (or (< (ash 1 33) most-positive-fixnum)
; 
; ; We found a failure during regression on the HONS version with 32-bit Allegro,
; ; because internal-real-time was not returning a fixnum.  Bob Boyer pointed out
; ; that this could be fixed, but it would take work because there are
; ; assumptions in the heart of memoize-fn that such quantities are indeed
; ; fixnums.  A simple test for 64-bit platforms, not perfect perhaps, is that
; ; post-positive-fixnum exceeds 2^33.
; 
;     (error "The experimental HONS extension of ACL2 requires 64-bit Lisp
; platforms, but the present platform appears not to be because the value
; of most-positive-fixnum, ~s, does not exceed (expt 2 33)."
;            most-positive-fixnum))
; 
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

; At one time we read the legal ACL2 characters from a string in a file, so
; that we could be confident that we know exactly what they are.  But if
; code-char is not a function, then we lose anyhow, because we have defined it
; in ACL2.  And if code-char is a function, then we can do our checking without
; having to get the characters from a file, the idea being that the range of
; code-char on {0,1,...,255} is exactly the set of legal ACL2 characters.

; Note that this issue is orthogonal to the problem of ensuring that #\c is
; read in as the same character in different ACL2 sessions, for any ACL2
; character c.  (Even #\Newline is potentially problematic, as its char-code is
; 10 in most Common Lisps but is 13 in MCL!)  Because of the latter issue, our
; story about ACL2 could include a caveat that certified books may only be
; soundly loaded into the same Lisp image in which they were certified.  When
; we say ``same lisp image'' we don't mean the same exact process necessarily,
; but rather simply an invocation of the same saved image.  Another reason for
; such a caveat, independent of the character-reading issue, is that different
; saved images may be tied into different compilers, thus making the object
; files of the books incompatible.

; However, we believe that we can prevent the most serious assaults on
; soundness due to implementation dependencies, simply by making notes in the
; version string, state global 'acl2-version; see :DOC version.

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

#-(or unix apple mswindows)
(error "This Common Lisp is unsuitable for ACL2 because~%~
        neither :UNIX nor :APPLE nor :MSWINDOWS is a member of *features*.")

(or (typep (1- array-dimension-limit) 'fixnum)
    (error "We assume that (1- ARRAY-DIMENSION-LIMIT) is a fixnum.  CLTL2 ~
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
; syntax of a lambda list keyword, that are either globally bound (as constants
; or else as special variables) or else have a global value when they are
; locally bound (and hence are special).

(let ((badvars nil))
  (dolist (var *copy-of-common-lisp-symbols-from-main-lisp-package*)
          (or (member var *copy-of-common-lisp-specials-and-constants*
                      :test #'eq)
              (if (and (let ((s (symbol-name var)))
                         (or (= (length s) 0)
                             (not (eql (char s 0) #\&))))
                       (or (boundp var)
                           (eval `(let ((,var t))
                                    (declare (ignore ,var))
                                    (boundp ',var)))))
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
