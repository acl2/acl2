; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/util/defines" :dir :system)
(include-book "xdoc/constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines remove-dead-if-branches
  :parents (std/system/term-transformations)
  :short "Remove all the dead @(tsee if) bramches in a term."
  :long
  (xdoc::topstring
   (xdoc::p
    "Each @('(if t a b)') or @('(if (not nil) a b)') is turned into @('a'),
     and each @('(if nil a b)') or @('(if (not t) a b)') is turned into @('b').
     This is done to @('a') and @('b'), recursively.")
   (xdoc::@def "remove-dead-if-branches")
   (xdoc::@def "remove-dead-if-branches-lst"))

  (define remove-dead-if-branches ((term pseudo-termp))
    :returns (new-term pseudo-termp :hyp :guard)
    (b* (((when (variablep term)) term)
         ((when (fquotep term)) term)
         (fn (ffn-symb term))
         ((when (and (eq fn 'if)
                     (= (len (fargs term)) 3))) ; should be always true
          (cond ((member-equal (fargn term 1)
                               (list *t* (fcons-term 'not (list *nil*))))
                 (remove-dead-if-branches (fargn term 2)))
                ((member-equal (fargn term 1)
                               (list *nil* (fcons-term 'not (list *t*))))
                 (remove-dead-if-branches (fargn term 3)))
                (t `(if ,(remove-dead-if-branches (fargn term 1))
                        ,(remove-dead-if-branches (fargn term 2))
                      ,(remove-dead-if-branches (fargn term 3))))))
         (new-args (remove-dead-if-branches-lst (fargs term)))
         ((when (symbolp fn)) (fcons-term fn new-args)))
      (fcons-term (make-lambda (lambda-formals fn)
                               (remove-dead-if-branches (lambda-body fn)))
                  new-args)))

  (define remove-dead-if-branches-lst ((terms pseudo-term-listp))
    :returns (new-terms (and (pseudo-term-listp new-terms)
                             (equal (len new-terms)
                                    (len terms)))
                        :hyp :guard)
    (b* (((when (endp terms)) nil)
         (new-term (remove-dead-if-branches (car terms)))
         (new-terms (remove-dead-if-branches-lst (cdr terms))))
      (cons new-term new-terms))))
