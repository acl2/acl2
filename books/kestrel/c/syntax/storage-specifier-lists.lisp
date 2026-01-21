; C Library
;
; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C$")

(include-book "abstract-syntax-trees")

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ storage-specifier-lists
  :parents (abstract-syntax)
  :short "Characterization of valid lists of storage specifiers."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-typedef-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('typedef')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-typedef))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-extern-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('extern')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-extern))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-static-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('static')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-static))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-thread-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('_Thread_local') or @('__thread')."
  (or (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-thread nil)))
      (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-thread t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-auto-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('auto')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-auto))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-register-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('register')."
  (equal (stor-spec-list-fix storspecs)
         (list (stor-spec-register))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-extern-thread-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('extern _Thread_local') or @('_Thread_local extern'),
          including the @('__thread') variant of @('_Thread_local')."
  (or (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-extern)
                   (stor-spec-thread nil)))
      (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-thread nil)
                   (stor-spec-extern)))
      (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-extern)
                   (stor-spec-thread t)))
      (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-thread t)
                   (stor-spec-extern)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stor-spec-list-static-thread-p ((storspecs stor-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of storage class specifiers
          has the form @('static _Thread_local') or @('_Thread_local static'),
          including the @('__thread') variant of @('_Thread_local')."
  (or (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-static)
                   (stor-spec-thread nil)))
      (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-thread nil)
                   (stor-spec-static)))
      (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-static)
                   (stor-spec-thread t)))
      (equal (stor-spec-list-fix storspecs)
             (list (stor-spec-thread t)
                   (stor-spec-static)))))
