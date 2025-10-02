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

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ type-specifier-lists
  :parents (abstract-syntax)
  :short "Characterization of valid lists of type specifiers."
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-permp ((tyspecs1 type-spec-listp)
                              (tyspecs2 type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if two lists of type specifiers are permutations."
  (b* (((when (endp tyspecs1)) (endp tyspecs2))
       (tyspec (car tyspecs1))
       ((unless (member-equal tyspec tyspecs2)) nil))
    (type-spec-list-permp (cdr tyspecs1) (remove1-equal tyspec tyspecs2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-char-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('char')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-char)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-char-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed char') or @('char signed'),
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-char)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-char)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-char))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-char-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned char') or @('char unsigned')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-char)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-short-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('short')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-short)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-short-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed short') or @('short signed'),
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-short)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-short)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-short))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-short-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('short int') or @('int short')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-short)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-short-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed short int') or any permutation of it,
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-short)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-short)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-short)
                                  (type-spec-int))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-short-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned short') or @('short unsigned')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-short)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-short-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned short int') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-short)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('int')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('signed'),
          including the GCC underscore variations of @('signed')."
  (or (equal (type-spec-list-fix tyspecs)
             (list (type-spec-signed (keyword-uscores-none))))
      (equal (type-spec-list-fix tyspecs)
             (list (type-spec-signed (keyword-uscores-start))))
      (equal (type-spec-list-fix tyspecs)
             (list (type-spec-signed (keyword-uscores-both)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed int') or @('int signed'),
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-int))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('unsigned')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-unsigned)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned int') or @('int unsigned')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('long')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-long)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long') or @('long signed'),
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-long)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-long)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-long))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long int') or @('int long')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-long)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long int') or any permutation of it,
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-long)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-long)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-long)
                                  (type-spec-int))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long') or @('long unsigned')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-long)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long int') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-long)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('long long')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-long)
               (type-spec-long)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long long') or any permutation of it,
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-long)
                                  (type-spec-long)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-long)
                                  (type-spec-long)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-long)
                                  (type-spec-long))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long long int') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-long)
                              (type-spec-long)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-long-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed long long int') or any permutation of it,
          including the GCC underscore variations of @('signed')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-long)
                                  (type-spec-long)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-long)
                                  (type-spec-long)
                                  (type-spec-int)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-long)
                                  (type-spec-long)
                                  (type-spec-int))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-long-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long long') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-long)
                              (type-spec-long)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-long-long-int-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned long long int') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-unsigned)
                              (type-spec-long)
                              (type-spec-long)
                              (type-spec-int)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('float')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-double-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('double')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-double)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-double-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long double') or @('double long')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-long)
                              (type-spec-double)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float16-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('_Float16')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float16)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float16x-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('_Float16x')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float16x)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;16

(define type-spec-list-float32-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('_Float32')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float32)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float32x-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('_Float32x')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float32x)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float64-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('_Float64')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float64)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float64x-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('_Float64x')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float64x)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float128-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('_Float128')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float128)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float128x-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('_Float128x')."
  (equal (type-spec-list-fix tyspecs)
         (list (type-spec-float128x)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('float _Complex') or @('_Complex float')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-double-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('double _Complex') or @('_Complex double')."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-double)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-long-double-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('long double _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-long)
                              (type-spec-double)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float16-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('_Float16 _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float16)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float16x-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('_Float16x _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float16x)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float32-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('_Float32 _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float32)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float32x-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('_Float32x _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float32x)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float64-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('_Float64 _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float64)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float64x-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('_Float64x _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float64x)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float128-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('_Float128 _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float128)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-float128x-complex-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('_Float128x _Complex') or any permutation of it."
  (type-spec-list-permp (type-spec-list-fix tyspecs)
                        (list (type-spec-float128x)
                              (type-spec-complex)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-int128-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form @('__int128') or
          @('__int128_t')."
  (or (equal (type-spec-list-fix tyspecs)
             (list (type-spec-int128 nil)))
      (equal (type-spec-list-fix tyspecs)
             (list (type-spec-int128 t))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-unsigned-int128-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('unsigned __int128') or @('__int128 unsigned'),
          including the @('__int128_t') variant of @('__int128')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-unsigned)
                                  (type-spec-int128 nil)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-unsigned)
                                  (type-spec-int128 t))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define type-spec-list-signed-int128-p ((tyspecs type-spec-listp))
  :returns (yes/no booleanp)
  :short "Check if a list of type specifiers has the form
          @('signed __int128') or @('__int128 signed'),
          including the GCC underscore variations of @('signed')
          the @('__int128_t') variant of @('__int128')."
  (or (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-int128 nil)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-int128 nil)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-int128 nil)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-none))
                                  (type-spec-int128 t)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-start))
                                  (type-spec-int128 t)))
      (type-spec-list-permp (type-spec-list-fix tyspecs)
                            (list (type-spec-signed (keyword-uscores-both))
                                  (type-spec-int128 t))))
  :hooks (:fix))
