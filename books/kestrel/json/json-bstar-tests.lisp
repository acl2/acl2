; JSON Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JSON")

(include-book "json-bstar")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test JSON patterns and b* binder.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Test pattern predicates

(assert-event (json-patternp "abc"))
(assert-event (json-patternp '_))
(assert-event (json-patternp 3))
(assert-event (json-patternp 3/2))
(assert-event (json-patternp 'bcd))

(assert-event (not (json-patternp 'T)))
(assert-event (not (json-patternp 'NIL)))
(assert-event (not (json-patternp '||)))
(assert-event (not (json-patternp ':_)))

;; *.. is not allowed at the top level.
;; Currently it is only allowed as the last array element or object member.
(assert-event (not (json-patternp '*..)))

(assert-event (json-patternp '(:null)))
(assert-event (json-patternp '(:true)))
(assert-event (json-patternp '(:false)))

(assert-event (json-patternp '(:string "cde")))
(assert-event (json-patternp '(:string def)))
(assert-event (json-patternp '(:string acl2::_)))
(assert-event (not (json-patternp '(:string acl2::*..))))

;; It is only json::match? that is let-bound to the full matching form
(assert-event (not (json-patternp '(:string match?))))
(assert-event (json-patternp '(:string acl2::match?)))

(assert-event (json-patternp '(:number 4)))
(assert-event (json-patternp '(:number 4/5)))
(assert-event (json-patternp '(:number efg)))
(assert-event (not (json-patternp '(:number :fgh))))

(assert-event (json-patternp '(:array *..)))
(assert-event (json-patternp '(:object *..)))

(assert-event (json-patternp '(:array)))
(assert-event (json-patternp '(:object)))

(assert-event (not (json-patternp '(:array v1 (:string v1)))))
(assert-event (not (json-patternp '(:array v1 (:array v1)))))
(assert-event (json-patternp '(:array v1 (:string v2))))

(assert-event (json-patternp '(:object (:member v1 v2))))
(assert-event (json-patternp '(:object (:member _ v2))))
(assert-event (json-patternp '(:object (:member "ab" v2))))
(assert-event (not (json-patternp '(:object (:member v2 v2)))))
(assert-event (not (json-patternp '(:object (:member *.. v2)))))
(assert-event (not (json-patternp '(:object (:member (:true) v2)))))

(assert-event (member-patternp '(:member "stuff" _)))
(assert-event (member-patternp '(:member _ _)))
(assert-event (member-patternp '(:member v1 _)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; test jpat-collect-match-requirements

(defconst *pat-test-1*
 (make-value-object :members (list (make-member :name "top"
						:value
   (make-value-object :members (list (make-member :name "fn"
						  :value
     (make-value-object :members (list (make-member :name "+"
						    :value
       (make-value-array :elements (list (make-value-string :get "3")
					 (make-value-string :get "4")))))))))))))

(assert-event (equal
               (mv-list 2
               (jpat-collect-match-requirements
                '_
                '*pat-test-1*))
               '(((VALUEP *PAT-TEST-1*)) NIL)))

(assert-event (equal
               (mv-list 2
               (jpat-collect-match-requirements
                'foo
                '*pat-test-1*))
               '(((VALUEP *PAT-TEST-1*))
                 ((FOO (IF MATCH? *PAT-TEST-1* :NOMATCH!))))))

(assert-event (equal
               (mv-list 2
               (jpat-collect-match-requirements
                '(:object
                  (:member "top"
                           (:object
                            (:member _
                                     (:object
                                      (:member op
                                               (:array arg1 arg2)))))))
                '*pat-test-1*))
               '(((VALUEP *PAT-TEST-1*)
  (TOP-JOBJECTP *PAT-TEST-1*)
  (CONSP (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))
  (MEMBERP (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*)))
  (EQUAL "top"
         (MEMBER->NAME (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))))
  (TOP-JOBJECTP (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))))
  (CONSP (VALUE-OBJECT->MEMBERS
              (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*)))))
  (MEMBERP
      (CAR (VALUE-OBJECT->MEMBERS
                (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))))))
  (TOP-JOBJECTP
   (MEMBER->VALUE
     (CAR (VALUE-OBJECT->MEMBERS
               (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*)))))))
  (CONSP
   (VALUE-OBJECT->MEMBERS
    (MEMBER->VALUE
     (CAR
         (VALUE-OBJECT->MEMBERS
              (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))))))))
  (MEMBERP
   (CAR
    (VALUE-OBJECT->MEMBERS
     (MEMBER->VALUE
      (CAR
        (VALUE-OBJECT->MEMBERS
             (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*)))))))))
  (TOP-JARRAYP
   (MEMBER->VALUE
    (CAR
     (VALUE-OBJECT->MEMBERS
      (MEMBER->VALUE
       (CAR
        (VALUE-OBJECT->MEMBERS
            (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))))))))))
  (CONSP
   (VALUE-ARRAY->ELEMENTS
    (MEMBER->VALUE
     (CAR
      (VALUE-OBJECT->MEMBERS
       (MEMBER->VALUE
        (CAR
         (VALUE-OBJECT->MEMBERS
           (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*)))))))))))
  (CONSP
   (CDR
    (VALUE-ARRAY->ELEMENTS
     (MEMBER->VALUE
      (CAR
       (VALUE-OBJECT->MEMBERS
        (MEMBER->VALUE
          (CAR (VALUE-OBJECT->MEMBERS
                    (MEMBER->VALUE
                         (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))))))))))))
  (NULL
   (CDR
    (CDR
     (VALUE-ARRAY->ELEMENTS
      (MEMBER->VALUE
       (CAR
        (VALUE-OBJECT->MEMBERS
         (MEMBER->VALUE
          (CAR
              (VALUE-OBJECT->MEMBERS
                   (MEMBER->VALUE
                        (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*)))))))))))))
  (NULL
   (CDR
    (VALUE-OBJECT->MEMBERS
     (MEMBER->VALUE
      (CAR
        (VALUE-OBJECT->MEMBERS
             (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*)))))))))
  (NULL
      (CDR (VALUE-OBJECT->MEMBERS
                (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))))))
  (NULL (CDR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))))
 ((OP
   (IF
    MATCH?
    (MEMBER->NAME
     (CAR
      (VALUE-OBJECT->MEMBERS
       (MEMBER->VALUE
        (CAR
         (VALUE-OBJECT->MEMBERS
             (MEMBER->VALUE (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*)))))))))
    :NOMATCH!))
  (ARG1
   (IF
    MATCH?
    (CAR
     (VALUE-ARRAY->ELEMENTS
      (MEMBER->VALUE
       (CAR
        (VALUE-OBJECT->MEMBERS
         (MEMBER->VALUE
           (CAR (VALUE-OBJECT->MEMBERS
                     (MEMBER->VALUE
                          (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*)))))))))))
    :NOMATCH!))
  (ARG2
   (IF
    MATCH?
    (CAR
     (CDR
      (VALUE-ARRAY->ELEMENTS
       (MEMBER->VALUE
        (CAR
         (VALUE-OBJECT->MEMBERS
          (MEMBER->VALUE
           (CAR
               (VALUE-OBJECT->MEMBERS
                    (MEMBER->VALUE
                         (CAR (VALUE-OBJECT->MEMBERS *PAT-TEST-1*))))))))))))
    :NOMATCH!))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; b* binder Tests

;; See the JSON AST value in defconst *pat-test-1* above.
;; Here's what that test produces:
#||
(:OBJECT
 (((NAME . "top")
   (VALUE
     :OBJECT
     (((NAME . "fn")
       (VALUE :OBJECT (((NAME . "+")
                        (VALUE :ARRAY ((:STRING "3") (:STRING "4"))))))))))))
||#



(defun pat-test-1 ()
  (b* (
       ((pattern _) '(:string "abc"))
       ((pattern (:string aaa)) '(:string "abd"))
       ((pattern acl2::_) '(:string ""))
       )
    (equal aaa "abd")))

(defun pat-test-2 ()
  (b* (((pattern (:object
		  (:member "top"
			   (:object
			    (:member _
				     (:object
				      (:member op
					       (:array arg1 arg2))))))))
	*pat-test-1*))
    (and (equal op "+")
         (equal arg1 (make-value-string :get "3"))
         (equal arg2 (make-value-string :get "4")))))

(defun pat-test-3 ()
  (b* (
       ((pattern _) '(:number 123))
       ((pattern (:number aaa)) '(:number -456))
       ((pattern acl2::_) '(:number 0))
       )
    (equal aaa -456)))

(assert-event (and (pat-test-1) (pat-test-2) (pat-test-3)))

;; test match? and not match?

(defun pat-test-4 ()
  (b* ((parent-form (cons
                     :mycar
                     (make-value-array
                      :elements (list (make-value-true)
                                      (make-value-string :get "two")
                                      (make-value-number :get 3)
                                      (make-value-false)
                                      (make-value-null)))))
       ((pattern (:array one "two" 3 four (:null))) (cdr parent-form))
       ((unless match?) nil)
       ((unless (and (jtruep one) (jfalsep four))) nil)
       ((pattern (:array one "two" 3 four (:null))) (car parent-form))
       ((when match?) nil)
       ((unless (and (eq one :nomatch!) (eq four :nomatch!))) nil)
       )
    t))

(assert-event (pat-test-4))

;; test new SYMBOL.. pattern that binds a variable to a tail of a list

(defun pat-test-5 ()
  (b* ((parent-form (cons
                     :mycar
                     (make-value-array
                      :elements (list (make-value-true)
                                      (make-value-string :get "two")
                                      (make-value-number :get 3)
                                      (make-value-false)
                                      (make-value-null)))))
       ((pattern (:array one rest..)) (cdr parent-form))
       ((unless match?) nil)
       ((unless (jtruep one)) nil)
       ((pattern (:array "two" cdr-rest..)) (make-value-array :elements rest..))
       ((unless (and match?
                     (equal (list* (make-value-true)
                                   (make-value-string :get "two")
                                   cdr-rest..)
                            (value-array->elements (cdr parent-form)))))
        nil))
    t))

(assert-event (pat-test-5))

;; Also apply SYMBOL.. to the tail of a member list

(defun pat-test-6 ()
  (b* ((parent-form (make-value-object :members (list (make-member :name "var" :value (make-value-string :get "x"))
                                                      (make-member :name "type" :value (make-value-string :get "int"))
                                                      (make-member :name "val" :value (make-value-number :get 3)))))
       ((pattern (:object (:member "var" v) type-and-val..)) parent-form)
       ((unless (and match?
                     (equal (len type-and-val..) 2))) nil))
    t))

(assert-event (pat-test-6))
