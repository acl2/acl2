#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags
              ((:ccg)) :load-compiled-file nil)
(include-book "acl2s/base-theory" :dir :system :ttags :all)
(include-book "acl2s/custom" :dir :system :ttags :all)
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)

(acl2s-defaults :set cgen-single-test-timeout 0)

#|

I discovered a number of bugs in defdata-core regarding the definition
of enumerators, eg, here is the previous definition of
nth-non-pos-integer-builtin, which has been there for a long time!


(defun nth-non-pos-integer-builtin (n)
   (declare (xargs :guard (natp n)))
   (+ 1 n))

This is guaranteed to return a positive integer, so the enumerator
will always fail!

There were similar problems with other enumerators, so I added this
file to test the definitions.

Every time we add a new custom data definition to the defdata books,
we should update this file.

I put these tests here because I want cgen, arithmetic, etc to be
available when reasoning about these definitions and I did not want to
add all those dependencies to base.lisp.

(redef!)

TODO: Make all the thms, rewrite & fc rules whose
triggers are the enumerators.

TODO: Write macros to generate the forms below so
that I only have to provide a list.

TODO: Add support in defdata to check that types are not
equal. This would be something like:

(defdata-not-equal T1 T2) ->

(must-fail
  (test? (equal (T1p x) (T2p x))))

(defdatas-not-equal (T1 ... Tn)) ->
similar to disjoint, where we do a O(n^2) comparison

Use that to walk through the known types 
at ACL2s build time and make sure I can find
counterexamples to all known types.

TODO: make sure to specify all disjoint type relationship

TODO: verify guards in base.lisp
|#

(must-succeed
 (thm (implies (natp n)
               (booleanp (nth-boolean-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (natp (nth-nat-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (posp (nth-pos-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (negp (nth-neg-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (non-pos-integerp (nth-non-pos-integer-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (non-0-integerp (nth-non-0-integer-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (integerp (nth-integer-builtin n)))))

(must-succeed
 (thm (implies (and (natp n)
                    (integerp lo)
                    (integerp hi)
                    (<= lo hi))
               (and (integerp (nth-integer-between n lo hi))
                    (<= lo (nth-integer-between n lo hi))
                    (>= hi (nth-integer-between n lo hi))))))

(must-succeed
 (test? (implies (natp n)
                 (pos-ratiop (nth-pos-ratio-builtin n)))))

(must-succeed
 (test? (implies (natp n)
                 (neg-ratiop (nth-neg-ratio-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (neg-rationalp (nth-neg-rational-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (pos-rationalp (nth-pos-rational-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (non-neg-rationalp (nth-non-neg-rational-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (non-pos-rationalp (nth-non-pos-rational-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (non-0-rationalp (nth-non-0-rational-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (rationalp (nth-rational-builtin n)))))

(must-succeed
 (test? (implies (and (natp n)
                      (rationalp lo)
                      (rationalp hi)
                      (<= lo hi))
                 (and (rationalp (nth-rational-between n lo hi))
                      (<= lo (nth-rational-between n lo hi))
                      (>= hi (nth-rational-between n lo hi))))))

(must-succeed
 (thm (implies (natp n)
               (stringp (nth-string-builtin n)))))

(must-succeed
 (test? (implies (natp n)
                 (standard-stringp (nth-standard-string-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (symbolp (nth-symbol-builtin n)))))

(must-succeed
 (thm (implies (natp n)
               (characterp (nth-character-builtin n)))))

(must-succeed
 (test? (implies (natp n)
                 (in (nth-alpha-num-character n)
                     *alpha-num-chars*))))

(must-succeed
 (thm (implies (natp n)
               (character-listp (nth-character-list-builtin n)))))

(must-succeed
 (test? (implies (natp n)
                 (standard-char-listp (nth-standard-char-list-builtin n)))))


#|
Skipping for now.

(defun nth-complex-rational-builtin (n)
(defun nth-complex-rational-between (n lo hi)
(defun nth-acl2-number-builtin (n)
(defun nth-acl2-number-between (n lo hi)
(defun nth-number-between-fn (n lo hi type)
(defmacro nth-number-between (n lo hi &key type)
|#

(defdata one 1)

(defdata loi (listof int))
(defdata r1 (record (a . loi)))

(defdata data (listof nat))
(defdata receiver-state (record (received . data)))

(definec bax (rs :data) :receiver-state
  (receiver-state rs))

(property (rs :data)
  (receiver-statep (receiver-state rs)))

(property (rs :receiver-state a b c :all)
  (equal (mget :received (msets rs :received a :received b :received c))
         c))
         
(must-fail
 (defdata-alias r2 r1))

(must-succeed
 (test? (=> (^ (intp lo) (intp hi) (natp n) (<= lo hi))
            (^ (<= lo (geometric-int-between lo hi n))
               (>= hi (geometric-int-between lo hi n))))))

(must-succeed
 (test? (=> (^ (rationalp lo) (rationalp hi) (natp n) (<= lo hi))
            (^ (<= lo (geometric-rat-between lo hi n))
               (>= hi (geometric-rat-between lo hi n))))))

(must-succeed
 (test? (=> (^ (intp lo) (intp hi) (<= lo hi))
            (b* (((mv mid1 mid2) (defdata::int-midpoints lo hi)))
              (^ (<= lo mid1)
                 (>= hi mid2))))))

(must-succeed
 (test? (=> (^ (rationalp lo) (rationalp hi) (<= lo hi))
            (b* (((mv mid1 mid2) (defdata::rat-midpoints lo hi)))
              (^ (<= lo mid1)
                 (>= hi mid2))))))

(defdata receiver-state (record (received . data)))

(defdata value-type int)

(defdata read-request   (list 'READ-REQUEST))
(defdata read-response  (list 'READ-RESPONSE value-type))
(defdata write-request  (list 'WRITE-REQUEST value-type))
(defdata write-response (list 'WRITE-RESPONSE))
(defdata repl-request   (list 'REPL-REQUEST nat value-type))
(defdata repl-response  (list 'REPL-RESPONSE))

(defdata operation (oneof read-request read-response
                    write-request write-response
                    repl-request repl-response))

(check (operationp (list 'READ-REQUEST)))
(check (operationp (list 'READ-RESPONSE 1)))
(check (operationp (list 'WRITE-REQUEST 1)))
(check (operationp (list 'WRITE-RESPONSE)))
(check (operationp (list 'REPL-REQUEST 1 2)))
(check (operationp (list 'REPL-RESPONSE)))
(check (write-requestp '(write-request 3)))

(defdata name (map nat nat))

(defdata d2 (map loi loi))
(defdata lloi (listof loi))
(defdata d3 (map lloi lloi))
(defdata d4 (map loi lloi))
(defdata d5 (map lloi loi))

(defdata d6
  (record (a . loi)
          (b . int)
          (c . non-neg-rational)))

(defdata d7 (map d6 d6))

; If a recognizer is already defined, but the guard is not t, then
; throw an error.
(must-fail
  (defdata zero 0))

; An example where the recognizer is already defined.
(defun zeerop (x)
  (declare (xargs :guard t))
  (equal x 0))

(defdata zeero 0)

; If we then try to define zerop using the alias route, still fail,
; but due to constraining a symbol in the main Lisp package.
(must-fail
  (defdata zero 0))

(defun zeeerop (x)
  (declare (xargs :guard (acl2-numberp x)))
  (equal x 0))

; If we then try to define zeerop using the alias route, still fail
; because we try to define zeeerop as a macro 
(must-fail
  (defdata zeeero 0))

(defdata ds1 (enum '(1 2 3 1 2 3)))
(defdata ds2 (or 1 2 3 1 2 3))
(defdata ds3 (or 1 2 3 1 2 3 int))
(defdata ds4 1)
(defdata ds5 'x)
(defdata ds6 int)
(defdata ds7 (or 1 nil))

(check= (defdata-domain-size ds1) 3)
(check= (defdata-domain-size ds2) 3)
(check= (defdata-domain-size ds3) 'infinite)
(check= (defdata-domain-size ds4) 1)
(check= (defdata-domain-size ds5) 1)
(check= (defdata-domain-size ds6) 1)
(check= (defdata-domain-size ds7) 2)

(defdata ds8 (record (a . int) (b . tl)))

; Can prove equivalence of records
(property (x y :ds8)
  :h (^ (== (ds8-a x) (ds8-a y))
	(== (ds8-b x) (ds8-b y)))
  (== x y))
