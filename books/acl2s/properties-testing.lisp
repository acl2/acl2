#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

(in-package "ACL2S")
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags
              ((:ccg)) :load-compiled-file nil)
(include-book "acl2s/base-theory" :dir :system :ttags :all)
(include-book "acl2s/custom" :dir :system :ttags :all)

(acl2s-defaults :set cgen-single-test-timeout 0)

#|

|#

(property (n :nat)
  (booleanp (nth-boolean-builtin n)))

(property (n :nat)
  :proofs? nil
  (booleanp (nth-boolean-builtin n)))

(property (n :nat)
  :testing? nil
  (booleanp (nth-boolean-builtin n)))

(property (n :nat)
  :proofs? nil
  :testing? nil
  (booleanp (nth-boolean-builtin n)))

(property (n :nat)
  (natp (+ 1 n))
  :hints (("goal" :do-not '(preprocess))))

; Checks to make sure we deal with hints
(must-fail
  (property (n :nat)
    (natp (+ 1 n))
    :hints (("goal" :do-not '(pre--process))))) ;misspelled

#|

test? is set up to succeed even if errors occur, as long
as we don't find counterexamples.

It should be changed to check hint syntax and return
an error so that the properties below fail.

(must-fail
  (property (n :nat)
    :proofs? nil
    (natp (+ 1 n))
    :hints (("goal" :do-not '(pre--process))))) ;misspelled

(must-fail
  (property (n :nat)
    :proofs? nil
    :testing? nil
    (natp (+ 1 n))
    :hints (("goal" :do-not '(pre--process))))) ;misspelled
|#

(must-fail
  (property (n :nat)
    :testing? nil
    (natp (+ 1 n))
    :hints (("goal" :do-not '(pre--process))))) ;misspelled

(property (n :nat)
  (negp (nth-neg-builtin n)))

(property (n :nat)
  (non-pos-integerp (nth-non-pos-integer-builtin n)))

(property (n :nat)
  (non-0-integerp (nth-non-0-integer-builtin n)))

(property (n :nat)
  (integerp (nth-integer-builtin n)))

(property (n :nat lo hi :int)
  :h (<= lo hi)
  :b (and (integerp (nth-integer-between n lo hi))
          (<= lo (nth-integer-between n lo hi))
          (>= hi (nth-integer-between n lo hi))))

(property (n :nat)
  :check-contracts? nil
  :proofs? nil
  (pos-ratiop (nth-pos-ratio-builtin n)))

(property (n :nat)
  :check-contracts? nil
  :proofs? nil
  (neg-ratiop (nth-neg-ratio-builtin n)))

(property (n :nat)
  (neg-rationalp (nth-neg-rational-builtin n)))

(property (n :nat)
  (pos-rationalp (nth-pos-rational-builtin n)))

(property (n :nat)
  (non-neg-rationalp (nth-non-neg-rational-builtin n)))

(property (n :nat)
  (non-pos-rationalp (nth-non-pos-rational-builtin n)))

(property (n :nat)
  (non-0-rationalp (nth-non-0-rational-builtin n)))

(property (n :nat)
  (rationalp (nth-rational-builtin n)))

(property (n :nat lo hi :rational)
  :proofs? nil
  :h (<= lo hi)
  :b (and (rationalp (nth-rational-between n lo hi))
          (<= lo (nth-rational-between n lo hi))
          (>= hi (nth-rational-between n lo hi))))


(defdata one 1)

(defdata loi (listof int))
(defdata r1 (record (a . loi)))

(defdata data (listof nat))
(defdata receiver-state (record (received . data)))

(definec bax (rs :data) :receiver-state
  (receiver-state rs))

(property (lo hi :int n :nat)
  :check-contracts? nil
  :h (<= lo hi)
  :b (^ (<= lo (geometric-int-between lo hi n))
        (>= hi (geometric-int-between lo hi n))))

(property (lo hi :rational n :nat)
  :check-contracts? nil
  :h (<= lo hi)
  (^ (<= lo (geometric-rat-between lo hi n))
     (>= hi (geometric-rat-between lo hi n))))

(property (lo hi :int)
  :check-contracts? nil
  :test-contracts? nil
  :proofs? nil
  :h (<= lo hi)
  (b* (((mv mid1 mid2) (defdata::int-midpoints lo hi)))
    (^ (<= lo mid1)
       (>= hi mid2))))

(property (lo hi :rational)
  :check-contracts? nil
  :test-contracts? nil
  :h (<= lo hi)
  (b* (((mv mid1 mid2) (defdata::rat-midpoints lo hi)))
    (^ (<= lo mid1)
       (>= hi mid2))))
