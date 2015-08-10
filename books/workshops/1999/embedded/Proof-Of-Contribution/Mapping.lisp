;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Section 3: Recognizer for Gem-to-Rtm variable mapping
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; According to the fact that the verifier operates over a black-box Gem2Rtm compiler,
;;; we do not provide a constructive definition of a variable mapping between two programs.
;;;
;;; Rather, we recognize an object to be a mapping if it obeys a set of properties.
;;;
;;; The properties are the following:
;;;
;;; - A mapping must be an associative list, where the key to each entry is a Gem variable address,
;;;   and the content is either an Rtm variable address, or a tuple of Rtm variable addresses. We say
;;;   that the entries of such associative list have the following `type':
;;;   - 'Bool if the number of Rtm addresses is 1
;;;   - 'Int if the number of Rtm addresses is |rns|
;;;
;;; - A mapping must feature a correct arity for each entry w.r.t. the Gem and Rtm memories if maps:
;;;   - it must map one Gem boolean to one Rtm variable, and
;;;   - it must map one Gem integer to |rns| Rtm variables
;;;
;;; - A mapping must not contain duplicate Gem variables
;;;
;;; A similar property to the last one must hold for the Rtm variables featured by a mapping. I.e.,
;;; no Rtm duplicates are allowed. We shall insert such property later on, when
;;; they will be necessary (e.g. when proving properties about translations of
;;; Gem instructions).
;;;




;;;
;;; Subsection 3.1 :
;;;
;;; Accessors on the elements of a mapping:
;;;
;;; (gemvar-0 m)      retrieves the gem variable of the first entry of the mapping
;;; (rtmboolvar-0 m)  retrieves the rtm variable of the first entry of the mapping
;;;                   (supposed to be related to a boolean gem variable)
;;; (rtmintvars-0 m)  retrieves the rtm variables of the first entry of the mapping
;;;                   (supposed to be related to an integer gem variable)
;;; (gemvar-i m)      retrieves the gem variable of the i-th entry of the mapping
;;; (rtmboolvar-i m)  retrieves the rtm variable of the i-th entry of the mapping
;;;                   (supposed to be related to a boolean gem variable)
;;; (rtmintvars-i m)  retrieves the rtm variables of the i-th entry of the mapping
;;;                   (supposed to be related to an integer gem variable)
;;;
;;;

(in-package "ACL2")


;; PGNEW

(include-book "Generic")

(include-book "Memory-Assoc")

(defun gemvar-0 (m)
 (car (car m)))


(defun rtmintvars-0 (m)
 (cdr (car m)))

;;;
;;; Recognizers for entries of a mapping:
;;;

(defun type-0 (m)
 (cond
  ( (and
     (true-listp (rtmintvars-0 m))
     (equal (len (rtmintvars-0 m)) 1))
    'bool)
  ( (and
     (true-listp (rtmintvars-0 m))
     (equal (len (rtmintvars-0 m)) (len *rns*)))
    'int)
  ( t
    'wrong-typing)))


(defun correct-type (type)
 (or
  (equal type 'int)
  (equal type 'bool)))

















