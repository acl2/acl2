;; Assumes that acl2s-interface has already been loaded
(load "conditions.lsp")
(load "prop-skel.lsp")
(in-package :tp)

(import 'prover::checker-error)
(import 'prover::defcond)
(import 'acl2s-interface::acl2s-query)

(defcond bijection-error checker-error
  (partial-bijection unused-fs unused-gs unused-f-idxs unused-g-idxs partial-bijection-idxs)
  ("Couldn't find a bijection between the elements in these lists:~%~a~%and~%~a~%But was able to find a partial bijection:~%~a" unused-fs unused-gs partial-bijection))

;; The code which generates induction proof obligations ends up
;; calling remove-guard-holders on something at some point. This
;; function performs some simplifications to forms; in particular it
;; turns unary-/ of a constant into a constant fraction.
;; This function should do something equivalent to that normalization.
(defun normalize-expr (f)
  (let ((res (acl2s-query
              `acl2s::(b* ((wrld (w state))
                           ((er tf) (acl2::translate ',tp::f t t t 'ctx wrld state))
                           (tf-without-guards (acl2::remove-guard-holders tf wrld)))
                          (mv nil (acl2::untranslate tf-without-guards nil wrld) state)))))
    (if (car res)
        (error "failed to normalize expression ~S" f)
      (second res))))

(assert (equal (normalize-expr '(/ x 3))
               '(* x 1/3)))

(assert (equal (normalize-expr '(/ 3 x))
               '(* 3 (/ x))))

;; Determine the propositional skeleton of a list of forms.
;; This is useful because it will assign the same symbol to identical
;; function calls. It does this by threading the map between added
;; symbols and function calls that p-skeleton produces through each
;; call to p-skeleton.
(defun p-skeletons (forms &optional (map nil) (abstract-termp #'(lambda (x) (declare (ignore x)) t)))
  (if (endp forms)
      (values nil map)
    (multiple-value-bind
        (res newmap)
        (p-skeleton- (car forms) map abstract-termp)
      (multiple-value-bind (cdrskels cdrmap)
          (p-skeletons (cdr forms) newmap abstract-termp)
        (values (cons res cdrskels) cdrmap)))))

;; Note that (foo a b) gets assigned the same new symbol in both
;; expressions
(assert
 (multiple-value-bind
     (res map)
     (p-skeletons '((and (foo a b) c)
                    (and d e (foo a b))))
   (equal res `((and ,(cdar map) c)
                (and d e ,(cdar map))))))

;; We define 2 versions of prop-equiv, prop-equiv-pairwise, and
;; prop-equiv-bijection: one that performs normalization of its
;; arguments, and one which does not and expects that its arguments
;; are already normalized.

;; This is for performance, particularly for prop-equiv-bijection
;; which has time complexity polynomial in the lengths of its input
;; arguments.

;; When in doubt, use the normal version of the function (i.e. the one
;; without no-normalize)

(declaim (ftype (function (t t) boolean) prop-equiv-no-normalize))
(defun prop-equiv-no-normalize (f g)
  (let ((skeletons (p-skeletons (list f g))))
    (not (car (acl2s-check-equal (first skeletons) (second skeletons))))))

(declaim (ftype (function (t t) boolean) prop-equiv))
(defun prop-equiv (f g)
  (prop-equiv-no-normalize (normalize-expr f) (normalize-expr g)))

(assert (prop-equiv t t))
(assert (not (prop-equiv t nil)))
(assert (prop-equiv 'x 'x))
(assert (not (prop-equiv 'x 'y)))
(assert (prop-equiv 'acl2::(iff x y) 'acl2::(and (implies x y) (implies y x))))
;; negate and swap
(assert (prop-equiv 'acl2::(implies (and x y) z) 'acl2::(implies (and x (not z)) (not y))))
(assert (not (prop-equiv 'acl2::(implies (and x y) z) 'acl2::(implies x z))))
(assert (not (prop-equiv 'acl2::(implies (and x (implies y z)) w) 'acl2::(implies (and x y z) w))))
;; ensuring it works with arbitrary functions
;; note that we use no-normalize here, because normalization chokes on
;; undefined functions
(assert (prop-equiv-no-normalize 'acl2::(implies (foo x y) (implies (baz y z) q))
                                 'acl2::(implies (and (foo x y) (baz y z)) q)))

(declaim (ftype (function (list list) boolean) prop-equiv-pairwise-no-normalize))
(defun prop-equiv-pairwise-no-normalize (fs gs)
  (cond ((and (endp fs) (endp gs)) t)
        ((or (endp fs) (endp gs)) nil)
        ((prop-equiv-no-normalize (car fs) (car gs))
         (prop-equiv-pairwise-no-normalize (cdr fs) (cdr gs)))
        (t nil)))

(declaim (ftype (function (list list) boolean) prop-equiv-pairwise))
(defun prop-equiv-pairwise (fs gs)
  (prop-equiv-pairwise-no-normalize
   (mapcar #'normalize-expr fs)
   (mapcar #'normalize-expr gs)))

(assert (prop-equiv-pairwise nil nil))
(assert (prop-equiv-pairwise '(t nil) '(t nil)))
(assert (not (prop-equiv-pairwise '(x y z) '(y x z))))

;; Remove a single occurrence of a value from a list
(declaim (ftype (function (t list) list) remove-one))
(defun remove-one (a l)
  (cond ((endp l) nil)
        ((equal a (car l)) (cdr l))
        (t (cons (car l) (remove-one a (cdr l))))))

(defun prop-equiv-bijection-helper-no-normalize (assoc-f assoc-gs)
  (cond ((endp assoc-gs) nil)
        ((prop-equiv-no-normalize (cdr assoc-f) (cdar assoc-gs)) (car assoc-gs))
        (t (prop-equiv-bijection-helper-no-normalize assoc-f (cdr assoc-gs)))))

(declaim (ftype (function (list list &optional list list list) list) prop-equiv-bijection-no-normalize))
(defun prop-equiv-bijection-no-normalize (assoc-fs assoc-gs &optional (bijection nil) (unused-fs nil) (unused-gs nil))
  (cond
   ((and (endp assoc-fs) (endp assoc-gs) (endp unused-fs) (endp unused-gs)) ;; we used all fs and gs, so we found a bijection.
    (reverse bijection))
   ((or (endp assoc-fs) (endp assoc-gs)) ;; at least one f or g was unused, so we couldn't find a bijection
    (error 'bijection-error
           :partial-bijection (reverse bijection)
           :unused-fs (append assoc-fs unused-fs)
           :unused-gs (append assoc-gs unused-gs)))
   (t (let ((matching-g (prop-equiv-bijection-helper-no-normalize (car assoc-fs) assoc-gs)))
        (if matching-g
            (prop-equiv-bijection-no-normalize
             (cdr assoc-fs)
             (remove-one matching-g assoc-gs)
             (cons (list (car assoc-fs) matching-g) bijection)
             unused-fs
             unused-gs)
          (prop-equiv-bijection-no-normalize
           (cdr assoc-fs)
           assoc-gs
           bijection
           (cons (car assoc-fs) unused-fs)
           unused-gs))))))

;; Produce a new alist where the cons of each pair is the same, and
;; the cdr of each pair is the result of evaluating f on the original cdr
(defun map-alist-cdr (f l)
  (mapcar (lambda (e) (cons (car e) (funcall f (cdr e)))) l))

;; Turn an index-tagged bijection (an alist where both keys and values are cons pairs (index . expression)
;; into a bijection containing just the indices
(defun alist-bij-to-idx-bij (bijection)
  (mapcar #'(lambda (assoc) (cons (caar assoc) (caadr assoc))) bijection))

;; Call assoc on alist for each element of keys
(defun assocs (keys alist)
  (mapcar (lambda (key) (assoc key alist)) keys))

;;(declaim (ftype (function (list list) (values list list)) prop-equiv-bijection))
(declaim (ftype (function (list list) list) prop-equiv-bijection))
(defun prop-equiv-bijection (fs gs)
  (let* ((indexed-fs (make-index-alist fs))
         (indexed-gs (make-index-alist gs))
         (normalized-indexed-fs (map-alist-cdr #'normalize-expr indexed-fs))
         (normalized-indexed-gs (map-alist-cdr #'normalize-expr indexed-gs)))
    (handler-case
        (prop-equiv-bijection-no-normalize
         normalized-indexed-fs
         normalized-indexed-gs)
      (bijection-error (c)
                       (let ((bij-idxs (alist-bij-to-idx-bij (bijection-error/partial-bijection c))))
                         (error 'bijection-error
                                :partial-bijection (mapcar (lambda (pair) (list (cdr (assoc (car pair) indexed-fs))
                                                                                (cdr (assoc (cdr pair) indexed-gs))))
                                                           bij-idxs)
                                :partial-bijection-idxs bij-idxs
                                :unused-fs (mapcar #'cdr (assocs (mapcar #'car (bijection-error/unused-fs c)) indexed-fs))
                                :unused-gs (mapcar #'cdr (assocs (mapcar #'car (bijection-error/unused-gs c)) indexed-gs))
                                :unused-f-idxs (mapcar #'car (bijection-error/unused-fs c))
                                :unused-g-idxs (mapcar #'car (bijection-error/unused-gs c)))))
      (:no-error (bijection)
                 (let ((bij-idxs (alist-bij-to-idx-bij bijection)))
                   (values (mapcar #'(lambda (pair) (list (cdr (assoc (car pair) indexed-fs))
                                                          (cdr (assoc (cdr pair) indexed-gs))))
                                   bij-idxs)
                           bij-idxs))))))

(defmacro assert-error (stmt)
  `(handler-case ,stmt
     (error (_) t)
     (:no-error (_) nil)))

;; Generates a list of the first n natural numbers
(defun firstn (hi)
  (loop for n below hi collect n))

;; Given a list, produce an alist where each element of the list is
;; associated with its index (0-indexed)
(defun make-index-alist (l)
  (mapcar #'cons (firstn (length l)) l))

(assert (equal (prop-equiv-bijection nil nil) nil))
(assert (equal (prop-equiv-bijection '(x y z) '(x y z))
               '((x x) (y y) (z z))))
(assert-error (prop-equiv-bijection '(x y z) '(x y)))
(assert (equal (prop-equiv-bijection '(x x y) '(x y x))
               '((x x) (x x) (y y))))
