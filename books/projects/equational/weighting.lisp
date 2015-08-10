;;
;; Utrecht Texas Equational Prover (UTEP) - Term Weighting Routines
;;
;; Written by Grant Olney Passmore {grant@math.utexas.edu}
;; Last updated on November 5th, 2006 by Grant in sleepy Utrecht.
;;
;; ** Note on Meta-level weighting **
;; Please note that the bulk most of these weighting routines are currently used for an
;; experimental meta-level interactive loop that uses weighting.  No time to go into
;; details now, but that's why for instance weight-term* is a macro.  For the normal
;; prover, all that's used at this point is (generic-weight ...) and the term-signature
;; processor.
;;

(in-package "ACL2")
(include-book "unification")

;; Essay - Weighting schemes
;;
;; We want to specify weighting schemes that are triggered through
;; a restricted form of unification.  As an example of the restrictions
;; we'd like to place, in a weighting assignment of (x 50), that is
;; what in Otter would be weight(x, 50), we want this to be interpreted
;; as assigning a weight of 50 to every *variable* in a term, not
;; just anything that could be unified with `x' (which would be everything).
;; This adds a bit of complexity to the weighting computations, but is
;; much more effective in proof search.
;;
;; ** I've found a nice compromise with the above declaration.  Instead of
;;    allowing `(x 1)' as a weighting scheme, we instead have a configuration
;;    value `RAW-VAR-WEIGHT' which is given to variables that appear in terms.
;;    This way, we can still use straight unification in the obvious fashion
;;    to match and then instantiate weighting schemes and functions (resp.).
;;
;; Examples of some weighting schemes we'd like to support (as in Otter p14):
;;
;;  ((e) 0)                      - The constant (e) is assigned a weight of 0.
;;  ((f x) ($- ($* 2 ($ x)) 50)) - The weight of (f x) is twice the weight of
;;                                 the parameter x minus 50.
;;
;; ** Please note that if a variable appears in a weighting scheme, it must
;;    be wrapped with `$'.  That is, if `x' is to be in a weighting scheme,
;;    it must appear as `($ x).
;;
;; An example term: (f (e) w)
;; An example weighting scheme: ( ((e) 5)
;;                                ((f x y) ($+ 10 ($* ($ x) 2) ($ y))) )
;; This should evaluate to:
;;  weight( (f (e) w) ) = ($+ 10 ($* ($ (e)) 2) ($ w))
;;                      = ($+ 10 ($* 5 2) ($ w))
;;                      = ($+ 10 10 1)               { by default, every symbol has a weight of 1 }
;;                      = 21.

;;
;; Now, we try the example in practice:
;;
;; ACL2 !>(weight-term* '(f (e) w) '( ((e) 5) ((f x y) ($+ 10 ($* 2 ($ x) ) ($ y))) ) nil nil)
;; 21
;;
;; Nice!
;; ***
;;
;; Another example:
;;
;; ACL2 !>(weight-term* '(f x) '( ((f x) ($+ ($+ 5 10 ($* 3 ($- 0 ($ x)))) 90)) ) nil nil)
;; 102
;;
;; Beautiful!
;; ***
;;
;; * Note that the only caveat I know of is one shouldn't use ($- foo) for -foo; just
;;   use ($- 0 foo) instead.
;;

;;
;; A-list for mapping weighting combinators to ACL2 arithmetic.
;; Add more arithmetic functions here (using the convention of
;; prepending the function symbol with '$' so as to keep it from
;; trapping when users use the normal arithmetic function symbols
;; in their clauses).
;;

(defconst *wfc-map*
  '( ($+ +) ($- -) ($* *) ($/ /)))

;;
;; If there's a matching weighting scheme for our term,
;; find it and instantiate it (via mgu).
;;

(defun find-matching-scheme (term weight-schema)
  (cond ((endp weight-schema) nil)
	(t (let ((cur-wterm-trigger (caar weight-schema))
		 (cur-wterm-function (cadar weight-schema)))
	     ;; Note: We have to standardize-apart the term and the possibly
	     ;;  matching weight-schema here.
	     (mv-let (ut mgu) (unify (car (standardize-apart cur-wterm-trigger (list term)))
				     cur-wterm-trigger)
		     (cond ((equal ut 'DNU)
			    (find-matching-scheme term (cdr weight-schema)))
			   (t (apply-unifier cur-wterm-function mgu))))))))

;;
;; Variables are given `RAW-VAR-WEIGHT' value as discussed
;; in the prelude of this file.  To make things simpler, we assume that
;; the function calling weight-term has looked-up and passed these
;; configuration values to us.
;;

;;
;; This function constructs a signature tree for a given term, differentiating
;; only between functions and variables.
;;
;; Example:
;; ACL2 !>(gw-term-signature '(f (e x y (g (e) z) x)))
;; (FCN (FCN VAR VAR (FCN (FCN) VAR) VAR))
;;

(defun gw-term-signature* (x cur-fcn-arity+1)
  (cond ((endp x) nil)
	((consp (car x)) (cons (append '(FCN) (gw-term-signature* (cdar x) (len (car x))))
			       (gw-term-signature* (cdr x) cur-fcn-arity+1)))
	((and (consp x) (equal (len x) cur-fcn-arity+1))
	 (append '(FCN) (gw-term-signature* (cdr x) cur-fcn-arity+1)))
	((and (consp x) (< (len x) cur-fcn-arity+1))
	 (append '(VAR) (gw-term-signature* (cdr x) cur-fcn-arity+1)))))

(defun gw-term-signature (x)
  (gw-term-signature* x (len x)))

;;
;; Given a term and a raw universal weight on variables as described above,
;; we construct a generic weighting of the term using the generators:
;;
;;  (wt VAR) := RAW-VAR-WEIGHT,
;;  (wt (FCN t_0 ... t_{n-1})) := 1 + wt(t_0) + ... + wt(t_{n-1}).
;;
;; We do this by iterating over the term-signature constructed above.
;; This is needlessly expensive, as it requires an extra linear pass over
;; the term tree, whereas only a single linear pass is truly needed as
;; in gw-term-signature* above.  This is done for stylistic reasons at
;; the moment, but may be changed in the future if this expense is noticable
;; in practice.
;;

(defun generic-weight* (term-sig raw-var-weight)
  (cond ((equal term-sig 'FCN) 1)
	((equal term-sig 'VAR) raw-var-weight)
	((endp term-sig) 0)
	(t (+ (generic-weight* (car term-sig) raw-var-weight)
	      (generic-weight* (cdr term-sig) raw-var-weight)))))

(defun generic-weight (term raw-var-weight)
  (generic-weight* (gw-term-signature term) raw-var-weight))

(defun generic-clause-weight (clause raw-var-weight)
  (cond ((endp clause) 0)
	(t (+ (generic-weight (car clause) raw-var-weight)
	   (generic-clause-weight (cdr clause) raw-var-weight)))))

;;
;; An adjusted find-matching-scheme wrapper that will return a raw weight
;; if a trigger isn't found.
;;

(defun find-matching-scheme* (term weight-schema prover-settings)
  (cond ((varp term) (if (acl2-numberp (get-setting prover-settings 'raw-var-weight))
			 (get-setting prover-settings 'raw-var-weight)
			 1))
	((acl2-numberp term) term)
	(t (let ((wf-instance (find-matching-scheme term weight-schema)))
	     (cond ((equal wf-instance nil)
		    (generic-weight term (fix (get-setting prover-settings 'raw-var-weight))))
		   (t wf-instance))))))

;;
;; This wrapper function does most of the rewriting so that our macro can act as a
;; restricted EVAL function.  Pretty slick! :)
;;

(defun annotate-wf-instance (wf-instance prover-settings in-f-scope weight-schema)
  (cond ((acl2-numberp wf-instance) wf-instance)
	((or (endp wf-instance) (endp (cdr wf-instance)))
	 (case in-f-scope ('+ 0) ('- 0) ('* 1) ('/ 1) (nil nil)))
	((equal (car wf-instance) '$) ; Note that '$'s will never be nested.
	 (append '(weight-term*) (append (list (list* 'quote (cdr wf-instance)))
					 (list (list* 'quote (list weight-schema)))
					 (list (list* 'quote (list prover-settings)))
					 (list (list* 'quote (list in-f-scope))))))
	((and (member (car wf-instance) '($+ $- $* $/)) (consp (cdr wf-instance)))
	 (list (cadr (assoc (car wf-instance) *wfc-map*))
	       (annotate-wf-instance (cadr wf-instance) prover-settings
				     (cadr (assoc (car wf-instance) *wfc-map*))
				     weight-schema)
	       (annotate-wf-instance (list* (car wf-instance) (cddr wf-instance)) prover-settings
				     (cadr (assoc (car wf-instance) *wfc-map*)) weight-schema)))
	((varp (car wf-instance)) (nfix (get-setting prover-settings 'raw-var-weight)))
	(in-f-scope (list in-f-scope
			  (annotate-wf-instance (car wf-instance) prover-settings nil weight-schema)
			  (annotate-wf-instance (cdr wf-instance) prover-settings in-f-scope weight-schema)))
	(t (generic-weight wf-instance (get-setting prover-settings 'raw-var-weight)))))


(defmacro weight-term* (term weight-schema prover-settings in-f-scope)
   (annotate-wf-instance (find-matching-scheme* (unquote term) (unquote weight-schema)
						(unquote prover-settings))
			 (unquote prover-settings)
			 (unquote in-f-scope)
			 (unquote weight-schema)))

;;
;; Filter out clauses that are too heavy, using our current weighting schemas.
;;
;; Currently weight-schema is ignored and generic weighting is done instead.
;;

(defun filter-out-heavy-clauses (moves max-clause-weight)
  (cond ((endp moves) nil)
	(t (let ((cur-move (extract-clause (car moves))))
	     (cond ((<= (generic-clause-weight cur-move 2) max-clause-weight)
		    (cons (car moves)
			  (filter-out-heavy-clauses (cdr moves) max-clause-weight)))
		   (t (filter-out-heavy-clauses (cdr moves) max-clause-weight)))))))

