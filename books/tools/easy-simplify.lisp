

(in-package "ACL2")

(include-book "bstar")

;; This provides a straightforward interface for simplifying a term.  It uses
;; the proof checker's pc-rewrite* function.  It can handle rewriting under
;; some hypotheses, under a user-provided equivalence relation, 


;; Note: replaced this with acl2's built-in expand-assumptions-1
;; (defun if-nest-to-hyp-list (x)
;;   (cond ((equal x ''t) nil)
;;         ((or (atom x)
;;              (not (eq (car x) 'if))
;;              (not (equal (fourth x) ''nil)))
;;          (list x))
;;         (t (append (if-nest-to-hyp-list (second x))
;;                    (if-nest-to-hyp-list (third x))))))


;; takes a translated term and an implicitly conjoined list of translated hyps
(defun easy-simplify-term1-fn (term hyps hints equiv
                              normalize rewrite
                              repeat
                              backchain-limit
                              state)
  (declare (XargS :mode :program :stobjs state))
  (b* ((world (w state))
       
       ((er hint-settings)
        (translate-hint-settings
         'simp-term "Goal" hints 'easy-simplify-term world state))
       (ens (ens state))
       (base-rcnst
        (change rewrite-constant
                *empty-rewrite-constant*
                :current-enabled-structure ens
                :force-info t))
       ((er rcnst)
        (load-hint-settings-into-rcnst
         hint-settings base-rcnst nil world 'easy-simplify-term state))
       (ens (access rewrite-constant rcnst :current-enabled-structure))
       ((mv flg hyps-type-alist ?ttree)
        (hyps-type-alist hyps ens world state))
       ((when flg)
        (mv "Contradiction in the hypotheses"
            nil state))
       ((mv ?step-limit new-term ?new-ttree state)
        (pc-rewrite*
         term hyps-type-alist
         (if (eq equiv 'equal)
             nil
           (list (make congruence-rule
                       :rune *fake-rune-for-anonymous-enabled-rule*
                       :nume nil
                       :equiv equiv)))
         (eq equiv 'iff)
         world rcnst nil nil normalize rewrite ens state
         repeat backchain-limit
         (initial-step-limit world state))))
    (value new-term)))

(defun easy-simplify-term-fn (term hyp-term hints equiv
                              normalize rewrite repeat backchain-limit state)
  (declare (XargS :mode :program :stobjs state))
  (b* ((world (w state))
       ((er trans-term)
        (translate term t nil t 'easy-simplify-term world state))
       ((er trans-hyp-term)
        (translate hyp-term t nil t 'easy-simplify-term world state))
       ;; ;; bozo find out how ACL2 does this, if it does
       ;; (hyps (if-nest-to-hyp-list trans-hyp-term))
       ;; ... like this:
       (hyps (expand-assumptions-1 trans-hyp-term))
       ((er new-term)
        (easy-simplify-term1-fn 
         trans-term hyps hints equiv normalize rewrite repeat backchain-limit
         state)))
    (value (untranslate new-term nil (w state)))))

(defmacro easy-simplify-term (term &key
                                   (hyp 't)
                                   hint
                                   (equiv 'equal)
                                   (normalize 't)
                                   (rewrite 't)
                                   (repeat '1000)
                                   (backchain-limit '1000))
  ":doc-section programming
 Easy-simplify-term:  simple interface for simplifying a term.~/

Usage:
~bv[]
 (easy-simplify-term (my-fn (foo) (bar baz))
                 ;; optional keyword args:
                 :hyp (and (integerp baz) (<= 0 baz))
                 :hint (:in-theory (enable my-fn) :expand ((foo)))
                 :equiv equal
                 :normalize t
                 :rewrite t
                 :repeat 555
                 :backchain-limit 5)
~ev[]

 Important NOTE: The HINT keyword should be given a hint keyword/val list,
 as in the example above, NOT a list of subgoal or computed hints,
 e.g. ((\"Goal\" :foo)). ~/

 Simplifies a term under the given hypothesis and equivalence context,
 with guidance from the given hint."
  `(easy-simplify-term-fn
    ',term ',hyp ',hint ',equiv
    ',normalize ',rewrite ',repeat ',backchain-limit
    state))
