; This book was produced by Claude and passed along by Eric Smith.  It
; illustrates a soundness bug in ACL2 Version 8.7 fixed before ACL2 Version
; 8.8.

; Finding 49: (:GUARD-THEOREM f) hands the user a formula to ASSUME that is not a
; theorem.  Third consumer of Finding 46's root cause, and the one where the
; failing direction is exactly what the user relies on.
;
; Writing segs = clausify(not guard) and O for the body's guard obligations,
; guard-clauses-for-fn1 (history-management.lisp:14247-14252) emits {seg_i or O},
; whose conjunction is (and segs) or O.
;   * verify-guards must PROVE that set; soundness needs (and segs) => not guard,
;     which is the direction clausify guarantees.  Sound.
;   * guard-theorem (history-management.lisp:14549, reached from translate-lmi's
;     :guard-theorem case at :14831) hands the same set to the user to ASSUME;
;     validity needs not guard => (and segs), the FAILING direction.  Since
;     clausify can be strictly stronger, the handed-out formula can be false.
;
; NOTE FOR THE FIX: the damage is done inside clausify, BEFORE clean-up-clause-set.
; (guard-theorem f :limited) and (guard-theorem f nil) are byte-identical on this
; witness, so changing or removing guard-theorem's simplify argument does NOT fix
; this, and neither does fixing clean-up-clause-set.  The repair that closes
; Findings 46 and 49 together is in convert-assumptions-to-clause-segment
; (rewrite.lisp:3366): build the segment with add-literal instead of plain cons.
;
; The guard here is genuinely SATISFIABLE and genuinely FALSE at the exploit point
; -- both are proved below rather than asserted, so this is not a vacuous-guard
; artifact.  verify-guards succeeds honestly.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun sat-g (a b c d)
  (declare (xargs :guard
                  (and (consp a)
                       (if (not (not (not (consp a))))
                           (not (if (not (consp a)) nil (if b c b)))
                         (not (if d (if (consp a) b (consp a))
                                (if b (consp a) nil)))))
                  :verify-guards t)
           (ignorable b c d))
  (car a))

; The guard as an ordinary function, so it can be reasoned about directly.
(defun gexpr (a b c d)
  (declare (xargs :guard t) (ignorable b c d))
  (and (consp a)
       (if (not (not (not (consp a))))
           (not (if (not (consp a)) nil (if b c b)))
         (not (if d (if (consp a) b (consp a))
                (if b (consp a) nil))))))

; NON-VACUITY, both directions, proved rather than asserted:
(defthm guard-is-satisfiable        (gexpr '(1) nil nil nil) :rule-classes nil)
(defthm guard-false-at-exploit-pt   (not (gexpr 17 nil nil t)) :rule-classes nil)

; THE DEFECT: the handed-out guard theorem is false at a=17, b=nil, d=t.
(must-fail
 (local (defthm proof-of-nil-gt
          nil
          :hints (("Goal" :use (:instance (:guard-theorem sat-g)
                                          (a 17) (b nil) (d t))))
          :rule-classes nil)))

; CONTROL -- the same shape WITHOUT the double negation must keep working, so the
; fix is not simply "disable :guard-theorem".
(defun plain-g (a)
  (declare (xargs :guard (consp a) :verify-guards t))
  (car a))
(defthm plain-guard-theorem-is-usable
  (implies (consp a) (consp a))
  :hints (("Goal" :use (:guard-theorem plain-g)))
  :rule-classes nil)
