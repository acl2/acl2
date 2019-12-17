
(in-package "RP")

(include-book "../eval-functions")


(defthmd rp-evl-of-ex-from-rp
  (equal (rp-evl (ex-from-rp term) a)
         (rp-evl term a))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-rp) ()))))

(defthmd is-rp-implies-fc
  (implies (is-rp term)
           (CASE-MATCH TERM
             (('RP ('QUOTE TYPE) &)
              (AND (SYMBOLP TYPE)
                   (NOT (BOOLEANP TYPE))
                   (NOT (EQUAL TYPE 'QUOTE))
                   (NOT (EQUAL TYPE 'RP))))
             (& NIL)))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthmd is-if-implies-fc
  (implies (is-if term)
           (CASE-MATCH TERM (('IF & & &) T)
                                   (& NIL)))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (is-if) ()))))



(defthm rp-evlt-of-ex-from-rp
  (EQUAL (RP-EVL (RP-TRANS (EX-FROM-RP TERM)) A)
         (RP-EVL (RP-TRANS TERM) A))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-rp) ()))))

(encapsulate
  nil
  (local
   (defthm valid-sc-single-step-lemma
     (implies (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                            A)
              (EQUAL (VALID-SC (EX-FROM-RP term) A)
                     (VALID-SC term A)))
     :hints (("Goal"
              :in-theory (e/d (is-if
                               is-rp) ())))))

  (local
   (defthm valid-sc-single-step-lemma2
     (implies (and (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL) A)
                   (IS-RP TERM))
              (EVAL-AND-ALL (CONTEXT-FROM-RP (CADDR TERM) NIL) A))
     :hints (("Goal"
              :in-theory (e/d (is-if
                               eval-and-all
                               context-from-rp
                               is-rp) ())))))

  (local
   (defthm valid-sc-single-step-lemma3-lemma
     (implies (not (equal fnc 'quote))
              (equal (RP-EVLt (LIST fnc (EX-FROM-RP term)) A)
                     (RP-EVLt (LIST fnc term) A)))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (is-if
                               rp-evl-of-ex-from-rp
                               eval-and-all
                               rp-evl-of-fncall-args
                               is-rp) ())))))

  (local
   (defthm valid-sc-single-step-lemma3
     (implies (and (IS-RP TERM)
                   (NOT (RP-EVLt (LIST (CADR (CADR TERM)) (CADDR TERM)) A)))
              (not (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL) A)))
     :hints (("Goal"
              :do-not-induct t
              :expand (CONTEXT-FROM-RP TERM NIL)
              :in-theory (e/d (is-if
                               eval-and-all
                               rp-evl-of-fncall-args
                               is-rp) ())))))

  (local
   (defthm valid-sc-single-step-lemma4
     (implies (and (IS-RP TERM)
                   (NOT (RP-EVLt (LIST (CADR (CADR TERM)) (CADDR TERM)) A)))
              (not (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL) A)))
     :hints (("Goal"
              :do-not-induct t
              :expand (CONTEXT-FROM-RP TERM NIL)
              :in-theory (e/d (is-if
                               rp-evl-of-fncall-args
                               eval-and-all
                               is-rp) ())))))

  (local
   (defthm valid-sc-single-step-lemma5
     (implies (and (RP-EVLt (LIST (CADR (CADR TERM)) (CADDR TERM))
                           A)
                   (IS-RP TERM)
                   (NOT (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                      A)))
              (NOT (EVAL-AND-ALL (CONTEXT-FROM-RP (caddr TERM) NIL)
                                 A)))
     :hints (("Goal"
              :in-theory (e/d (is-rp eval-and-all
                                     rp-evl-of-fncall-args
                                     context-from-rp) ())))))

  (local
   (defthm valid-sc-single-step-lemma6
     (implies (and (NOT (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                      A)))
              (NOT (VALID-SC term A)))
     :hints (("Goal"
              :in-theory (e/d (is-rp eval-and-all
                                     is-if
                                     context-from-rp) ())))))

  (defthmd valid-sc-single-step
    (implies (and ;(rp-termp term)
                  (is-rp term))
             (equal (valid-sc term a)
                    (and (rp-evlt `(,(cadr (cadr term)) ,(caddr term))  a)
                         (valid-sc (caddr term) a))))
    :hints (("Goal"
             :do-not-induct t
             :expand ((VALID-SC TERM A))
             :in-theory (e/d (is-rp-implies-fc
                              is-if-implies-fc)
                             ())))))


(defthm valid-sc-of-ex-from-rp
  (implies (valid-sc term a)
           (valid-sc (ex-from-rp term) a))
  :hints (("Goal"
;:induct (ex-from-rp-loose term)
           :in-theory (e/d (valid-sc
                            is-rp
                            is-if
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm valid-sc-cadr
  (IMPLIES (AND
            (CONSP term)
            (Not (EQUAL (CAR term) 'if))
            (Not (EQUAL (CAR term) 'rp))
            (Not (EQUAL (CAR term) 'quote))
            (CONSP (CDR term))
            (VALID-SC TERM A))
           (VALID-SC (CADR term) A))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-if
                            is-rp) ()))))

(defthm valid-sc-caddr
  (IMPLIES (AND
            (CONSP term)
            (Not (EQUAL (CAR term) 'if))
            (Not (EQUAL (CAR term) 'rp))
            (Not (EQUAL (CAR term) 'quote))
            (CONSP (CDR term))
            (CONSP (CDdR term))
            (VALID-SC TERM A))
           (VALID-SC (CADdR term) A))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-if
                            is-rp) ()))))

(defthm valid-sc-cadddr
  (IMPLIES (AND
            (CONSP term)
            (Not (EQUAL (CAR term) 'if))
            (Not (EQUAL (CAR term) 'rp))
            (Not (EQUAL (CAR term) 'quote))
            (CONSP (CDR term))
            (CONSP (CDdR term))
            (CONSP (CDddR term))
            (VALID-SC TERM A))
           (VALID-SC (CAdDdR term) A))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-if
                            is-rp) ()))))

(defthm eval-and-all-nil
  (EVAL-AND-ALL NIL A))


(defthm-rp-trans
  (defthm rp-trans-is-term-when-list-is-absent
    (implies (not (include-fnc term 'list))
             (equal (rp-evl (rp-trans term) a)
                    (rp-evl term a)))
    :flag rp-trans)
  (defthm rp-trans-lst-is-lst-when-list-is-absent
    (implies (not (include-fnc-subterms lst 'list))
             (equal (rp-evl-lst (rp-trans-lst lst) a)
                    (rp-evl-lst lst a)))
    :flag rp-trans-lst)
  :hints (("Goal"
           :in-theory (e/d (rp-evl-of-fncall-args) ()))))
