(in-package "ACL2")
(include-book "bcv-model")
(include-book "bcv-simple-model")


(defthm extract-code-wff-code1-same
  (implies (wff-code1 code pc)
           (equal (extract-code (append code '(END_OF_CODE)))
                  code)))


(defthm |s-same-g-lemma|
  (IMPLIES (AND (EQUAL (G 'IS-INST INST) T)
                (NOT (G 'IS-STACK-MAP INST)))
           (EQUAL (S 'IS-INST
                     T (S 'IS-STACK-MAP NIL INST))
                  INST))
  :hints (("Goal" :in-theory (disable s-same-g)
           :use ((:instance S-SAME-G
                            (a 'is-inst) 
                            (R (s 'is-stack-map nil inst)))
                 (:instance S-SAME-G
                            (a 'is-stack-map)
                            (R inst))))))


(defthm inst-implies-make-inst-same
  (implies (inst? inst)
           (equal (make-inst inst) inst))
  :hints (("Goal" :in-theory (enable inst? make-inst))))


(defthm extract-code-mergeStackMapAndCode
  (implies (and (equal (car (last (mergeStackMapAndCode maps code method-name method-table)))
                       'END_OF_CODE)
                (wff-code1 code pc))
           (equal (extract-code (mergeStackMapAndCode maps code method-name method-table))
                  code))
  :hints (("Goal" :in-theory (enable inst?))))

(defthm not-inst-end-of-code
  (not (inst? 'END_OF_CODE)))

(defthm get-is-inst-make-inst
  (g 'is-inst (make-inst inst))
  :hints (("Goal" :in-theory (enable make-inst))))

(defthm make-inst-inst
  (implies (inst? inst)
           (inst? (make-inst inst)))
  :hints (("Goal" :in-theory (enable make-inst inst?))))

(defthm g-end-of-code
  (not (g 'is-inst 'END_OF_CODE)))

(defthm make-inst-never-end-of-code
  (not (equal (make-inst inst) 'END_OF_CODE))
  :hints (("Goal" :in-theory (disable make-inst
                                      get-is-inst-make-inst
                                      g-end-of-code)
           :use ((:instance get-is-inst-make-inst)
                 (:instance g-end-of-code)))))


