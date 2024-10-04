(in-package "ACL2")
(include-book "bcv-model")
(include-book "generic")


;; (encapsulate () 
;;    (local (include-book "bcv-find-correct-witness-sig-vector-1"))
;;    (defthm verified-implies-partial-sig-vector-compatible-with-full-vector-lemma
;;    (implies (and (merged-code-safe merged-code init-frame)
;;                  (consp (cdr merged-code))
;;                  (wff-code1 (extract-code merged-code)
;;                             (g 'pc (car merged-code)))
;;                  (member stack-map merged-code)
;;                  (or (stack-map? init-frame)
;;                      (equal init-frame 'aftergoto))
;;                  (stack-map? stack-map)
;;                  (equal (g 'pc stack-map) pc))
;;             (sig-frame-compatible 
;;              stack-map
;;              (cdr (assoc-equal pc (collect-witness-merged-code-safe 


;; (defthm verified-extract-bound-partial-then-equal-bound-full
;;   (implies (and (merged-code-safe merged-code init-frame)
;;                 (bound? pc (extract-partial-sig-vector 
;;                             (extract-maps merged-code))))
;;            (equal (cdr (assoc-equal pc (collect-witness-merged-code-safe
;;                                         merged-code init-frame)))
;;                   (cdr (assoc-equal pc (extract-partial-sig-vector 
;;                                         (extract-maps merged-code))))))
;;   :hints (("Goal" :in-theory 

;;;
;;; this is not true. because it is possible to have multiple map at the same
;;; location!!
;;; 
;;; In that case the extract-partial-sig-vector returns the first one
;;; (binding ... (collect-witness-merged-code-safe ...)) return the last one!!




(encapsulate () 
   (local (include-book "bcv-find-correct-witness-sig-vector-1"))
   (defthm verified-implies-partial-sig-vector-compatible-with-full-vector-lemma
   (implies (and (merged-code-safe merged-code init-frame)
                 (consp (cdr merged-code))
                 (wff-code1 (extract-code merged-code)
                            (g 'pc (car merged-code)))
                 (member stack-map merged-code)
                 (or (stack-map? init-frame)
                     (equal init-frame 'aftergoto))
                 (stack-map? stack-map)
                 (equal (g 'pc stack-map) pc))
            (sig-frame-compatible 
             stack-map
             (cdr (assoc-equal pc (collect-witness-merged-code-safe 
                                   merged-code init-frame)))))))


;; >L            (DEFUN
;;                MERGESTACKMAPANDCODE
;;                (MAPS PARSEDCODE METHOD-TABLE)
;;                (IF
;;                 (ENDP MAPS)
;;                 (APPEND PARSEDCODE (LIST 'END_OF_CODE))
;;                 (IF
;;                  (ENDP PARSEDCODE)
;;                  NIL
;;                  (LET
;;                     ((MPC (MAPOFFSET (CAR MAPS)))
;;                      (PC (INSTROFFSET (CAR PARSEDCODE))))
;;                     (IF (EQUAL MPC PC)
;;                         (CONS (MAKESTACKMAP (CAR MAPS) METHOD-TABLE)
;;                               (CONS (MAKE-INST (CAR PARSEDCODE))
;;                                     (MERGESTACKMAPANDCODE (CDR MAPS)
;;                                                           (CDR PARSEDCODE)
;;                                                           METHOD-TABLE)))
;;                         (IF (< PC MPC)
;;                             (CONS (MAKE-INST (CAR PARSEDCODE))
;;                                   (MERGESTACKMAPANDCODE MAPS (CDR PARSEDCODE)
;;                                                         METHOD-TABLE))
;;                             NIL))))))

;;
;; our definition of mergestackmapandcode will prevent multiple stackmap of the
;; same pc.
;; 

(defthm verified-implies-member-stack-map-merged-code
  (implies (and (merged-code-safe merged-code init-frame)
                (bound? pc (extract-partial-sig-vector (extract-maps
                                                        merged-code))))
           (member (cdr (assoc-equal pc 
                                     (extract-partial-sig-vector (extract-maps
                                                                  merged-code))))
                   merged-code)))


(defthm verified-implies-extract-partial-stack-map
  (implies  (bound? pc (extract-partial-sig-vector (extract-maps
                                                    merged-code)))
            (stack-map?  (cdr (assoc-equal pc 
                                           (extract-partial-sig-vector (extract-maps
                                                                        merged-code)))))))


(defthm subsetp-bound
  (implies (and (subsetp l l2)
                (alistp l2)
                (consp l))
           (assoc-equal (car (car l)) l2)))

(defthm alistp-extract-partial-sig-vector
  (alistp (extract-partial-sig-vector maps)))

(defthm g-pc-extract-partial-sig-vector
  (implies (bound? pc (extract-partial-sig-vector maps))
           (equal (g 'pc (cdr (assoc-equal pc (extract-partial-sig-vector maps))))
                  pc)))



(defthm verified-extract-partial-sig-compatible-with-full-sig-lemma
  (implies (and (merged-code-safe merged-code init-frame)
                (consp (cdr merged-code))
                (stack-map? init-frame)
                (wff-code1 (extract-code merged-code)
                           (g 'pc (car merged-code)))
                (subsetp l (extract-partial-sig-vector (extract-maps merged-code))))
           (partial-sig-vector-compatible1
            l
            (extract-partial-sig-vector (extract-maps merged-code))
            (collect-witness-merged-code-safe merged-code init-frame)))
  :hints (("Goal" :in-theory (disable sig-frame-compatible
                                      extract-partial-sig-vector
                                      extract-maps
                                      extract-code
                                      wff-code1
                                      merged-code-safe
                                      stack-map?
                                      collect-witness-merged-code-safe)
           :restrict ((verified-implies-member-stack-map-merged-code
                       ((init-frame init-frame))))
           :do-not '(generalize))))



(defthm subsetp-reflexive-lemma
  (subsetp x (append any x)))

(defthm append-nil-x-is-x
  (equal (append nil x) x))

(defthm subsetp-x-x
  (subsetp x x)
  :hints (("Goal" :use ((:instance subsetp-reflexive-lemma
                                   (any nil))))))


;; (defthm merged-code-safe-implies-wff-code1
;;   (implies (merged-code-safe merged-code init-frame)
;;            (wff-code1 (extract-code merged-code)
;;                       (g 'pc (car merged-code))))
;;   :hints (("Goal" :do-not '(generalize))))


(defthm verified-extract-partial-sig-compatible-with-full-sig
  (implies (and (merged-code-safe merged-code init-frame)
                (stack-map? init-frame)
                (wff-code1 (extract-code merged-code)
                           (g 'pc (car merged-code))))
           (partial-sig-vector-compatible 
            (extract-partial-sig-vector (extract-maps merged-code))
            (collect-witness-merged-code-safe merged-code init-frame)))
  :hints (("Goal" :in-theory (disable sig-frame-compatible
                                      extract-partial-sig-vector
                                      extract-maps
                                      extract-code
                                      wff-code1
                                      merged-code-safe
                                      stack-map?
                                      partial-sig-vector-compatible1
                                      collect-witness-merged-code-safe)
           :cases ((not (consp (cdr merged-code)))))
          ("Subgoal 1" :in-theory (enable merged-code-safe
                                          partial-sig-vector-compatible1
                                          extract-code))))
                                          


