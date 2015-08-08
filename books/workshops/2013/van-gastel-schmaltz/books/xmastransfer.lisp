#|$ACL2s-Preamble$;
(BEGIN-BOOK T :TTAGS :ALL);$ACL2s-Preamble$|#


(in-package "ACL2")

(include-book "akeys")
(include-book "xmasnetwork")

(defstub xmas-can-receive (component ntkstate) nil)
(defstub xmas-can-send (component ntkstate) nil)
(defstub xmas-next-data (component ntkstate) nil)

(defun resourcetypes ()
  '(queue sink source))
(in-theory (disable resourcetypes (:EXECUTABLE-COUNTERPART resourcetypes)))

(defthm resourcetypes-is-subset-of-componenttypes
  (subsetp (resourcetypes) (componenttypes))
  :hints (("Goal" :in-theory (e/d (resourcetypes componenttypes) ()))))

(defun xmas-function (component data)
  (if (equal data 'error)
    'error
    (apply-field 0 component data)))

(defun xmas-switch-function (component data)
    (if (equal data 'error)
    'error
    (apply-field 0 component data)))

(in-theory (disable xmas-switch-function))

(defstructure xmas bool routing transfer)

; can not be a 'mv' (multivalue) because this whole function should return the same number of arguments, so a different 'error state is not possible
(defun xmas-result (bool routing transfer)
  (if (equal bool 'error)
    'error
    (xmas bool routing transfer))
  )

(defun xmas-or (a b)
  (let ((routing (append (xmas-routing a) (xmas-routing b)))
        (at (xmas-transfer a))
        (bt (xmas-transfer b))
        (ab (xmas-bool a))
        (bb (xmas-bool b)))
    (cond ((or (equal a 'error) (equal b 'error)) 'error)
          ((and ab bb) (xmas-result t routing (append at bt)))
          (ab (xmas-result t routing at))
          (bb (xmas-result t routing bt))
          (t (xmas-result nil routing nil)))
    ))

(defun xmas-and (a b)
  (let ((routing (append (xmas-routing a) (xmas-routing b))))
    (cond ((or (equal a 'error) (equal b 'error)) 'error)
          ((and (xmas-bool a) (xmas-bool b)) (xmas-result t routing (append (xmas-transfer a) (xmas-transfer b))))
          (t (xmas-result nil routing nil)))))

; do not use for irdy or trdy signals
; use only for data and functions
(defun xmas-not (a)
  (cond ((equal a 'error) 'error)
        (t (not a))))

(defun xmas-component (bool component frame)
  (xmas-result bool (list (cons component frame)) (if bool (list (cons component frame)) nil)))

(defun generateUnvisitedHelper (channels)
  (if (endp channels)
    nil
    (append (list (cons (car channels) 'irdy)
                  (cons (car channels) 'trdy)
                  (cons (car channels) 'data))
            (generateUnvisitedHelper (cdr channels)))))

(defun generateUnvisited (xmasnetwork)
  (generateUnvisitedHelper (xmasnetwork-channels xmasnetwork)))

 (defun xmas-transfer-calculate (flg channel xmasnetwork unvisited ntkstate)
   (declare (xargs :measure (len unvisited)))
   (cond ((not (member-equal (cons channel flg) unvisited)) 'error)
         ((equal flg 'data)
          (let* ((component (get-init-component channel xmasnetwork))
                 (type (component-type component))
                 (next-unvisited  (remove1 (cons channel flg) unvisited)))
            (cond
             ;; queue
             ((equal type 'queue) (xmas-next-data component ntkstate))
             ; sink
             ((equal type 'sink) 'error)
             ;; source
             ((equal type 'source) (xmas-next-data component ntkstate))
             ;; switch
             ((equal type 'switch) (xmas-transfer-calculate 'data (get-in-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate))
             ; function
             ((equal type 'function) (xmas-function component (xmas-transfer-calculate 'data (get-in-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate)))
             (t (xmas-result nil nil nil)))))
         ((equal flg 'irdy)
           (let* ((component (get-init-component channel xmasnetwork))
                  (type (component-type component))
                  (index-out (if (equal (get-in-channel component 0 xmasnetwork) channel) 0 1))
                  (next-unvisited  (remove1 (cons channel flg) unvisited))
                  )
             (cond
              ;; queue
              ((equal type 'queue) (xmas-result (xmas-can-send component ntkstate) nil nil))
              ;; sinks
              ((equal type 'sink) 'error)
              ;; source
              ((equal type 'source) (xmas-result (xmas-can-send component ntkstate) nil nil))
              ;; switch, a.irdy
              ((and (equal type 'switch) (equal index-out 0)) (xmas-and (xmas-transfer-calculate 'irdy (get-in-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate)
                                                                                     (xmas-result (xmas-switch-function component (xmas-transfer-calculate 'data (get-in-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate)) nil nil)))
              ;; switch, b.irdy
              ((and (equal type 'switch) (equal index-out 1)) (xmas-and (xmas-transfer-calculate 'irdy (get-in-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate)
                                                                                     (xmas-result (xmas-not (xmas-switch-function component (xmas-transfer-calculate 'data (get-in-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate))) nil nil)))
              ((equal type 'function) (xmas-transfer-calculate 'irdy (get-in-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate))

              (t (xmas-result nil nil nil)))
           )
         )
         ((equal flg 'trdy)
          (let* ((component (get-target-component channel xmasnetwork))
                 (type (component-type component))
                 (next-unvisited  (remove1 (cons channel flg) unvisited)))
            (cond
             ((equal type 'queue) (xmas-component (xmas-can-receive component ntkstate) component (xmas-transfer-calculate 'data channel xmasnetwork next-unvisited ntkstate))) ; 'notfull);
             ((equal type 'sink) (xmas-component (xmas-can-receive component ntkstate) component (xmas-transfer-calculate 'data channel xmasnetwork next-unvisited ntkstate)))
             ((equal type 'source) 'error)
             ((equal type 'switch) (xmas-or (xmas-and (xmas-transfer-calculate 'irdy (get-out-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate)
                                                      (xmas-transfer-calculate 'trdy (get-out-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate))
                                            (xmas-and (xmas-transfer-calculate 'irdy (get-out-channel component 1 xmasnetwork) xmasnetwork next-unvisited ntkstate)
                                                      (xmas-transfer-calculate 'trdy (get-out-channel component 1 xmasnetwork) xmasnetwork next-unvisited ntkstate))))
             ((equal type 'function) (xmas-transfer-calculate 'trdy (get-out-channel component 0 xmasnetwork) xmasnetwork next-unvisited ntkstate))
             (t (xmas-result nil nil nil)))))
         (t 'error)))

 (defthm xmas-or-bool-thm
   (let ((a (xmas-transfer-calculate flga channela xmasnetwork unvisited ntkstate))
         (b (xmas-transfer-calculate flgb channelb xmasnetwork unvisited ntkstate)))
     (implies (and (xmasnetworkp xmasnetwork)
                   (member-equal channela (xmasnetwork-channels xmasnetwork))
                   (member-equal signala '(irdy trdy))
                   (member-equal channelb (xmasnetwork-channels xmasnetwork))
                   (member-equal signalb '(irdy trdy))
                   (not (equal a 'error))
                   (not (equal b 'error)))
              (iff (xmas-bool (xmas-or a b)) (or (xmas-bool a) (xmas-bool b))))))

 (defthm xmas-and-bool-thm
   (let ((a (xmas-transfer-calculate flga channela xmasnetwork unvisited ntkstate))
         (b (xmas-transfer-calculate flgb channelb xmasnetwork unvisited ntkstate)))
     (implies (and (not (equal a 'error))
                   (not (equal b 'error)))
              (iff (xmas-bool (xmas-and a b)) (and (xmas-bool a) (xmas-bool b)) ))))

 (defthm xmas-or-error-thm-simple
  (equal (equal (xmas-or a b) 'error) (or (equal a 'error) (equal b 'error))))

(defthm xmas-and-error-thm-simple
    (equal (equal (xmas-and a b) 'error) (or (equal a 'error) (equal b 'error))))

 (defun resource-predicate (comp xmasnetwork)
   (and (member-equal comp (xmasnetwork-components xmasnetwork));(consp xmasnetwork);(componentp (car comps) (len (xmasnetwork-channels xmasnetwork)))
        (member-equal (component-type comp) (resourcetypes))
         ))

(create-for-all resource-predicate :extra (xmasnetwork) :name A-resources)

(defthm components-do-not-start-with-and
  (implies (and (componentp comp n))
           (not (equal (component-type comp) 'and)))
   :hints (("Goal" :in-theory (enable componentp))))
(defthm components-dont-start-with-or
  (implies (and (componentp comp n))
           (not (equal (component-type comp) 'or)))
   :hints (("Goal" :in-theory (enable componentp))))

(defthm components-do-not-start-with-and-componentsp
  (implies (and (componentsp comps n)
                (member-equal comp comps))
           (not (equal (component-type comp) 'and)))
  :hints (("Goal" :in-theory (enable componentsp))))
(defthm components-do-not-start-with-or-componentsp
  (implies (and (componentsp comps n)
                (member-equal comp comps))
           (not (equal (component-type comp) 'or)))
  :hints (("Goal" :in-theory (enable componentsp))))

(defthm components-do-not-start-with-and-general
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal comp (xmasnetwork-components xmasnetwork)))
           (not (equal (component-type comp) 'and)))
  :hints (("Goal" :in-theory (enable xmasnetworkp))))
(defthm components-do-not-start-with-or-general
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal comp (xmasnetwork-components xmasnetwork)))
           (not (equal (component-type comp) 'or)))
    :hints (("Goal" :in-theory (enable xmasnetworkp))))


(defthm components-are-not-and
  (implies
           (equal comp 'and)
           (not (componentp comp n)))
   :hints (("Goal" :in-theory (enable componentp))))
(defthm components-are-not-or
  (implies
           (equal comp 'or)
           (not (componentp comp n)))
   :hints (("Goal" :in-theory (enable componentp))))
(defthm componentsp-implies-componentp
  (implies (and (componentsp comps n)
                (member-equal comp comps))
           (componentp comp n)))
(defthm components-are-not-and-componentsp
  (implies (componentsp comps n)
           (not (member-equal 'and comps)))
    :hints (("Goal" :in-theory (enable componentsp))))
(defthm components-are-not-or-componentsp
  (implies (componentsp comps n)
           (not (member-equal 'or comps)))
    :hints (("Goal" :in-theory (enable componentsp))))
(defthm components-are-not-and-xmasnetworkp
  (implies (xmasnetworkp xmasnetwork)
           (not (member-equal 'and (xmasnetwork-components xmasnetwork))))
    :hints (("Goal" :in-theory (enable xmasnetworkp))))
(defthm components-are-not-or-xmasnetworkp
  (implies (xmasnetworkp xmasnetwork)
           (not (member-equal 'or (xmasnetwork-components xmasnetwork))))
    :hints (("Goal" :in-theory (enable xmasnetworkp))))
(defthm components-are-not-and-xmasnetworkp-alt
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal comp (xmasnetwork-components xmasnetwork)))
           (not (equal comp 'and)))
  :hints (("Goal" :in-theory (enable xmasnetworkp))))
(defthm components-are-not-or-xmasnetworkp-alt
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal comp (xmasnetwork-components xmasnetwork)))
           (not (equal comp 'or)))
    :hints (("Goal" :in-theory (enable xmasnetworkp))))

(defthm xmas-transfer-calculate-target-are-resources
  (let ((result (xmas-transfer-calculate signal channel xmasnetwork unvisited ntkstate)))
    (implies (and (xmasnetworkp xmasnetwork)
                  (member-equal signal '(irdy trdy))
                  (member-equal channel (xmasnetwork-channels xmasnetwork))
                  )
             (A-resources (strip-cars (xmas-routing result)) xmasnetwork)))
  :hints (("Goal" :in-theory (enable (resourcetypes)) )))

(defthm A-resources-and-element-lookup
  (implies (and (A-resources (strip-cars alist) xmasnetwork)
                (assoc element alist))
           (resource-predicate element xmasnetwork)))

(defthm A-resources-implies-member-equal-comps
  (implies (and (xmasnetworkp xmasnetwork)
                (A-resources resources xmasnetwork)
                (member-equal resource resources))
           (member-equal resource (xmasnetwork-components xmasnetwork))))

(defthm A-resources-implies-resource-is-resource
  (implies (and (xmasnetworkp xmasnetwork)
                (A-resources queues xmasnetwork)
                (member-equal queue queues))
           (member-equal (component-type queue) (resourcetypes))))

(defthm A-resources-implies-subset-of-components
  (implies (and (xmasnetworkp xmasnetwork)
                (A-resources queues xmasnetwork))
           (subsetp queues (xmasnetwork-components xmasnetwork))))

(defun-sk exists-a-queue-with-room (xmasnetwork ntkstate)
  (exists (component)
          (and (member-equal component (xmasnetwork-components xmasnetwork))
               (equal (component-type component) 'queue)
               (xmas-can-receive component ntkstate))))
(in-theory (disable exists-a-queue-with-room))

(create-for-all xmas-can-receive :extra (ntkstate) :domain queues :name A-queues-can-receive)

(defthm transfer-indicates-a-queue-that-can-receive
  (let ((result (xmas-transfer-calculate flg channel xmasnetwork unvisited ntkstate)))
    (implies (and (xmasnetworkp xmasnetwork)
                  (member-equal channel (xmasnetwork-channels xmasnetwork))
                  )
             (cond ((equal flg 'data)
                    t)
                   ((equal flg 'irdy)
                    (equal (xmas-transfer result)
                           nil))
                   ((equal flg 'trdy)
                    (and (A-queues-can-receive (strip-cars (xmas-transfer result)) ntkstate)
                         (alistp (xmas-transfer result))))
                   (t
                    (equal result 'error))
                   )))
  :rule-classes nil
  :hints (("Goal" :induct (xmas-transfer-calculate flg channel xmasnetwork unvisited ntkstate)
                  :in-theory (e/d (xmas-and xmas-or xmas-bool) ())
                  )
          ))

(defthm flatten-of-routing-result-in-alistp
  (let ((result (xmas-transfer-calculate flg channel xmasnetwork unvisited ntkstate)))
    (implies (and (xmasnetworkp xmasnetwork)
                  (member-equal channel (xmasnetwork-channels xmasnetwork))
                  )
             (cond ((equal flg 'data)
                    t)
                   ((equal flg 'irdy)
                    (alistp (xmas-routing result)))
                   ((equal flg 'trdy)
                    (alistp (xmas-routing result)))
                   (t
                    (equal result 'error))
                   )))
  :rule-classes nil
  :hints (("Goal" :induct (xmas-transfer-calculate flg channel xmasnetwork unvisited ntkstate)
                  :in-theory (e/d (xmas-and xmas-or xmas-bool) ())
                  )
          ))

(defthm transfer-is-subset-of-routing
  (let ((result (xmas-transfer-calculate signal channel xmasnetwork unvisited ntkstate)))
    (implies (member-equal signal '(irdy trdy))
             (subsetp-equal (xmas-transfer result) (xmas-routing result)))))

(defthm xmas-calculate-at-least-one
  (let ((result (xmas-transfer-calculate 'trdy channel xmasnetwork unvisited ntkstate)))
    (implies (and (xmasnetworkp xmasnetwork)
                  (member-equal channel (xmasnetwork-channels xmasnetwork))
                  (not (equal result 'error)))
             (consp (xmas-routing result))))
  :hints (("Subgoal *1/7" :in-theory (e/d (COMPONENTTYPES) (POSSIBLE-TYPES-OF-COMPONENTS-INVERSE))
                  :use (:instance possible-types-of-components-inverse
                                   (comp (get-target-component channel xmasnetwork))))))

(defthm no-nil-is-stable-under-flatten-strip-cars
  (let ((result (xmas-transfer-calculate signal channel xmasnetwork unvisited ntkstate)))
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal signal '(trdy irdy))
                (member-equal channel (xmasnetwork-channels xmasnetwork)))
           (not (member-equal nil (strip-cars (xmas-routing result)))))))

(defthm xmas-transfer-calculate-produces-alist-routing
  (let ((result (xmas-transfer-calculate signal channel xmasnetwork unvisited ntkstate)))
    (implies (and (xmasnetworkp xmasnetwork)
                  (member-equal signal '(irdy trdy))
                  (member-equal channel (xmasnetwork-channels xmasnetwork))
                  )
             (alistp (xmas-routing result))))
  :hints (("Goal" :in-theory (enable (resourcetypes)))))

(defthm xmas-transfer-calculate-produces-alist-transfer
  (let ((result (xmas-transfer-calculate signal channel xmasnetwork unvisited ntkstate)))
    (implies (and (xmasnetworkp xmasnetwork)
                  (member-equal signal '(irdy trdy))
                  (member-equal channel (xmasnetwork-channels xmasnetwork)))
             (alistp (xmas-transfer result))))
  :hints (("Goal" :in-theory (enable (resourcetypes)))))

(in-theory (disable xmas-bool xmas-routing xmas-transfer xmas-result xmas-or xmas-and))

(defthm subsetp-implies-member
  (implies (and (subsetp-equal a b)
                (member-equal x a))
           (member-equal x b)))

(defthm xmas-transfer-implies-available-resource
  (let ((result (xmas-transfer-calculate 'trdy channel xmasnetwork unvisited ntkstate)))
    (implies (and (xmasnetworkp xmasnetwork)
                  (member-equal channel (xmasnetwork-channels xmasnetwork))
                  (member-equal resource (strip-cars (xmas-transfer result))))
              (xmas-can-receive resource ntkstate)))
  :hints (("Goal" :use ((:instance transfer-indicates-a-queue-that-can-receive
                         (flg 'trdy))))))

(defthm no-nil-is-stable-under-flatten-specified-on-component
  (let ((result (xmas-transfer-calculate 'trdy (get-out-channel curr 0 xmasnetwork) xmasnetwork (generateUnvisited xmasnetwork) nil)))
  (implies (and (xmasnetworkp xmasnetwork)
                (> (len (component-outs curr)) 0)
                (member-equal curr (xmasnetwork-components xmasnetwork)))
           (not (member-equal nil (strip-cars (xmas-routing result)))))))#|ACL2s-ToDo-Line|#

