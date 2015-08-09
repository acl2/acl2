#|$ACL2s-Preamble$;
(begin-book t :ttags :all);$ACL2s-Preamble$|#


(in-package "ACL2")
(include-book "GeNoC-misc")
(include-book "macro")

(include-book "arithmetic/top" :dir :system)

;; xmasnetwork = [[channel] [component]]
;; A list of channels and a list of components.
;; In both lists, signals or states may be altered during the execution.

;; channel = [irdy trdy data initiator target]
;; A list of the three signals. The values are boolean (nil or t).
;; Plus two references to components. These are naturals.

;; component = [type [channel-ref] [channel-ref] [field]]
;; A list containing the type (e.g. 'switch or 'queue), a list of input- and a list of output-channels of the component.
;; A channel-ref is an integer referring the channel in the xmasnetwork data structure: given a channel-ref `cr':
;; (nth cr (car xmasnetwork)) returns the channel.
;; The field is a list of component-specific fields, e.g., the types of injections for a source, or a routing function for a switch.
;; We cannot store higher order functions in lists (ACL2 restriction) but since we can assume functions are finite,
;; we represent functions in association lists.

;; signal = [channel-ref type]
;; A signal is a channel-ref (see above) and a type (i.e., 'irdy, 'trdy or 'data)



;; ACCESSOR FUNCTIONS FOR XMAS DATA STRUCTURES

;; We let all accessor and update functions first check whether the input is valid.
;; This way we can create assumption-free theorems, which are easy for ACL2 to use in automatic rewriting.
;; If some day we want to make these function efficiently executable, we simply add all these checks as guards and make mbe's without the checks.

(defun componenttypes ()
  '(queue switch sink source function))
(in-theory (disable componenttypes (:EXECUTABLE-COUNTERPART componenttypes)))

(defstructure component type ins outs field
  (:options (:representation :list)
   ;(:do-not :tag)
   (:assert (and (member-equal type (componenttypes))))))

(defun component-in (n component)
  (nth n (component-ins component)))

(defun component-out (n component)
  (nth n (component-outs component)))

(create-for-all component-p)

(defstructure channel init target
  (:options (:representation :list)
   ;(:do-not :tag)
   ))

(create-for-all channel-p)

(defstructure xmasnetwork channels components
  (:options (:representation :list)
   ;(:do-not :tag)
   (:assert (and (A-component-p components)
                 (A-channel-p channels)))))

(defstructure xmas-signal channel-ref type
  (:options (:representation :list)
   ;(:do-not :tag)
   ))

;; The `type'-value of the channel (type == irdy,trdy,data)
(defun get-value (channel type)
    (cond ((equal type 'irdy)
           (nth 0 channel))
          ((equal type 'trdy)
           (nth 1 channel))
          ((equal type 'data)
           (nth 2 channel))
          (t
           nil)))

(defun get-in-channel (component i xmasnetwork)
  (nth (component-in i component) (xmasnetwork-channels xmasnetwork)))

(defun get-out-channel (component i xmasnetwork)
  (nth (component-out i component) (xmasnetwork-channels xmasnetwork)))

(defun get-target-component (channel xmasnetwork)
  (nth (channel-target channel) (xmasnetwork-components xmasnetwork)))

(defun get-init-component (channel xmasnetwork)
  (nth (channel-init channel) (xmasnetwork-components xmasnetwork)))

;; Apply a function (represented by an alist stored in the `n'th field of the component) to a parameter
(defun apply-field (n component parameter)
  (let ((func (nth n (component-field component))))
        (cdr (assoc parameter func))))
;; checks whether a queue is full
(defun full (queue)
  (not (member-equal nil (component-field queue))))
;; returns the packet at the head of the queue
(defun get-header (queue)
  (car (component-field queue)))

;; PREDICATES FOR XMAS DATA STRUCTURES

;; Types of xMAS channels
(defun xmas-chan-typep (type)
  (or (equal type 'trdy)
      (equal type 'irdy)
      (equal type 'data)))
;; Predicate for signals
(defun signalp (signal n)
  (and (natp (car signal))
       (< (car signal) n)
       (xmas-chan-typep (cadr signal))
       (not (cddr signal))))
;; Predicate for channel refs
(defmacro channel-refp (n x)
  `(and (natp ,n)
        (< ,n ,x)))
;; Predicate for comp refs
(defmacro comp-refp (n x)
    `(and (natp ,n)
        (< ,n ,x)))
;; Predicate for components
(defun componentp (comp n)
  (let ((type (component-type comp))
        (ins (component-ins comp))
        (outs (component-outs comp)))
  (and (component-p comp)
       (cond ((equal type 'switch)
              (and ;; One input channel
                   (equal (len ins) 1)
                   (channel-refp (nth 0 ins) n)
                   ;; Two different output channels
                   (equal (len outs) 2)
                   (channel-refp (nth 0 outs) n)
                   (channel-refp (nth 1 outs) n)
                   (no-duplicatesp outs)))
             ((equal type 'queue)
              (and ;; One input channel
                   (equal (len ins) 1)
                   (channel-refp (nth 0 ins) n)
                   ;; One output channel
                   (equal (len outs) 1)
                   (channel-refp (nth 0 outs) n)))
             ((equal type 'sink)
              (and ;; One input channel
                   (equal (len ins) 1)
                   (channel-refp (nth 0 ins) n)
                   ;; no output channel
                   (equal (len outs) 0)))
             ((equal type 'source)
              (and ;; no input channels
                   (equal (len ins) 0)
                   ;; One output channel
                   (equal (len outs) 1)
                   (channel-refp (nth 0 outs) n)))
             ((equal type 'function)
              (and ;; One input channel
                   (equal (len ins) 1)
                   (channel-refp (nth 0 ins) n)
                   ;; One output channel
                   (equal (len outs) 1)
                   (channel-refp (nth 0 outs) n)))
             (t
              nil)))))

;; returns the list of in-channels of the list of components
(defun in-channels-of (components)
  (if (endp components)
    nil
    (append (component-ins (car components))
            (in-channels-of (cdr components)))))
;; returns the list of out-channels of the list of components
(defun out-channels-of (components)
  (if (endp components)
    nil
    (append (component-outs (car components))
            (out-channels-of (cdr components)))))
;; returns t iff lists x and y are disjoint
(defun disjoint (x y)
  (if (endp x)
    t
    (and (not (member-equal (car x) y))
         (disjoint (cdr x) y))))
(defthm subsets-are-also-disjoint
  (equal (disjoint xs (append ys zs))
         (and (disjoint xs zs)
              (disjoint xs ys))))


;; Predicate for a list of components
;; n is the total number of components
(defun componentsp (comps n)
  (if (endp comps)
    t
    (and ;; Each element is a component
         (componentp (car comps) n)
         ;; The ins of each component is disjoint of all other ins
         ;(disjoint (ins (car comps)) (in-channels-of (cdr comps)))
         ;; The outs of each component is disjoint of all other outs
         ;(disjoint (outs (car comps)) (out-channels-of (cdr comps)))
         (componentsp (cdr comps) n))))
;; Predicate for a channel
(defun channelp (chan n)
  (and (channel-p chan)
       (comp-refp (channel-init chan) n)
       (comp-refp (channel-target chan) n)))
;; Predicate for a list of channels
(defun channelsp (chans n)
  (if (endp chans)
    t
    (and (channelp (car chans) n)
         (channelsp (cdr chans) n))))

(defun-sk component-to-channel-inversable-ins (xmasnetwork)
  (forall (component i)
          (implies (and (componentp component (len (xmasnetwork-channels xmasnetwork)))
                        (< i (len (component-ins component))))
                   (equal (get-target-component (get-in-channel component i xmasnetwork) xmasnetwork)
                          component)
                   )
          )
  )

(defun-sk component-to-channel-inversable-outs (xmasnetwork)
  (forall (component i)
          (implies (and (componentp component (len (xmasnetwork-channels xmasnetwork)))
                        (< i (len (component-outs component))))
                   (equal (get-init-component (get-out-channel component i xmasnetwork) xmasnetwork)
                          component)
                   )
          )
  )#|ACL2s-ToDo-Line|#


(defun-sk component-has-channel-as-input (component channel xmasnetwork)
  (exists (i)
          (and (natp i)
               (< i (len (component-ins component)))
               (equal (get-in-channel component i xmasnetwork)
                      channel))))

(defun-sk channel-to-component-inversable-target (xmasnetwork)
  (forall (channel)
          (implies (channelp channel (len (xmasnetwork-components xmasnetwork)))
                   (and (componentp (get-target-component channel xmasnetwork) (len (xmasnetwork-channels xmasnetwork)))
                        (component-has-channel-as-input (get-target-component channel xmasnetwork)
                                                        channel
                                                        xmasnetwork)))))
(defun-sk component-has-channel-as-output (component channel xmasnetwork)
  (exists (i)
          (and (natp i)
               (< i (len (component-outs component)))
               (equal (get-out-channel component i xmasnetwork)
                      channel))))

(defun-sk channel-to-component-inversable-init (xmasnetwork)
  (forall (channel)
          (implies (channelp channel (len (xmasnetwork-components xmasnetwork)))
                   (and (componentp (get-init-component channel xmasnetwork) (len (xmasnetwork-channels xmasnetwork)))
                        (component-has-channel-as-output (get-init-component channel xmasnetwork)
                                                         channel
                                                         xmasnetwork)))))

#|
(defun-sk target-of-channel-is-valid-component (xmasnetwork)
  (forall (channel)
          (implies (member-equal channel (chans xmasnetwork))
                   (member-equal (get-target-component channel xmasnetwork) (chans xmasnetwork)))))
|#

(in-theory (disable component-to-channel-inversable-outs component-to-channel-inversable-ins
                    channel-to-component-inversable-init channel-to-component-inversable-target
                    component-has-channel-as-output component-has-channel-as-input))

;; Predicate for an xMAS network
(defun xmasnetworkp (xmasnetwork)
  (and (xmasnetwork-p xmasnetwork)
       (componentsp (xmasnetwork-components xmasnetwork) (len (xmasnetwork-channels xmasnetwork)))
       (channelsp (xmasnetwork-channels xmasnetwork) (len (xmasnetwork-components xmasnetwork)))
       (component-to-channel-inversable-ins xmasnetwork)
       (component-to-channel-inversable-outs xmasnetwork)
       (channel-to-component-inversable-init xmasnetwork)
       (channel-to-component-inversable-target xmasnetwork)
       (no-duplicatesp (xmasnetwork-channels xmasnetwork))
       (no-duplicatesp (xmasnetwork-components xmasnetwork))
       (true-listp (xmasnetwork-channels xmasnetwork))
       (true-listp (xmasnetwork-components xmasnetwork))
       )
  )

(defthm xmasnetworkp-implies-weak-xmasnetwork-p
  (implies (XMASNETWORKP xmasnetwork)
           (WEAK-XMASNETWORK-P xmasnetwork)))
(defthm xmasnetworkp-implies-xmasnetwork-p
  (implies (XMASNETWORKP xmasnetwork)
           (XMASNETWORK-P xmasnetwork)))
(defthm no-nil-in-components
  (implies (componentsp comps n)
           (not (member-equal nil comps))))

(defthm no-nil-in-components-xmasnetworkp-version
  (implies (xmasnetworkp xmasnetwork)
           (not (member-equal nil (xmasnetwork-components xmasnetwork)))))

(defthm no-nil-in-channels
  (implies (channelsp channels n)
           (not (member-equal nil channels))))

(defthm no-nil-in-channels-xmasnetworkp-version
  (implies (xmasnetworkp xmasnetwork)
           (not (member-equal nil (xmasnetwork-channels xmasnetwork)))))

;; ACCESSOR - PART 2
;; Returns the value of a signal in the network
(defun get-signal-value (signal xmasnetwork)
  (if (and (signalp signal (len (xmasnetwork-channels xmasnetwork)))
           (xmasnetworkp xmasnetwork))
    (get-value (nth (xmas-signal-channel-ref signal) (xmasnetwork-channels xmasnetwork)) (xmas-signal-type signal))
    nil))


;; MODIFYING/EXECUTION OF XMASNETWORK

;; Replace in `list' the `n'th object by `object'
(defun replace-nth (n list object)
  (cond ((zp n)
         (if (endp list)
           list
           (cons object (cdr list))))
        ((endp list)
         list)
        (t
         (cons (car list) (replace-nth (1- n) (cdr list) object)))))
#|
;; Updates in the channel object with a new value for type (type = 'trdy, ...)
(defun channel-update (channel type value xmasnetwork)
  (cond ((not (channelp channel (len (xmasnetwork-components xmasnetwork))))
         channel)
        ((equal type 'irdy)
         (update-channel channel :irdy value))
        ((equal type 'trdy)
         (update-channel channel :trdy value))
        ((equal type 'data)
         (update-channel channel :data value))
        (t
         channel)))

;; Updates the signal with the new value in the xmasnetwork
(defun signal-update (signal value xmasnetwork)
  (let* ((channel-ref (xmas-signal-channel-ref signal))
         (type (xmas-signal-type signal))
         (channel (nth channel-ref (xmasnetwork-channels xmasnetwork))))
    (if (and (signalp signal (len (xmasnetwork-channels xmasnetwork)))
             (xmasnetworkp xmasnetwork))
      (xmasnetwork (replace-nth channel-ref (xmasnetwork-channels xmasnetwork) (channel-update channel type value xmasnetwork))
            (xmasnetwork-components xmasnetwork))
      xmasnetwork)))



;; PROOFS

(defthm update-signal-preserves-componentsp
  (equal (componentsp (xmasnetwork-components (signal-update signal value xmasnetwork)) n)
         (componentsp (xmasnetwork-components xmasnetwork) n)))
(defthm update-signal-preserves-number-of-components
  (equal (len (xmasnetwork-components (signal-update signal value xmasnetwork)))
         (len (xmasnetwork-components xmasnetwork))))
(defthm update-signal-is-identity-if-signal-is-not-valid
  (implies (not (signalp signal (len (xmasnetwork-channels xmasnetwork))))
           (equal (signal-update signal value xmasnetwork) xmasnetwork)))
(defthm nth-element-of-replace-nth
  (equal (nth n (replace-nth m list object))
         (if (or (and (equal n m)
                      (natp n)
                      (< m (len list)))
                 (and (zp n)
                      (zp m)
                      (consp list)))
           object
           (nth n list))))
(defthm first-element-of-replace-nth
  (equal (car (replace-nth m list object))
         (if (zp m)
           (if (consp list)
             object
             nil)
           (car list))))
(defthm replace-nth-nil
  (equal (replace-nth n nil object)
         nil))
(defthm nth-out-of-bounds-is-nil
  (implies (and (natp n)
                (>= n (len x)))
           (equal (nth n x) nil)))
(defthm replace-nth-preserves-consp
  (equal (consp (replace-nth n l o))
         (consp l)))
(defthm replace-nth-preserves-len
  (equal (len (replace-nth n l o))
         (len l)))
(defthm replace-nth-is-identity-if-out-of-bounds
  (implies (and (natp n)
                (< (len l) n))
           (equal (replace-nth n l o) l)))
(defthm channelsp-replace-nth
  (implies (and (channelsp channels n)
                (channelp channel n))
           (channelsp (replace-nth x channels channel) n)))
(defthm spec-of-channelsp
  (implies (and (channelsp channels n)
                (member-equal channel channels))
           (channelp channel n)))
(defthm true-listp-replace--nth
  (implies (true-listp x)
           (true-listp (replace-nth n x a))))
(defthm update-channel-preserves-channelp
  (equal (channelp (channel-update channel type value xmasnetwork) n)
         (channelp channel n)))

(defthm channelsp-replace-nth.1
  (implies (and (natp channel-ref)
                (< channel-ref (len channels))
                (channelsp channels n))
           (equal (len (nth channel-ref channels)) 5)))
(defthm channelsp-replace-nth.6
  (implies (and (natp channel-ref)
                (< channel-ref (len channels))
                (channelsp channels n))
           (consp (nth channel-ref channels))))
(defthm channelsp-replace-nth.9
  (implies (and
                (natp channel-ref)
                (< channel-ref (len channels))
                (channelsp channels n))
           (< (nth 4 (nth channel-ref channels)) n)))
(defthm channelsp-replace-nth.10
  (implies (and (natp channel-ref)
                (< channel-ref (len channels))
                (channelsp channels n))
           (>= (nth 4 (nth channel-ref channels)) 0))
  :rule-classes :linear)
(defthm channelsp-replace-nth.11
  (implies (and
                (natp channel-ref)
                (< channel-ref (len channels))
                (channelsp channels n))
           (< (nth 3 (nth channel-ref channels)) n)))
(defthm channelsp-replace-nth.12
  (implies (and
                (natp channel-ref)
                (< channel-ref (len channels))
                (channelsp channels n))
           (natp (nth 3 (nth channel-ref channels))))
  :rule-classes :type-prescription)
(defthm channelsp-replace-nth.13
  (implies (and (natp channel-ref)
                (< channel-ref (len channels))
                (channelsp channels n))
           (natp (nth 4 (nth channel-ref channels))))
  :rule-classes :type-prescription)
(defthm channelsp-replace-nth.14
  (implies (and (natp channel-ref)
                (< channel-ref (len channels))
                (channelsp channels n))
           (true-listp (nth channel-ref channels)))
  :rule-classes :type-prescription)
(defthm channelsp-replace-nth.15
  (implies (and (natp channel-ref)
                (< channel-ref (len channels))
                (channelsp channels n))
           (equal (len (cdr (nth channel-ref channels))) 4)))

(defthm replace-nth-preserves-consp-cdr
  (equal (consp (cdr (replace-nth n l o)))
         (consp (cdr l))))
(defthm replace-nth-preserves-consp-cddr
  (equal (consp (cddr (replace-nth n l o)))
         (consp (cddr l))))
(defthm update-signal-preserves-components
  (equal (xmasnetwork-components (signal-update signal value xmasnetwork))
         (xmasnetwork-components xmasnetwork)))

(defthm update-signal-preserves-channelsp
           (equal (channelsp (xmasnetwork-channels (signal-update signal value xmasnetwork)) (len (xmasnetwork-components xmasnetwork)))
                  (channelsp (xmasnetwork-channels xmasnetwork) (len (xmasnetwork-components xmasnetwork))))
  :hints (("Goal" :in-theory (disable channelp))
          ("Subgoal 24" :use ((:instance channelsp-replace-nth
                              (x (xmas-signal-channel-ref signal))
                              (n (len (xmasnetwork-components xmasnetwork)))
                              (channels (xmasnetwork-channels xmasnetwork))
                              (channel (channel-update (nth (xmas-signal-channel-ref signal) (xmasnetwork-channels xmasnetwork)) (xmas-signal-type signal) value xmasnetwork)))))
          ("Subgoal 15" :use ((:instance channelsp-replace-nth
                              (x (xmas-signal-channel-ref signal))
                              (n (len (xmasnetwork-components xmasnetwork)))
                              (channels (xmasnetwork-channels xmasnetwork))
                              (channel (channel-update (nth (xmas-signal-channel-ref signal) (xmasnetwork-channels xmasnetwork)) (xmas-signal-type signal) value xmasnetwork)))))

                              ))


(defthm update-signal-preserves-number-of-channels
  (equal (len (chans (update-signal signal value xmasnetwork)))
         (len (chans xmasnetwork))))
                       |#
(defthmd nth-cdr
  (implies (natp n)
           (equal (nth n (cdr x))
                  (nth (1+ n) x))))

#|
;(set-gag-mode :goals)
;(skip-proofs
(defthm get-signal-value-after-updating-signal
  (equal (get-signal-value signal1 (update-signal signal2 value xmasnetwork))
         (cond ((or (not (signalp signal2 (len (chans xmasnetwork))))
                    (not (xmasnetworkp xmasnetwork)))
                (get-signal-value signal1 xmasnetwork))
               ((not (signalp signal1 (len (chans xmasnetwork))))
                nil)
               ((equal signal1 signal2)
                value)
               (t
                (get-signal-value signal1 xmasnetwork))))
:hints (
        ("Goal" :in-theory (e/d (nth-cdr) (update-signal-preserves-componentsp component-to-channel-inversable-ins component-to-channel-inversable-outs)))
        ("Subgoal 538.1.3"  :use (:instance update-signal-preserves-componentsp
                                  (signal signal1)
                                  ))
        ))

 ;)
|#
;; Theorem get-signal-value-after-updating-signal allows to nicely abstract from the datastructures. We no longer need to expand functions get-signal-value or update-signal:
;(in-theory (disable update-signal get-signal-value))

(in-theory (disable component-in component-out))

(defthm get-target-get-in-is-original
  (implies (and (force (channelp channel (len (xmasnetwork-components xmasnetwork))))
                (force (xmasnetworkp xmasnetwork))
                (force (equal 1 (len (component-ins (get-target-component channel xmasnetwork))))))
           (equal (get-in-channel (get-target-component channel xmasnetwork) 0 xmasnetwork) channel))
  :hints (("goal" :use ((:instance channel-to-component-inversable-target-necc)))
          ("subgoal 4" :expand (component-has-channel-as-input (nth (channel-target channel)
                                                                    (xmasnetwork-components xmasnetwork))
                                                               channel xmasnetwork))
          ("subgoal 3" :expand (component-has-channel-as-input (nth (channel-target channel)
                                                                    (xmasnetwork-components xmasnetwork))
                                                               channel xmasnetwork))
          ("subgoal 2" :expand (component-has-channel-as-input (nth (channel-target channel)
                                                                    (xmasnetwork-components xmasnetwork))
                                                               channel xmasnetwork))
          ("subgoal 1" :expand (component-has-channel-as-input (nth (channel-target channel)
                                                                    (xmasnetwork-components xmasnetwork))
                                                               channel xmasnetwork))))

(defthm get-init-get-out-is-original
  (implies (and (force (channelp channel (len (xmasnetwork-components xmasnetwork))))
                (force (xmasnetworkp xmasnetwork))
                (force (equal 1 (len (component-outs (get-init-component channel xmasnetwork))))))
           (equal (get-out-channel (get-init-component channel xmasnetwork) 0 xmasnetwork) channel))
  :hints (("goal" :use ((:instance channel-to-component-inversable-init-necc)))
          ("subgoal 3" :expand (component-has-channel-as-output (nth (channel-init channel)
                                                                    (xmasnetwork-components xmasnetwork))
                                                               channel xmasnetwork))
          ("subgoal 2" :expand (component-has-channel-as-output (nth (channel-init channel)
                                                                    (xmasnetwork-components xmasnetwork))
                                                               channel xmasnetwork))
          ("subgoal 1" :expand (component-has-channel-as-output (nth (channel-init channel)
                                                                    (xmasnetwork-components xmasnetwork))
                                                               channel xmasnetwork))))

(defthm get-in-get-target-is-original
  (implies (and (force (componentp component (len (xmasnetwork-channels xmasnetwork))))
                (force (xmasnetworkp xmasnetwork))
                (force (< i (len (component-ins component)))))
           (equal (get-target-component (get-in-channel component i xmasnetwork) xmasnetwork) component))
  :hints (("Goal" :use ((:instance component-to-channel-inversable-ins-necc)))))

(defthm get-out-get-init-is-original
  (implies (and (force (componentp component (len (xmasnetwork-channels xmasnetwork))))
                (force (xmasnetworkp xmasnetwork))
                (force (< i (len (component-outs component)))))
           (equal (get-init-component (get-out-channel component i xmasnetwork) xmasnetwork) component))
  :hints (("Goal" :use ((:instance component-to-channel-inversable-outs-necc)))))

(defthm nth-with-correct-bounds-implies-member-equal
  (implies (and (natp i)
                (< i (len list)))
           (member-equal (nth i list) list)))
(defthm channelsp-implies-correct-bounds-for-trgt-of-channel
  (implies (and (channelsp channels n)
                (member-equal channel channels))
           (and (natp (channel-target channel))
                (< (channel-target channel) n))))
(defthm get-target-from-channel-implies-component
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal channel (xmasnetwork-channels xmasnetwork)))
           (member-equal (get-target-component channel xmasnetwork) (xmasnetwork-components xmasnetwork))))
(defthm channelsp-implies-correct-bounds-for-init-of-channel
  (implies (and (channelsp channels n)
                (member-equal channel channels))
           (and (natp (channel-init channel))
                (< (channel-init channel) n))))
(defthm get-init-from-channel-implies-component
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal channel (xmasnetwork-channels xmasnetwork)))
           (member-equal (get-init-component channel xmasnetwork) (xmasnetwork-components xmasnetwork))))


(defthm componentsp-implies-correct-bounds-for-outs-of-component
  (implies (and (componentsp components n)
                (member-equal component components)
                (natp i)
                (< i (len (component-outs component))))
           (and (natp (component-out i component))
                (< (component-out i component) n)))
    :hints (("Goal" :in-theory (enable component-out)))
)

(defthm get-out-from-component-implies-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (natp i)
                (< i (len (component-outs component)))
                (member-equal component (xmasnetwork-components xmasnetwork))
                )
           (member-equal (get-out-channel component i xmasnetwork) (xmasnetwork-channels xmasnetwork))))

(defthm componentsp-implies-correct-bounds-for-ins-of-component
  (implies (and (componentsp components n)
                (member-equal component components)
                (natp i)
                (< i (len (component-ins component))))
           (and (natp (component-in i component))
                (< (component-in i component) n)))
  :hints (("Goal" :in-theory (enable component-in)))
)
(defthm get-in-from-component-implies-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (natp i)
                (< i (len (component-ins component)))
                (member-equal component (xmasnetwork-components xmasnetwork))
                )
           (member-equal (get-in-channel component i xmasnetwork) (xmasnetwork-channels xmasnetwork)))
)
;; switch
(defthm switch-implies-two-output-channels-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'switch (component-type component)))
           (equal (len (component-outs component)) 2)))
(defthm switch-implies-two-output-channels
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'switch (component-type component)))
           (equal (len (component-outs component)) 2)))
(defthm switch-implies-one-input-channel-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'switch (component-type component)))
           (equal (len (component-ins component)) 1)))
(defthm switch-implies-on-input-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'switch (component-type component)))
           (equal (len (component-ins component)) 1)))

;; queue
(defthm queue-implies-one-output-channel-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'queue (component-type component)))
           (equal (len (component-outs component)) 1)))
(defthm queue-implies-one-output-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'queue (component-type component)))
           (equal (len (component-outs component)) 1)))
(defthm queue-implies-one-input-channel-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'queue (component-type component)))
           (equal (len (component-ins component)) 1)))
(defthm queue-implies-one-input-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'queue (component-type component)))
           (equal (len (component-ins component)) 1)))

;; sink
(defthm sink-implies-no-output-channel-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'sink (component-type component)))
           (equal (len (component-outs component)) 0)))
(defthm sink-implies-no-output-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'sink (component-type component)))
           (equal (len (component-outs component)) 0)))
(defthm sink-implies-one-input-channel-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'sink (component-type component)))
           (equal (len (component-ins component)) 1)))
(defthm sink-implies-one-input-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'sink (component-type component)))
           (equal (len (component-ins component)) 1)))
;; source
(defthm source-implies-one-output-channel-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'source (component-type component)))
           (equal (len (component-outs component)) 1)))
(defthm source-implies-one-output-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'source (component-type component)))
           (equal (len (component-outs component)) 1)))
(defthm source-implies-no-input-channel-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'source (component-type component)))
           (equal (len (component-ins component)) 0)))
(defthm source-implies-no-input-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'source (component-type component)))
           (equal (len (component-ins component)) 0)))
;; function
(defthm function-implies-one-output-channel-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'function (component-type component)))
           (equal (len (component-outs component)) 1)))
(defthm function-implies-one-output-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'function (component-type component)))
           (equal (len (component-outs component)) 1)))
(defthm function-implies-one-input-channel-lemma
  (implies (and (componentsp components n)
                (member-equal component components)
                (equal 'function (component-type component)))
           (equal (len (component-ins component)) 1)))
(defthm function-implies-one-input-channel
  (implies (and (xmasnetworkp xmasnetwork)
                (member-equal component (xmasnetwork-components xmasnetwork))
                (equal 'function (component-type component)))
           (equal (len (component-ins component)) 1)))

(defthm components-implies-component
  (implies (and (member-equal comp comps)
                (componentsp comps n))
           (componentp comp n)))
(defthm component-implies-componentp
  (implies (and (member-equal comp (xmasnetwork-components xmasnetwork))
                (xmasnetworkp xmasnetwork))
           (componentp comp (len (xmasnetwork-channels xmasnetwork)))))
(defthm component-implies-possible-types
  (IMPLIES (componentp comp n)
           (member-equal (component-type comp) (componenttypes)))
  )
(defthm possible-types-of-components
  (implies (and (member-equal comp (xmasnetwork-components xmasnetwork))
                (xmasnetworkp xmasnetwork))
           (member-equal (component-type comp) (componenttypes)))
  :hints (("Goal" :use (:instance component-implies-possible-types (n (len (xmasnetwork-channels xmasnetwork))))))
  )

(defthm possible-types-of-components-inverse
  (implies (and (not (member-equal (component-type comp) (componenttypes)))
                (xmasnetworkp xmasnetwork))
           (not (member-equal comp (xmasnetwork-components xmasnetwork))))
    :hints (("Goal" :use (:instance component-implies-possible-types (n (len (xmasnetwork-channels xmasnetwork))))))
)

(defthm if-target-component-of-channel-is-not-part-of-xmasnetwork-then-channel-is-not-part
  (implies (and (not (member-equal (get-target-component channel xmasnetwork) (xmasnetwork-components xmasnetwork)))
                (xmasnetworkp xmasnetwork))
           (not (member-equal channel (xmasnetwork-channels xmasnetwork)))))
(defthm if-init-component-of-channel-is-not-part-of-xmasnetwork-then-channel-is-not-part
  (implies (and (not (member-equal (get-init-component channel xmasnetwork) (xmasnetwork-components xmasnetwork)))
                (xmasnetworkp xmasnetwork))
           (not (member-equal channel (xmasnetwork-channels xmasnetwork)))))

(defthm componentsp-and-member-implies-channelp
  (implies (and (member-equal component components)
                (componentsp components n))
           (componentp component n)))

(defthm xmasnetwork-and-component-implies-componentp
   (implies (and (xmasnetworkp xmasnetwork)
                 (member-equal component (xmasnetwork-components xmasnetwork)))
            (componentp component (len (xmasnetwork-channels xmasnetwork)))))

(defthm channelsp-and-member-implies-channelp
  (implies (and (member-equal channel channels)
                (CHANNELSP channels n))
           (channelp channel n)))

(defthm xmasnetwork-and-channel-implies-channelp
   (implies (and (xmasnetworkp xmasnetwork)
                 (member-equal channel (xmasnetwork-channels xmasnetwork)))
            (channelp channel (len (xmasnetwork-components xmasnetwork)))))

(in-theory (disable get-out-channel get-in-channel get-target-component get-init-component))
(in-theory (disable componentsp channelsp componentp channelp))
(in-theory (disable xmasnetworkp))
