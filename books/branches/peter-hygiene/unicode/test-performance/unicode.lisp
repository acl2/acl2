(include-book "../read-utf8")

(comp t)

;; 7,273,110
(mv-let (data state)
        (read-utf8 "/var/local/jared/chinese" state)
        (mv (length data) state))

;; 19,757,860
(mv-let (data state)
        (read-utf8 "/var/local/jared/english" state)
        (mv (length data) state))

(time$ 
 (mv-let (data state)
         (read-utf8 "/var/local/jared/chinese" state)
         (declare (ignore data))
         state))

(time$ 
 (mv-let (data state)
         (read-utf8 "/var/local/jared/english" state)
         (declare (ignore data))
         state))
