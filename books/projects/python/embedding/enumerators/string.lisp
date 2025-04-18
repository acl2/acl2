(in-package "ACL2S")
(include-book "utils")

(defun ascii-codepoint-enum (seed)
  (defdata::random-integer-between-seed 0 127 seed))

(defun ascii-only-codepoints-enum-acc (len seed acc)
  (declare (xargs :mode :program))
  (if (or (not (acl2-numberp len))
          (<= len 0))
      (mv acc seed)
    (b* (((mv codepoint seed) (ascii-codepoint-enum seed)))
      (ascii-only-codepoints-enum-acc (1- len) seed (cons codepoint acc)))))

(defmacro ascii-only-codepoints-enum (len seed)
  `(ascii-only-codepoints-enum-acc ,len ,seed nil))

(defmacro defdata-enum-for-range-excluding (name min max excluding)
  `(defdata ,name
     (enum ',(set-difference-equal (gen-below max :start min) excluding))))

(defdata-enum-for-range-excluding greek-unicode-codepoint
  #x0370 #x03FF
  (#x0378 #x0379
          #x0380 #x0381 #x0382 #x0383 #x038B #x038D
          #x03A2))

(defun greek-only-codepoints-enum-acc (len seed acc)
  (declare (xargs :mode :program))
  (if (or (not (acl2-numberp len))
          (<= len 0))
      (mv acc seed)
    (b* (((mv codepoint seed)
          (nth-greek-unicode-codepoint/acc 0 seed)))
      (greek-only-codepoints-enum-acc (1- len) seed (cons codepoint acc)))))

(defmacro greek-only-codepoints-enum (len seed)
  `(greek-only-codepoints-enum-acc ,len ,seed nil))

(defun mathematical-operator-codepoint-enum (seed)
  (defdata::random-integer-between-seed #x2200 #x22FF seed))

(defun logic-only-codepoints-enum-acc (len seed acc)
  (declare (xargs :mode :program))
  (if (or (not (acl2-numberp len))
          (<= len 0))
      (mv acc seed)
    (b* (((mv codepoint seed)
          (mathematical-operator-codepoint-enum seed)))
      (logic-only-codepoints-enum-acc (1- len) seed (cons codepoint acc)))))

(defmacro logic-only-codepoints-enum (len seed)
  `(logic-only-codepoints-enum-acc ,len ,seed nil))

(defun diacritic-codepoint-enum (seed)
  (defdata::random-integer-between-seed #x300 #x370 seed))

(defun alpha-codepoint-enum (seed)
  (defdata::random-integer-between-seed 65 123 seed))

(defun diacritic-modified-alpha-enum (seed)
  (b* (((mv diacritic-codepoint seed) (diacritic-codepoint-enum seed))
       ((mv base-codepoint seed) (alpha-codepoint-enum seed)))
    (mv (list base-codepoint diacritic-codepoint) seed)))

(defun diacritics-only-codepoints-enum-acc (len seed acc)
  (declare (xargs :mode :program))
  (if (or (not (acl2-numberp len))
          (<= len 0))
      ;; order matters here
      (mv (reverse acc) seed)
    (b* (((mv codepoints seed) (diacritic-modified-alpha-enum seed)))
      (diacritics-only-codepoints-enum-acc (1- len) seed (append codepoints acc)))))

(defmacro diacritics-only-codepoints-enum (len seed)
  `(diacritics-only-codepoints-enum-acc ,len ,seed nil))

(defun optional-skin-color-modifier-enum (seed)
  (b* (((mv choice seed) (switch-nat-safe-seed 6 seed)))
    (mv (and (!= choice 5) (list (+ #x1F3FB choice))) seed)))

(defun optional-hair-color-modifier-enum (seed)
  (b* (((mv choice seed) (switch-nat-safe-seed 5 seed)))
    (mv (and (!= choice 4) (list #x200D (+ #x1F9B0 choice))) seed)))

(defconst *compound-codepoint-examples*
  '(;; E11.0 pirate flag "🏴‍☠️"
    (#x1F3F4 #x200D #x2620 #xFE0F)
    ;; another encoding for the above (minimally qualified) "🏴‍☠"
    (#x1F3F4 #x200D #x2620)
    ;; E5.0 child: dark skin tone "🧒🏿"
    (#x1F9D2 #x1F3FF)
    ;; E2.0 family: woman, woman, girl, boy  "👩‍👩‍👧‍👦"
    (#x1F469 #x200D #x1F469 #x200D #x1F467 #x200D #x1F466)
    ;; E12.0 people holding hands: medium-dark skin tone, light skin tone "🧑🏾‍🤝‍🧑🏻"
    (#x1F9D1 #x1F3FE #x200D #x1F91D #x200D #x1F9D1 #x1F3FB)
    ;; E12.0 woman and man holding hands: light skin tone "👫🏻"
    (#x1F46B #x1F3FB)
    ;; E13.0 ninja: light skin tone "🥷🏻"
    (#x1F977 #x1F3FB)
    ;; E13.1 kiss: woman, man, medium skin tone, dark skin tone "👩🏽‍❤️‍💋‍👨🏿"
    (#x1F469 #x1F3FD #x200D #x2764 #xFE0F #x200D #x1F48B #x200D #x1F468 #x1F3FF)
    ;; another encoding for the above, but this one is minimally qualified "👩🏽‍❤‍💋‍👨🏿"
    (#x1F469 #x1F3FD #x200D #x2764 #x200D #x1F48B #x200D #x1F468 #x1F3FF)
    ;; E4.0 men wrestling "🤼‍♂️"
    (#x1F93C #x200D #x2642 #xFE0F)
    ;; another encoding for the above, minimally qualified "🤼‍♂"
    (#x1F93C #x200D #x2642)))

(defconst *num-compound-codepoint-examples*
  (length *compound-codepoint-examples*))

(defun compound-only-codepoint-enum (seed)
  (b* (((mv choice seed)
        (defdata::weighted-switch-nat
          '(10 ;; a constant example
            40 ;; hand + skin color
            40 ;; person/man/woman + hair + skin color
            ) seed)))
    (case choice
      (0 ;; constant example
       (b* (((mv idx seed) (defdata::random-index-seed *num-compound-codepoint-examples* seed)))
         (mv (nth idx *compound-codepoint-examples*) seed)))
      (1 ;; hand + skin color
       (b* (((mv hand-choice seed) (switch-nat-safe-seed 5 seed))
            (hand-codepoint (case hand-choice (0 #x1F448) (1 #x1F449) (2 #x1F44D) (3 #x1F44E) (t #x1F918)))
            ((mv optional-skin-color-modifier seed) (optional-skin-color-modifier-enum seed)))
         (mv (cons hand-codepoint optional-skin-color-modifier) seed)))
      (t ;; person/man/woman + hair + skin color
       (b* (((mv person-choice seed) (switch-nat-safe-seed 3 seed))
            (person-codepoint (case person-choice (0 #x1F468) (1 #x1F469) (t #x1F9D1)))
            ((mv optional-skin-color-modifier seed) (optional-skin-color-modifier-enum seed))
            ((mv optional-hair-color-modifier seed) (optional-hair-color-modifier-enum seed)))
         (mv (cons person-codepoint (append optional-skin-color-modifier optional-hair-color-modifier))
             seed))))))

(defun compound-only-codepoints-enum-acc (len seed acc)
  (declare (xargs :mode :program))
  (if (or (not (acl2-numberp len))
          (<= len 0))
      ;; order matters here
      (mv (reverse acc) seed)
    (b* (((mv compound-codepoints seed)
          (compound-only-codepoint-enum seed)))
      (compound-only-codepoints-enum-acc (1- len) seed (append compound-codepoints acc)))))

(defmacro compound-only-codepoints-enum (len seed)
  `(compound-only-codepoints-enum-acc ,len ,seed nil))


(defun emoji-codepoint-enum (seed)
  (select-from-ranges
   ((:min #x1F400 :max #x1F42C)
    (:min #x1F980 :max #x1F9AD)
    (:min #x1F4BA :max #x1F4DC))
   seed))

(defun emoji-only-codepoints-enum-acc (len seed acc)
  (declare (xargs :mode :program))
  (if (or (not (acl2-numberp len))
          (<= len 0))
      (mv acc seed)
    (b* (((mv codepoint seed)
          (emoji-codepoint-enum seed)))
      (emoji-only-codepoints-enum-acc (1- len) seed (cons codepoint acc)))))

(defmacro emoji-only-codepoints-enum (len seed)
  `(emoji-only-codepoints-enum-acc ,len ,seed nil))

(defun mixed-codepoint-enum (seed)
  (b* (((mv choice seed)
        (defdata::weighted-switch-nat
          '(5 ;; ASCII
            1 ;; Emoji
            1 ;; Greek
            1 ;; Logic
            1 ;; Diacritic
            1 ;; Compound
            ) seed)))
    (case choice
      (0 (b* (((mv codepoint seed) (ascii-codepoint-enum seed)))
           (mv (list codepoint) seed)))
      (1 (b* (((mv codepoint seed) (emoji-codepoint-enum seed)))
           (mv (list codepoint) seed)))
      (2 (b* (((mv codepoint seed) (nth-greek-unicode-codepoint/acc 0 seed)))
           (mv (list codepoint) seed)))
      (3 (b* (((mv codepoint seed) (mathematical-operator-codepoint-enum seed)))
           (mv (list codepoint) seed)))
      (4 (diacritic-modified-alpha-enum seed))
      (t (compound-only-codepoint-enum seed)))))

(defun mixed-codepoints-enum-acc (len seed acc)
  (declare (xargs :mode :program))
  (if (or (not (acl2-numberp len))
          (<= len 0))
      (mv (reverse acc) seed)
    (b* (((mv codepoints seed)
          (mixed-codepoint-enum seed)))
      (mixed-codepoints-enum-acc (1- len) seed (append codepoints acc)))))

(defmacro mixed-codepoints-enum (len seed)
  `(mixed-codepoints-enum-acc ,len ,seed nil))
