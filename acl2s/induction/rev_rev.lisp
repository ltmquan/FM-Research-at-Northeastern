; This file demonstrates a sketch of the automated induction procedure
; using the intuition behind rippling. This is an example where we only
; need to generate enabling lemmas (in this case, just one)
;
; Main theorem : (tlp x) => (rev (rev x)) = x
; i.e. The reverse of the reverse of a list is itself

(in-package "ACL2S")

; Definitions

(definec ap (a b :tl) :tl
  (match a
    (nil b)
    ((f . r) (cons f (ap r b)))))

(definec rv (x :tl) :tl
  (match x
    (nil nil)
    ((f . r) (ap (rv r) (list f)))))

; Proof settings (optional)

(set-induction-depth-limit 1)

; Main theorem (will fail)
(property rv-rv (x :tl)
  (== (rv (rv x)) x))

; Fail analysis: induction on x
; In the induction step, we have:
;   (*) IH: (rv (rv (cdr x))) = (cdr x)
;   (*) IC: (rv (rv x)) = x
;        => (rv (ap (rv (cdr x)) (list (car x)))) = x
; (+) Apply destructor elim with (car x) => x1, (cdr x) => x2, x => (cons x1 x2)
;   (*) IH: (rv (rv x2)) = x2
;   (*) IC: (rv (ap (rv x2) (list x1))) = (cons x1 x2)
; This is where the ACL2s gets stuck. Here we will speculate what
; additional lemma we need. Generally, we want to be able to apply
; the IH to the LHS of the IC. The difference between the IC and the
; IH in that regards is that, the IC has an additional (ap ...) and
; (list x1). Thus, we suspect the lemma we need will be of the form:
;   (== (rv (ap (rv x2) (list x1)))
;       (?F1 (list x1) (rv (rv x2))))
; where ?F1 is a meta-variable. Here, the theoreotically correct
; thing to do would be to use HO unification, but we can't afford
; that. Instead, we'll just try to substitute all the appropriate
; functions we have for ?F1 (WIP). Eventually, we should get that
; setting ?F1 = ap works. Thus, we get the conjecture lemma:
;   (== (rv (ap (rv x2) (list x1)))
;       (ap (list x1) (rv (rv x2))))
; where we can do some generalizations to get
;   (== (rv (ap y (list z)))
;       (ap (list z) (rv y))).

; Generalized enabling lemma for rv-rv
(property gen-e-lemma (y :tl z :all)
  (== (rv (ap y (list z)))
      (ap (list z) (rv y))))

; Enabling lemma for rv-rv
(property e-lemma (x1 :all x2 :tl)
  (== (rv (ap (rv x2) (list x1)))
      (ap (list x1) (rv (rv x2)))))

; From here, we can continue with the induction proof:
; (*) IH: (rv (rv x2)) = x2
; (*) IC: (rv (ap (rv x2) (list x1))) = (cons x1 x2)
;      => (ap (list x1) (rv(rv x2)))  = (cons x1 x2) {rv-ap}
;      => (ap (list x1) x2)           = (cons x1 x2) {IH}
;      => t                                          {trivial}

; Main theorem (restated)
(property rv-rv (x :tl)
  (== (rv (rv x)) x))
