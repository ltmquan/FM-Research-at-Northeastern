; This file demonstrates a sketch of the automated induction procedure
; using the intuition behind rippling.
;
; Main theorem : (tlp x) => (qsort x) = (isort x)
; i.e. The reverse of the reverse of a list is itself

(in-package "ACL2S")

; Definitions

(definec <<= (x y :all) :bool
  (or (== x y)
      (<< x y)))

(definec insert (a :all x :tl) :tl
  (match x
    (() (list a))
    ((e . es) (if (<<= a e)
                  (cons a x)
                (cons e (insert a es))))))

(definec isort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (insert e (isort es)))))

(definec less (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<< e a)
                  (cons e (less a es))
                (less a es)))))

(definec notless (a :all x :tl) :tl
  (match x
    (() ())
    ((e . es) (if (<<= a e)
                  (cons e (notless a es))
                (notless a es)))))

(definec qsort (x :tl) :tl
  (match x
    (() ())
    ((e . es) (app (qsort (less e es))
                   (list e)
                   (qsort (notless e es))))))

; Proof settings (optional)

(set-induction-depth-limit 2)

; Main theorem (will fail)
(property qsort=isort (x :tl)
  (== (qsort x) (isort x)))

; Fail analysis: induction on (qsort x)
; In the induction, we have:
;   (*) IH1: (qsort (less (car x) (cdr x))) = (isort (less (car x) (cdr x)))
;   (*) IH2: (qsort (notless (car x) (cdr x))) = (isort (notless (car x) (cdr x)))
;   (*) IC: (qsort x) = (isort x)
;        => (app (qsort (less (car x) (cdr x))) (list (car x)) (qsort (notless (car x) (cdr x)))) = (insert (car x) (isort (cdr x)))
; (+) Apply destructor elim with (car x) => x1, (cdr x) => x2
;   (*) IH1: (qsort (less x1 x2)) = (isort (less x1 x2))
;   (*) IH2: (qsort (notless x1 x2)) = (isort (notless x1 x2))
;   (*) IC: (app (qsort (less x1 x2)) (list x1) (qsort (notless x1 x2))) = (insert x1 (isort x2))
;        => (app (qsort (less x1 x2)) (cons x1 (qsort (notless x1 x2)))) = (insert x1 (isort x2))
; Notice we can substitute IH1 and IH2 into IC:
;   (*) IC: (app (isort (less x1 x2)) (cons x1 (isort (notless x1 x2))) = (insert x1 (isort x2))
; Even after substitution, ACL2s will still get stuck. Hence, we need
; to make this its own lemma.

; Closing lemma for qsort_isort (will fail)
; NOTE: you're encouraged to uncomment the ":proofs? nil" line to
; check if this is enough to prove qsort_isort (it should be). This
; would mean we have reduced the proof of qsort_isort down to proving
; this lemma.
(property closing_lemma (a :all x :tl)
;  :proofs? nil
  (== (app (isort (less a x)) (cons a (isort (notless a x))))
      (insert a (isort x))))

; Fail analysis: induction on (notless a x)
; In the induction step, we have
;   (*) IH: (app (isort (less a (cdr x))) (cons a (isort (notless a (cdr x))))) = (insert a (isort (cdr x)))
;   (*) IC: (app (isort (less a x)) (cons a (isort (notless a x)))) = (insert a (isort x))
;        => (app (isort (less a x)) (cons a (isort (notless a x)))) = (insert a (insert (car x) (isort (cdr x))))
; (+) Apply destructor elim with (car x) => x1, (cdr x) => x2, x => (cons x1 x2)
;   (*) IH: (app (isort (less a x2)) (cons a (isort (notless a x2)))) = (insert a (isort x2))
;   (*) IC: (app (isort (less a (cons x1 x2))) (cons a (isort (notless a (cons x1 x2))))) = (insert a (insert x1 (isort x2)))
; Since we are inducting on notless, we actually split this into
; 2 cases: (<<= a x1) and (not (<<= a x1)). Let's tackle the second case first as it's easier.

; CASE 2: (not (<<= a x1)) or, equivalently, (<< x1 a)
; The IC can be simplified to turn into:
;   (*) IC: (app (insert x1 (isort (less a x2))) (cons a (isort (notless a x2))) = (insert a (insert x1 (isort x2)))
; The ACL2s gets stuck here. We will speculate what additional lemma
; we need. We notice that the difference between the LHS of the IC and
; the LHS of the IH is the additional (insert x1 ...) inside the 
; first (isort ...). Thus, we suspect the lemma we need will be of 
; the form:
;   (=> (<< x1 a)
;       (== (app (insert x1 (isort (less a x2))) (cons a (isort (notless a x2))))
;           (?F1 x1 (app (isort (less a x2)) (cons a (isort (notless a x2)))))
; where ?F1 is a meta-variable. We'll bypass HO unification by simply
; trying out different functions we have for ?F1 and using cgen to 
; quickly find a possible match. Eventually, we should get that 
; setting ?F1 = insert works. Thus, we get the conjecture lemma:
;   (=> (<< x1 a)
;       (== (app (insert x1 (isort (less a x2))) (cons a (isort (notless a x2))))
;           (insert x1 (app (isort (less a x2)) (cons a (isort (notless a x2)))))
; where we can do some generalizations to get
;   (=> (<< x1 a)
;       (== (app (insert x1 y) (cons a z))
;           (insert x1 (app y (cons a z)))))

; Generalized enabling lemma for case 2 of closing_lemma
(property gen-e-lemma-case-2 (x1 a :all y z :tl)
  :h (<< x1 a)
  (== (app (insert x1 y) (cons a z))
      (insert x1 (app y (cons a z)))))

; Enabling lemma for case 2 of closing_lemma
(property e-lemma-case-2 (a x1 :all x2 :tl)
  :h (<< x1 a)
  (== (app (insert x1 (isort (less a x2))) (cons a (isort (notless a x2))))
      (insert x1 (app (isort (less a x2)) (cons a (isort (notless a x2)))))))

; Let's continue with the induction proof:
;   (*) IH: (app (isort (less a x2)) (cons a (notless a x2))) = (insert a (isort x2))
;   (*) IC: (app (insert x1 (isort (less a x2))) (cons a (notless a x2))) = (insert a (insert x1 (isort x2)))
;        => (insert x1 (app (isort (less a x2)) (cons a (notless a x2)))) = (insert a (insert x1 (isort x2))) {case-2}
;        => (insert x1 (insert a (isort x2)) = (insert a (insert x1 (isort x2)) {IH}
; Although ACL2s will still get stuck here, the good news is we can 
; again write this as its own lemma, which ACL2s can automate.

; Closing lemma for case 2 of closing_lemma
(property insert-insert (a b :all x :tl)
  (== (insert a (insert b x))
      (insert b (insert a x))))

; Let's move back to the first case where (<<= a x1)
 
; CASE 1: (<<= a x1)
; The IC can be simplied to turn into:
;   (*) IC: (app (isort (less a x2)) (cons a (insert x1 (isort (notless a x2))))) = (insert a (insert x1 (isort x2)))
; We speculate similarly to case 2, with one important difference. 
; Here, we have the additional structure of (insert x1 ...) being 
; inside a (cons ...), which is inside the outer (app ...). Hence,
; we would ideally want to match the structure of the inner
; (cons ...) first. Our (sub)lemma should then be of the form:
;   (=> (<<= a x1)
;       (== (app (isort (less a x2)) (cons a (insert x1 (isort (notless a x2)))))
;           (app (isort (less a x2)) (?F2 x1 (cons a (isort (notless a x2)))))
; Eventually, we should get that setting ?F2 = insert works. Thus, our sublemma is:
;   (=> (<<= a x1)
;       (== (app (isort (less a x2)) (cons a (insert x1 (isort (notless a x2)))))
;           (app (isort (less a x2)) (insert x1 (cons a (isort (notless a x2)))))))
; where we can generalize to get
;   (=> (<< a x1)
;       (== (cons a (insert x1 (isort (notless a x2))))
;           (insert x1 (cons a (isort (notless a x2)))))).

; Enabling sublemma 1 for case 1 of closing_lemma
(property e-sublemma-1-case-1 (a x1 :all x2 :tl)
  :h (<<= a x1)
  (== (cons a (insert x1 (isort (notless a x2))))
      (insert x1 (cons a (isort (notless a x2))))))

; This transforms the IC into
;   (*) IC: (app (isort (less a x2)) (insert x1 (cons a (isort (notless a x2))))) = (insert a (insert x1 (isort x2)))
; Now, we can generate a sublemma to match the outer (app ...) of the form:
;   (=> (<<= a x1)
;       (== (app (isort (less a x2)) (insert x1 (cons a (isort (notless a x2)))))
;           (?F3 x1 (app (isort (less a x2)) (cons a (isort (notless a x2)))))))
; Again, setting ?F3 = insert works, which gives us
;   (=> (<<= a x1)
;       (== (app (isort (less a x2)) (insert x1 (cons a (isort (notless a x2)))))
;           (insert x1 (app (isort (less a x2)) (cons a (isort (notless a x2)))))))
; where we can generalize to get
;   (=> (<<= a x1)
;       (== (app (isort (less a x2)) (insert x1 (cons a y)))
;           (insert x1 (app (isort (less a x2)) (cons a y)))))

; Enabling sublemma 2 for case 1 of closing_lemma
(property e-sublemma-2-case-1 (a x1 :all x2 y :tl)
  :h (<<= a x1)
  (== (app (isort (less a x2)) (insert x1 (cons a y)))
      (insert x1 (app (isort (less a x2)) (cons a y)))))

; Enalbling lemma for case 1 of closing_lemma
(property e-lemma-case-1 (a x1 :all x2 :tl)
  :hints (("goal" :use ((:instance e-sublemma-1-case-1
				   (a a) (x1 x1) (x2 x2))
			(:instance e-sublemma-2-case-1
				   (a a) (x1 x1) (x2 x2) (y (isort (notless a x2)))))))
  :h (<<= a x1)
  (== (app (isort (less a x2)) (cons a (insert x1 (isort (notless a x2)))))
      (insert x1 (app (isort (less a x2)) (cons a (isort (notless a x2)))))))

; From here, we get:
;   (*) IC: (app (isort (less a x2)) (insert x1 (cons a (isort (notless a x2))))) = (insert a (insert x1 (isort x2)))
;        => (insert x1 (app (isort (less a x2)) (cons a (isort (notless a x2))))) = (insert a (insert x1 (isort x2))) {case-1-app}
;        => (insert x1 (insert a (isort x2))) = (insert a (insert x1 (isort x2))) {IH}
;        => t {insert-insert}

; Closing lemma for qsort_isort (restated)
(property closing_lemma (a :all x :tl)
  :hints (("goal" :in-theory (disable gen-e-lemma-case-2
				      e-sublemma-1-case-1
				      e-sublemma-2-case-1)))
  (== (app (isort (less a x)) (cons a (isort (notless a x))))
      (insert a (isort x))))

; Main theorem (restated)
(property qsort_isort (x :tl)
  (== (qsort x) (isort x)))
