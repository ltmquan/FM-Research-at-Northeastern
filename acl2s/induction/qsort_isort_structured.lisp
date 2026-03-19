(in-package "ACL2S")

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

; Proof: The high-level idea of the proof is to follow along the automation of ACL2s and generate lemmas whenever ACL2s gets stuck. There are two types of lemmas that needs to be generated: (1) *enabling* lemmas that help turn the induction goal into the induction hypothesis and (2) *closing* lemmas that proves the goal. Enabling lemmas are generated inside an induction step where the induction hypothesis has not been used yet, its purpose is to match the induction goal to the induction hypothesis. Closing lemmas are generated after the induction hypothesis has been used, its purpose is to prove what's left of the goal.

; Let's start with letting ACL2s try to do the proof on its own. A big thing to notice here is that ACL2s will actually use the induction hypothesis twice in the induction step. ACL2s only acknowledges the second use of the induction hypothesis, so I suspect the first use was due to some simplification rewrites. Specifically, Subgoal *1/5' has the first use, and subgoals *1/5'4' and *1/5'5' have the second use.

(set-gag-mode nil)
(set-induction-depth-limit 1)

(property qsort=isort (x :tl)
  (== (qsort x) (isort x)))

; Now let's move on to the actual proof plan of qsort=isort. Every lemma is labeled by either "enabling" or "closing" to indicate its use.

:u
(set-induction-depth-limit 2) ; Only needed for "cons-insert-2"

; Closing lemma for the lemma "induction step"
(property insert-insert (a b :all x :tl)
  (== (insert a (insert b x))
      (insert b (insert a x))))

; Enabling lemma for the lemma "case-2"
(property cons-insert-2 (a :all x :tl)
  (== (cons a (insert a (isort (notless a x))))
      (insert a (cons a (isort (notless a x))))))

; Enabling lemma for the lemma "case-3"
(property cons-insert-3 (a b :all x :tl)
  :h (<< a b)
  (== (cons a (insert b (isort (notless a x))))
      (insert b (cons a (isort (notless a x))))))

; Enabling lemma for the lemma "case-1"
(property app-insert-1 (a b :all x1 x2 :tl)
  :h (<< b a)
  (== (app (insert b x1) (cons a x2))
      (insert b (app x1 (cons a x2)))))

; Enabling lemma for the lemma "case-2"
(property app-insert-2 (a :all x1 x2 :tl)
  (== (app (isort (less a x1)) (insert a (cons a x2)))
      (insert a (app (isort (less a x1)) (cons a x2)))))

; Enabling lemma for the lemma "case-3"
(property app-insert-3 (a b :all x1 x2 :tl)
  :h (<< a b)
  (== (app (isort (less a x1)) (insert b (cons a x2)))
      (insert b (app (isort (less a x1)) (cons a x2)))))

; Enabling lemma for the lemma "induction step"
(property case-1 (a b :all x :tl)
  :h (<< b a)
  (== (app (insert b (isort (less a x))) (cons a (isort (notless a x))))
      (insert b (app (isort (less a x)) (cons a (isort (notless a x)))))))

; Enabling lemma for the lemma "induction step"
(property case-2 (a :all x :tl)
  :hints (("goal" :use ((:instance app-insert-2
				   (a a) (x1 x) (x2 (isort (notless a x)))))))
  (== (app (isort (less a x)) (cons a (insert a (isort (notless a x)))))
      (insert a (app (isort (less a x)) (cons a (isort (notless a x)))))))

; Enabling lemma for the lemma "induction step"
(property case-3 (a b :all x :tl)
  :h (<< a b)
  (== (app (isort (less a x)) (cons a (insert b (isort (notless a x)))))
      (insert b (app (isort (less a x)) (cons a (isort (notless a x)))))))

; Closing lemma for the lemma "qsort=isort"
; Note: I had to disable all the enabling lemmas in order to prove this, I think having them allows ACL2s to do some simplification rewrites that makes it harder to apply, specifically, the lemma "case-2".
(property induction-step (a :all x :tl)
  :hints (("goal" :in-theory (disable cons-insert-2
				      cons-insert-3
				      app-insert-1
				      app-insert-2
				      app-insert-3)))
  (== (app (isort (less a x)) (cons a (isort (notless a x))))
      (insert a (isort x))))

; Main theorem
(property qsort=isort (x :tl)
  (== (qsort x) (isort x)))
  