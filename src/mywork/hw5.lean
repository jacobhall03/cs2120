import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)
  (p : α → Prop)
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition.

(3) Write an informal proof of the proposition.
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:
-/
/-
If there's a function,f, that maps/takes every α value to β such 
it that satifies the proposition that p applied to a implies q
applied to f applied to a, and if there exists an a of type α
that satisfies the proposition p applied to a, then there must
exist a b of type β that satisfies the proposition q applied
to b. 

-/

-- Give your formal proof here
begin
  assume h1,
  assume h2,
  cases h1 with aimpb patoqb,
  cases h2 with aa pa,
  apply exists.intro _ _,
  have b := aimpb aa,
  apply b,
  have qfa := patoqb aa pa,
  exact qfa,
end
  
/-
Informal Proof:

Assume ∃ (f : α → β) such that it satisfies ∀ (a : α), p a → q (f a).
Assume that ∃ (a : α), p a. 
From ∃ (f : α → β), ∀ (a : α), p a → q (f a) we can have a proof
of α → β (call it 'aimpb') and a proof of ∀ (a : α), p a → q (aimpb a),
which we'll call 'qatoqb'.
From ∃ (a : α), p a, we can have a proof of an arbitrary value of α
(call it 'aa') and a proof of 'p a' which we can simply call 'pa'. 
To prove ∃ (b : β), q b it suffices to provide a proof of an arbitrary
value of type β and a proof of q applied to a value of type β. We can
obtian a proof of an arbitrary value of β by applying aimpb to aa. 
We can obtian a proof of q b (the same as q applied to aimpb applied to aa)
by applying patoqb to the arbitrary value of α (aa) and the proof of
p applied to a (pa). QED.

-/
