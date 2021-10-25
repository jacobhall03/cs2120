import data.set

/-
Exercise: Prove that for any set, L, L ∩ L = L.
-/
example : ∀ (α : Type) (L : set α), L ∩ L = L :=
begin
  intros a L,
  apply set.ext _,
  assume x,
  split,
  --rightwards
  assume ll,
  cases ll,
  apply ll_right,
  --leftwards
  assume l, 
  apply and.intro l l,
end 

/-
Exercise: Give a formal statement and proof, then an 
English language proof, that the union operator on 
sets is commutative.
-/
example : ∀ (α : Type) (A B : set α), A ∪ B = B ∪ A :=
begin
  assume a A B,
  apply set.ext _,
  assume x,
  split,
  --rightwards
  assume aub,
  cases aub with a b,
  apply or.intro_right _ a,
  apply or.intro_left _ b,
  --leftwards
  assume bua,
  cases bua with b a,
  apply or.intro_right _ b,
  apply or.intro_left _ a,
end



/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/


/-
Assignment: read (at least skim) the Sections 1 and 2 of 
the Wikipedia page on set identities: 
https://en.wikipedia.org/wiki/List_of_set_identities_and_relations 
There, , among *many* other facts, you will find definitions 
of left and right distributivity. To complete the remainder
of this assignment, you need to understand what it means for 
one operator to be left- (or right-) distributive over another. 
-/


/-
Exercise: Formally state and prove both formally and 
informally that ∩ is left-distributive over ∩.
-/


/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/


