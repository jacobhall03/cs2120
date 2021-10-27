-- Name: Jacob Hall
-- Computing ID: weh7xp


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
Proof that union operator on sets is commutative:
Assume we have type α and two sets, A and B, of type α.
Applying the set extensionality enables us to prove 
∀ (x : a), x ∈ A ∪ B ↔ x ∈ B ∪ A. We assume we have a value of type
a. Then we must prove the bimpication both ways. 
The first direction (rightward) can be proven by case analysis. 
If consider both cases (x ∈ A and x ∈ B), then, in both, we can obtain
a proof of x ∈ B ∪ A.
The second direction (leftwards) can be proven by case analysis.
Both cases (x ∈ B and x ∈ A) allow the construction of a proof of
x ∈ A ∪ B. 
QED.
-/


/-
Exercise: Prove that ⊆ is reflexive and transitive.
Give a formal statement, a formal proof, and an English
language (informal) proof of this fact.
-/
example : ∀ (α : Type) (A B C: set α),
(A ⊆ B ∧ B ⊆ C → A ⊆ C) ∧ (A ⊆ A) :=
begin
  assume α A B C,
  split,
  --transitive
  assume abbc,
  have ab := and.elim_left abbc,
  have bc := and.elim_right abbc,
  assume a,
  assume ainA,
  have ainB := ab ainA,
  have ainC := bc ainB,
  exact ainC,
  --reflexive
  assume x,
  assume a,
  exact a,
end
/-
Proof that ⊆ is reflexive and transitive:

Assume we have proofs of a type α and three sets of type α, A, B, and C.
To prove that ⊆ is transitive, we first assume that we have a proof
of A ⊆ B ∧ B ⊆ C. 
If we assume that we have an arbitrary value, a, and that a is in A, then
we must now prove a ∈ C. Applying A ⊆ B to our proof that a is in A gives
us a proof that a is in B. Applying B ⊆ C to our proof that a is in B gives
us a proof that a is in C (a ∈ C).
To prove that ⊆ is reflexive, we simply assume we have an arbitrary value, x,
and that x ∈ A. This assumption yeilds no contradictions, so
QED.
-/


/-
Exercise: Prove that ∪ and ∩ are associative.
Give a formal statement, a formal proof, and an 
English language (informal) proof of this fact.
-/
example : ∀ (α : Type) (A B C : set α),
((A ∪ B) ∪ C) = (A ∪ (B ∪ C)) ∧
((A ∩ B) ∩ C) = (A ∩ (B ∩ C)) :=
begin
  assume α A B C,
  split,

  --union
  apply set.ext _,
  assume x,
  split,
    --rightwards
    assume aubuc,
    cases aubuc with ab c,
    cases ab with a b,
    apply or.intro_left _ a,
    apply or.intro_right _ _, 
    apply or.intro_left _ b,
    apply or.intro_right _ _,
    apply or.intro_right _ c,
    --leftwards
    assume aubuc,
    cases aubuc with a bc,
    apply or.intro_left _ _,
    apply or.intro_left _ a,
    cases bc with b c,
    apply or.intro_left _ _,
    apply or.intro_right _ b,
    apply or.intro_right _ _,
    exact c,

  --intersect
  apply set.ext _,
  assume x,
  split,
    --rightwards
    assume anbnc,
    have anb := anbnc.left,
    have c := anbnc.right,
    have a := anb.left,
    have b := anb.right,
    have bnc := and.intro b c,
    have anbncp := and.intro a bnc,
    exact anbncp,
    --leftwards
    assume anbncp,
    have a := anbncp.left,
    have bc := anbncp.right,
    have b := bc.left,
    have c := bc.right,
    have anb := and.intro a b,
    have anbnc := and.intro anb c,
    exact anbnc,
end
/-
Proof that union and intersect are associative:

Assume we have proofs of a type α and three sets of type α, A, B, and C.

To prove that union associative, we apply set extensionality, which entitles
us to prove ∀ (x : α), x ∈ A ∪ B ∪ C ↔ x ∈ A ∪ (B ∪ C). We assume we have
an arbitrary value of x. We must prove the bimplication both ways.
To prove the proposition rightwards,
we must consider both cases, x ∈ A ∪ B and x ∈ C.
When x ∈ A ∪ B, we must consider the case that x ∈ A and x ∈ B.
When x ∈ A, x ∈ B, or x ∈ C, we can obtian a proof of x ∈ A ∪ (B ∪ C).
To prove the proposition leftwards,
we must consider both cases, x ∈ A and x ∈ B ∪ C.
When x ∈ B ∪ C, we must consider the case that x ∈ B and x ∈ C.
From x ∈ A, x ∈ B, x ∈ C, x ∈ A ∩ B ∩ C follows.

To prove that intersect is associative, we apply set extensionality, which
entitles us to obtain a proof of ∀ (x : α), x ∈ A ∩ B ∩ C ↔ x ∈ A ∩ (B ∩ C).
We assume we have an arbitrary value of x. We must prove the biimplication 
both ways. To prove the proposition rightwards,
we assume we have a proof of x ∈ A ∩ B ∩ C. We can obtian proofs of
x ∈ A, B, and C, separately. We construct a proof of x ∈ B ∩ C, then, in
that context, construct a proof of x ∈ A ∩ (B ∩ C).
To prove the proposition leftwards,
we assume we have a proof of x ∈ A ∩ (B ∩ C), which we can obtian proofs
of x ∈ A and x ∈ B ∩ C from. From x ∈ B ∩ C, we obtain proofs of 
x ∈ B and x ∈ C. We get a proof of x ∈ A ∩ B from the proofs of x ∈ A and
x ∈ B. We get a proof of x ∈ (A ∩ B) ∩ C from the proofs of x ∈ A ∩ B
and x ∈ C. 
QED.


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
example : ∀ (α : Type) (L M R : set α),
L ∩ (M ∩ R) = (L ∩ M) ∩ (L ∩ R) :=
begin
  assume α L M R,
  apply set.ext _,
  assume x,
  split,
    --righwards
    assume lnmnrp,
    have l := lnmnrp.left,
    have mnr := lnmnrp.right,
    have m := mnr.left,
    have r := mnr.right,
    have lnm := and.intro l m,
    have lnr := and.intro l r,
    have lnmnlnr := and.intro lnm lnr,
    exact lnmnlnr,
    --leftwards
    assume lnmnlnr,
    have lnm := lnmnlnr.left,
    have lnr := lnmnlnr.right,
    have l := lnm.left, --or lnr.left
    have m := lnm.right,
    have r := lnr.right,
    have mnr := and.intro m r,
    have lnmnr := and.intro l mnr,
    exact lnmnr,
end
/-
Proof that ∩ is left-distributive over ∩:

Assume that we have a type α and three sets of α: L, M, and R.
Applying set extensionality entitles us to prove 
∀ (x : α), x ∈ L ∩ (M ∩ R) ↔ x ∈ L ∩ M ∩ (L ∩ R).
We assume that we have arbitrary value of x.
We must prove the bimplication in both directions.
To prove the bimplication rightwards, we first assume 
that we have a proof of x ∈ L ∩ (M ∩ R). x ∈ L, x ∈ M, 
and x ∈ R follows from x ∈ L ∩ (M ∩ R). We construct a
proof of x ∈ L ∩ M and a proof of x ∈ L ∩ R, which we can
use to construct a proof of x ∈ L ∩ M ∩ (L ∩ R). 
To prove leftwards, we first assume that we have a proof
of x ∈ L ∩ M ∩ (L ∩ R). From x ∈ L ∩ M ∩ (L ∩ R) we get
proofs of x ∈ L ∩ M and x ∈ L ∩ R. From x ∈ L ∩ M and x ∈ L ∩ R
we get proofs x ∈ L, x ∈ M, and x ∈ R. We can use x ∈ M and x ∈ R
to construct a proof of x ∈ M ∩ R. We can use x ∈ L and x ∈ M ∩ R
to construct a proof of x ∈ L ∩ (M ∩ R).
QED.
-/

/-
Exercise: Formally state and prove both formally 
and informally that ∪ is left-distributive over ∩.
-/
example : ∀ (α : Type) (L M R : set α),
L ∪ (M ∩ R) = (L ∪ M) ∩ (L ∪ R) :=
begin
  assume α L M R,
  apply set.ext _,
  assume x,
  split,
    --rightwards
    assume lumnr,
    cases lumnr with l mnr,
      --case l
      apply and.intro _ _,
      apply or.intro_left _ l, 
      apply or.intro_left _ l,
      --case mnr
      apply and.intro _ _,
      have m := mnr.left,
      apply or.intro_right _ m,
      have r := mnr.right,
      apply or.intro_right _ r,
    --leftwards
    assume lumnlur,
    have lum := lumnlur.left,
    have lur := lumnlur.right,
    cases lum with l m,
      --case l
      apply or.intro_left _ l,
      --case m
      cases lur with l r,
        -- case l & m
        apply or.intro_left _ l,
        --case m & r
        have mnr := and.intro m r,
        apply or.intro_right _ mnr,
end
/-
Proof that ∪ is left-distributive over ∩:

Assume we have a type α and three sets of type α: L, M, and R.
Applying set extensionality entitiles us to prove
∀ (x : α), x ∈ L ∪ M ∩ R ↔ x ∈ (L ∪ M) ∩ (L ∪ R).
We assume we are given an arbitrary value of x.
We must prove the bimplication both ways.

To prove rightwards,
We assume we have a proof of x ∈ L ∪ M ∩ R. Our goal is to now prove
x ∈ (L ∪ M) ∩ (L ∪ R). We must consider both cases:
the case where x ∈ L and the the case where x ∈ M ∩ R.
The case where x ∈ L can be proven by constructing a proof of x ∈ L ∪ M and
x ∈ L ∪ R from x ∈ L. We can then construct a proof of x ∈ (L ∪ M) ∩ (L ∪ R).
The case where x ∈ M ∩ R can be proven by having a proof of x ∈ M and x ∈ R.
From x ∈ M we have a proof of x ∈ L ∪ M. Likewise, from x ∈ R, we have a
proof of x ∈ R we have a proof of x ∈ L ∪ R. From x ∈ L ∪ M and x ∈ L ∪ R
we have a proof of x ∈ (L ∪ M) ∩ (L ∪ R).

To prove leftwards,
We assume we have a proof of x ∈ (L ∪ M) ∩ (L ∪ R). Our goal is to now prove
x ∈ L ∪ (M ∩ R).
We must consider the case where we have a proof of x ∈ L and the case
where we have proof of x ∈ M and x ∈ R.
From x ∈ L, a proof of x ∈ L ∪ (M ∩ R) follows.
From x ∈ M and x ∈ R, a proof of x ∈ M ∩ R follows. From x ∈ M ∩ R
a proof of x ∈ L ∪ (M ∩ R) follows. 
QED.
-/

