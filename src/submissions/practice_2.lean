/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.

↔ (if and only if)


-/

example : true := true.intro

example : false := _    -- trick question? why?
--There are no proofs of 'false'.

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    --left disjunct
      assume p,
      exact p,
    --right disjunct
      assume p,
      exact p,
    
  -- backwards
  assume p,
  apply or.intro_left P p,
end
/-
Proof: If we assume that we are given an arbitrary proposition, P, and that
we apply the ↔ introduction rule, we must then proof the proposition that P ∨ P → P and P → P ∨ P, separately. 
For the former proposition, P ∨ P → P, we assume that we are given a proof
of P ∨ P, then we apply the or elimination rule to obtain a proof of P.
To use the elimination rule to deduce a proof of P, we must obtain a proof
that P → P, twice (one for the left disjunct, the other for the right disjunct).
We prove these by applying the → (implies) introduction rule. Now we must 
obtain a proof of the latter proposition, P → P ∨ P. Applying the introduction
rule for → gives a proof of P. Apply either introduction rule for ∨ using
the proof of P. QED.

-/



example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --rightwards
    assume pandp,
    apply and.elim_left pandp,
  --leftwards
    assume p,
    apply and.intro p p,
end
/-
Proof:
Assume that we are given a proof of an arbitary proposition, P.
Apply the ↔ introduction rule. Now the goal is to prove P ∧ P → P
and P → P ∧ P, separately. For the former proposition, P ∧ P → P,
we obtian a proof of P ∧ P by application of the introduction rule
for →. Then by application of either ∧ elimination rule (left or right)
we obtian a proof of P. For the latter propostion, P → P ∧ P, we start by
applying the → introduction rule, which gives a proof of P. Apply the proof
of P as both arguements for the ∧ introduction rule, which then gives a proof
of P ∧ P. QED.
-/

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --rightwards
    assume porq,
    apply or.elim porq,
    --left disjunct
      assume p,
      apply or.intro_right Q p,
    --right disjunct
      assume q,
      apply or.intro_left P q,
  --leftwards
    assume qorp,
    apply or.elim qorp,
    --left disjunct
      assume q,
      apply or.intro_right P q,
    --right disjunct
      assume p, 
      apply or.intro_left Q p,
end
/-
Proof:
Assume we are given arbitrary propositions, P and Q, separately.
Apply the ↔ introduction rule to P ∨ Q ↔ Q ∨ P.
Now we are left to prove P ∨ Q → Q ∨ P and Q ∨ P → P ∨ Q, separately.
For the former proposition, P ∨ Q → Q ∨ P, we start by assuming that we
have a proof of P ∨ Q. Applying the or elimination rule to the proof of
P ∨ Q, changes our subgoal to proving the propositions that P → Q ∨ P and
Q → Q ∨ P, separately. For the left disjunct, assume that we are given a
proof of P and apply the right ∨ introduction rule using that proof of P.
For the right disjunct, assume that we are given a proof of Q and apply the
left ∨ introduction rule using that proof of Q.
For the latter proposition, Q ∨ P → P ∨ Q, assume that we have a proof of
Q ∨ P. Applying the or elimination rule with Q ∨ P requires us to proof
that Q → P ∨ Q and P → P ∨ Q, separately. To prove the left disjunct, we assume
that we area given a proof of Q and apply the right ∨ introducion rule using
that proof of Q. To prove the right disjunct, we assume that we are given a
proof of P and apply the left ∨ introduction rule using the proof of P. QED. 

-/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --leftwards
    assume pandq,
    apply and.intro (and.elim_right pandq) (and.elim_left pandq),
  --rightwards
    assume qandp,
    apply and.intro (and.elim_right qandp) (and.elim_left qandp),
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --rightwards
    assume pandqorr,
    have qorr : Q ∨ R := and.elim_right pandqorr,
    cases qorr,
    --case that Q is true
      apply or.intro_left _ _,
      apply and.intro (and.elim_left pandqorr) qorr,
    --case that R is true
      apply or.intro_right _ _,
      apply and.intro (and.elim_left pandqorr) qorr,
  --leftwards
    assume pandqorpandr,
    cases pandqorpandr,
    --case that P ∧ Q is true
      apply and.intro _ _,
      apply and.elim_left pandqorpandr,
      apply or.intro_left _ _,
      apply and.elim_right pandqorpandr,
    --case that P ∧ R is true
      apply and.intro _ _,
      apply and.elim_left pandqorpandr,
      apply or.intro_right _ _,
      apply and.elim_right pandqorpandr,
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --rightwards
    assume pandporq,
    apply and.elim_left pandporq,
  --leftwards
    assume p,
    apply and.intro p _,
    apply or.intro_left Q p,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
    assume P Q,
    apply iff.intro _ _,
    --rightwards
      assume porpandq,
      cases porpandq with p pandq,
      --case P
      apply p,
      --case P ∧ Q
      apply and.elim_left pandq,
    --leftwards
      assume p,
      apply or.intro_left _ p,
end

example : ∀ (P : Prop), P ∨ true ↔ true :=   --need a proof for each direction
begin
  assume P,
  apply iff.intro _ _,
  --rightwards
    assume port,
    apply true.intro,
  --leftwards
    assume t,
    apply or.intro_right _ t,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --rightwards
    assume porfalse,
    sorry
end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --rightwards
    assume pandtrue,
    apply and.elim_left pandtrue,
  --leftwards
    assume p,
    apply and.intro p true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  --rightwards
    assume pandfalse,
    apply and.elim_right pandfalse,
  --leftwards
    assume f,
    sorry
end


