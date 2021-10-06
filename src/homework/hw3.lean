/-
Name: Jacob Hall
Computing ID: weh7xp
-/


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
<<<<<<< HEAD:src/homework/practice_2.lean
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
=======
>>>>>>> fcba5ad44160653f0c0421bdee35d9d0532b3390:src/homework/hw3.lean
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
/-
Proof:
Assume that we are given abitrary propositions P and Q, separately.
Apply the ↔ introduction rule to P ∧ Q ↔ Q ∧ P.
This changes our goal to now prove P ∧ Q → Q ∧ P and Q ∧ P → P ∧ Q, separately.
For the former proposition, P ∧ Q → Q ∧ P, we assume that we have a proof
of P ∧ Q, which warrants us to now prove Q ∧ P. Apply both ∧ (and) elimination
rules (left and right) to our proof  of P ∧ Q to obtain proofs of P and Q,
separately. Apply the and introduction rule with the proof of Q and proof
of P as arguements to obtain a proof Q ∧ P. 
For the latter propsition, Q ∧ P → P ∧ Q, we assume that we have a proof
of Q ∧ P, which warrants us to now prove P ∧ Q. Apply both ∧ (and) elimination
rules to the proof of Q ∧ P, which gives us proofs of Q and P, separately. 
Apply the ∧ introduction rule with the proofs of P and Q to obtain a proof
of P ∧ Q. QED.

-/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --rightwards
    assume pandqorr,
    have p : P := and.elim_left pandqorr,
    have qorr : Q ∨ R := and.elim_right pandqorr,
    cases qorr with q r,
    --case that Q is true
      apply or.intro_left _ _,
      apply and.intro p q,
    --case that R is true
      apply or.intro_right _ _,
      apply and.intro p r,
  --leftwards
    assume pandqorpandr,
    cases pandqorpandr with pandq pandr,
    --case that P ∧ Q is true
      apply and.intro _ _,
      apply and.elim_left pandq,
      apply or.intro_left _ _,
      apply and.elim_right pandq,
    --case that P ∧ R is true
      apply and.intro _ _,
      apply and.elim_left pandr,
      apply or.intro_right _ _,
      apply and.elim_right pandr,
end
/-
∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R)
Proof:
Assume we are given arbitrary propositions P, Q, and R. 
Apply the ↔ introduction rule to P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R), which
changes to goal to proving P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) and
(P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R), separately.

For the former proposition, P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R), assume
we are given a proof of P ∧ (Q ∨ R), which warrants us to now prove
(P ∧ Q) ∨ (P ∧ R). Applying both ∧ elimination rules to P ∧ (Q ∨ R)
gives us proofs of P and (Q ∨ R), separately. Now there are two cases,
one where P and Q have proofs, and the other where P and R have proofs.
In the former case (P and Q have proofs), our goal is to prove (P ∧ Q) ∨ (P ∧ R),
so apply the left or introduction rule, whose requirement is a proof of P ∧ Q,
which can be obtained by applying the ∧ introduction rule with the individual
proofs of P and Q. In the latter case (P and R have proofs), our goal, again,
is to prove (P ∧ Q) ∨ (P ∧ R), so we would apply the right ∨ introduction rule,
whose requirement is a proof of (P ∧ R), which is attainable by application of
the ∧ introduction rule with the individual proofs of P and R.

For the latter proposition, (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R), we would assume
that we have a proof of (P ∧ Q) ∨ (P ∧ R), which warrants us to prove P ∧ (Q ∨ R).
We must consider the two cases, (P ∧ Q) has a proof and (P ∧ R) has a proof. For
the former case, (P ∧ Q) has a proof, apply both ∧ elimination rules to obtain
proofs of P and Q. Our goal is to prove P ∧ (Q ∨ R), so we can apply the 
∧ introduction rule with the proof of P and an application of the left ∨
introduction rule with a proof of Q. For the latter case, (P ∧ R) has a proof,
apply both ∧ elimination rules to obtain proofs of P and R, separately. Our goal
is to prove P ∧ (Q ∨ R), so we would apply the ∧ introduction rule using the proof
of P and an application of the right ∨ introduction rule using a proof of R.
QED.
-/

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  --rightwards
    assume porqandr,
    cases porqandr with p qandr,
    --case p
      apply and.intro _ _,
      apply or.intro_left _ p,
      apply or.intro_left _ p,
    --case qandr
      apply and.intro _ _,
      apply or.intro_right _ (and.elim_left qandr),
      apply or.intro_right _ (and.elim_right qandr),

  --leftwards
    assume porqandporr,
    have porq : (P ∨ Q) := and.elim_left porqandporr,
    have porr : (P ∨ R) := and.elim_right porqandporr,
    cases porq with p q,
    --case p
      apply or.intro_left _ p,

    --case q
      cases porr with p r,
      --case p
        apply or.intro_left _ p,
      --case r
        apply or.intro_right _ (and.intro q r),
end
/-
Proof:
Assume we are given arbitrary propositions P, Q, and R.
Apply ↔ introduction rule, which changes our goal to proving both
P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R) and (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R).

To prove the former proposition P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R), assume
that we have a proof of P ∨ (Q ∧ R). In the case that we have a proof of P, apply
the ∧ introduction rule. This changes our goal for this case to prove both (P ∨ Q)
and (P ∨ R), separately. We do this by applying the left ∨ introduction rule with
our proof of P to each. In the case that we have a proof of (Q ∧ R), apply the ∧
introduction rule, which changes our case proof goal to proving both (P ∨ Q) and
(P ∨ R), separately. We obtain a proof of (P ∨ Q) by application of the right ∨
introduction rule with a proof of Q obtained by application of the left ∧
elimination rule. We obtain a proof of (P ∨ R) by application of the right ∨
introduction rule with a proof of R obtained by application of the right ∧ 
elimination rule. 

To prove the latter proposition, (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R), we start by
assuming we have a proof of (P ∨ Q) ∧ (P ∨ R), which changes our goal to proving
P ∨ (Q ∧ R). We obtain proofs of (P V Q) and (P ∨ R) by application of the left
and right ∧ elimination rules, respectively. By application of a case analysis, we
can prove P ∨ (Q ∧ R). In the case that we have a proof of P obtained from our proof
of (P ∨ Q), we simply apply the left ∨ introduction rule with the proof of P. In the
case that we have a proof of Q obtained from the case that we have a proof of
(P ∨ Q) and a proof of R obtained from the xase that we have a proof of (P ∨ R), we
apply the right ∨ introduction rule with a proof of (P ∧ R) obtained by application
of the ∧ introduction rule with the proofs of Q and R.
QED.

-/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  --rightwards
    assume pandporq,
    exact and.elim_left pandporq,
  --leftwards
    assume p,
    apply and.intro p _,
    apply or.intro_left Q p,
end
/-
Proof:
Assume we have proofs of the propositions P and Q, separately.
Apply the ↔ introduction rule, which warrants us to prove
both P ∧ (P ∨ Q) → P and P → P ∧ (P ∨ Q). 

For the former proposition, P ∧ (P ∨ Q) → P, we start by assuming we
have a proof of P ∧ (P ∨ Q), which changes our goal to finding a proof of P,
which we can apply the left ∧ elimination rule to our proof of P ∧ (P ∨ Q) to
obtain. 

For the latter proposition, P → P ∧ (P ∨ Q), we start by assuming that we have
a proof of P, which changes our goal to finding a proof of P ∧ (P ∨ Q). We obtain
a proof of this by applying the ∧ introduction rule with our proof of P and an
application of the left ∨ introduction rule with the proof of P. 

QED.

-/

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
/-
Proof:
Assume that we are given arbitrary propositions P and Q.
Apply the ↔ introduction rule, which warrants us to prove the propositions
P ∨ (P ∧ Q) → P and P → P ∨ (P ∧ Q).

For the former proposition, P ∨ (P ∧ Q) → P, we start by assuming we have a
proof of P ∨ (P ∧ Q), which then changes our subgoal to obtaining a proof of P.
There are two cases: one where we have a proof of P and, the other, where we have
a proof of (P ∧ Q). For the first case, we would simply already have exactly a
proof P. For the seccond case, we use the left ∧ elimination rule to obtain a proof
of P, which is exactly what is need to prove P.

For the latter proposition, P → P ∨ (P ∧ Q), we start by assume we have a proof
of P, which warrants us to prove P ∨ (P ∧ Q). Apply the left introduction rule for
∨ using the proof of P, to obtian a proof of P ∨ (P ∧ Q). 
QED.
-/

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
/-
Proof:
Assume we are given an arbitrary proposition, P.
Apply the ↔ introduction rule, which changes our goal to proving
P ∨ true → true and true → P ∨ true. 

To prove the former proposition, P ∨ true → true, we simply assume we
have a proof of P ∨ true and apply the true introduction rule.

To prove the latter proposition, true → P ∨ true, we assume we have a proof
of true, then apply the right ∨ introduction rule using our proof of true.
QED.

-/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --rightwards
    assume porfalse,
    cases porfalse with p f,
    --left disjunct
      exact p,
    --right disjunct
      exact false.elim f,
  --leftwards
    assume p,
    exact or.intro_left _ p,
end
/-
Proof:
Assume that we are given an arbitrary proposition, P.
Apply the ↔ introduction rule, which changes our goal to proving
P ∨ false → P and P → P ∨ false. 

To prove the former proof, we assume we have a proof of P ∨ false, which
changes our subgoal to obtaining a proof of P.
Conducting a case analysis on P ∨ false gives us the case where we have a proof of P
and the case where we have a proof of false. For the first case, we simply apply our
proof of P. For the second case, it is impossible to have a prove of false, so we apply
the false elimination rule. So in order for us to have a proof of P ∨ false, we have a proof 
of P. 

To prove the latter proof, we assume we are given a proof of P, which changes our goal
to proving P ∨ false. Apply the left ∨ introduction rule using the proof of P. 
QED.
-/

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
/-
Proof:
Assume we are given a proof an arbitrary proposition, P.
Apply the ↔ introduction rule, which warrant us to proof 
P ∧ true → P and P → P ∧ true.

To prove the former proposition, P ∧ true → P, assume we have a 
proof of P ∧ true, then apply a proof of P obtained by application
of the left elimination rule for ∧. 

To prove the latter proposition, P → P ∧ true, assume we have a proof
of P, then apply the ∧ introduction rule with our proof of P and the
true introduction rule. 
QED.
-/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro _ _,
  --rightwards
    assume pandfalse,
    exact and.elim_right pandfalse,
  --leftwards
    assume f,
    cases f,
end
/-
Proof:
Assume we are given an arbitrary proposition, P.
Apply the ↔ introduction rule, which changes our goal to proving
P ∧ false → false and false → P ∧ false.

To prove the former proposition, P ∧ false → false, we assume we have
a proof of P ∧ false, which changes our subgoal to obtaining a proof of false.
We do this by application of the right ∧ elimination rule on our proof of P ∧ false.

To prove the latter proposition, false → P ∧ false, we assume we are given a proof of false,
which changes our goal to obtaining a proof of P ∧ false. We then consider our cases, which
there are none that we can obtain a proof of P ∧ false. So false → P ∧ false.
QED.
-/


