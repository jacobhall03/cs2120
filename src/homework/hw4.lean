-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  -- (0 = 1) → false
  assume h,
  trivial,
end


-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h,
  have zeqz := eq.refl 0,
  have f : false := h zeqz,
  exact false.elim (f),
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  assume P,
  assume (p : P),
  -- ¬¬P
  -- ¬P → false
  -- (P → false) → false
  assume h,
  have f := h p,
  exact f,
end 

-- We might need classical (vs constructive) reasoning 
#check classical.em
open classical
#check em

/-
axiom em : ∀ (p : Prop), p ∨ ¬p

This is the famous and historically controversial
"law" (now axiom) of the excluded middle. It's is
a key to proving many intuitive theorems in logic
and mathematics. But it also leads to giving up on
having evidence *why* something is either true or
not true, in that you no longer need a proof of 
either P or of ¬P to have a proof of P ∨ ¬P.
-/

-- 4
theorem neg_elim : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume h,
  have pornp := classical.em P,
  cases pornp with p pn,
  assumption,
  contradiction,
end

-- 5
theorem demorgan_1 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  assume P Q,
<<<<<<< HEAD
  apply iff.intro,
  --rightwards
    assume notpandq,
    have pornp := classical.em P,
    have qornq := classical.em Q,
    cases pornp with p np,
    --case p
      cases qornq with q nq,
      --case p & q
      have f := notpandq (and.intro p q),
      exact false.elim f,
      --case p & nq
      exact or.intro_right _ nq,
    --case np 
      exact or.intro_left _ np,
  
  --leftwards
    assume notpornotq,
    apply not.intro,
    assume pandq,
    cases notpornotq with notp notq,
    --case notp
      have p := and.elim_left pandq,
      have f := notp p,
      exact f,
    --case notq
     have q := and.elim_right pandq,
     have f := notq q,
     exact f,
=======
  split,
  -- forward
  assume h,
  cases (classical.em P) with p np,
  cases (classical.em Q) with q nq,
  have pq := and.intro p q,
  contradiction,
  exact or.inr nq,
  exact or.inl np,
  -- backward
  admit,
>>>>>>> fcba5ad44160653f0c0421bdee35d9d0532b3390
end
/-
My note on how to prove demorgan 1:

Assume proof of propositions P and Q.
Apply ↔ introduction rule.

Prove (rightwards):
        ¬(P ∧ Q) → ¬P ∨ ¬Q

Assume that we have a proof of ¬(P ∧ Q). Goal changes to proving ¬P ∨ ¬Q.
Invoke law of excluded middle for both P and Q to get separate proofs of
P ∨ ¬P and Q ∨ ¬Q. Consider cases:

Proof of P:
  with proof of Q:
    Obtain proof of P ∧ Q by and introduction rule applied to proofs of P and Q.
    Apply proof of ¬(P ∧ Q) to proof of P ∧ Q to obtain proof of false. Apply false
    elimination rule to proof of false.
  with proof of ¬Q:
    Apply right ∨ introduction rule to proof of ¬Q to get proof of ¬P ∨ ¬Q.
Proof of ¬P:
  with proof Q or ¬Q (ultimately doesn't matter so no need to invoke a further
  case analysis):
    Apply left ∨ introduction rule to proof of ¬P to get proof of ¬P ∨ ¬Q.


Prove (leftwards):
        ¬P ∨ ¬Q → ¬(P ∧ Q)

Assume that we have a proof of ¬P ∨ ¬Q, which changes goal to proving
¬(P ∧ Q).
¬(P ∧ Q) is the same statement as (P ∧ Q) → false.
Assume we have a proof of P ∧ Q. Goal changes to proving false.
Perform case analysis using proof of ¬P ∨ ¬Q.

First case is that we have a proof of ¬P. Apply left and elimination rule to
proof of P ∧ Q to get proof of P. Get proof of false by applying proof of ¬P
to proof of P. 

Second case is that we have a proof of ¬Q. Apply right and elimnation rule to
proof of P ∧ Q to get proof of Q. Get proof of falase by applying proof of ¬Q
to proof of Q. 

QED.
-/


-- 6
theorem demorgan_2 : ∀ (P Q : Prop), ¬ (P ∨ Q) → (¬P ∧ ¬Q) :=
begin
  assume P Q,
<<<<<<< HEAD
  assume notporq,
  have pornotp := classical.em P,
  have qornotq := classical.em Q,
  cases pornotp with p notp,
  --case p
    have f := notporq (or.intro_left _ p),
    exact false.elim f,
  --case notp
    cases qornotq with q notq,
    --case q
      have f := notporq (or.intro_right _ q),
      exact false.elim f,
    --case notq
      exact and.intro notp notq,
=======
  assume h,
  cases (classical.em P) with p np,
  cases (classical.em Q) with q nq,
  have porq := or.intro_left Q p,
  contradiction,
  have porq := or.intro_left Q p,
  contradiction,
  cases (classical.em Q) with q nq,

>>>>>>> fcba5ad44160653f0c0421bdee35d9d0532b3390
end
/-
My note on proving demorgan 2:

Assume proof of propositions P and Q.
Prove:
        ¬(P ∨ Q) → ¬P ∧ ¬Q
Assume we have proof of ¬(P ∨ Q). Changes our goal to proving ¬P ∧ ¬Q.
Get proof of P ∨ ¬P by invoking law of excluded middle with prop P.
Consider cases:
  with proof of P:
    Get a proof of P ∨ Q by applying the left ∨ introduction rule to
    proof of P. Apply proof of ¬(P ∨ Q) to proof of P ∨ Q to get proof
    of false. Apply false elimination rule to proof of false.
  with proof of ¬P:
    with proof of Q:
      Get a proof of P ∨ Q by applying the right ∨ introduction rule to
      proof of Q. Apply proof of ¬(P ∨ Q) to proof of P ∨ Q to get proof
      of false. Apply false elimination rule to proof of false.
    with proof of ¬Q:
      Get proof of ¬P ∧ ¬Q by applying the ∧ introduction rule to proofs
      of ¬P and ¬Q.
  QED.

-/

-- 7
theorem disappearing_opposite : 
  ∀ (P Q : Prop), P ∨ ¬P ∧ Q ↔ P ∨ Q := 
begin
  assume P Q,
  apply iff.intro,
  --rightwards
    assume pornotpandq,
    cases pornotpandq with p notpandq,
    --case P
      exact or.intro_left _ p,
    --case ¬P ∧ Q
      exact or.intro_right _ (and.elim_right notpandq),
  
  --leftwards
    assume porq,
    cases porq with p q,
    --case P
      exact or.intro_left _ p,
    --case Q
      have pornotp := classical.em P,
      cases pornotp with p notp,
      --case P
      exact or.intro_left _ p,
      --case ¬P
      exact or.intro_right _ (and.intro notp q),
end
/-
Note on proving disappearing opposite:

Assume proofs of propositions P and Q.
Apply ↔ introduction rule.

Prove (rightwards):
      P ∨ (¬P ∧ Q) → P ∨ Q

  Assume proof of P ∨ (¬P ∧ Q). Changes goal to proving P ∨ Q.
  Consider cases:
    with proof of P:
      Obtain proof of P ∨ Q by applying the left ∨ introduction rule
      to proof of P.

    with proof of ¬P ∧ Q:
      Get proof of Q by applying the right ∧ elimination rule to proof
      of ¬P ∧ Q. Obtain proof of P ∨ Q by applying the right ∨ introduction
      rule to the proof of Q.

Prove (leftwards):
      P ∨ Q → P ∨ (¬P ∧ Q)

  Assume proof of P ∨ Q. Changes goal to proving P ∨ (¬P ∧ Q).
  Consider cases:
    with proof of P:
      Obtian proof of P ∨ (¬P ∧ Q) by applying the left ∨
      introduction rule to proof of P.
    with proof of Q:
      Get proof of P ∨ ¬P by invoking law of excluded middle on proof
      of proposition P.
      Consider cases:
        with proof of P:
          Obtian proof of P ∨ (¬P ∧ Q) by applying the left ∨
          introduction rule to proof of P.
        with proof of ¬P:
          Get a proof of ¬P ∧ Q by applying the ∧ introduction rule to
          proofs of ¬P and Q. Get proof of P ∨ (¬P ∧ Q) by applying
          the right ∨ introduction rule to proof of ¬P ∧ Q.
  QED.
-/

-- 8
theorem distrib_and_or : 
  ∀ (P Q R: Prop), (P ∨ Q) ∧ (P ∨ R) ↔
                    P ∨ (Q ∧ R) :=
begin
  assume P Q R,
  apply iff.intro,
  --rightwards
    assume porqandporr,
    have porq := and.elim_left porqandporr,
    have porr := and.elim_right porqandporr,
    cases porq with p q,
    --case P
      exact or.intro_left _ p,
    --case q
      cases porr with p r,
      --case p
        exact or.intro_left _ p,
      --case r
        exact or.intro_right _ (and.intro q r),

  --leftwards
    assume porqandr,
    cases porqandr with p qandr,
    --case p
      exact and.intro (or.intro_left _ p) (or.intro_left _ p),
    --case qandr
      have q := and.elim_left qandr,
      have r := and.elim_right qandr,
      exact and.intro (or.intro_right _ q) (or.intro_right _ r),
end

-- remember or is right associative
-- you need this to know what the lefts and rights are
-- 9
theorem distrib_and_or_foil : 
  ∀ (P Q R S : Prop),
  (P ∨ Q) ∧ (R ∨ S) ↔
  (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S) :=
begin
  assume P Q R S,
  apply iff.intro,
  --rightwards
    assume porq_and_rors,
    have porq := and.elim_left porq_and_rors,
    have rors := and.elim_right porq_and_rors,
    cases porq with p q,
    --case p
      cases rors with r s,
      --case p and r
        exact or.intro_left _ (and.intro p r),
      --cases p and s
        have pands := and.intro p s,
        have pandsorqandrqands := or.intro_left _ pands,
        exact or.intro_right _ pandsorqandrqands,
    --case q
      cases rors with r s,
      --case q and r
        have qandr := and.intro q r,
        have qandrorqands := or.intro_left _ qandr,
        have pandsorqandrorqands := or.intro_right _ qandrorqands,
        exact or.intro_right _ pandsorqandrorqands,
      --case q and s
        have qands := and.intro q s,
        have qandrorqands := or.intro_right _ qands,
        have pandsorqandrorqands := or.intro_right _ qandrorqands,
        exact or.intro_right _ pandsorqandrorqands,

  --leftwards
    assume longor, --#lazy
    cases longor with pandr pandsorqandrorqands,
    --case pandr
      have p := and.elim_left pandr,
      have r := and.elim_right pandr,
      have porq := or.intro_left _ p,
      have rors := or.intro_left _ r,
      exact and.intro porq rors,
    --case pandsorqandrorqands
      cases pandsorqandrorqands with pands qandrorqands,
        --case pands
          have p := and.elim_left pands,
          have s := and.elim_right pands,
          have porq := or.intro_left _ p,
          have rors := or.intro_right _ s,
          exact and.intro porq rors,
        --case qandrorqands
          cases qandrorqands with qandr qands,
          --case qandr
            have q := and.elim_left qandr,
            have r := and.elim_right qandr,
            have porq := or.intro_right _ q,
            have rors := or.intro_left _ r,
            exact and.intro porq rors,
          --case qands
            have q := and.elim_left qands,
            have s := and.elim_right qands,
            have porq := or.intro_right _ q,
            have rors := or.intro_right _ s,
            exact and.intro porq rors,
end
--Note:
axioms (P Q R S : Prop)
#check (P ∧ R) ∨ (P ∧ S) ∨ (Q ∧ R) ∨ (Q ∧ S)
#check (P ∧ R) ∨ (P ∧ S) ∨ ((Q ∧ R) ∨ (Q ∧ S))
#check (P ∧ R) ∨ ((P ∧ S) ∨ ((Q ∧ R) ∨ (Q ∧ S)))
--Last check shows 'order of operations'


/- 10
Formally state and prove the proposition that
not every natural number is equal to zero.
-/
lemma not_all_nats_are_zero : ∀(n : ℕ), (n = 0) ∨ (n ≠ 0):=
begin
  assume n,
  apply classical.em,
end 

-- 11. equivalence of P→Q and (¬P∨Q)
example : ∀ (P Q : Prop), (P → Q) ↔ (¬P ∨ Q) :=
begin
  assume P Q,
  apply iff.intro,
  --rightwards
    assume pimpliesq,
    have pornotp := classical.em P,
    cases pornotp with p notp,
    --case p
      have q := pimpliesq p,
      exact or.intro_right _ q,
    --case notp
      exact or.intro_left _ notp,
  
  --leftwards
    assume notporq,
    assume p,
    cases notporq with notp q,
    --case notp
      have f := notp p,
      exact false.elim f,
    --case q
      exact q,
end

-- 12
example : ∀ (P Q : Prop), (P → Q) → (¬ Q → ¬ P) :=
begin
  assume P Q,
  assume pimpliesq,
  assume notq,
  apply not.intro,
  assume p,
  have q := pimpliesq p, 
  have f := notq q,
  exact false.elim f,
end

-- 13
example : ∀ (P Q : Prop), ( ¬P → ¬Q) → (Q → P) :=
begin
  assume P Q,
  assume notpimpliesnotq,
  assume q,
  have pornotp := classical.em P,
  cases pornotp with p notp, 
  --case p
    exact p,
  --case notp
    have notq := notpimpliesnotq notp,
    have f := notq q,
    exact false.elim f,
end



axioms (T : Type) (Q : Prop) (f : ∀ (t : T), Q) (t : T)
example : Q := f t
#check f
