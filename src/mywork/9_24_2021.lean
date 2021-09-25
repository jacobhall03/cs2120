-- 1
example : 0 ≠ 1 :=
begin
  -- ¬ (0 = 1)
  apply not.intro, -- (0 = 1) → false
  assume h, --no cases
  cases h, --case analysis
end 

-- 2
example : 0 ≠ 0 → 2 = 3 :=
begin
  assume h, -- 0 = 0 → false
  exact false.elim (h (eq.refl 0)), -- get proof of 0 = 0 by eq.refl
  --apply to h to get proof of false
  --apply false.elim with proof of false, done.
end

--or

example : 0 ≠ 0 → 2 = 3 :=
begin
  contradiction,
end

-- 3
example : ∀ (P : Prop), P → ¬¬P :=
begin
  -- P → (¬P → false)
  -- P → ((P → false) → false)
  assume P,
  assume p,
  apply not.intro, --not neccessary
  assume notp,
  have f : false := notp p,
  exact f,
  -- or cases f
end

-- 4
example : ∀ (P : Prop), ¬¬P → P :=
begin
  assume P,
  assume notnotp, --stuck
  have pornotp := classical.em P,
  cases pornotp with p notp,
  -- case p
    exact p,
  -- case notp
    have f := notnotp notp,
    exact false.elim f,
    contradiction,
end