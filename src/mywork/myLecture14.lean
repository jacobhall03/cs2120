axioms 
  (Person : Type)
  (Likes : Person → Person → Prop)

example :
  ¬ (∀ p : Person, Likes p p) ↔
  ∃ p : Person, ¬ Likes p p :=
  begin
    apply iff.intro,
    --forwards
      assume h,
      have f := classical.em (∃ (p : Person), ¬ Likes p p),
      cases f,
      --case there is someone who dislikes self
        exact f,
      --case there is NOT someone who dislikes self
        --propose new fact, proof to be constructed in this ---
        have contra : ∀ (p : Person), Likes p p := _,
        --prove current goal using proposed fact
        contradiction,

        assume p,

        have g := classical.em (Likes p p),
        cases g,
        exact g,
        have a : ∃ (p : Person), ¬Likes p p := exists.intro p g,
        contradiction,
    
    --backwards
      
  end