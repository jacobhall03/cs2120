/-
Numbers:

ℕ: Natural numbers. The non-negative whole numbers. (0, 3, 11, 29, …)
ℤ: Integers: The negative and non-negative whole numbers. (-29, 0, 3, 11) 
ℚ: Rationals: Ratios of an integer and a non-zero natural number. (1/2, -3/4, 23/7)
ℝ: Reals: Equivalence classes of convergent sequence of rationals. (0.000…, .33333……, 3.1415…..)
Irrational numbers: Real numbers not "isomorphic" to any rationals. (3.1415….., e, sqrt(2) )
-/

/-
Inference Rules:

#1: Equality is Reflexive. 
    Proof that everything is equal to itself
    ∀ (T : Type) (t : T), t = t

#2: Substitution of Equals for Equals.
    Proof that if P is a type, and all types have property, t, and 
    x and y are of a type, x has a property, p, and x = y, then
    you can conclude that y has property, p. 
-/

/-
Introduction Rules:
  

      =
  Apply eq.refl

-/