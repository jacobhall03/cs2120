--comment
/-

multi-line comment

-/


/-
Theorem: Equality is symetric
If x = y, then y = x
∀ (T : Type) (x y : T), x = y → y = x

Prof:
First we'll assume that T is any type and we have objects
x and y of this type. What remains to be shown is that
x = y → y = x. To prove this, we'll assume the premise,
that x = y, and in this context we to prove y = x. ..

Personal:
Assume T is some arbitrary type. Assume x and y is of that type.
Assume proof 'e' (made-up) proves that x = y.
Rewrite x using the axiom of substitutability.
Apply axiom of reflexivity to y = y. QED.
-/

theorem eq_symm :
  ∀ (T : Type) (x y : T), x = y → y = x :=
  begin
    assume (T : Type),
    assume (x y : T),
    assume (e : x = y),
    rw e,    
  end 


/-
Prove that equality is transitive.
-/

theorem eq_trans :
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z :=
  begin
    assume (T : Type),
    assume (x y z : T),
    assume (e1 : x = y),
    assume (r2 : y = z),
    rw e1,
    exact r2,
  end
