def py_triple (A B C : ℕ) : Prop :=
  A*A + B*B = C*C

example: ∃(a b c : ℕ), py_triple a b c :=
begin
  assert py_triple 3 4 5,
end

example: py_triple 3 4 5 :=
begin
  unfold py_triple,
  apply eq.refl,
  apply rfl,
end

example: py_triple 3 4 6 :=
begin
  unfold py_triple,
  apply rfl,
end

