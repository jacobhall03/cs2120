
-- Jacob Hall
-- weh7xp

import data.set
import tactic.ring
namespace relation

-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive,
  assume ex,
  assume asym,
  assume reflex,
  cases ex with b pf,
  have rbb := reflex b,
  have contra := asym rbb,
  contradiction,
end
/-
English Language Proof:
Assume that β is inhibited (exists), r is asymmetric, and that r is 
reflexive. We now must derive a contradiction. From our proof that
there exists a (b : β), we have ourselves a proof of (b : β) and of true.
If we apply the property of reflexivity to (b : β) we get a proof of (r b b).
If we apply the property of asymmetrity to (r b b) we get a proof of (¬r b b),
which is a contradiction.
QED.

Removing the first condition will make the proposition false. You would
be unable to derive a contradiction that r is both asymmetric and reflexive. 
-/


/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.
-/
example : (∃ (b : β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  assume b,
  unfold transitive reflexive asymmetric,
  assume trans refl asym, --proof by negation
  cases b with b pf,
  have rbb := refl b,
  have contra := asym rbb,
  contradiction,
end





/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  assume s s1 s2,
  assume s1ins s2ins,
  assume s1s2 s2s1,
  apply set.ext,
  assume x,
  split,
  --right
  assume xins1,
  have xins2 := s1s2 xins1,
  exact xins2,
  --left
  assume xins2,
  have xins1 := s2s1 xins2,
  exact xins1,
end
/-
Informal Proof:
  If we assume that we are given a set, s, and two sets, s1 and s2, that are
  powersets of the the set s. We them assume that s1 is a subset of s2
  and that s2 is a subset of s1. We must not prove that s1 = s2. By applying
  set extensionality, that now entitles us to prove that for all x in s1
  x is in s2, and vice-versa. We can assume that we have a proof of an
  arbitrary x. To prove that if x is in s1, then x is in s2, we first assume
  that x is in s1. Then we apply our proof that s1 is a subset of s2 to get
  a proof that x is in s2, which gives us a proof that x is in s2. To prove
  that if x is in s2, then x is in s1, we first assume that x is in s2.
  Then we apply our proof that s2 is a subset s1 to our proof that x is in s1,
  which gives us a proof that x is in s1.
  QED. 
-/


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  assume n,
  unfold divides,
  apply exists.intro n,
  ring,
end
/-
Informal Proof that, for any n, 1 divided n:
Assume that we are given an arbitrary value, n. This leaves us to
proof that there exists some k such that n = k * 1. Applying the
introduction rule for exists to n, leaves us to prove n = n * 1, which
is true BY THE RING AXIOMS! QED.
-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  assume n,
  unfold divides,
  apply exists.intro 1,
  ring,
end
/-
Informal Proof that, for any n, n divides n:
Assume that we are given an arbitrary value, n. This leaves us to
prove that there exists some k such that n = k * n. Applying the
introduction rule for exists to 1, leaves us to prove n = 1 * n,
which is true by basic algebra.QED.
-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive divides,
  assume x,
  apply exists.intro 1,
  ring,
end 
/-
Informal Proof that divides is reflexive:
Assume that we are given an arbitrary value, n. This leaves us to prove
that there exists some k such that x = k * x. Apply the intro rule for exists
to 1. We then prove x = 1 * x by basic algebra. QED.
-/

-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive divides,
  assume x y z,
  assume h1 h2,
  cases h1 with k1 h1p,
  cases h2 with k2 h2p,
  rw h2p,
  rw h1p,
  apply exists.intro (k1*k2),
  ring,
end 
/-
Informal Proof that divides is transitive:
Assume that we are given arbitrary values x, y, and z. Assume that
there exists some k such that y = k * x and that there exists some other k
such that x = k * y. We must now prove that there exists some k such that
z = k * x. By case analysis on our proof that y = k * x and z = k * y
We can get proofs of some arbitrary k-values that satisfy y = k1 * x and z = k2 *y
and proofs of both y = k1 * x and z = k2 * y with those k-values. We rewrite
z = k * x to k2 * y = k * x, then k2 * y = k * x to k2 * (k1 * x) = k * x.
We must now prove that there exists some k such that k2 * (k1 * x) = k * x.
We can apply the intro rule for exists to our proof of k1 times our proof of k2.
Now we must prove k2 * (k1 * x) = k1 * k2 * x, which is easily provable by
the basic rules of algebra. 
-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/
/-
Divides is not symetric. Take, for example, divides 2 8 (8 = k * 2) which
would be provable by the natural number 4 in place of k. divides 8 2 (2 = k * 8)
would have to be satisfied by k being equal to 1/4, which is not a natural number.
By definition, k must be a natural number, so we have demonstrated that
divides 2 8 and divided 8 2 are a counterexample to the proposition that
divides is symmetric. 
-/

/- 
#F. Prove that divides is antisymmetric. 
-/
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric divides,
  assume x y,
  assume h1 h2,
  cases h1 with k1 h1p,
  cases h2 with k2 h2p,
  rw h1p,
  -- it's obviously true that k1 must equal 1:
  have k1isone : k1 = 1 := sorry,
  rw k1isone,
  ring,
end
/-
Informal proof that divides is antisymmetric:
Assume that we are given arbitrary values x and y. Assume that there exists
some k-values such that y = k * x and x = k * y. From ∃ (k : ℕ), y = k * x
we can get a proof of, say, k1, a value that satifies the proof that y = k1 * x,
and the proof that y = k1 * x. From ∃ (k : ℕ), x = k * y, we can get a proof
of k2, a value that that satifies the proof that x = k2 * y, and the proof that
x = k2 * y. We can rewrite x = y to x = k1 * x. It's obviously true the k1 must
equal to 1, so we now must prove x = 1 * x, which is provable by the basic 
rules of algebra. 
-/


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric irreflexive,
  assume asym,
  assume x,
  assume rxx,
  have notrxx := asym rxx,
  contradiction,
end
/-
Proof that if r is asymmetric then r is irreflexive:
We first assume that r is asymmetric, we have an abitrary value of
type β (call it 'x'), and that we have a proof of the relation x ≺ x (r x x).
Our goal is to now prove false, in other words, derive a contradiction.
From the assumption that r is asymmetric we can get a proof of ¬ x ≺ x (¬r x x).
Our proofs of (r x x) and (¬r x x) contradict eachother. QED.
-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive transitive asymmetric,
  assume irr trans,
  assume x y,
  assume rxy,
  assume ryx,
  have rxx := trans rxy ryx,
  have contra := irr x,
  contradiction,
end
/-
Proof that, if r is irreflexive, and, if r is transitive, then r is asymmetric:
We first assume that r is irreflexive and transitive. We also assume that we
are given arbitrary values (x : β) and (y : β), a proof of (r x y), and a
proof of (r y x). Our goal is to now derive a contradiction.
From transitivity, we can have a proof of (r x x). From irreflexivity, we can
have a proof of (¬ r x x). QED.
-/

-- C
example : (∃ (b : β), true) → transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive,
  assume b trans notsym irr,
  cases b with b t,
  have notrbb := irr b,
  /-
  At this point, we are unable to derive any other proofs
  that would assist us in proving the proposition by contradiction.
  
  However, we can think of a case where r is transitive, not symmetric
  and irreflexive.
  
  Take this series of relations, for example:
  
  1 -> 2
  2 -> 3
  1 -> 3

  The set of relations is transitive because 1 -> 2 and 2 -> 3 exist, so
  1 -> 3 must exist. The set of relations is not sysmmetric because, for example,
  1 -> 2 is a relation, but 2 -> 1 is not present in our set of relations.
  The set of relations is irreflexive, though, because there are no relations
  that say 1 -> 1, 2 -> 2, or 3 -> 3.
  This is a contradiction to the proposition that if a binary relation, r, is
  transitive, and if r is not symetric, then r is NOT irreflexive. We have shown
  that in one case (and possibly more), this simply is not true.
   -/
end


end relation
