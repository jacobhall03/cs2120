namespace implies

axioms (P Q : Prop)

def if_P_is_true_then_so_is_Q : Prop :=
  P → Q

-- assume P is true
-- assume we have a proof of P (p)
axiom p : P

axiom pq : if_P_is_true_then_so_is_Q
--assume that we have a proof, pq, of P → Q

--intro for implies: assume premise, show conclusion
--elim for implies: 

#check pq
#check p
#check (pq p) --pq is sort of like a function that, when given p,
--returns a proof of Q
/-
Suppose P and Q are propositions and you
know that P → Q and that P are both true.
Show that Q is true. 

Proof: Apply the truth of P → Q to the
truth of P to derive the truth of Q.

Alt. Proof: By the elimination rule for → with
pq applied to p.

Alt. Alt. Proof: By "modues ponens". QED
-/

end implies
namespace all
/-
FORALL
-/

axioms
 (T : Type)
 (P : T → Prop)
 (t : T)
 (a : ∀ (x : T), P x)

--Does t have property P?

example : P t := a t

#check a t

end all


/-
AND & →
-/

axioms (P Q : Prop)

/-
Want a proof of P ∧ Q.
-/