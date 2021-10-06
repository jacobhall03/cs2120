/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
----------------------------------
              (q : Q)
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q p2q p,
  apply p2q p,
end

-- Extra credit [2 points]. Who invented this principle?
--Theophrastus


-- -------------------------------------


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

-- For any given proposition, there is either a proof or no proof of it.
We could say that to have a proof of proposition means that it
is true, but to not have a proof of a proposition means that it
is false, untill proven otherwise. So, logically, for a proposition
to be true, there must be a proof of it. So, for true to be true, then
there must always be a proof of true. 

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := true.intro


-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

-- If you have a proof of P and Q, separately, then,
by applying the ∧ introduction rule, you can construct
a proof of P ∧ Q.

ELIMINATION

Given the elimination rules for ∧ in both
inference rule and English language forms.
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀(P Q : Prop), Q ∧ P → P :=
  begin
    assume P Q pandq,
    apply and.elim_right pandq,
  end


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

-- The introduction rule for ∀ is to assume that, if you are given a
proof of an arbitrary proposition that you had no control over, P, and,
in that context, can derive a proof of the proposition Q, then you can
conlude that you have a proof that 'for all' propositions P, you can
derive a proof of Q.
-- You would prove ∀ (t : T), Q by, first, assuming you are given a proof
of t of an arbitrary type, T, then derive a proof of Q, in that context.
Because you had no influence on the type of the proposition, t, then, you
can conclude that 'for all propositions, t, of type, T, a prove of Q can be
derived'.   

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                        (q : Q)

-- If you have a proof that for all propositions t, of type, T, there is
proof of Q and you have a proof of t and it is an arbitrary type, T, then you
can apply the 'for all' proof to the proof of t, to get a proof of Q.

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- You would simply apply the proof pf to the value (t : T), to get a
proof of Q.
-/

/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  (Lynn : Person)
  -- (2) Lynn knows logic
  (LynnKnowsLogic : KnowsLogic Lynn)

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example : BetterComputerScientist Lynn := 
begin
  apply LogicMakesYouBetterAtCS,
  apply LynnKnowsLogic,
end



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

/-
Proof by negation is the act of assuming that one has a proof
of a proposition, let's call it P, and, in that context,
deriving a proof of false or some other contradiction, such
as having proofs of P and ¬P.

Becuase ¬P is the same as P → false, we start by assuming we have
a proof of P and, in that context, we derive a proof of false. We
then apply the false elimination rule using our proof of false. 
-/

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume __¬P__ and show that ____you can derive a contradiction______.
From this derivation you can conclude _____¬¬P_____.
Then you apply the rule of negation ______elimination______
to that result to arrive at a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is _____logically_____ valid, and that accepting the axiom
of the __________ suffices to establish negation
__________ (better called double _____ _________)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀(a b : Prop), (a ↔ b) → (b ↔ a) :=
begin
 assume a b,
 assume aiffb,
 apply iff.intro _ _,
 apply iff.elim_right aiffb,
 apply iff.elim_left aiffb,
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

/-
For all people, p, who have the distinct properties Nice and
Talented, all people, q, likes person, p. John Lennon is a person.
There is an assumed proof (axiom), JLNT, that John Lennon has both
properties Nice and Talented. All people, p, therefore, like John
Lennon.
-/
def ELJL : Prop := 
  ∀ (Person : Type)
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)
    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    

example : ELJL :=
begin
  unfold ELJL,
  intros,
  apply elantp,
  apply JLNT.left,
  apply JLNT.right,
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? _4_
-- list the cases (informaly)
    -- the car is heavy and red
    -- the car is heavy and blue
    -- the car is light and red
    -- the car is light and blue

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop :=
  ∀ (T : Type) (x y z : T), x = y → y = z → x = z


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
  ∀(P : Prop), (¬¬P → P) ↔ (P ∨ ¬P)

example : negelim_equiv_exmid :=
begin
  unfold negelim_equiv_exmid,
  assume P,
  apply iff.intro,
  --rightwards
    assume nnpimpp,
    have pornp := classical.em P,
    exact pornp,
  --leftwards
    assume pornp,
    assume nnp,
    cases pornp with p np,
    --case p
      exact p,
    --case np
      have f := nnp np,
      exact false.elim f,
end
/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

axiom Loves : Person → Person → Prop

example : (∃(x : Person), ∀(y : Person), (Loves x y)) →
(∀(a s : Person), (Loves a s) ↔ (Loves s a)) → 
(∀(e : Person), ∃(x : Person), (Loves e x)) :=
begin
  assume h1 h2,
  assume e,
  cases h1 with x pf,
  apply exists.intro x,
  have lexifflxe := h2 e x,
  have lxeimplex := iff.elim_right lexifflxe,
  have lxe := pf e,
  have lex := lxeimplex lxe,
  exact lex,
end
