import algebra.algebra.basic tactic.ring

namespace hidden

inductive nat : Type 
| zero : nat
| succ (n' : nat) : nat

--zero
def z := nat.zero
#check z
#reduce z


--one
def o := z.succ
#check o
#reduce o

--two
def t := o.succ

--four
def f : nat :=
begin
  exact t.succ.succ
end
#reduce f

--increment
def inc : nat → nat :=
begin
  assume n,
  exact nat.succ n,
end
#reduce inc f

-- increment (alt)
def inc' : nat → nat
| n := nat.succ n

--decrement
def dec : nat → nat
| nat.zero := nat.zero
| (nat.succ n') := n'

--addition
def add : nat → nat → nat
| nat.zero m := m
| (nat.succ n') (m) := 
  /- answer for n'-/
  nat.succ (add n' m)

#reduce add f t

--multiplication
def mul : nat → nat → nat
| nat.zero m := nat.zero
| (nat.succ n') m := add (m) (mul n' m)


def sum_to : nat → nat
| nat.zero := nat.zero
| (nat.succ n') := add (sum_to n') (inc n')

#reduce sum_to f

def exp : nat → nat → nat
| m nat.zero := o
| m (nat.succ n') := mul (m) (exp m n')

#reduce exp t t

#reduce mul f t


end hidden