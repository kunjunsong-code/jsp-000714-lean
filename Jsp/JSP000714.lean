import Init.Data.List.Basic
import Init.Data.List.Lemmas

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

/-!
# JSP-000714 - Lean 4.20.0, no Mathlib

## Question
How many Sidon subsets do the first several positive integers have?

## Answer (for {1,...,6})
A subset S is Sidon if all pairwise sums a+b (a ≤ b) from S are distinct.
For {1,...,6} there are exactly 36 Sidon subsets out of 2^6 = 64.

All proofs use decide. No sorry, no admit, no native_decide.
-/

def pairSums (S : List Nat) : List Nat :=
  S.flatMap fun a => S.flatMap fun b => if a <= b then [a + b] else []

def hasDuplicate : List Nat -> Bool
  | [] => false
  | (x::xs) => xs.contains x || hasDuplicate xs

def isSidon (S : List Nat) : Bool :=
  ! hasDuplicate (pairSums S)

def powerSet {alpha : Type} : List alpha -> List (List alpha)
  | [] => [[]]
  | (x::xs) => (powerSet xs).map (fun s => x :: s) ++ powerSet xs

def countSidon (n : Nat) : Nat :=
  (powerSet (List.range' 1 n)).filter isSidon |>.length

theorem sidonCount_6 : countSidon 6 = 36 := by decide

#print axioms sidonCount_6