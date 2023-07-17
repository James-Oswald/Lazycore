import Lazycore.NDFormula
import Mathlib.Data.Multiset.Basic

--A simple sequent conditional in the form assumptions ⊢ formula
--see https://en.wikipedia.org/wiki/Sequent#The_form_and_semantics_of_sequents
structure Sequent (α  : Type) where
anticendents : Multiset (NDFormula α) 
concequent : NDFormula α

infix:15 " ⊢ₛ " => Sequent.mk
infix:15 " |-ₛ " => Sequent.mk

/-
Semantics of a Simple conditional assertion sequent
If all of the anticendents are true than the concequent is true
-/
def Sequent.sat [DecidableEq α] (interpretation : α -> Prop) (s : Sequent α) : Prop :=
(∀ (f : NDFormula α), f ∈ s.anticendents -> (interpretation ⊨ₙ f)) ->
(interpretation ⊨ₙ s.concequent)

infix:15 " ⊨ₛ " => Sequent.sat
infix:15 " |=ₛ " => Sequent.sat

def Sequent.valid [DecidableEq α] (sequent : Sequent α) : Prop :=
∀ (interpretation : α -> Prop), interpretation ⊨ₛ sequent

prefix:15 " ⊨ₛ " => Sequent.valid
prefix:15 " |=ₛ " => Sequent.valid