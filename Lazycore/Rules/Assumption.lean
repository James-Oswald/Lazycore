import Lazycore.InferenceRule
import Lazycore.NDFormula
import Lazycore.Sequent

def InfrenceRule.Assumption {α : Type} [DecidableEq α] (φ : NDFormula α)
: InfrenceRule α := 
⟨[], φ ⊢ₛ φ, InfrenceRule.noRestrictions⟩

theorem InfrenceRule.Assumption.Valid [DecidableEq α] (φ : NDFormula α) :
⊨ᵢ (InfrenceRule.Assumption φ)
:= by{
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  rw [Assumption] at *;
  simp at *;
  rw [Sequent.sat];
  intro f;
  simp at *;
  exact f;
}