
import Lazycore.InferenceRule
import Lazycore.NDFormula
import Lazycore.Sequent

def InfrenceRule.IfIntro [DecidableEq α] (φ ψ : NDFormula α)
(Γ: Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ∪ φ ⊢ₛ ψ], Γ ⊢ₛ φ →ₙ ψ, InfrenceRule.noRestrictions⟩

def InfrenceRule.IfIntro.Valid [DecidableEq α] (φ ψ : NDFormula α)
(Γ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.IfIntro φ ψ Γ)
:= by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  clear inp;
  rw [IfIntro] at *;
  simp at *;
  rw [Sequent.sat] at *;
  simp at *;
  intro f;
  rw [NDFormula.sat];
  intro i;
  apply s;
  intro f2 fOr;
  cases fOr;{
    apply f;
    exact h;
  };{
    rw [h];
    exact i;
  }
}