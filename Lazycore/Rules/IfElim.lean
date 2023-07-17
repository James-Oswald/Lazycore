
import Lazycore.InferenceRule
import Lazycore.NDFormula
import Lazycore.Sequent

def InfrenceRule.IfElim [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
InfrenceRule α := 
⟨[Γ ⊢ₛ φ →ₙ ψ, Δ ⊢ₛ φ], Γ ∪ Δ ⊢ₛψ, InfrenceRule.noRestrictions⟩

def InfrenceRule.IfIntro.Valid [DecidableEq α] (φ ψ : NDFormula α)
(Γ Δ : Multiset (NDFormula α)) :
⊨ᵢ (InfrenceRule.IfElim φ ψ Γ Δ)
:= by{
  unhygienic
  rw [InfrenceRule.valid];
  intros i;
  rw [InfrenceRule.sat];
  intros s inp;
  clear inp;
  rw [IfElim] at *;
  simp at *;
  cases s;
  rw [Sequent.sat] at *;
  simp at *;
  intro f;
  rw [NDFormula.sat] at *;
  apply left;
  {
    intro f2 fg;
    apply f;
    apply Or.inl;
    exact fg;
  };
  apply right;
  {
    intro f2 fd;
    apply f;
    apply Or.inr;
    exact fd;
  }
}