

import Lazycore.NDFormula
import Lazycore.Sequent
import Lazycore.InferenceRule
import Mathlib.Data.Multiset.Basic

import Lazycore.Rules.Assumption
import Lazycore.Rules.AndIntro
import Lazycore.Rules.AndElim
import Lazycore.Rules.OrIntro
import Lazycore.Rules.OrElim
import Lazycore.Rules.NotIntro
import Lazycore.Rules.NotElim
import Lazycore.Rules.IfIntro
import Lazycore.Rules.IfElim
import Lazycore.Rules.IffIntro
import Lazycore.Rules.IffElim

inductive Justification where
| Assumption
| AndIntro
| AndElim
| OrIntro
| OrElim
| NotIntro
| IfIntro
| IffElim
deriving Repr, BEq, DecidableEq

abbrev JA := Justification.Assumption
abbrev JAI := Justification.AndIntro
abbrev JAE := Justification.AndElim
abbrev JOI := Justification.IfIntro
abbrev JOE := Justification.OrElim

structure UnvalidatatedProofNode (α : Type) where
formula : NDFormula α
justification : Justification

abbrev Upn := UnvalidatatedProofNode
alias UnvalidatatedProofNode.formula ← F 
alias UnvalidatatedProofNode.justification ← J

structure ValidatedProofNode (α : Type) where
original : UnvalidatatedProofNode α
assumptions : Multiset (NDFormula α)

abbrev Vpn := ValidatedProofNode
alias ValidatedProofNode.original ← O
alias ValidatedProofNode.assumptions ← A

--An unvalidated proofnode is just a formula with extra information
def Upn.asFormula (n : Upn α) : (NDFormula α) := n.formula
instance : Coe (Upn α) (NDFormula α) where coe := Upn.asFormula

--A Validated proof node can just be interpreted as a sequent as a structure with
--A set of assuptions and a formulae they prove
def Vpn.asSequent (n : Vpn α) : (Sequent α) := n.assumptions ⊢ₛ n.original.formula 
instance : Coe (Vpn α) (Sequent α) where coe:= Vpn.asSequent
alias Vpn.asSequent ← σ

-- instance [BEq α] : BEq (UnvalidatatedProofNode (α : Type)) where
-- beq a b := a.justification == b.justification && a.formula == b.formula

def verifyAssumption [DecidableEq α] (n : Upn α) 
: Except String (Vpn α) :=
if n.justification = JA then
  .ok ⟨n, (InfrenceRule.Assumption n.formula).conclusion.anticendents⟩ 
else
  .error "Expected Assumption justification"

theorem verifyAssumption.sound {α : Type} 
[ToString α] [DecidableEq α]
(vn: Vpn α) (φ : NDFormula α):
verifyAssumption (O vn) = .ok vn →
(⊨ᵢ [] ⊢ᵢ σ vn) ∧ vn = ⟨⟨φ , JA⟩, φ⟩ 
:= by{
  intro H;
  rw [verifyAssumption] at H;
  split at H;
  . next h =>{
    simp [InfrenceRule.Assumption] at H;
    rw [<-H, σ, Vpn.asSequent];
    apply And.intro;
    {
      apply InfrenceRule.Assumption.Valid;
    };{
      simp at H;
      simp [H, h, O] at *;
      rw [<-H];
      simp [h, H];
      
    }
    
  }
  .next => contradiction
}

theorem verifyAssumption.complete {α : Type} 
[ToString α] [DecidableEq α]
(vn: Vpn α) (φ : NDFormula α):
(⊨ᵢ [] ⊢ᵢ σ vn) ∧ vn = ⟨⟨φ , JA⟩, φ⟩
→ verifyAssumption (O vn) = .ok vn
:= by{
  intro H;
  unhygienic
  cases H;
  rw [verifyAssumption];
  split;
  . next => {
    simp [InfrenceRule.Assumption];
    
  }
  . next => contradiction;
}
  
def verifyAndIntro [ToString α] [DecidableEq α] 
(lp rp : Vpn α) (n : Upn α) 
: Except String (ValidatedProofNode α) := 
if n.justification = Justification.AndIntro then
  if let NDFormula.and lf rf := n.formula then
    let lpof := lp.original.formula
    let rpof := rp.original.formula
    if lf = lpof then
      if rf = rpof then
        .ok ⟨n, (InfrenceRule.AndIntro lf rf lp.assumptions rp.assumptions).conclusion.anticendents⟩ 
      else
        .error s!"Right subformulae {rf} expected to match right parent formula {rpof}"
    else
      .error s!"Left subformulae {lf} expected to match left parrent {lpof}"
  else
    .error "Expected formula to have top level and operator"
else
  .error "Expected AndIntro justification"


theorem verifyAndIntro.sound
{α : Type} [ToString α] [DecidableEq α] (n : Upn α) (lp rp vn: Vpn α) 
: verifyAndIntro lp rp n = .ok vn →
(⊨ᵢ [lp.asSequent, rp.asSequent] ⊢ᵢ vn.asSequent)     
:= by{
    rw [verifyAndIntro];
    intro H;
    split at H;
    . next h1 => {
      split at H;
      . next x lf rf h2 => {
        simp at H;
        split at H;
        . next h3 => {
          split at H;
          . next h4 => {
            simp [InfrenceRule.AndIntro] at H;
            rw [Vpn.asSequent, Vpn.asSequent, Vpn.asSequent];
            rw [<-H, h2, h3, h4];
            simp;
            rw [<-InfrenceRule.AndIntro];
            apply InfrenceRule.AndIntro.Valid;
          }
          . next => contradiction;
        }
        . next => contradiction;
      }
      . next => contradiction;
    }
    . next h => contradiction
}

theorem verifyAndIntro.complete
{α : Type} [ToString α] [DecidableEq α] (lp rp vn: Vpn α) 
: (⊨ᵢ [lp.asSequent, rp.asSequent] ⊢ᵢ vn.asSequent) ∧  
  (vn.original.justification = Justification.AndIntro) → 
  verifyAndIntro lp rp vn.original = .ok vn
:= by{
  intro H;
  unhygienic
  cases H;
  rw [verifyAndIntro];
  split;
  . next h1 => {
    split;
    . next h2 => {sorry}
    . next h2 => {sorry}
  };
  . next h1 => contradiction; 
}

--verifyAndIntro is correct w.r.t inferential semantics of 
--Bringsjordian natural deduction
-- theorem verifyAndIntro.Correct
-- {α : Type} [ToString α] [DecidableEq α] (n : Upn α) (lp rp vn: Vpn α) 
-- : verifyAndIntro lp rp n = .ok vn ↔ 
-- (⊨ᵢ [lp.asSequent, rp.asSequent] ⊢ᵢ vn.asSequent)     
-- := by{
--   rw [verifyAndIntro];
--   apply Iff.intro;
--   --Soundness
--   {
--     intro H;
--     split at H;
--     . next h1 => {
--       split at H;
--       . next x lf rf h2 => {
--         simp at H;
--         split at H;
--         . next h3 => {
--           split at H;
--           . next h4 => {
--             simp [InfrenceRule.AndIntro] at H;
--             rw [Vpn.asSequent, Vpn.asSequent, Vpn.asSequent];
--             rw [<-H, h2, h3, h4];
--             simp;
--             rw [<-InfrenceRule.AndIntro];
--             apply InfrenceRule.AndIntro.Valid;
--           }
--           . next => contradiction;
--         }
--         . next => contradiction;
--       }
--       . next => contradiction;
--     }
--     . next h => contradiction
--   };
--   --Completeness
--   {
--     intro H;
--     split;
--     . next h1 => sorry;
--     . next h2 => {
--       cases n;
--     } 
--   };
-- }
