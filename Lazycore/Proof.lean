
import Lazycore.NDFormula
import Lazycore.InferenceRule

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

import Mathlib.Data.Finset.Basic
import Lean.Data.HashMap

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

structure ProofNode (α : Type) where
formula : NDFormula α
justification : Justification

instance [BEq α] : BEq (ProofNode (α : Type)) where
beq a b := a.justification == b.justification && a.formula == b.formula

deriving instance DecidableEq for ProofNode

-- α is the type of node IDs, must be comparable and hashable
-- β is the type of proposition symbols
structure ProofState (α β : Type) [BEq α] [Hashable α] [DecidableEq β] where
nodes : Lean.HashMap α (ProofNode β)
--links is in the form of a map from nodeIDs to the finite set of parents
links : Lean.HashMap α (Array α)
--assumptions is an updated map that maps 
assumptions : Lean.HashMap α (Multiset α)

-- instance: BEq (Option (ProofNode β)) where
-- beq a b := 


def verifyAssumption 
  [BEq α] [Hashable α] [DecidableEq β]
  (p : ProofState α β) (id : α) 
  : Sum String (ProofState α β) :=
let nodeOpt := p.nodes.find? id;
let parentsOpt := p.assumptions.find? id;
if H1 : nodeOpt = Option.none ∨ parentsOpt = Option.none then
  Sum.inl "Invalid Index"
else
  let node := nodeOpt.some_get (by{
    simp [Option.isSome, H1] at *;
    cases C : (Lean.HashMap.find? p.nodes id);
    contradiction;
    simp;
  })
  let parents := parentsOpt.some_get (by{
    clear node;
    simp [And.intro] at H1;
    cases C : (Lean.HashMap.find? p.assumptions id);
    contradiction;
    simp;
  })
  if node.justification != Justification.Assumption then
    Sum.inl "Not Justified as an Assumption"
  else
    if parents.size = 0 then
      Sum.inr 
      {p with assumptions := assumptions.insert id (InfrenceRule.Assumption node.formula).conclusion.anticendents} 
    else
      Sum.inl "Assumption has parents but should not"


-- NOTE: Use if-let instead of match with single case

-- def verify [DecidableEq α] (p : Proof idt α) (id : idt) : String ⊕ (Multiset (NDFormula α)) :=
-- let node := p.nodes id
-- let parents := p.links id
-- match node.justification with
-- | Assumption => verifyAssumption p id
-- | AndIntro =>
--   match node.formula with
--   | NDFormula.and leftFormula rightFormula => 
--     if h : parents.size = 2 then 
--       let leftId := (parents[0]'(by simp [h]))
--       let rightId := (parents[1]'(by simp [h]))
--       let leftNode := p.nodes leftId
--       let rightNode := p.nodes rightId
--       if leftFormula != leftNode.formula then
--         Sum.inl "Not Justified as AndIntro"
--       else
--         if rightFormula != rightNode.formula then 
--           Sum.inl "Not Justified as AndIntro"
--         else
--           match (verify p leftId), (verify p leftId) with
--           | Sum.inr Γ, Sum.inr Δ => 
--             Sum.inr (InfrenceRule.AndIntro leftFormula rightFormula Γ Δ).conclusion.anticendents
--           | Sum.inl ε, _ => Sum.inl ε
--           | _, Sum.inl ε => Sum.inl ε
--     else
--       Sum.inl "AndIntro node must have 2 parents but does not"
--   | _ => 
--     Sum.inl "AndIntro node must be a an And formula"
-- | _ => Sum.inl "Nope"
