
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
structure ProofState (α β : Type) [BEq α] [Hashable α] [DecidableEq α] where
nodes : Lean.HashMap α (ProofNode β)
--links is in the form of a map from nodeIDs to the finite set of parents
links : Lean.HashMap α (Array α)
--assumptions is an updated map that maps 
assumptions : Lean.HashMap α (Multiset (NDFormula β))

-- instance: BEq (Option (ProofNode β)) where
-- beq a b := 


def verifyAssumption
  [BEq α] [Hashable α] [ToString α]
  [DecidableEq α] [DecidableEq β]
  (p : ProofState α β) (id : α) 
  : Sum String (ProofState α β) :=
let nodeOpt := p.nodes.find? id;
let parentsOpt := p.links.find? id;
if let (some node, some parents) := (nodeOpt, parentsOpt) then
  if node.justification = Justification.Assumption then
    if parents.size = 0 then
        Sum.inr 
        {p with assumptions := (Lean.HashMap.insert p.assumptions id 
          (InfrenceRule.Assumption node.formula).conclusion.anticendents
        )} 
    else
      Sum.inl s!"Assumption has {parents.size} parents but should not have any"
  else
    Sum.inl "Not Justified as an Assumption"
else
  Sum.inl s!"Invalid Index Proof Node index: {id}"
  
/-
α is the type of node IDs
β is the type of prop names on formulae 
-/
def verifyAndIntro
  [BEq α] [Hashable α] [ToString α]
  [DecidableEq α] [DecidableEq β]
  (p : ProofState α β) (id : α)
  : Sum String (ProofState α β) :=
let nodeOpt := p.nodes.find? id;
let parentsOpt := p.links.find? id;
if let (some node, some parents) := (nodeOpt, parentsOpt) then
  if node.justification = Justification.AndIntro then
    if h : parents.size = 2 then
      let leftId := (parents[0]'(by simp [h]))
      let rightId := (parents[1]'(by simp [h]))
      let leftParentOpt := p.nodes.find? leftId
      let rightParentOpt := p.nodes.find? rightId
      if let (some left, some right) := (leftParentOpt, rightParentOpt) then
        if let NDFormula.and leftFormula rightFormula := node.formula then
          if left.formula = leftFormula ∧ right.formula = rightFormula then
            let leftParentAssumptionsOpt := p.assumptions.find? leftId
            let rightParentAssumptionsOpt := p.assumptions.find? rightId
            if let (some leftAssumptions, some rightAssumptions) := 
              (leftParentAssumptionsOpt, rightParentAssumptionsOpt) then
              Sum.inr 
              {p with assumptions := (Lean.HashMap.insert p.assumptions id 
                (InfrenceRule.AndIntro leftFormula rightFormula leftAssumptions rightAssumptions).conclusion.anticendents
              )} 
            else
              Sum.inl "Non-existant parent node ID in assumptions map"
          else 
            Sum.inl "A parent formula does not match formula on the node"
        else
          Sum.inl "AndIntro node does not have And Formula"
      else
        Sum.inl "Non-existant parent node ID in links map"
    else
      Sum.inl s!"AndIntro node has {parents.size} parents but should have 2"
  else
    Sum.inl "Not Justified as an AndIntro"
else
  Sum.inl s!"Invalid Index Proof Node index: {id}"

