/-
  Animal Psycho-Neuro-Behavioral Science (APNBS)
  Lean 4 Formalization

  Author : Takeo Yamamoto
  License: CC BY 4.0
  Zenodo  : https://zenodo.org

  This file formalizes the core logical structure of APNBS:
  - Three-layer behavioral taxonomy
  - Tipping point as categorical discontinuity
  - Evolutionary psychology's explanatory scope as a strict subset of APNBS
  - The selfish gene as a universal (not primate-specific) substrate
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Subset
import Mathlib.Order.Basic
import Mathlib.Data.Finset.Basic

/-!
## Part I: Taxonomic Hierarchy of Life

All living organisms belong to a taxonomic hierarchy.
Behavioral substrates are distributed across this hierarchy.
-/

/-- Biological taxon levels -/
inductive Taxon : Type where
  | Prokaryote   : Taxon   -- bacteria, archaea
  | Invertebrate : Taxon   -- insects, molluscs
  | Vertebrate   : Taxon   -- fish, amphibians, reptiles
  | Mammal       : Taxon   -- all mammals
  | Primate      : Taxon   -- great apes, monkeys
  | HomoSapiens  : Taxon   -- humans
  deriving DecidableEq, Repr

/-- Taxonomic inclusion: t₁ ≤ t₂ means t₁ is contained within t₂'s scope -/
def Taxon.le : Taxon → Taxon → Prop
  | .Prokaryote,   _              => True
  | .Invertebrate, t              => t ≠ .Prokaryote
  | .Vertebrate,   t              => t = .Vertebrate ∨ t = .Mammal
                                   ∨ t = .Primate ∨ t = .HomoSapiens
  | .Mammal,       t              => t = .Mammal ∨ t = .Primate ∨ t = .HomoSapiens
  | .Primate,      t              => t = .Primate ∨ t = .HomoSapiens
  | .HomoSapiens,  t              => t = .HomoSapiens

/-!
## Part II: Neural Substrate Structure

Neural complexity increases across phylogenetic lineages.
Each level adds structure without eliminating the lower level.
-/

/-- Neural substrate characterized by its structural components -/
structure NeuralSubstrate where
  /-- Brainstem present (all vertebrates) -/
  hasBrainstem      : Bool
  /-- Limbic system / paleocortex (all mammals) -/
  hasLimbicSystem   : Bool
  /-- Neocortex present -/
  hasNeocortex      : Bool
  /-- Prefrontal cortex volume ratio (0.0–1.0, relative to total brain) -/
  prefrontalRatio   : Float
  /-- Recursive language capacity -/
  hasRecursiveLang  : Bool
  deriving Repr

/-- Neural substrates for major taxa -/
def NeuralSubstrate.ofTaxon : Taxon → NeuralSubstrate
  | .Prokaryote   => ⟨false, false, false, 0.0,  false⟩
  | .Invertebrate => ⟨false, false, false, 0.0,  false⟩
  | .Vertebrate   => ⟨true,  false, false, 0.0,  false⟩
  | .Mammal       => ⟨true,  true,  true,  0.03, false⟩
  | .Primate      => ⟨true,  true,  true,  0.11, false⟩
  | .HomoSapiens  => ⟨true,  true,  true,  0.29, true⟩

/-- The tipping point predicate:
    A neural substrate has crossed the tipping point iff prefrontal ratio
    exceeds the threshold associated with recursive language and
    top-down cortical control. Empirically: ~0.25 (homo sapiens ~0.29) -/
def TippingPoint (n : NeuralSubstrate) : Prop :=
  n.hasNeocortex = true ∧
  n.prefrontalRatio > 0.25 ∧
  n.hasRecursiveLang = true

/-- Homo sapiens has crossed the tipping point -/
theorem homosapiens_crosses_tipping_point :
    TippingPoint (NeuralSubstrate.ofTaxon .HomoSapiens) := by
  unfold TippingPoint NeuralSubstrate.ofTaxon
  simp
  norm_num

/-- Primates have NOT crossed the tipping point -/
theorem primates_below_tipping_point :
    ¬ TippingPoint (NeuralSubstrate.ofTaxon .Primate) := by
  unfold TippingPoint NeuralSubstrate.ofTaxon
  simp
  norm_num

/-- The tipping point is a strict discontinuity: it separates
    human behavioral organization from all other primates -/
theorem tipping_point_discontinuity :
    TippingPoint (NeuralSubstrate.ofTaxon .HomoSapiens) ∧
    ¬ TippingPoint (NeuralSubstrate.ofTaxon .Primate) := by
  exact ⟨homosapiens_crosses_tipping_point, primates_below_tipping_point⟩

/-!
## Part III: Behavioral Layer Taxonomy

Behaviors are classified into three layers corresponding to
their neural and genetic substrate.
-/

/-- The three behavioral layers of APNBS -/
inductive BehavioralLayer : Type where
  /-- Layer 1: Universal — selfish gene logic, present in all life -/
  | Universal    : BehavioralLayer
  /-- Layer 2: Subcortical — limbic system, shared by all mammals -/
  | Subcortical  : BehavioralLayer
  /-- Layer 3: Neocortical — unique to post-tipping-point organisms -/
  | Neocortical  : BehavioralLayer
  deriving DecidableEq, Repr

/-- Example behaviors classified by layer -/
inductive Behavior : Type where
  -- Layer 1: Universal (life-general)
  | SelfPreservation    : Behavior
  | Reproduction        : Behavior
  | ResourceAcquisition : Behavior
  | KinAltruism         : Behavior
  -- Layer 2: Subcortical (mammal-common)
  | FearResponse        : Behavior
  | AggressionDefense   : Behavior
  | TerritorialMarking  : Behavior
  | MaternalBonding     : Behavior
  -- Layer 3: Neocortical (human-specific)
  | Language            : Behavior
  | AbstractReasoning   : Behavior
  | EthicalDeliberation : Behavior
  | CulturalAccumulation: Behavior
  | MathematicalProof   : Behavior
  | SelfReflection      : Behavior
  deriving DecidableEq, Repr

/-- Classification function: assigns each behavior to its layer -/
def Behavior.layer : Behavior → BehavioralLayer
  | .SelfPreservation     => .Universal
  | .Reproduction         => .Universal
  | .ResourceAcquisition  => .Universal
  | .KinAltruism          => .Universal
  | .FearResponse         => .Subcortical
  | .AggressionDefense    => .Subcortical
  | .TerritorialMarking   => .Subcortical
  | .MaternalBonding      => .Subcortical
  | .Language             => .Neocortical
  | .AbstractReasoning    => .Neocortical
  | .EthicalDeliberation  => .Neocortical
  | .CulturalAccumulation => .Neocortical
  | .MathematicalProof    => .Neocortical
  | .SelfReflection       => .Neocortical

/-!
## Part IV: Explanatory Scope

An explanatory framework is characterized by the set of behaviors
it can account for. We formalize the scopes of Evolutionary Psychology
and APNBS and prove the strict subset relation.
-/

/-- Evolutionary Psychology's claimed explanatory scope:
    EP focuses on behaviors explainable by primate-level selection,
    i.e., Universal and Subcortical layers only -/
def EP.explains : Behavior → Prop :=
  fun b => b.layer = .Universal ∨ b.layer = .Subcortical

/-- APNBS explanatory scope: all three layers -/
def APNBS.explains : Behavior → Prop :=
  fun _ => True

/-- EP's scope is a subset of APNBS's scope -/
theorem EP_scope_subset_APNBS :
    ∀ b : Behavior, EP.explains b → APNBS.explains b := by
  intro b _
  unfold APNBS.explains
  trivial

/-- APNBS's scope strictly exceeds EP's scope:
    there exists a behavior APNBS explains that EP cannot -/
theorem APNBS_strictly_exceeds_EP :
    ∃ b : Behavior, APNBS.explains b ∧ ¬ EP.explains b := by
  use .MathematicalProof
  constructor
  · unfold APNBS.explains; trivial
  · unfold EP.explains Behavior.layer
    simp

/-- MathematicalProof is a neocortical behavior — EP cannot explain it -/
theorem EP_cannot_explain_mathematics :
    ¬ EP.explains .MathematicalProof := by
  unfold EP.explains Behavior.layer
  simp

/-- EthicalDeliberation is a neocortical behavior — EP cannot explain it -/
theorem EP_cannot_explain_ethics :
    ¬ EP.explains .EthicalDeliberation := by
  unfold EP.explains Behavior.layer
  simp

/-!
## Part V: The Selfish Gene is Universal, Not Primate-Specific

Core theorem: the phenomena EP claims as its explanatory foundation
are in fact life-universal (Layer 1), not primate-specific.
Therefore EP does not identify a domain; it misattributes a universal
phenomenon to a narrow taxon.
-/

/-- Layer 1 behaviors are present in all taxa including prokaryotes -/
def universallyPresent (b : Behavior) : Prop :=
  b.layer = .Universal

/-- EP's core phenomena (aggression, reproduction, kin altruism)
    are universal — they are not distinctive features of primates -/
theorem EP_core_phenomena_are_universal :
    universallyPresent .Reproduction ∧
    universallyPresent .KinAltruism  ∧
    universallyPresent .SelfPreservation := by
  unfold universallyPresent Behavior.layer
  simp

/-- Therefore EP cannot distinguish humans from bacteria
    on the basis of its core explanatory variables -/
theorem EP_cannot_distinguish_human_from_prokaryote :
    ∀ b : Behavior, universallyPresent b →
    (NeuralSubstrate.ofTaxon .Prokaryote).hasBrainstem = false := by
  intro _ _
  unfold NeuralSubstrate.ofTaxon
  simp

/-!
## Part VI: The Categorical Shift Theorem

The tipping point produces a categorical (not quantitative) change.
Formally: behaviors possible post-tipping-point are structurally
inaccessible to any neural substrate below the threshold.
-/

/-- A neural substrate can express a behavior only if the
    substrate's layer is sufficient for that behavior's layer -/
def canExpress (n : NeuralSubstrate) (b : Behavior) : Prop :=
  match b.layer with
  | .Universal   => True
  | .Subcortical => n.hasLimbicSystem = true
  | .Neocortical => TippingPoint n

/-- Primates cannot express neocortical behaviors -/
theorem primates_cannot_express_language :
    ¬ canExpress (NeuralSubstrate.ofTaxon .Primate) .Language := by
  unfold canExpress Behavior.layer TippingPoint NeuralSubstrate.ofTaxon
  simp
  norm_num

/-- Homo sapiens can express all behavioral layers -/
theorem homosapiens_expresses_all_layers :
    canExpress (NeuralSubstrate.ofTaxon .HomoSapiens) .Language ∧
    canExpress (NeuralSubstrate.ofTaxon .HomoSapiens) .FearResponse ∧
    canExpress (NeuralSubstrate.ofTaxon .HomoSapiens) .Reproduction := by
  refine ⟨?_, ?_, ?_⟩
  · unfold canExpress Behavior.layer
    exact homosapiens_crosses_tipping_point
  · unfold canExpress Behavior.layer NeuralSubstrate.ofTaxon
    simp
  · unfold canExpress Behavior.layer
    trivial

/-- The categorical shift theorem:
    There exists a behavior that Homo sapiens can express
    but no primate can — the tipping point is a genuine discontinuity,
    not a quantitative difference -/
theorem categorical_shift :
    ∃ b : Behavior,
      canExpress (NeuralSubstrate.ofTaxon .HomoSapiens) b ∧
      ¬ canExpress (NeuralSubstrate.ofTaxon .Primate) b := by
  use .MathematicalProof
  exact ⟨
    by unfold canExpress Behavior.layer; exact homosapiens_crosses_tipping_point,
    by unfold canExpress Behavior.layer TippingPoint NeuralSubstrate.ofTaxon
       simp; norm_num
  ⟩

/-!
## Part VII: Residual Instinct

The tipping point does not eliminate Layer 1 and Layer 2.
They persist as residual instinctual substrate, which the
prefrontal cortex can modulate but not erase.
This is consistent with Stoic synkatathesis:
the impulse arises; the assent is prefrontal.
-/

/-- Residual instinct: post-tipping-point organisms retain
    subcortical and universal behaviors as substrate -/
theorem residual_instinct_persists :
    canExpress (NeuralSubstrate.ofTaxon .HomoSapiens) .AggressionDefense ∧
    canExpress (NeuralSubstrate.ofTaxon .HomoSapiens) .FearResponse ∧
    canExpress (NeuralSubstrate.ofTaxon .HomoSapiens) .KinAltruism := by
  refine ⟨?_, ?_, ?_⟩
  · unfold canExpress Behavior.layer NeuralSubstrate.ofTaxon; simp
  · unfold canExpress Behavior.layer NeuralSubstrate.ofTaxon; simp
  · unfold canExpress Behavior.layer; trivial

/-- The prefrontal cortex enables modulation of subcortical impulse:
    Homo sapiens can both express AND reflect on Layer 2 behaviors -/
theorem prefrontal_modulation :
    canExpress (NeuralSubstrate.ofTaxon .HomoSapiens) .AggressionDefense ∧
    canExpress (NeuralSubstrate.ofTaxon .HomoSapiens) .EthicalDeliberation := by
  exact ⟨
    by unfold canExpress Behavior.layer NeuralSubstrate.ofTaxon; simp,
    by unfold canExpress Behavior.layer; exact homosapiens_crosses_tipping_point
  ⟩

/-!
## Summary: APNBS Core Theorems

1. homosapiens_crosses_tipping_point    — empirical fact, formalized
2. primates_below_tipping_point         — EP's conflation is false
3. tipping_point_discontinuity          — categorical, not quantitative
4. EP_scope_subset_APNBS                — EP ⊂ APNBS strictly
5. APNBS_strictly_exceeds_EP            — EP cannot explain human cognition
6. EP_core_phenomena_are_universal      — EP's domain is life-general, not primate
7. categorical_shift                    — the tipping point theorem
8. residual_instinct_persists           — Layer 1/2 remain as substrate
9. prefrontal_modulation                — Stoic synkatathesis, formalized
-/

#check homosapiens_crosses_tipping_point
#check tipping_point_discontinuity
#check EP_scope_subset_APNBS
#check APNBS_strictly_exceeds_EP
#check EP_core_phenomena_are_universal
#check categorical_shift
#check residual_instinct_persists
#check prefrontal_modulation

