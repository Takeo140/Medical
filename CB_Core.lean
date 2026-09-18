License Apache 2.0  Takeo Yamamoto
namespace Bio

/-
  Computational Biology Core
  --------------------------

  Pipeline:

    Variant / Genotype
          ↓
         PRS
          ↓
    GeneticEffect
          ↓
       CellCore
      /       \
  Protein   CellState
      \       /
       Protocol
          ↓
      Simulation

  Design:
    * Pure functional state transitions
    * No mutation
    * Valid diploid dosage: 0 / 1 / 2
    * PRS is separated from cellular state
    * Genetic background modifies model parameters
-/

/- ============================================================
   Basic genomic types
   ============================================================ -/

abbrev GeneId := String
abbrev VariantId := String
abbrev ProteinId := String

inductive Base
  | A
  | C
  | G
  | T
  deriving Repr, DecidableEq

/-- Genetic variant / SNP. -/
structure Variant where
  id         : VariantId
  gene       : GeneId
  pos        : Nat
  riskAllele : Base
  deriving Repr, DecidableEq

/-- Valid diploid dosage: 0, 1, or 2. -/
structure Dosage where
  value : Nat
  valid : value ≤ 2
  deriving Repr

namespace Dosage

def zero : Dosage :=
  { value := 0
    valid := by decide }

def one : Dosage :=
  { value := 1
    valid := by decide }

def two : Dosage :=
  { value := 2
    valid := by decide }

def ofNat? (n : Nat) : Option Dosage :=
  if h : n ≤ 2 then
    some
      { value := n
        valid := h }
  else
    none

def toFloat (d : Dosage) : Float :=
  Float.ofNat d.value

end Dosage

/-- Individual genotype. -/
structure Genotype where
  variant : Variant
  dosage  : Dosage
  deriving Repr

/-- GWAS effect size. -/
structure VariantWeight where
  variant : Variant
  beta    : Float
  deriving Repr

/- ============================================================
   PRS
   ============================================================ -/

/-- One auditable contribution to PRS. -/
structure VariantContribution where
  variantId    : VariantId
  gene         : GeneId
  dosage       : Dosage
  beta         : Float
  contribution : Float
  deriving Repr

/-- Gene-level score. -/
structure GeneScore where
  gene          : GeneId
  score         : Float
  contributions : List VariantContribution
  deriving Repr

/-- Complete PRS result. -/
structure PolygenicRiskScore where
  geneScores      : List GeneScore
  totalScore      : Float
  variantsUsed    : Nat
  variantsMissing : Nat
  deriving Repr

/-- Find GWAS weight corresponding to a variant ID. -/
def findWeight
    (variantId : VariantId)
    (weights : List VariantWeight) :
    Option VariantWeight :=
  weights.find?
    (fun w => w.variant.id = variantId)

/-- Calculate one variant contribution. -/
def variantContribution
    (gt : Genotype)
    (weights : List VariantWeight) :
    Option VariantContribution :=
  match findWeight gt.variant.id weights with

  | none =>
      none

  | some w =>
      let c :=
        gt.dosage.toFloat * w.beta

      some
        { variantId := gt.variant.id
          gene := gt.variant.gene
          dosage := gt.dosage
          beta := w.beta
          contribution := c }

/-- Calculate contributions belonging to one gene. -/
def geneContributions
    (gene : GeneId)
    (genos : List Genotype)
    (weights : List VariantWeight) :
    List VariantContribution :=
  genos
    |>.filter
      (fun gt => gt.variant.gene = gene)
    |>.filterMap
      (fun gt => variantContribution gt weights)

/-- Sum variant contributions. -/
def sumContributions
    (xs : List VariantContribution) :
    Float :=
  xs.foldl
    (fun acc x => acc + x.contribution)
    0.0

/-- Calculate a gene-level PRS. -/
def computeGeneScore
    (gene : GeneId)
    (genos : List Genotype)
    (weights : List VariantWeight) :
    GeneScore :=
  let cs :=
    geneContributions gene genos weights

  { gene := gene
    score := sumContributions cs
    contributions := cs }

/-- Distinct genes represented in genotype data. -/
def genes
    (genos : List Genotype) :
    List GeneId :=
  genos
    |>.map (fun gt => gt.variant.gene)
    |>.eraseDup

/-- Count genotypes having a GWAS weight. -/
def countUsed
    (genos : List Genotype)
    (weights : List VariantWeight) :
    Nat :=
  genos.countP
    (fun gt =>
      match findWeight gt.variant.id weights with
      | some _ => true
      | none   => false)

/-- Count genotypes without a GWAS weight. -/
def countMissing
    (genos : List Genotype)
    (weights : List VariantWeight) :
    Nat :=
  genos.length - countUsed genos weights

/-- Complete PRS calculation. -/
def computePRS
    (genos : List Genotype)
    (weights : List VariantWeight) :
    PolygenicRiskScore :=

  let gs :=
    genes genos
      |>.map
        (fun gene =>
          computeGeneScore gene genos weights)

  let total :=
    gs.foldl
      (fun acc g => acc + g.score)
      0.0

  { geneScores := gs
    totalScore := total
    variantsUsed := countUsed genos weights
    variantsMissing := countMissing genos weights }

/-- Direct variant-level PRS. -/
def computeVariantPRS
    (genos : List Genotype)
    (weights : List VariantWeight) :
    Float :=
  genos.foldl
    (fun acc gt =>
      match findWeight gt.variant.id weights with
      | some w =>
          acc + gt.dosage.toFloat * w.beta
      | none =>
          acc)
    0.0

/- ============================================================
   Cellular model
   ============================================================ -/

/-- Protein state. -/
structure Protein where
  id         : ProteinId
  abundance  : Float
  activity   : Float
  deriving Repr

/-- Abstract cellular state. -/
structure CellState where
  energy : Float
  stress : Float
  growth : Float
  deriving Repr

/-- Cellular perturbation / protocol. -/
inductive Protocol
  | activate (protein : ProteinId)
  | inhibit (protein : ProteinId)
  | stress (amount : Float)
  | recover (amount : Float)
  | grow (amount : Float)
  deriving Repr

/-- Cellular computational core. -/
structure CellCore where
  proteins : List Protein
  state    : CellState
  deriving Repr

/- ============================================================
   Genetic effects
   ============================================================ -/

/--
  Parameters through which genetic background influences
  the cellular model.

  PRS is NOT itself treated as a cell state.
-/
structure GeneticEffect where
  activityScale     : Float
  stressSensitivity : Float
  growthBias        : Float
  deriving Repr

/-- Individual biological system. -/
structure Cell where
  core   : CellCore
  prs    : PolygenicRiskScore
  effect : GeneticEffect
  deriving Repr

/--
  Convert PRS into cellular parameters.

  The caller supplies the biological scaling coefficients.
-/
def geneticEffect
    (prs : PolygenicRiskScore)
    (activityScale : Float)
    (stressSensitivity : Float)
    (growthBias : Float) :
    GeneticEffect :=
  { activityScale :=
      activityScale * prs.totalScore

    stressSensitivity :=
      stressSensitivity * prs.totalScore

    growthBias :=
      growthBias * prs.totalScore }

/- ============================================================
   Protein operations
   ============================================================ -/

/-- Modify activity of a selected protein. -/
def modifyProtein
    (id : ProteinId)
    (delta : Float)
    (proteins : List Protein) :
    List Protein :=

  proteins.map
    (fun p =>
      if p.id = id then
        { p with
          activity := p.activity + delta }
      else
        p)

/-- Modify abundance of a selected protein. -/
def modifyAbundance
    (id : ProteinId)
    (delta : Float)
    (proteins : List Protein) :
    List Protein :=

  proteins.map
    (fun p =>
      if p.id = id then
        { p with
          abundance := p.abundance + delta }
      else
        p)

/-- Find a protein. -/
def findProtein
    (id : ProteinId)
    (proteins : List Protein) :
    Option Protein :=
  proteins.find?
    (fun p => p.id = id)

/- ============================================================
   Cellular state transitions
   ============================================================ -/

/-- Apply one biological protocol. -/
def applyProtocol
    (p : Protocol)
    (cell : Cell) :
    Cell :=

  match p with

  | Protocol.activate id =>
      { cell with
        core.proteins :=
          modifyProtein
            id
            cell.effect.activityScale
            cell.core.proteins }

  | Protocol.inhibit id =>
      { cell with
        core.proteins :=
          modifyProtein
            id
            (-cell.effect.activityScale)
            cell.core.proteins }

  | Protocol.stress amount =>
      { cell with
        core.state.stress :=
          cell.core.state.stress
          + amount * cell.effect.stressSensitivity

        core.state.energy :=
          cell.core.state.energy - amount }

  | Protocol.recover amount =>
      { cell with
        core.state.stress :=
          cell.core.state.stress - amount

        core.state.energy :=
          cell.core.state.energy + amount }

  | Protocol.grow amount =>
      { cell with
        core.state.growth :=
          cell.core.state.growth
          + amount
          + cell.effect.growthBias }

/-- Apply a sequence of biological perturbations. -/
def simulate
    (protocols : List Protocol)
    (cell : Cell) :
    Cell :=
  protocols.foldl
    (fun c p => applyProtocol p c)
    cell

/- ============================================================
   Analysis utilities
   ============================================================ -/

/-- Total protein activity. -/
def totalProteinActivity
    (proteins : List Protein) :
    Float :=
  proteins.foldl
    (fun acc p => acc + p.activity)
    0.0

/-- Total protein abundance. -/
def totalProteinAbundance
    (proteins : List Protein) :
    Float :=
  proteins.foldl
    (fun acc p => acc + p.abundance)
    0.0

/-- Overall cellular activity. -/
def cellularActivity
    (cell : Cell) :
    Float :=
  totalProteinActivity cell.core.proteins

/-- Basic cellular observation vector. -/
structure CellObservation where
  prs           : Float
  energy        : Float
  stress        : Float
  growth        : Float
  proteinActivity : Float
  proteinAbundance : Float
  deriving Repr

/-- Extract observable model state. -/
def observe
    (cell : Cell) :
    CellObservation :=
  { prs :=
      cell.prs.totalScore

    energy :=
      cell.core.state.energy

    stress :=
      cell.core.state.stress

    growth :=
      cell.core.state.growth

    proteinActivity :=
      totalProteinActivity cell.core.proteins

    proteinAbundance :=
      totalProteinAbundance cell.core.proteins }

/-- Human-readable PRS summary. -/
def prsSummary
    (prs : PolygenicRiskScore) :
    String :=
  "PRS="
    ++ toString prs.totalScore
    ++ ", used="
    ++ toString prs.variantsUsed
    ++ ", missing="
    ++ toString prs.variantsMissing

end Bio
