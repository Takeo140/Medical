License Apache 2.0  Takeo Yamamoto
namespace Bio

/-
  Practical PRS Core
  ------------------
  Exact input validation + auditable contribution tracking.

  NOTE:
  Float is retained for GWAS beta compatibility.
  For production-grade scientific reproducibility,
  Decimal/rational coefficients can be substituted later.
-/

/-- DNA base -/
inductive Base
  | A | C | G | T
  deriving Repr, DecidableEq

abbrev GeneId := String
abbrev VariantId := String

/-- SNP / genetic variant -/
structure Variant where
  id         : VariantId
  gene       : GeneId
  pos        : Nat
  riskAllele : Base
  deriving Repr, DecidableEq

/-- Valid diploid dosage: 0, 1, or 2. -/
structure Dosage where
  value : Nat
  isValid : value ≤ 2
  deriving Repr

namespace Dosage

def zero : Dosage :=
  { value := 0, isValid := by decide }

def one : Dosage :=
  { value := 1, isValid := by decide }

def two : Dosage :=
  { value := 2, isValid := by decide }

def ofNat? (n : Nat) : Option Dosage :=
  if h : n ≤ 2 then
    some { value := n, isValid := h }
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

/-- GWAS-derived effect size. -/
structure VariantWeight where
  variant : Variant
  beta    : Float
  deriving Repr

/--
  One auditable contribution to the final PRS.
  Keeping this information makes the score inspectable.
-/
structure VariantContribution where
  variantId : VariantId
  gene      : GeneId
  dosage    : Dosage
  beta      : Float
  contribution : Float
  deriving Repr

/-- Gene-level PRS. -/
structure GeneScore where
  gene         : GeneId
  score        : Float
  contributions : List VariantContribution
  deriving Repr

/-- Complete PRS result. -/
structure PolygenicRiskScore where
  geneScores       : List GeneScore
  totalScore       : Float
  variantsUsed     : Nat
  variantsMissing  : Nat
  variantsInvalid  : Nat
  deriving Repr

/-- Input validation error. -/
inductive PRError
  | invalidDosage (variant : VariantId) (dosage : Nat)
  | duplicateGenotype (variant : VariantId)
  | duplicateWeight (variant : VariantId)
  deriving Repr, DecidableEq

/--
  Convert ordinary Nat dosage into a validated Dosage.
-/
def validateDosage
    (variant : Variant)
    (dosage : Nat) :
    Except PRError Dosage :=
  match Dosage.ofNat? dosage with
  | some d => .ok d
  | none   => .error (.invalidDosage variant.id dosage)

/--
  Construct a genotype from raw dosage.
-/
def makeGenotype
    (variant : Variant)
    (dosage : Nat) :
    Except PRError Genotype :=
  match validateDosage variant dosage with
  | .ok d   => .ok { variant := variant, dosage := d }
  | .error e => .error e

/--
  Find the effect size for a variant.
-/
def findWeight
    (variantId : VariantId)
    (weights : List VariantWeight) :
    Option VariantWeight :=
  weights.find? (fun w => w.variant.id = variantId)

/--
  Calculate one variant contribution.
-/
def variantContribution
    (gt : Genotype)
    (weights : List VariantWeight) :
    Option VariantContribution :=
  match findWeight gt.variant.id weights with
  | none => none
  | some w =>
      let c := gt.dosage.toFloat * w.beta
      some
        { variantId := gt.variant.id
          gene := gt.variant.gene
          dosage := gt.dosage
          beta := w.beta
          contribution := c }

/--
  Calculate all contributions for a gene.
-/
def geneContributions
    (gene : GeneId)
    (genos : List Genotype)
    (weights : List VariantWeight) :
    List VariantContribution :=
  genos
    |>.filter (fun gt => gt.variant.gene = gene)
    |>.filterMap (fun gt => variantContribution gt weights)

/--
  Sum contributions.
-/
def sumContributions
    (xs : List VariantContribution) : Float :=
  xs.foldl
    (fun acc x => acc + x.contribution)
    0.0

/--
  Calculate one gene score.
-/
def computeGeneScore
    (gene : GeneId)
    (genos : List Genotype)
    (weights : List VariantWeight) :
    GeneScore :=
  let cs := geneContributions gene genos weights
  { gene := gene
    score := sumContributions cs
    contributions := cs }

/--
  Distinct genes represented in the genotype data.
-/
def genes
    (genos : List Genotype) : List GeneId :=
  genos
    |>.map (fun gt => gt.variant.gene)
    |>.eraseDup

/--
  Number of genotypes for which a matching weight exists.
-/
def countUsed
    (genos : List Genotype)
    (weights : List VariantWeight) : Nat :=
  genos.countP
    (fun gt =>
      match findWeight gt.variant.id weights with
      | some _ => true
      | none   => false)

/--
  Number of genotype variants without a weight.
-/
def countMissing
    (genos : List Genotype)
    (weights : List VariantWeight) : Nat :=
  genos.length - countUsed genos weights

/--
  Calculate total PRS.
-/
def computePRS
    (genos : List Genotype)
    (weights : List VariantWeight) :
    PolygenicRiskScore :=
  let gs :=
    genes genos |>.map
      (fun g => computeGeneScore g genos weights)

  let total :=
    gs.foldl
      (fun acc g => acc + g.score)
      0.0

  { geneScores := gs
    totalScore := total
    variantsUsed := countUsed genos weights
    variantsMissing := countMissing genos weights
    variantsInvalid := 0 }

/--
  Direct variant-level PRS.

  This is the simplest production-facing calculation:
      PRS = Σ dosage × beta
-/
def computeVariantPRS
    (genos : List Genotype)
    (weights : List VariantWeight) :
    Float :=
  genos.foldl
    (fun acc gt =>
      match findWeight gt.variant.id weights with
      | some w => acc + gt.dosage.toFloat * w.beta
      | none => acc)
    0.0

/--
  Add an intercept/baseline to the PRS.
-/
def computePRSWithIntercept
    (genos : List Genotype)
    (weights : List VariantWeight)
    (intercept : Float) :
    Float :=
  intercept + computeVariantPRS genos weights

/--
  Verify that every genotype has a corresponding weight.
-/
def allVariantsWeighted
    (genos : List Genotype)
    (weights : List VariantWeight) : Bool :=
  genos.all
    (fun gt =>
      match findWeight gt.variant.id weights with
      | some _ => true
      | none   => false)

/--
  Return variants with no GWAS weight.
-/
def missingVariants
    (genos : List Genotype)
    (weights : List VariantWeight) :
    List VariantId :=
  genos
    |>.filterMap
      (fun gt =>
        match findWeight gt.variant.id weights with
        | some _ => none
        | none   => some gt.variant.id)

/--
  Return a human-readable summary.
-/
def summary
    (prs : PolygenicRiskScore) : String :=
  "PRS=" ++
    toString prs.totalScore ++
    ", used=" ++
    toString prs.variantsUsed ++
    ", missing=" ++
    toString prs.variantsMissing

end Bio
