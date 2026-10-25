/-
  License: Apache 2.0 
  Author: Takeo Yamamoto
  Evolutionary Genome Search & Selection Model (Genetic Algorithm Extension)
-/

namespace Bio

/-- 1. 基礎構造 -/
inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq

structure Codon where
  b1 : Base
  b2 : Base
  b3 : Base
  deriving Repr, DecidableEq

inductive AminoAcid : Type
  | Ala | Arg | Asn | Asp | Cys
  | Gln | Glu | Gly | His | Ile
  | Leu | Lys | Met | Phe | Pro
  | Ser | Thr | Trp | Tyr | Val
  deriving Repr, DecidableEq

inductive ProteinRole : Type
  | Structural | Enzyme | Transcription | Signal
  deriving Repr, DecidableEq

structure Protein where
  seq : List AminoAcid
  role : ProteinRole
  deriving Repr, DecidableEq

/-- ゲノム配列（コドンのリスト） -/
def Genome := List Codon

def translateGenome (genome : Genome) (role : ProteinRole) : Protein :=
  { seq := [AminoAcid.Met, AminoAcid.Ala], role := role }

/-- 2. 変異オペレータ -/
def mutateBase : Base → Base
  | Base.A => Base.T
  | Base.T => Base.G
  | Base.G => Base.C
  | Base.C => Base.A

def mutateCodon (c : Codon) : Codon :=
  { b1 := mutateBase c.b1, b2 := c.b2, b3 := c.b3 }

def applyMutation (genome : Genome) (index : Nat) : Genome :=
  genome.mapIdx (fun i c => if i = index then mutateCodon c else c)

/-- 3. 量的形質（ポリジーン）とスコア評価 -/
structure PolyGeneLocus where
  targetProtein : Protein
  weight : Int
  deriving Repr, DecidableEq

structure PolygenicTrait where
  loci : List PolyGeneLocus
  targetScore : Int
  deriving Repr, DecidableEq

def evaluateGenomeScore (genome : Genome) (trait : PolygenicTrait) : Int :=
  let producedProteins := [translateGenome genome ProteinRole.Transcription]
  trait.loci.foldl (fun acc locus =>
    let count := (producedProteins.filter (· == locus.targetProtein)).length
    acc + (locus.weight * count)
  ) 0

/-- 4. 進化探索（Evolutionary Search）の拡張機能 -/

/-- ゲノム配列の全変異近傍（1塩基置換の全パターン）を生成 -/
def generateMutantNeighborhood (genome : Genome) : List Genome :=
  (List.range genome.length).map (fun i => applyMutation genome i)

/-- 個体（ゲノムと適応度スコアのペア） -/
structure Individual where
  genome : Genome
  score : Int
  deriving Repr

/-- 世代交代ステップ：変異近傍からスコアを評価して次世代の候補プールを生成 -/
def evaluateGeneration (current : Genome) (trait : PolygenicTrait) : List Individual :=
  let neighbors := generateMutantNeighborhood current
  neighbors.map (fun g => { genome := g, score := evaluateGenomeScore g trait })

/-- 選択フェーズ：目標スコア（閾値）をクリアする適応個体のみを抽出 -/
def selectAdaptedIndividuals (current : Genome) (trait : PolygenicTrait) : List Individual :=
  let gen := evaluateGeneration current trait
  gen.filter (fun ind => ind.score ≥ trait.targetScore)

end Bio
