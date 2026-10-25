/-
  License: Apache 2.0 
  Author: Takeo Yamamoto
  Active Inference with Epigenetic Memory & Collective Cellular Signaling
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
  | Structural
  | Enzyme
  | Transcription
  | Signal
  deriving Repr, DecidableEq

structure Protein where
  seq : List AminoAcid
  role : ProteinRole
  deriving Repr, DecidableEq

inductive CellState : Type
  | Stem
  | IPS
  | Direct
  | Differentiated
  deriving Repr, DecidableEq

/-- 2. エピジェネティック修飾（履歴による応答性・重みの変化） -/
inductive EpigeneticMark : Type
  | Methylation   -- 抑制的修飾（感度低下）
  | Acetylation   -- 活性化修飾（感度亢進）
  deriving Repr, DecidableEq

/-- 3. エピジェネティック記憶を持つ細胞モデル -/
structure Cell where
  proteins : List Protein
  marks : List EpigeneticMark        -- 過去の履歴の蓄積
  state : CellState
  deriving Repr, DecidableEq

/-- 4. 外部環境シグナル -/
structure EnvironmentSignal where
  targetRole : ProteinRole
  expectedIntensity : Int
  deriving Repr, DecidableEq

/-- エピジェネティック修飾による感度係数（アセチル化は感度倍増、メチル化は半減など） -/
def getEpigeneticFactor (marks : List EpigeneticMark) : Int :=
  marks.foldl (fun acc mark =>
    match mark with
    | EpigeneticMark.Acetylation => acc + 1
    | EpigeneticMark.Methylation => acc - 1
  ) 1

/-- 5. 能動推論：エピジェネティック記憶を考慮した自由エネルギー（予測誤差）計算 -/
def calculateFreeEnergyWithEpigenetics (c : Cell) (env : EnvironmentSignal) : Int :=
  let matchingCount := (c.proteins.filter (fun p => p.role == env.targetRole)).length
  let factor := max 1 (getEpigeneticFactor c.marks) -- 最小感度は1
  let diff := env.expectedIntensity - matchingCount
  let rawError := if diff ≥ 0 then diff else -diff
  rawError / factor

/-- 6. 複数細胞による組織（Tissue）と集団的シグナル伝達 -/
structure Tissue where
  cells : List Cell
  environment : EnvironmentSignal
  deriving Repr, DecidableEq

/-- 組織全体の平均自由エネルギーを評価する集団推論関数 -/
def tissueCollectiveFreeEnergy (t : Tissue) : Int :=
  t.cells.foldl (fun acc cell => acc + calculateFreeEnergyWithEpigenetics cell t.environment) 0

/-- 7. 集団的適応ステップ：組織内の全細胞が一斉に能動推論による状態更新を行う -/
def tissueAdapt (t : Tissue) (targetState : CellState) : Tissue :=
  { cells := t.cells.map (fun c =>
      let fe := calculateFreeEnergyWithEpigenetics c t.environment
      if fe = 0 then c
      else { proteins := c.proteins, marks := EpigeneticMark.Acetylation :: c.marks, state := targetState }
    ),
    environment := t.environment }

end Bio
