/-
  License: CC BY 4.0  Apache 2.0
  Author: Takeo Yamamoto (Extended for Leukemia Treatment / Hematopoiesis)

  白血病治療のメカニズムをモデル化。
  造血幹細胞の異常増殖（Blast細胞の蓄積）という状態を定義し、
  標的治療やアポトーシス誘導による異常細胞の排除（Blastの減少）と
  寛解（Remission）状態への移行を表現する。
-/

namespace Bio

-- ※既存の Base, Codon, AminoAcid, ProteinRole, CellState, Cell, Protocol の定義を前提とします。

/-- 20. 骨髄・造血系の組織状態 -/
inductive MarrowState : Type
  | Leukemic  -- 白血病状態（異常な芽球が骨髄を占拠し、正常造血が阻害されている）
  | Remission -- 寛解（異常細胞が検出限界以下まで減少し、正常な造血が回復しつつある）
  | Healthy   -- 正常造血
  deriving Repr, DecidableEq

/-- 骨髄組織モデル -/
-- 正常な細胞リストに加え、白血病細胞（Blast）の腫瘍量をカウントとして保持する
structure BoneMarrow where
  cells : List Cell
  blastCount : Nat    -- 異常な白血病細胞（Blast）の数
  state : MarrowState
  deriving Repr

/-- 21. 白血病治療（寛解導入）プロトコル -/
-- 分子標的薬（異常シグナルの阻害：Signal）や、異常な転写因子の制御（Transcription）が必要
def LeukemiaTreatmentProtocol : Protocol :=
  { name := "Induction Therapy / Targeted Therapy",
    requiredRoles := [ProteinRole.Signal, ProteinRole.Transcription],
    -- 治療後は、正常な造血幹細胞(Stem)からの再構築を促すためStemをターゲットとする
    targetState := CellState.Stem } 

/-- 治療開始の前提条件（命題レベル） -/
-- 必要な治療用タンパク質（シグナル阻害剤などに相当）が供給・機能していること
def CanTreatLeukemia (p : Protocol) (m : BoneMarrow) : Prop :=
  ∀ r ∈ p.requiredRoles, ∃ c ∈ m.cells, ∃ pr ∈ c.proteins, pr.role = r

-- 命題の決定可能性
instance (p : Protocol) (m : BoneMarrow) : Decidable (CanTreatLeukemia p m) :=
  Classical.propDecidable _

/-- 22. 骨髄状態遷移（治療プロセスの実行） -/
-- 条件を満たした場合、Blast（白血病細胞）が排除され、寛解状態へ移行する
def applyLeukemiaTreatment (p : Protocol) (m : BoneMarrow) (h : CanTreatLeukemia p m) : BoneMarrow :=
  -- 正常な造血を再構築するため、細胞群の状態をStem（幹細胞）へリセット・維持する
  let treatedCells := m.cells.map (λ c => { proteins := c.proteins, state := p.targetState })
  { cells := treatedCells,
    -- 治療により異常な白血病細胞（Blast）をゼロ（検出限界以下）にリセット
    blastCount := 0,
    -- 臨床的正確性を期すため、即座にHealthyではなく、まずはRemission（寛解）へ移行
    state := MarrowState.Remission }

end Bio
