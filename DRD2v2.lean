-- =============================================================================
-- Verified Schizophrenia Polygenic Risk Score Architecture
-- License: CC BY 4.0 Apache 2.0 Takeo Yamamoto
-- =============================================================================

import Std.Data.Array.Basic

/-!
# 設計方針（元の治療プロトコル設計と同型）
1. String依存からの脱却: アレル数を `Fin 3`（0/1/2）で表し、範囲外の値を型レベルで排除。
2. 検証済み骨格と未検証数値の分離: 効果量（重み）・閾値・参照集団は
   意図的に「開いたスタブ」として扱う。
   ここで保証されるのは「モデルの構造的整合性」であり、「遺伝統計学的・臨床的正しさ」ではない。
3. 依存型の導入: `PolygenicModel` に整合性の証明を埋め込み、
   空のバリアント集合・空の参照集団記述などの無効なモデル生成を排除。

注意：多遺伝子リスクスコア（PRS）は確率的な指標であり、診断・予測の確定には使えない。
祖先集団間で移植性が低い点にも留意（ancestryNote で明示）。
-/

-- ============================================================
-- 1. Pathway Domain (経路ドメイン) Type & Operations
-- ============================================================

/-- バリアントが属する生物学的経路の大分類 -/
inductive PathwayDomain : Type
  | dopaminergic   -- ドーパミン系
  | glutamatergic  -- グルタミン酸系
  | synaptic       -- シナプス機能
  | immune         -- 免疫・MHC領域
  | other          -- その他
  deriving Repr, DecidableEq, Inhabited

namespace PathwayDomain

@[inline]
def toChar : PathwayDomain → Char
  | dopaminergic  => 'D'
  | glutamatergic => 'G'
  | synaptic      => 'S'
  | immune        => 'I'
  | other         => 'O'

def fromChar? : Char → Option PathwayDomain
  | 'D' => some dopaminergic
  | 'G' => some glutamatergic
  | 'S' => some synaptic
  | 'I' => some immune
  | 'O' => some other
  | _   => none

end PathwayDomain

-- ============================================================
-- 2. Variant & Genotype Architecture
-- ============================================================

/--
PRSに含まれる1バリアント。
`weightMilli` は効果量（対数オッズ比など）を ×1000 した固定小数点整数。
値そのものは外部（GWAS要約統計）入力であり、未検証スタブ。
-/
structure Variant where
  rsId        : String
  pathway     : PathwayDomain
  weightMilli : Int   -- 未検証スタブ：外部GWASから供給
  h_rsId      : rsId ≠ ""

namespace Variant

def mk? (rsId : String) (pathway : PathwayDomain) (weightMilli : Int) : Option Variant :=
  if h : rsId = "" then none
  else some ⟨rsId, pathway, weightMilli, h⟩

end Variant

/-- 個人の1バリアントに対するジェノタイプ呼び出し。dosage は効果アレル数（0〜2）。 -/
structure GenotypeCall where
  rsId   : String
  dosage : Fin 3
  deriving Repr

/-- 個人のジェノタイプ集合。空でないことを構造的に保証する。 -/
structure GenotypeProfile where
  calls      : Array GenotypeCall
  h_nonempty : calls.size > 0

namespace GenotypeProfile

/-- 検証境界：生の配列から安全に構築 -/
def mk? (raw : Array GenotypeCall) : Option GenotypeProfile :=
  if h : raw.size > 0 then some ⟨raw, h⟩ else none

/-- 指定 rsId の効果アレル数（未呼び出しは 0 として扱う） -/
def dosageOf (g : GenotypeProfile) (rs : String) : Nat :=
  match g.calls.find? (fun c => c.rsId == rs) with
  | some c => c.dosage.val
  | none   => 0

/-- 同一 rsId の重複呼び出しがあるかの監査用述語 -/
def hasDuplicates (g : GenotypeProfile) : Bool :=
  let ids := g.calls.map (·.rsId)
  ids.size != (ids.foldl (fun acc s => if acc.contains s then acc else acc.push s) #[]).size

end GenotypeProfile

-- ============================================================
-- 3. Verified Polygenic Model (依存型パラダイム)
-- ============================================================

/-- リスク階層 -/
inductive RiskTier : Type
  | low
  | intermediate
  | high
  deriving Repr, DecidableEq, Inhabited

/--
命題（Prop）をフィールドとして内包する構造体。
この型のインスタンスが存在する時点で、
variants / referencePopulation / ancestryNote が空でないことが証明されている。

注意：variants の重み、referencePopulation の中身（GWAS名・サンプル規模）は
未検証の外部入力。「検証」は構造の欠落がないことの保証に限る。
-/
structure PolygenicModel where
  variants            : Array Variant
  referencePopulation : String   -- 未検証スタブ：参照GWAS・サンプル集団
  ancestryNote        : String   -- 祖先集団の適用範囲・移植性に関する注記
  h_variants   : variants.size > 0
  h_reference  : referencePopulation ≠ ""
  h_ancestry   : ancestryNote ≠ ""

namespace PolygenicModel

def mk? (vs : Array Variant) (ref ancestry : String) : Option PolygenicModel :=
  if hv : vs.size > 0 then
    if hr : ref = "" then none
    else if ha : ancestry = "" then none
    else some ⟨vs, ref, ancestry, hv, hr, ha⟩
  else none

/-- 生スコア（固定小数点 ×1000）：Σ weight × dosage -/
def rawScore (m : PolygenicModel) (g : GenotypeProfile) : Int :=
  m.variants.foldl
    (fun acc v => acc + v.weightMilli * (g.dosageOf v.rsId : Int)) 0

/-- 経路別スコア（元コードの domainAlert に相当する分解） -/
def pathwayScore (m : PolygenicModel) (g : GenotypeProfile) (d : PathwayDomain) : Int :=
  m.variants.foldl
    (fun acc v =>
      if v.pathway == d then acc + v.weightMilli * (g.dosageOf v.rsId : Int) else acc) 0

/-- モデル中のバリアントのうち、個人側に呼び出しがないものの数（カバレッジ監査） -/
def missingCount (m : PolygenicModel) (g : GenotypeProfile) : Nat :=
  m.variants.foldl
    (fun acc v => if g.calls.any (fun c => c.rsId == v.rsId) then acc else acc + 1) 0

/-- 監査用述語：カバレッジが不完全か（強制排除ではなくログ用） -/
def isIncompleteCoverage (m : PolygenicModel) (g : GenotypeProfile) : Bool :=
  m.missingCount g > 0

end PolygenicModel

/-- 階層化閾値。具体値は外部（参照集団の分布）入力で未検証。順序のみ型で保証。 -/
structure RiskThresholds where
  lowerMilli : Int
  upperMilli : Int
  h_order    : lowerMilli ≤ upperMilli

namespace RiskThresholds

def mk? (lo hi : Int) : Option RiskThresholds :=
  if h : lo ≤ hi then some ⟨lo, hi, h⟩ else none

def classify (t : RiskThresholds) (score : Int) : RiskTier :=
  if score < t.lowerMilli then RiskTier.low
  else if score > t.upperMilli then RiskTier.high
  else RiskTier.intermediate

end RiskThresholds

-- ============================================================
-- 4. Protocol Integration (統合プロトコル)
-- ============================================================

/-- モデル・ジェノタイプ・閾値を紐付けたリスク評価記録 -/
structure RiskRecord where
  model      : PolygenicModel
  profile    : GenotypeProfile
  thresholds : RiskThresholds
  reportDate : String
  h_report   : reportDate ≠ ""

namespace RiskRecord

def mk? (model : PolygenicModel) (profile : GenotypeProfile)
    (thresholds : RiskThresholds) (reportDate : String) : Option RiskRecord :=
  if h : reportDate = "" then none
  else some ⟨model, profile, thresholds, reportDate, h⟩

def score (r : RiskRecord) : Int := r.model.rawScore r.profile

def tier (r : RiskRecord) : RiskTier := r.thresholds.classify r.score

/-- F-Theory A1 (Extremum Principle) 的発想：スコアがより小さい（低リスク）側への遷移を判定。
    モデル更新（再重み付け）前後の比較などに用いる。 -/
def isLowerRisk (before after : RiskRecord) : Bool :=
  after.score < before.score

end RiskRecord
