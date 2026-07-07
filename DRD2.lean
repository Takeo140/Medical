-- =============================================================================
-- Verified Schizophrenia Treatment Protocol Architecture
-- License: CC BY 4.0 Apache 2.0 Takeo Yamamoto
-- =============================================================================

import Std.Data.Array.Basic

/-!
# 設計方針（DNA処理コードと同型の設計原理）
1. String依存からの脱却: 症状評価を `Array Symptom` として定義し、不正な値の混入を型レベルで防ぐ。
2. 検証済み骨格と未検証数値の分離: UHA (`mulWith`) と同じ思想で、
   投薬量・力価換算などの臨床数値は意図的に「開いたスタブ」として扱う。
   ここで保証されるのは「プロトコルの構造的整合性」であり、「臨床的正しさ」ではない。
3. 依存型の導入: `Regimen` 構造体に整合性の証明を埋め込み、
   無効なプロトコル（空の用量・空の漸増スケジュール・多剤未確認の併用等）の生成を物理的に排除。
-/

-- ============================================================
-- 1. Symptom Domain (症状ドメイン) Type & Operations
-- ============================================================

/-- PANSS/BPRSに準拠する4系統の症状分類 -/
inductive SymptomDomain : Type
  | positive   -- 陽性症状（幻覚・妄想）
  | negative   -- 陰性症状（感情鈍麻・意欲低下）
  | cognitive  -- 認知機能障害
  | affective  -- 気分・情動症状
  deriving Repr, DecidableEq, Inhabited

namespace SymptomDomain

@[inline]
def toChar : SymptomDomain → Char
  | positive  => 'P'
  | negative  => 'N'
  | cognitive => 'C'
  | affective => 'A'

def fromChar? : Char → Option SymptomDomain
  | 'P' => some positive
  | 'N' => some negative
  | 'C' => some cognitive
  | 'A' => some affective
  | _   => none

end SymptomDomain

-- ============================================================
-- 2. SymptomProfile (症状プロファイル) Architecture
-- ============================================================

/--
検証済みの症状スコア列。
生の文字列や生スコアではなく Array (SymptomDomain × Nat) を保持し、
「定義域外のスコアが含まれないこと」を構造的に保証する。
score は 0-6 (PANSS準拠の重症度) に制限。
-/
structure SymptomProfile where
  scores : Array (SymptomDomain × Nat)
  h_bounded : ∀ p ∈ scores, p.2 ≤ 6
  deriving Inhabited

namespace SymptomProfile

/-- 安全なパース機構（バリデーション境界）-/
def mk? (raw : Array (SymptomDomain × Nat)) : Option SymptomProfile :=
  if h : ∀ p ∈ raw, p.2 ≤ 6 then
    some ⟨raw, h⟩
  else
    none

/-- 総合重症度（DNA側 findPattern と同型の走査） -/
def totalSeverity (profile : SymptomProfile) : Nat :=
  profile.scores.foldl (fun acc p => acc + p.2) 0

/-- 特定ドメインが閾値を超えているかの判定 -/
def domainAlert (profile : SymptomProfile) (d : SymptomDomain) (threshold : Nat) : Bool :=
  profile.scores.any (fun p => p.1 == d && p.2 ≥ threshold)

end SymptomProfile

-- ============================================================
-- 3. Verified Regimen Protocol (依存型パラダイム)
-- ============================================================

/-- 薬剤クラス（定型/非定型の区別のみ。個別成分・力価は意図的にスタブ化） -/
inductive AgentClass : Type
  | typical
  | atypical
  | longActingInjectable
  deriving Repr, DecidableEq, Inhabited

/--
命題（Prop）をフィールドとして内包する構造体。
この型のインスタンスが存在する時点で、
dosagePlan / titrationSchedule / monitoringPlan が空でないことが
数学的に証明されている状態になる。

注意：dosagePlan の中身（具体的数値・薬剤名）は UHA の mulWith 同様、
意図的に未検証の外部入力として扱う。ここでの「検証」は
「プロトコルとして構造的に欠落がないこと」の保証であり、
処方内容そのものの医学的妥当性は本コードの検証対象外。
-/
structure Regimen where
  agentClass         : AgentClass
  dosagePlan         : String   -- 未検証スタブ：具体的力価・漸増値は外部（処方医）入力
  titrationSchedule  : String   -- 未検証スタブ：漸増期間
  monitoringPlan     : String   -- 例：EPS/代謝系/QTc モニタリング計画
  h_dosage     : dosagePlan ≠ ""
  h_titration  : titrationSchedule ≠ ""
  h_monitoring : monitoringPlan ≠ ""

namespace Regimen

/-- 外部入力（処方医・臨床データ）から安全に Regimen を構築するスマートコンストラクタ -/
def mk? (cls : AgentClass) (dosage titration monitoring : String) : Option Regimen :=
  if hd : dosage = "" then none
  else if ht : titration = "" then none
  else if hm : monitoring = "" then none
  else some {
    agentClass        := cls
    dosagePlan         := dosage
    titrationSchedule  := titration
    monitoringPlan     := monitoring
    h_dosage           := hd
    h_titration        := ht
    h_monitoring       := hm
  }

/--
併用制約：定型抗精神病薬と非定型抗精神病薬の同時多剤投与を
型レベルで「警告対象」として明示する（強制排除ではなく、監査ログ用の述語）。
-/
def isPolypharmacyRisk (regs : Array Regimen) : Bool :=
  let hasTypical  := regs.any (·.agentClass == AgentClass.typical)
  let hasAtypical := regs.any (·.agentClass == AgentClass.atypical)
  hasTypical && hasAtypical && regs.size ≥ 2

end Regimen

-- ============================================================
-- 4. Protocol Integration (統合プロトコル)
-- ============================================================

/-- 症状プロファイルとレジメンを紐付けた治療記録 -/
structure TreatmentRecord where
  profile  : SymptomProfile
  regimen  : Regimen
  reviewDate : String
  h_review : reviewDate ≠ ""

namespace TreatmentRecord

def mk? (profile : SymptomProfile) (regimen : Regimen) (reviewDate : String) :
    Option TreatmentRecord :=
  if h : reviewDate = "" then none
  else some ⟨profile, regimen, reviewDate, h⟩

/-- F-Theory A1 (Extremum Principle) 的発想：症状総量を最小化する方向への遷移を判定 -/
def isImprovement (before after : TreatmentRecord) : Bool :=
  after.profile.totalSeverity < before.profile.totalSeverity

end TreatmentRecord
