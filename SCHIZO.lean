-- =============================================================================
-- Verified Pharmacogenomics (PGx) Prescription Engine
-- License: CC BY 4.0 Takeo Yamamoto
-- =============================================================================

import Std.Data.Array.Basic

/-!
# 実用化に向けたアーキテクチャの進化
1. 表現型のモデル化: 実際の精神科医療で重要な薬物代謝酵素（CYP2D6）の代謝レベルを定義。
2. 依存型による安全性証明: `VerifiedPrescription` 型に「患者の代謝限界を超えていないこと」の証明を要求。
3. 堅牢なエラーハンドリング: `Option` ではなく `Except` モナドを使用し、失敗時の理由を明確化。
-/

namespace SchizophreniaPGx

-- ============================================================
-- 1. Clinical Data Models (臨床データモデル)
-- ============================================================

/-- 
薬物代謝酵素（例：CYP2D6）の表現型。
実際の遺伝子検査（配列解析）の結果から、以下のいずれかにマッピングされる前提。
-/
inductive MetabolizerType
  | Poor         -- 代謝遅延（PM）: 薬効が強く出すぎるため減量が必要
  | Intermediate -- 中間代謝（IM）
  | Normal       -- 正常代謝（NM）
  | UltraRapid   -- 超迅速代謝（UM）: 薬がすぐ抜けるため増量が必要
  deriving Repr, DecidableEq

/-- 患者プロファイル -/
structure Patient where
  id : String
  age : Nat
  cyp2d6_status : MetabolizerType
  deriving Repr

-- ============================================================
-- 2. Clinical Guidelines Engine (診療ガイドライン)
-- ============================================================

/--
特定の患者に対する、抗精神病薬（例：アリピプラゾール等）の1日あたりの最大許容量（mg）。
ガイドラインに基づく安全の「上限値」を決定する関数。
-/
def maxAllowedDose (p : Patient) : Nat :=
  match p.cyp2d6_status with
  | MetabolizerType.Poor => 10  -- 代謝が遅い患者は10mgまで
  | MetabolizerType.UltraRapid => 30 -- 代謝が早い患者は30mgまで
  | _ => 20                     -- 通常は20mgまで

-- ============================================================
-- 3. Verified Prescription (証明付き処方箋)
-- ============================================================

/--
実世界の医療システムで最も重要な「安全な処方箋」の型。
この型のインスタンスが生成された時点で、以下の2点が数学的に証明されている。
 1. 投与量が0より大きいこと (h_positive)
 2. 投与量がその患者の代謝限界（上限）を超えていないこと (h_safe)
-/
structure VerifiedPrescription (p : Patient) where
  drugName : String
  doseMg   : Nat
  h_positive : doseMg > 0
  h_safe     : doseMg ≤ maxAllowedDose p

namespace VerifiedPrescription

/--
外部入力（医師の入力やAIの推論結果）から安全に処方箋を構築する機構。
制約を満たさない場合は、Exceptを用いて詳細なエラーメッセージを返す。
-/
def tryPrescribe (p : Patient) (drug : String) (dose : Nat) : Except String (VerifiedPrescription p) :=
  -- 条件1: 0mg以下の無効な処方を弾く
  if h_pos : dose > 0 then
    -- 条件2: ガイドラインの上限値チェック
    if h_limit : dose ≤ maxAllowedDose p then
      -- 両方の証明（h_pos, h_limit）が揃った場合のみインスタンス化可能
      Except.ok {
        drugName   := drug
        doseMg     := dose
        h_positive := h_pos
        h_safe     := h_limit
      }
    else
      let limit := maxAllowedDose p
      Except.error s!"[Safety Violation] Dose {dose}mg exceeds the maximum allowed {limit}mg for patient's metabolic profile."
  else
    Except.error "[Invalid Dose] Dosage must be strictly greater than 0mg."

end VerifiedPrescription

-- ============================================================
-- 4. Execution & Logging (実行テスト)
-- ============================================================

/-- 実行結果をフォーマットするユーティリティ -/
def processPrescription (p : Patient) (drug : String) (dose : Nat) : String :=
  match VerifiedPrescription.tryPrescribe p drug dose with
  | Except.ok prescription =>
      s!"[SUCCESS] Verified Prescription generated for {p.id}: {prescription.drugName} {prescription.doseMg}mg/day."
  | Except.error errMsg =>
      s!"[REJECTED] {p.id} - {errMsg}"

end SchizophreniaPGx
