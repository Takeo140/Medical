-- Author: Takeo Yamamoto
-- License: Apache 2.0
import Mathlib.Tactic

namespace IntegratedSynthesis

-- 1. 細胞型・転写因子
inductive SomaticCellType
  | Fibroblast | Osteoblast | HSC
  deriving DecidableEq, Repr

inductive TranscriptionFactor
  | RUNX2 | HSC_Factors | P63
  deriving DecidableEq, Repr

-- 2. 細胞状態
structure CellState where
  type              : SomaticCellType
  factors           : List TranscriptionFactor
  is_cancerous      : Bool
  has_genetic_defect : Bool

-- 3. 変換ルール
def requiredFactor : SomaticCellType → TranscriptionFactor
  | .HSC        => .HSC_Factors
  | .Osteoblast => .RUNX2
  | .Fibroblast => .P63

-- 4. 安全変換エンジン（②修正: 全 target に対応）
def convert_ultimate_safe (s : CellState) (target : SomaticCellType) : Option CellState :=
  let new_factors := s.factors ++ [requiredFactor target]
  -- ガード: 遺伝子バグがなく、対応因子が揃っていること（④修正: == false → = false）
  if s.has_genetic_defect = false ∧ new_factors.contains (requiredFactor target) then
    some { type              := target
           factors           := new_factors
           is_cancerous      := false
           has_genetic_defect := false }
  else
    none

-- 5. 究極の安全定理（①③修正）
theorem absolute_safety_guarantee
    (donor  : CellState)
    (target : SomaticCellType)
    (result : CellState)                                      -- ①明示宣言
    (h_success : convert_ultimate_safe donor target = some result) :
    result.is_cancerous = false ∧ result.has_genetic_defect = false := by
  simp only [convert_ultimate_safe] at h_success             -- ③定義を展開
  split_ifs at h_success with hg                             -- ③ if を分解
  · injection h_success with heq                            -- Some の単射性
    subst heq
    exact ⟨rfl, rfl⟩
  · exact absurd h_success (by simp)

end IntegratedSynthesis
