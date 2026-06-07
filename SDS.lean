-- Author: Takeo Yamamoto
-- License: Apache 2.0
import Mathlib.Tactic
/-!
 # Somatic-to-Somatic Direct Synthesis (Integrated)
 
 任意の体細胞型(target)へ変換するための最小完結モデル。
-/
namespace IntegratedSynthesis

inductive SomaticCellType
  | Fibroblast | Osteoblast | Hematopoietic | Keratinocyte
  deriving DecidableEq, Repr

inductive TranscriptionFactor
  | RUNX2 | GATA1 | HOXC13 | P63
  deriving DecidableEq, Repr

structure CellState where
  type    : SomaticCellType
  factors : List TranscriptionFactor

/-- 各細胞型への変換に必要な転写因子 -/
def requiredFactor : SomaticCellType → TranscriptionFactor
  | .Osteoblast    => .RUNX2
  | .Hematopoietic => .GATA1
  | .Keratinocyte  => .HOXC13
  | .Fibroblast    => .P63   -- 注: P63は上皮系因子。Fibroblastへの逆変換に用いる場合は要検討

/-- 変換エンジン: target型の必須因子を追加し、細胞型を更新する -/
def convert (s : CellState) (target : SomaticCellType) : CellState :=
  { type    := target
    factors := s.factors ++ [requiredFactor target] }

/-- 統合定理: 任意の体細胞から target 型への変換が存在し、型・因子の整合性が保たれる -/
theorem synthesize
    (donor : CellState) (target : SomaticCellType) :
    ∃ result : CellState,
        result.type = target ∧
        result.factors = (convert donor target).factors := by
  exact ⟨convert donor target, rfl, rfl⟩

end IntegratedSynthesis
