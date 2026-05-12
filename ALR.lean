import Mathlib.Data.List.Basic

namespace AlzheimerRepair

inductive PropType where
  | Hydrophobic
  | Hydrophilic
  | Neutral
  deriving Repr, DecidableEq

-- Lean 4のパターンマッチを安全に展開（| の連続使用のパースエラーを回避）
def amino_property : Char → PropType
  | 'A' => .Hydrophobic | 'V' => .Hydrophobic | 'L' => .Hydrophobic | 'I' => .Hydrophobic
  | 'M' => .Hydrophobic | 'F' => .Hydrophobic | 'W' => .Hydrophobic | 'P' => .Hydrophobic
  | 'S' => .Hydrophilic | 'T' => .Hydrophilic | 'C' => .Hydrophilic | 'Y' => .Hydrophilic
  | 'N' => .Hydrophilic | 'Q' => .Hydrophilic | 'D' => .Hydrophilic | 'E' => .Hydrophilic
  | 'K' => .Hydrophilic | 'R' => .Hydrophilic | 'H' => .Hydrophilic
  | _ => .Neutral

/-- sticky_score の帰納法用補助関数（List Char ベース） -/
def sticky_score_list : List Char → Nat
  | []        => 0
  | c :: rest => (if amino_property c = .Hydrophobic then 10 else 0) + sticky_score_list rest

def sticky_score (s : String) : Nat := sticky_score_list s.toList

/-- String 再帰を List Char に分解（疎水性残基を親水性の 'S' に置換） -/
def generate_patch_list : List Char → List Char
  | []        => []
  | c :: rest => (if amino_property c = .Hydrophobic then 'S' else c) :: generate_patch_list rest

-- 修正：Lean 4 の String 生成は String.mk を使用
def generate_anti_amyloid_patch (s : String) : String :=
  String.mk (generate_patch_list s.toList)

def is_effective_repair (bug repair : String) : Prop :=
  sticky_score repair < sticky_score bug

/-- 補題1：パッチ後の配列は疎水性残基を含まないので、スコアは常に0になる -/
theorem patch_score_zero (l : List Char) : sticky_score_list (generate_patch_list l) = 0 := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp [generate_patch_list]
    -- 文字cが疎水性かどうかで分岐
    cases h : amino_property c
    · -- Hydrophobic の場合 ('S'に置換される)
      simp [sticky_score_list, ih]
      -- 'S' は Hydrophilic なのでスコアは加算されない
      have hS : amino_property 'S' = .Hydrophilic := rfl
      simp [hS]
    · -- Hydrophilic の場合 (そのまま)
      simp [sticky_score_list, h, ih]
    · -- Neutral の場合 (そのまま)
      simp [sticky_score_list, h, ih]

/-- 最終定理：凝集（バグ）が発生している配列にパッチを当てると、必ずスコアが改善する -/
theorem patch_is_effective (s : String) (h : sticky_score s > 0) : 
    is_effective_repair s (generate_anti_amyloid_patch s) := by
  unfold is_effective_repair generate_anti_amyloid_patch sticky_score
  -- 補題1を適用し、パッチ後のスコアが0であることを証明
  have h_zero : sticky_score_list (generate_patch_list s.toList) = 0 := patch_score_zero s.toList
  -- 0 < (元のスコア) となり、前提 h により証明完了
  linarith [h_zero, h]

end AlzheimerRepair
