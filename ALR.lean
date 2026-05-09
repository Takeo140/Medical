import Mathlib.Data.List.Basic

namespace AlzheimerRepair

inductive PropType where
  | Hydrophobic
  | Hydrophilic
  | Neutral
  deriving Repr, DecidableEq

def amino_property : Char → PropType
  | 'A'|'V'|'L'|'I'|'M'|'F'|'W'|'P' => .Hydrophobic
  | 'S'|'T'|'C'|'Y'|'N'|'Q'|'D'|'E'|'K'|'R'|'H' => .Hydrophilic
  | _ => .Neutral

/-- sticky_score の帰納法用補助関数（List Char ベース） -/
def sticky_score_list : List Char → Nat
  | []        => 0
  | c :: rest => (if amino_property c = .Hydrophobic then 10 else 0) + sticky_score_list rest

def sticky_score (s : String) : Nat := sticky_score_list s.toList

/-- String 再帰を List Char に分解（Lean 4 は String の構造的帰納法を持たない） -/
def generate_patch_list : List Char → List Char
  | []        => []
  | c :: rest => (if amino_property c = .Hydrophobic then 'S' else c) :: generate_patch_list rest

def generate_anti_amyloid_patch (s : String) : String :=
  ⟨generate_patch_list s.toList⟩

def is_effective_repair (bug repair : String) : Prop :=
  sticky_score repair < sticky_score bug

/-- 補題1：パッチ後の配列は疎水性残基を含まないのでスコアは常に
