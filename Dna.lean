inductive Dna : Type := 
  | mkDna : String → Dna

namespace Dna

/-- 1. 文字ベースではなく、専用のBase型を介することで論理的整合性を高める -/
inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq

def char_to_base : Char → Option Base
  | 'A' => some Base.A
  | 'T' => some Base.T
  | 'G' => some Base.G
  | 'C' => some Base.C
  | _   => none

def base_to_complement : Base → Base
  | Base.A => Base.T
  | Base.T => Base.A
  | Base.G => Base.C
  | Base.C => Base.G

/-- 2. reverse_complement の修正: 
       Stringを直接弄るのではなく、検証済みのリストとして処理する -/
def reverse_complement (s : String) : String :=
  s.toList.reverse.map (λ c => 
    match char_to_base c with
    | some b => match base_to_complement b with
                | Base.A => 'A'
                | Base.T => 'T'
                | Base.G => 'G'
                | Base.C => 'C'
    | none   => c -- DNA塩基以外はそのまま（またはエラー処理）
  ).asString

/-- 3. find_pattern の修正: 
       drop/take の代わりにスライス的な整合性を高める -/
def find_pattern (pattern : String) (dna : String) : List Nat :=
  let p_len := pattern.length
  let d_list := dna.toList
  (List.range (dna.length - p_len + 1)).filter (λ i => 
    (d_list.drop i).take p_len = pattern.toList
  )

/-- 4. Treatment の検証ロジックを Prop (命題) レベルへ引き上げる -/
structure Treatment where
  description : String
  dosage : String
  scheduling : String

/-- 単なる Bool ではなく、証明可能な命題として定義 -/
def IsValidProtocol (t : Treatment) : Prop :=
  t.dosage ≠ "" ∧ t.scheduling ≠ ""

/-- 実行時チェック用の決定可能インスタンス -/
instance (t : Treatment) : Decidable (IsValidProtocol t) :=
  by unfold IsValidProtocol; infer_instance

end Dna
