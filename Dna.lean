/-
  License: Apache 2.0 / CC BY 4.0
  Author: Takeo Yamamoto

  細胞構造に合わせて DNA → Codon → AminoAcid → Protein → Cell → Protocol
  までを一つに統合した抽象モデル。
-/

namespace Bio

/-- 1. DNA塩基（Takeoの4bit構造と同型） -/
inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq

/-- Char → Base の安全変換 -/
def char_to_base : Char → Option Base
  | 'A' => some Base.A
  | 'T' => some Base.T
  | 'G' => some Base.G
  | 'C' => some Base.C
  | _   => none

/-- 相補的塩基 -/
def complement : Base → Base
  | Base.A => Base.T
  | Base.T => Base.A
  | Base.G => Base.C
  | Base.C => Base.G

/-- reverse_complement（検証済みリスト処理） -/
def reverse_complement (s : String) : String :=
  s.toList.reverse.map (λ c =>
    match char_to_base c with
    | some b =>
        match complement b with
        | Base.A => 'A'
        | Base.T => 'T'
        | Base.G => 'G'
        | Base.C => 'C'
    | none => c
  ).asString

/-- 2. Codon（3塩基） -/
structure Codon where
  b1 : Base
  b2 : Base
  b3 : Base
  deriving Repr, DecidableEq

/-- String → Codon の安全変換 -/
def string_to_codon (s : String) : Option Codon :=
  match s.toList.map char_to_base with
  | [some b1, some b2, some b3] => some ⟨b1, b2, b3⟩
  | _ => none

/-- 3. アミノ酸（20種類） -/
inductive AminoAcid : Type
  | Ala | Arg | Asn | Asp | Cys
  | Gln | Glu | Gly | His | Ile
  | Leu | Lys | Met | Phe | Pro
  | Ser | Thr | Trp | Tyr | Val
  deriving Repr, DecidableEq

/-- Codon → AminoAcid（簡略版） -/
def codonToAA : Codon → Option AminoAcid
  | ⟨Base.A, Base.T, Base.G⟩ => some AminoAcid.Met   -- 開始コドン
  | ⟨Base.T, Base.A, Base.A⟩ => none                 -- 終止コドン
  | _ => some AminoAcid.Ala                           -- 簡略化

/-- 4. タンパク質の役割 -/
inductive ProteinRole : Type
  | Structural      -- 細胞骨格
  | Enzyme          -- 代謝酵素
  | Transcription   -- 転写因子
  | Signal          -- シグナル伝達
  deriving Repr, DecidableEq

/-- タンパク質 -/
structure Protein where
  seq : List AminoAcid
  role : ProteinRole
  deriving Repr

/-- 5. 細胞状態（iPS / Direct を含む） -/
inductive CellState : Type
  | Stem
  | IPS
  | Direct
  | Differentiated
  deriving Repr, DecidableEq

/-- 細胞はタンパク質の集合として表現できる -/
structure Cell where
  proteins : List Protein
  state : CellState
  deriving Repr

/-- 6. 細胞生成プロトコル（iPS / Direct） -/
structure Protocol where
  name : String
  requiredRoles : List ProteinRole
  targetState : CellState

/-- iPS生成プロトコル -/
def IPSProtocol : Protocol :=
  { name := "iPS Induction",
    requiredRoles := [ProteinRole.Transcription],
    targetState := CellState.IPS }

/-- Direct分化プロトコル -/
def DirectProtocol : Protocol :=
  { name := "Direct Conversion",
    requiredRoles := [ProteinRole.Signal],
    targetState := CellState.Direct }

/-- プロトコル適用可能性（命題レベル） -/
def CanApply (p : Protocol) (c : Cell) : Prop :=
  ∀ r ∈ p.requiredRoles, ∃ pr ∈ c.proteins, pr.role = r

instance (p : Protocol) (c : Cell) : Decidable (CanApply p c) :=
  classical.decEq _

/-- 7. 細胞状態遷移（プロセス思考の核） -/
def applyProtocol (p : Protocol) (c : Cell) (h : CanApply p c) : Cell :=
  { proteins := c.proteins, state := p.targetState }

end Bio
