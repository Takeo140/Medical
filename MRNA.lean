-- MRnaVaccine.lean
-- mRNAワクチン設計の形式化 (F-Theory A1–A4準拠)
-- 既存 Dna 名前空間を拡張する形で構築
-- Apache 2.0 / Takeo Yamamoto

/- =========================================================
   §0  既存 Dna 定義の再掲（依存部分のみ）
   ========================================================= -/

inductive Base : Type
  | A | T | G | C | U   -- U はRNA専用
  deriving Repr, DecidableEq

namespace Base

def complement_dna : Base → Base
  | A => T | T => A | G => C | C => G | U => A -- RNA→DNA逆転写時

def transcribe : Base → Base
  -- DNA鋳型鎖 → mRNA塩基 (T→U, others map directly)
  | A => U   -- DNA鋳型の A は mRNA で U
  | T => A   -- DNA鋳型の T は mRNA で A
  | G => C
  | C => G
  | U => U   -- already RNA

def to_char : Base → Char
  | A => 'A' | T => 'T' | G => 'G' | C => 'C' | U => 'U'

def from_char : Char → Option Base
  | 'A' => some A | 'T' => some T | 'G' => some G
  | 'C' => some C | 'U' => some U | _ => none

end Base

/- =========================================================
   §1  コドン・アミノ酸
   ========================================================= -/

/-- コドン : mRNA塩基3つ組 -/
structure Codon where
  b1 : Base
  b2 : Base
  b3 : Base
  deriving Repr, DecidableEq

/-- 標準的なアミノ酸 (20 + Stop) -/
inductive AminoAcid : Type
  | Phe | Leu | Ile | Met | Val
  | Ser | Pro | Thr | Ala
  | Tyr | His | Gln | Asn | Lys
  | Asp | Glu | Cys | Trp | Arg | Gly
  | Stop
  deriving Repr, DecidableEq

/-- 標準遺伝暗号表（主要コドンのみ; 完全版は Mathlib外部テーブル参照） -/
def genetic_code : Codon → AminoAcid
  | ⟨Base.A, Base.U, Base.G⟩ => AminoAcid.Met   -- 開始コドン
  | ⟨Base.U, Base.A, Base.A⟩ => AminoAcid.Stop
  | ⟨Base.U, Base.A, Base.G⟩ => AminoAcid.Stop
  | ⟨Base.U, Base.G, Base.A⟩ => AminoAcid.Stop
  | ⟨Base.U, Base.U, Base.U⟩ => AminoAcid.Phe
  | ⟨Base.U, Base.U, Base.C⟩ => AminoAcid.Phe
  | ⟨Base.U, Base.U, Base.A⟩ => AminoAcid.Leu
  | ⟨Base.U, Base.U, Base.G⟩ => AminoAcid.Leu
  | ⟨Base.U, Base.G, Base.G⟩ => AminoAcid.Trp
  | ⟨Base.G, Base.G, Base.G⟩ => AminoAcid.Gly
  | ⟨Base.G, Base.G, Base.A⟩ => AminoAcid.Gly
  | ⟨Base.G, Base.G, Base.C⟩ => AminoAcid.Gly
  | ⟨Base.G, Base.G, Base.U⟩ => AminoAcid.Gly
  | _                          => AminoAcid.Gly   -- fallback（要完全表）

/-- 開始コドン判定 -/
def is_start_codon (c : Codon) : Bool :=
  c == ⟨Base.A, Base.U, Base.G⟩

/-- 終止コドン判定 -/
def is_stop_codon (c : Codon) : Bool :=
  genetic_code c == AminoAcid.Stop

/- =========================================================
   §2  mRNA配列型と基本操作
   ========================================================= -/

/-- mRNA配列 : U を含む塩基リスト -/
structure MRna where
  seq : List Base
  deriving Repr

namespace MRna

/-- DNA鋳型鎖からmRNAへの転写 -/
def from_template_strand (dna : List Base) : MRna :=
  { seq := dna.map Base.transcribe }

/-- 配列長 -/
def length (m : MRna) : Nat := m.seq.length

/-- i番目の塩基取得 -/
def get (m : MRna) (i : Nat) : Option Base := m.seq.get? i

/-- コドンリストに変換 (読み枠 0 から) -/
def to_codons (m : MRna) : List Codon :=
  let rec go : List Base → List Codon
    | b1 :: b2 :: b3 :: rest => ⟨b1, b2, b3⟩ :: go rest
    | _ => []
  go m.seq

/-- タンパク質（アミノ酸列）への翻訳 -/
def translate (m : MRna) : List AminoAcid :=
  m.to_codons.map genetic_code

/-- ORF（開放読み枠）を開始コドンから終止まで抽出 -/
def extract_orf (m : MRna) : List Codon :=
  let codons := m.to_codons
  let after_start := codons.dropWhile (fun c => !is_start_codon c)
  after_start.takeWhile (fun c => !is_stop_codon c)

end MRna

/- =========================================================
   §3  抗原設計仕様（スパイクタンパク質モデル）
   ========================================================= -/

/-- 抗原タンパク質の設計仕様 -/
structure AntigenSpec where
  name         : String          -- 例: "SARS-CoV-2 Spike RBD"
  target_seq   : List AminoAcid  -- 目的アミノ酸配列
  min_length   : Nat             -- 最小長（免疫原性確保）
  has_signal   : Bool            -- シグナルペプチド有無
  deriving Repr

/-- 抗原設計の妥当性（Prop レベル） -/
def IsValidAntigen (spec : AntigenSpec) : Prop :=
  spec.target_seq.length ≥ spec.min_length ∧
  spec.name ≠ "" ∧
  spec.target_seq ≠ []

instance (spec : AntigenSpec) : Decidable (IsValidAntigen spec) := by
  unfold IsValidAntigen; infer_instance

/- =========================================================
   §4  コドン最適化
   ========================================================= -/

/-- コドン最適化戦略 -/
inductive OptimizationStrategy : Type
  | HighExpression   -- 高発現型（ヒトの高頻度コドン優先）
  | BalancedGC       -- GC含量バランス型
  | RNAStability     -- RNA安定性優先
  deriving Repr, DecidableEq

/-- GCコンテンツ計算 -/
def gc_content (seq : List Base) : Float :=
  let gc := seq.filter (fun b => b == Base.G || b == Base.C) |>.length
  if seq.length = 0 then 0.0
  else Float.ofNat gc / Float.ofNat seq.length

/-- GC含量が適正範囲か (0.4 ≤ GC ≤ 0.7) -/
def is_optimal_gc (seq : List Base) : Bool :=
  let gc := gc_content seq
  0.4 ≤ gc && gc ≤ 0.7

/-- コドン最適化の適用（簡略モデル） -/
def optimize_codons (_ : OptimizationStrategy) (m : MRna) : MRna :=
  -- 実装: 同義コドン置換テーブルを用いたリマッピング
  -- 現バージョンはパスthrough（完全実装は外部同義コドン表を要する）
  m

/- =========================================================
   §5  5'UTR / 3'UTR / PolyA テール設計
   ========================================================= -/

/-- mRNAワクチン構造要素 -/
structure MRnaVaccineConstruct where
  utr5        : List Base   -- 5'非翻訳領域
  kozak       : List Base   -- Kozakコンセンサス配列
  antigen_rna : MRna        -- コドン最適化済み抗原配列
  utr3        : List Base   -- 3'非翻訳領域
  poly_a_len  : Nat         -- PolyAテール長
  deriving Repr

/-- Kozakコンセンサス配列 (GCCACCAUG) の検証 -/
def kozak_consensus : List Base :=
  [Base.G, Base.C, Base.C, Base.A, Base.C, Base.C,
   Base.A, Base.U, Base.G]

def has_valid_kozak (c : MRnaVaccineConstruct) : Bool :=
  c.kozak == kozak_consensus

/-- PolyAテール長の妥当性（≥ 100 nt 推奨） -/
def has_valid_poly_a (c : MRnaVaccineConstruct) : Bool :=
  c.poly_a_len ≥ 100

/-- 全構築物の妥当性（Prop レベル） -/
def IsValidConstruct (c : MRnaVaccineConstruct) : Prop :=
  has_valid_kozak c = true ∧
  has_valid_poly_a c = true ∧
  c.antigen_rna.length ≥ 9  -- 最低3コドン分

instance (c : MRnaVaccineConstruct) : Decidable (IsValidConstruct c) := by
  unfold IsValidConstruct; infer_instance

/- =========================================================
   §6  脂質ナノ粒子（LNP）デリバリー仕様
   ========================================================= -/

/-- LNP組成仕様 -/
structure LnpSpec where
  ionizable_lipid_ratio : Float  -- イオン化可能脂質比率
  helper_lipid_ratio    : Float  -- ヘルパー脂質比率
  cholesterol_ratio     : Float  -- コレステロール比率
  peg_lipid_ratio       : Float  -- PEG脂質比率
  deriving Repr

/-- LNP組成比率合計 = 1.0 の検証（Prop） -/
def IsValidLnpComposition (lnp : LnpSpec) : Prop :=
  lnp.ionizable_lipid_ratio + lnp.helper_lipid_ratio +
  lnp.cholesterol_ratio + lnp.peg_lipid_ratio = 1.0

/-- SM-102系 LNP標準組成（Moderna型参考値） -/
def standard_lnp : LnpSpec :=
  { ionizable_lipid_ratio := 0.50
    helper_lipid_ratio    := 0.10
    cholesterol_ratio     := 0.38
    peg_lipid_ratio       := 0.02 }

/- =========================================================
   §7  ワクチン完全仕様
   ========================================================= -/

/-- mRNAワクチン完全仕様 -/
structure MRnaVaccine where
  id          : String
  target      : AntigenSpec
  construct   : MRnaVaccineConstruct
  delivery    : LnpSpec
  deriving Repr

/-- ワクチン全体の妥当性 -/
def IsValidVaccine (v : MRnaVaccine) : Prop :=
  IsValidAntigen v.target ∧
  IsValidConstruct v.construct ∧
  v.id ≠ ""

instance (v : MRnaVaccine) : Decidable (IsValidVaccine v) := by
  unfold IsValidVaccine; infer_instance

/- =========================================================
   §8  定理・証明
   ========================================================= -/

/-- 補題: 空でない mRNA から翻訳されるアミノ酸列も空でない（9塩基以上） -/
theorem translate_nonempty
    (m : MRna)
    (h : m.seq.length ≥ 3) :
    m.to_codons.length ≥ 1 := by
  simp only [MRna.to_codons]
  match m.seq, h with
  | b1 :: b2 :: b3 :: _, _ => simp
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h

/-- 補題: 転写の反転 (DNA→mRNA の T↔U 対称性) -/
theorem transcribe_T_gives_A :
    Base.transcribe Base.T = Base.A := by rfl

theorem transcribe_A_gives_U :
    Base.transcribe Base.A = Base.U := by rfl

/-- 補題: PolyA が100以上なら has_valid_poly_a = true -/
theorem valid_poly_a_iff (c : MRnaVaccineConstruct) :
    c.poly_a_len ≥ 100 ↔ has_valid_poly_a c = true := by
  simp [has_valid_poly_a]

/-- 補題: 有効な抗原は空でない名前を持つ -/
theorem valid_antigen_has_name
    (spec : AntigenSpec)
    (h : IsValidAntigen spec) :
    spec.name ≠ "" := h.2.1

/- =========================================================
   §9  サンプルインスタンス（SARS-CoV-2 RBD モデル）
   ========================================================= -/

/-- サンプル DNA 鋳型鎖（RBD 断片, 30 nt） -/
def sample_template : List Base :=
  [ Base.T, Base.A, Base.C, Base.G, Base.A, Base.T
  , Base.T, Base.G, Base.A, Base.C, Base.T, Base.A
  , Base.C, Base.G, Base.A, Base.T, Base.T, Base.G
  , Base.A, Base.C, Base.T, Base.A, Base.C, Base.G
  , Base.A, Base.T, Base.T, Base.G, Base.A, Base.C ]

def sample_mrna : MRna := MRna.from_template_strand sample_template

/-- サンプルワクチン構築物 -/
def sample_construct : MRnaVaccineConstruct :=
  { utr5        := [Base.G, Base.G, Base.A, Base.A, Base.U, Base.U]
    kozak       := kozak_consensus
    antigen_rna := sample_mrna
    utr3        := [Base.U, Base.G, Base.A, Base.A, Base.A, Base.U]
    poly_a_len  := 120 }

def sample_antigen : AntigenSpec :=
  { name        := "SARS-CoV-2 Spike RBD"
    target_seq  := sample_mrna.translate
    min_length  := 8
    has_signal  := true }

def sample_vaccine : MRnaVaccine :=
  { id        := "YMT-VAC-001"
    target    := sample_antigen
    construct := sample_construct
    delivery  := standard_lnp }

/-- 実行時妥当性チェック -/
#eval (IsValidConstruct sample_construct)   -- Decidable で検査
#eval (IsValidAntigen sample_antigen)
#eval sample_mrna.translate                 -- アミノ酸配列確認
#eval sample_mrna.extract_orf.length        -- ORF コドン数
#eval is_optimal_gc sample_mrna.seq         -- GC含量検査
