import Mathlib

-- DirectReprogramming.lean
-- 直接変換（トランスダイファレンシェーション）形式化
-- F-Theory A1–A4 準拠 / Apache 2.0
-- Takeo Yamamoto

namespace DirectReprogramming

/- =========================================================
   §1  細胞種・分化能階層 (A4: 階層構造)
   ========================================================= -/

/-- 分化能レベル -/
inductive Potency : Type
  | Totipotent      -- 全能性（受精卵）
  | Pluripotent     -- 多能性（ES/iPS）
  | Multipotent     -- 多分化能（成体幹細胞）
  | Unipotent       -- 単分化能
  | Somatic         -- 体細胞（終末分化）
  deriving Repr, DecidableEq, Ord

/-- 分化能の順序: Somatic が最も低い -/
def Potency.rank : Potency → Nat
  | .Totipotent  => 4
  | .Pluripotent => 3
  | .Multipotent => 2
  | .Unipotent   => 1
  | .Somatic     => 0

/-- 体細胞種別 -/
inductive SomaticType : Type
  | Fibroblast      -- 皮膚線維芽細胞
  | Hepatocyte      -- 肝細胞
  | Cardiomyocyte   -- 心筋細胞
  | Neuron          -- 神経細胞
  | Astrocyte       -- アストロサイト
  | PancreaticBeta  -- 膵β細胞
  | Keratinocyte    -- ケラチノサイト
  deriving Repr, DecidableEq

/-- 細胞ノード: 種別と分化能をペアで持つ
    ※ 注意: この CellNode は §3 以降の DirectReprogrammingProtocol からは
      参照されていない（source/target は素の SomaticType のまま）。
      「分化能を上げない」ことを型レベルで保証したいなら、
      source/target をここに差し替える設計変更が必要。 -/
structure CellNode where
  cell_type : SomaticType
  potency   : Potency
  deriving Repr, DecidableEq

/- =========================================================
   §2  転写因子 (A3: 論理整合性)
   ========================================================= -/

/-- 転写因子識別子 -/
inductive TranscriptionFactor : Type
  | Ascl1 | Brn2 | Myt1l | NeuroD1 | Ngn2
  | Gata4 | Mef2c | Tbx5 | Hand2
  | Hnf4a | Foxa1 | Foxa2 | Foxa3
  | Pdx1 | Ngn3 | MafA
  | Oct4 | Sox2 | Klf4 | cMyc
  deriving Repr, DecidableEq

abbrev TFSet := List TranscriptionFactor

/- =========================================================
   §3  直接変換プロトコル定義 (A2: 位相空間)
   ---------------------------------------------------------
   注: efficiency / tumor_risk は Float ではなく ℚ で保持する。
   理由は DNAGenomicDifferentiation.lean と同一
   （Float は Mathlib 上で LinearOrder / OrderedField を持たず、
    Nat.floor / Nat.ceil / div_pos / nlinarith が適用できないため）。
   ========================================================= -/

/-- 直接変換プロトコル -/
structure DirectReprogrammingProtocol where
  name          : String
  source        : SomaticType
  target        : SomaticType
  factors       : TFSet
  efficiency    : ℚ          -- 変換効率 0–1
  duration_days : Nat
  tumor_risk    : ℚ          -- 腫瘍化リスク 0–1
  deriving Repr

/-- プロトコル妥当性 (Prop) -/
def IsValidProtocol (p : DirectReprogrammingProtocol) : Prop :=
  p.factors ≠ [] ∧
  0 < p.efficiency ∧ p.efficiency ≤ 1 ∧
  0 ≤ p.tumor_risk ∧ p.tumor_risk ≤ 1 ∧
  p.source ≠ p.target ∧
  p.duration_days > 0

instance (p : DirectReprogrammingProtocol) : Decidable (IsValidProtocol p) := by
  unfold IsValidProtocol; infer_instance

/-- iPS経由より安全か（腫瘍リスク < 0.05） -/
def IsSaferThanIPS (p : DirectReprogrammingProtocol) : Prop :=
  p.tumor_risk < 0.05

instance (p : DirectReprogrammingProtocol) : Decidable (IsSaferThanIPS p) := by
  unfold IsSaferThanIPS; infer_instance

/- =========================================================
   §4  実証済みプロトコルデータベース (A4: 知識階層)
   ========================================================= -/

/-- Wernig 2010: 線維芽細胞 → 神経細胞 -/
def protocol_fibro_to_neuron : DirectReprogrammingProtocol :=
  { name          := "Wernig2010_iN"
    source        := SomaticType.Fibroblast
    target        := SomaticType.Neuron
    factors       := [.Ascl1, .Brn2, .Myt1l]
    efficiency    := 0.20
    duration_days := 21
    tumor_risk    := 0.02 }

/-- Ieda 2010: 線維芽細胞 → 心筋細胞 -/
def protocol_fibro_to_cardio : DirectReprogrammingProtocol :=
  { name          := "Ieda2010_iCM"
    source        := SomaticType.Fibroblast
    target        := SomaticType.Cardiomyocyte
    factors       := [.Gata4, .Mef2c, .Tbx5]
    efficiency    := 0.15
    duration_days := 28
    tumor_risk    := 0.01 }

/-- Huang 2011: 線維芽細胞 → 肝細胞 -/
def protocol_fibro_to_hepato : DirectReprogrammingProtocol :=
  { name          := "Huang2011_iHep"
    source        := SomaticType.Fibroblast
    target        := SomaticType.Hepatocyte
    factors       := [.Hnf4a, .Foxa1, .Foxa2, .Foxa3]
    efficiency    := 0.08
    duration_days := 14
    tumor_risk    := 0.03 }

/-- Zhou 2008: 膵外分泌細胞 → 膵β細胞 -/
def protocol_exo_to_beta : DirectReprogrammingProtocol :=
  { name          := "Zhou2008_iBeta"
    source        := SomaticType.Hepatocyte
    target        := SomaticType.PancreaticBeta
    factors       := [.Pdx1, .Ngn3, .MafA]
    efficiency    := 0.12
    duration_days := 10
    tumor_risk    := 0.02 }

def protocol_db : List DirectReprogrammingProtocol :=
  [ protocol_fibro_to_neuron
  , protocol_fibro_to_cardio
  , protocol_fibro_to_hepato
  , protocol_exo_to_beta ]

/- =========================================================
   §5  変換グラフ探索 (A2: 位相空間上の経路)
   ========================================================= -/

def find_protocol
    (src : SomaticType) (tgt : SomaticType) :
    Option DirectReprogrammingProtocol :=
  protocol_db.find? (fun p => p.source == src && p.target == tgt)

/-- src から出発する p1 と、p1.target を出発点として tgt に到達する p2 を連結する。
    (この実装は p1.target == p2.source の連結条件を正しく使っており、
     DNAGenomicDifferentiation.lean の find_two_step_cascade のような
     バグはない) -/
def find_two_step_path
    (src : SomaticType) (tgt : SomaticType) :
    Option (DirectReprogrammingProtocol × DirectReprogrammingProtocol) :=
  let intermediates := protocol_db.filterMap (fun p1 =>
    if p1.source == src then
      protocol_db.find? (fun p2 =>
        p2.source == p1.target && p2.target == tgt)
        |>.map (fun p2 => (p1, p2))
    else none)
  intermediates.head?

/-- 直接変換可能性（Prop）-/
def IsDirectlyConvertible (src tgt : SomaticType) : Prop :=
  ∃ p ∈ protocol_db, p.source = src ∧ p.target = tgt

/- =========================================================
   §6  効率・リスク評価 (A1: 極値原理)
   ========================================================= -/

/-- 複合スコア: efficiency / (tumor_risk + ε) -/
def safety_efficiency_score (p : DirectReprogrammingProtocol) : ℚ :=
  p.efficiency / (p.tumor_risk + 0.001)

/-- 最良プロトコル選択 -/
def best_protocol
    (src : SomaticType) (tgt : SomaticType) :
    Option DirectReprogrammingProtocol :=
  let candidates := protocol_db.filter
    (fun p => p.source == src && p.target == tgt)
  candidates.foldl (fun acc p =>
    match acc with
    | none => some p
    | some best =>
      if safety_efficiency_score p > safety_efficiency_score best
      then some p else some best) none

/-- iPS経由との比較サマリー -/
structure ComparisonResult where
  protocol       : DirectReprogrammingProtocol
  ips_tumor_risk : ℚ
  risk_reduction : ℚ
  deriving Repr

def compare_to_ips (p : DirectReprogrammingProtocol) : ComparisonResult :=
  let ips_risk : ℚ := 0.15
  { protocol       := p
    ips_tumor_risk := ips_risk
    risk_reduction := (ips_risk - p.tumor_risk) / ips_risk }

/- =========================================================
   §7  収量シミュレーション (A1: 極値原理)
   ========================================================= -/

def estimated_yield (input_cells : Nat)
    (p : DirectReprogrammingProtocol) : Nat :=
  Nat.floor ((input_cells : ℚ) * p.efficiency)

def required_input (target_yield : Nat)
    (p : DirectReprogrammingProtocol)
    (h : p.efficiency > 0) : Nat :=
  Nat.ceil ((target_yield : ℚ) / p.efficiency)

/- =========================================================
   §8  定理・証明 (sorry-free)
   ========================================================= -/

/-- 全登録プロトコルはiPS腫瘍リスク(0.15)未満 -/
theorem all_protocols_safer_than_ips :
    ∀ p ∈ protocol_db, p.tumor_risk < 0.15 := by
  intro p hp
  simp [protocol_db] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    norm_num [protocol_fibro_to_neuron, protocol_fibro_to_cardio,
              protocol_fibro_to_hepato, protocol_exo_to_beta]

/-- 変換収量 ≤ 入力細胞数 (efficiency ≤ 1.0 条件下) -/
theorem yield_le_input
    (n : Nat) (p : DirectReprogrammingProtocol)
    (h : p.efficiency ≤ 1) :
    estimated_yield n p ≤ n := by
  unfold estimated_yield
  have hx : (n : ℚ) * p.efficiency ≤ (n : ℚ) :=
    mul_le_of_le_one_right (Nat.cast_nonneg n) h
  have hmono := Nat.floor_mono hx
  simpa using hmono

/-- DBに同一ソース=ターゲットのプロトコルは存在しない -/
theorem no_identity_protocol :
    ∀ p ∈ protocol_db, p.source ≠ p.target := by
  intro p hp
  simp [protocol_db] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    simp [protocol_fibro_to_neuron, protocol_fibro_to_cardio,
          protocol_fibro_to_hepato, protocol_exo_to_beta]

/-- safety_efficiency_score は efficiency > 0 かつ tumor_risk ≥ 0 なら正値 -/
theorem score_positive (p : DirectReprogrammingProtocol)
    (heff : p.efficiency > 0) (hrisk : 0 ≤ p.tumor_risk) :
    safety_efficiency_score p > 0 := by
  unfold safety_efficiency_score
  apply div_pos heff
  linarith

/-- 【注意: 空虚な定理】
    結論 `Potency.rank Potency.Somatic = 0` は p にも `p ∈ protocol_db` にも
    依存しない定数の事実であり、見出しが意図する「直接変換は分化能を
    上げない（Somatic→Somatic を保つ）」という主張を実際には何も
    検証していない。現行モデルでは source/target が CellNode ではなく
    素の SomaticType なので、型レベルでこれ以上の主張は表現できない。
    意味のある定理にするには §1 の CellNode を source/target に
    採用するモデル変更が必要。 -/
theorem direct_reprog_stays_somatic
    (p : DirectReprogrammingProtocol)
    (_ : p ∈ protocol_db) :
    Potency.rank Potency.Somatic = 0 := by
  rfl

/- =========================================================
   §9  #eval サンプル実行
   ========================================================= -/

-- プロトコル検索
#eval find_protocol SomaticType.Fibroblast SomaticType.Neuron

-- 全プロトコルのスコア
#eval protocol_db.map (fun p =>
  (p.name, safety_efficiency_score p))

-- 100万細胞投入時の収量推定
#eval protocol_db.map (fun p =>
  (p.name, estimated_yield 1_000_000 p))

-- iPS比較（リスク削減率）
#eval protocol_db.map (fun p =>
  let r := compare_to_ips p
  (p.name, r.risk_reduction))

-- 妥当性・安全性チェック
#eval protocol_db.map (fun p =>
  (p.name,
   decide (IsValidProtocol p),
   decide (IsSaferThanIPS p)))

-- 2ステップ経路探索例
#eval find_two_step_path
  SomaticType.Fibroblast SomaticType.PancreaticBeta

end DirectReprogramming
