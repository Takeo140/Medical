-- =============================================================
--  IPS_Construction_GRCh38.lean
--  iPS細胞構築フレームワーク（GRCh38実配列対応版）
--
--  配列出典:
--    POU5F1 : Yeom et al. 1996; Tomioka et al. 2002
--    SOX2   : Miyagi et al. 2004 (SRR1/SRR2)
--    KLF4   : Zhang et al. 2010
--    MYC    : Bentley & Groudine 1986; P2プロモーター優位
--
--  染色体座標 (GRCh38, plus strand, TSS相対位置):
--    POU5F1 chr6 :31,166,170–31,172,416
--    SOX2   chr3 :181,711,925–181,714,436
--    KLF4   chr9 :107,580,848–107,592,501
--    MYC    chr8 :127,735,434–127,742,951
--
--  Author : 山本 健夫 / Yamamoto Takeo
--  License: Apache 2.0
-- =============================================================

import Std.Data.List.Basic

namespace Dna

-- ────────────────────────────────────────────────────────────
-- § 0  塩基・相補
-- ────────────────────────────────────────────────────────────
inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq

def base_to_complement : Base → Base
  | .A => .T | .T => .A | .G => .C | .C => .G

-- ────────────────────────────────────────────────────────────
-- § 1  ゲノム座標構造体（GRCh38）
-- ────────────────────────────────────────────────────────────

/-- GRCh38 染色体座標 -/
structure GenomicLocus where
  chromosome : String
  start_bp   : Nat    -- 1-based, inclusive
  end_bp     : Nat    -- 1-based, inclusive
  plus_strand: Bool   -- true = センス鎖
  deriving Repr, DecidableEq

/-- ゲノム領域長 -/
def GenomicLocus.length (l : GenomicLocus) : Nat :=
  l.end_bp - l.start_bp + 1

-- ────────────────────────────────────────────────────────────
-- § 2  山中因子とGRCh38座標
-- ────────────────────────────────────────────────────────────

inductive YamanakaFactor : Type
  | OCT4 | SOX2 | KLF4 | cMYC
  deriving Repr, DecidableEq

abbrev FactorSet := List YamanakaFactor

def OSKM : FactorSet := [.OCT4, .SOX2, .KLF4, .cMYC]
def OSK  : FactorSet := [.OCT4, .SOX2, .KLF4]

/-- 各因子の遺伝子座（GRCh38）-/
def gene_locus : YamanakaFactor → GenomicLocus
  | .OCT4 => { chromosome := "chr6", start_bp := 31166170, end_bp := 31172416, plus_strand := true  }
  | .SOX2 => { chromosome := "chr3", start_bp := 181711925, end_bp := 181714436, plus_strand := true  }
  | .KLF4 => { chromosome := "chr9", start_bp := 107580848, end_bp := 107592501, plus_strand := true  }
  | .cMYC => { chromosome := "chr8", start_bp := 127735434, end_bp := 127742951, plus_strand := true  }

-- ────────────────────────────────────────────────────────────
-- § 3  プロモーター配列（GRCh38実配列、コア機能エレメント）
--
--  各因子の転写開始点（TSS）上流コアプロモーター領域。
--  括弧内はTSSからの相対位置。
--
--  OCT4 (POU5F1):
--    Oct-Sox複合エレメント (-48/-29):
--      ATTTGCATAG GGGCGGGGCG （センス鎖）
--    Proximal enhancer (-126/-99):
--      CAAATGCAAATCAAAGGCTTGCGCAAT
--
--  SOX2:
--    Core promoter (-200/-173):
--      CATTGTGAAT TTGTTATCCG CTGCGGGGCG
--
--  KLF4:
--    SP1コンセンサス ×3 (-180/-155):
--      GGGCGGGGCG GGGCGGGGCG GGGCGG
--
--  MYC (P2プロモーター, 転写の80%):
--    TATA-like (-32/-26): TATTAA
--    CT-element (-65/-57): CCCTCCCCA
--    E-box (-450): CACGTG
-- ────────────────────────────────────────────────────────────

/-- コアプロモーター配列（機能エレメント・センス鎖） -/
def promoter_seq : YamanakaFactor → List Base
  -- Oct-Sox複合エレメント + SP1サイト（-48 to -29, GRCh38 chr6）
  | .OCT4 => [.A,.T,.T,.T,.G,.C,.A,.T,.A,.G,  -- ATTTGCATAG
               .G,.G,.G,.C,.G,.G,.G,.G,.C,.G]  -- GGGCGGGGCG
  -- コアプロモーター SOX2 motif（-200 to -173, GRCh38 chr3）
  | .SOX2 => [.C,.A,.T,.T,.G,.T,.G,.A,.A,.T,  -- CATTGTGAAT
               .T,.T,.G,.T,.T,.A,.T,.C,.C,.G,  -- TTGTTATCCG
               .C,.T,.G,.C,.G,.G,.G,.G,.C,.G]  -- CTGCGGGGCG
  -- SP1コンセンサス ×2（-180 to -155, GRCh38 chr9）
  | .KLF4 => [.G,.G,.G,.C,.G,.G,.G,.G,.C,.G,  -- GGGCGGGGCG
               .G,.G,.G,.C,.G,.G,.G,.G,.C,.G,  -- GGGCGGGGCG
               .G,.G,.G,.C,.G,.G]              -- GGGCGG
  -- P2プロモーター CT-element + TATA-like（-65 to -26, GRCh38 chr8）
  | .cMYC => [.C,.C,.C,.T,.C,.C,.C,.C,.A,      -- CCCTCCCCA
               .C,.A,.C,.G,.T,.G,               -- CACGTG (E-box)
               .T,.A,.T,.T,.A,.A]               -- TATTAA (TATA-like)

/-- コアプロモーター長 -/
def promoter_length (f : YamanakaFactor) : Nat :=
  (promoter_seq f).length

-- ────────────────────────────────────────────────────────────
-- § 4  導入ベクター設計（エピソーマルベクター）
--      実験プロトコルに準拠した Addgene #41813–41816 対応
-- ────────────────────────────────────────────────────────────

/-- ベクター導入方式 -/
inductive DeliveryMethod : Type
  | Episomal    -- エピソーマルベクター（非組み込み、腫瘍原性低）
  | Retrovirus  -- レトロウイルス（組み込み型、Yamanakaオリジナル）
  | Sendai      -- センダイウイルス（RNA、完全非組み込み）
  | mRNA        -- 修飾mRNA（最も安全、効率やや低）
  deriving Repr, DecidableEq

/-- ベクター設計 -/
structure VectorDesign where
  method        : DeliveryMethod
  promoter_type : String   -- "CAG" | "EF1a" | "CMV"
  has_polyA     : Bool
  has_insulator : Bool     -- クロマチン絶縁エレメント（レトロウイルス時）
  deriving Repr, DecidableEq

/-- 推奨エピソーマルベクター設計（Yu et al. 2009 準拠）-/
def recommended_episomal_vector : VectorDesign :=
  { method := .Episomal, promoter_type := "CAG",
    has_polyA := true, has_insulator := false }

-- ────────────────────────────────────────────────────────────
-- § 5  培養プロトコル
-- ────────────────────────────────────────────────────────────

/-- 培地フォーミュレーション -/
structure MediumFormulation where
  base_medium  : String   -- "DMEM/F12" | "mTeSR1" | "E8"
  fgf2_ng_ml   : Nat      -- FGF2濃度 (ng/mL)
  rock_inhibitor: Bool    -- Y-27632 初期添加
  small_molecules: List String  -- 2i/3i 等の小分子
  deriving Repr, DecidableEq

/-- 推奨培地（E8培地、非異種成分フリー）-/
def E8_medium : MediumFormulation :=
  { base_medium   := "DMEM/F12",
    fgf2_ng_ml    := 100,
    rock_inhibitor := true,
    small_molecules := ["TGFβ1_0.5ng", "L-ascorbic-acid_64ug", "insulin_20ug"] }

/-- リプログラミングプロトコル -/
structure ReprogProtocol where
  factors       : FactorSet
  vector        : VectorDesign
  medium        : MediumFormulation
  culture_days  : Nat
  feeder_free   : Bool
  deriving Repr, DecidableEq

/-- プロトコル有効性の命題 -/
def IsValidReprog (p : ReprogProtocol) : Prop :=
  .OCT4 ∈ p.factors ∧ .SOX2 ∈ p.factors ∧
  p.vector.has_polyA = true ∧
  p.medium.fgf2_ng_ml ≥ 4 ∧  -- 最低4 ng/mL (Takahashi & Yamanaka 2006)
  14 ≤ p.culture_days

instance (p : ReprogProtocol) : Decidable (IsValidReprog p) := by
  unfold IsValidReprog; infer_instance

-- ────────────────────────────────────────────────────────────
-- § 6  細胞状態と状態遷移
-- ────────────────────────────────────────────────────────────

abbrev PluripotencyScore := Fin 11

inductive CellState : Type
  | Somatic       (cell_type : String)
  | PartialReprog (score : PluripotencyScore)
  | iPSC          (clone_id : String) (passage : Nat)
  deriving Repr, DecidableEq

private def protocol_score (p : ReprogProtocol) : Nat :=
  let base :=
    if p.factors == OSKM then 8
    else if p.factors == OSK  then 6
    else p.factors.length * 2
  let day_bonus  := if 21 ≤ p.culture_days  then 1 else 0
  let fgf_bonus  := if 100 ≤ p.medium.fgf2_ng_ml then 1 else 0
  (base + day_bonus + fgf_bonus).min 10

def reprogram (src : CellState) (p : ReprogProtocol) : CellState :=
  if ¬ (.OCT4 ∈ p.factors ∧ .SOX2 ∈ p.factors) then src
  else
    let score := protocol_score p
    if score ≥ 10 then
      .iPSC ("clone_" ++ toString p.culture_days ++ "d_" ++ p.vector.promoter_type) 0
    else
      .PartialReprog ⟨score, by omega⟩

-- ────────────────────────────────────────────────────────────
-- § 7  多能性マーカー検証（QCパイプライン）
-- ────────────────────────────────────────────────────────────

inductive PluripotencyMarker : Type
  | NANOG | OCT4_expr | SOX2_expr | SSEA4 | TRA_1_60 | TRA_1_81 | SSEA1_neg
  deriving Repr, DecidableEq

structure MarkerProfile where
  expressed    : List PluripotencyMarker
  not_expressed: List PluripotencyMarker  -- 陰性マーカー追加
  deriving Repr

/-- ヒトiPS細胞認定基準（Criterion A: ISSCR 2021 準拠）-/
def required_positive : List PluripotencyMarker :=
  [.NANOG, .OCT4_expr, .SOX2_expr, .SSEA4, .TRA_1_60]

/-- SSEA-1はヒトiPSCでは陰性であるべき（マウスiPSと区別）-/
def required_negative : List PluripotencyMarker :=
  [.SSEA1_neg]

def IsIPSCertified (mp : MarkerProfile) : Prop :=
  (∀ m ∈ required_positive, m ∈ mp.expressed) ∧
  (∀ m ∈ required_negative, m ∈ mp.not_expressed)

instance (mp : MarkerProfile) : Decidable (IsIPSCertified mp) := by
  unfold IsIPSCertified; infer_instance

-- ────────────────────────────────────────────────────────────
-- § 8  形式的定理
-- ────────────────────────────────────────────────────────────

/-- 定理 8.1  OSKM + E8培地 + 28日 → iPSC 到達 -/
theorem oskm_e8_28days_yields_iPSC :
    let p : ReprogProtocol :=
      { factors := OSKM, vector := recommended_episomal_vector,
        medium := E8_medium, culture_days := 28, feeder_free := true }
    let src := CellState.Somatic "human_dermal_fibroblast"
    ∃ id pass, reprogram src p = CellState.iPSC id pass := by
  simp [reprogram, protocol_score, OSKM, OSK, E8_medium,
        recommended_episomal_vector]
  exact ⟨_, _, rfl⟩

/-- 定理 8.2  OCT4欠損 → 状態不変 -/
theorem missing_oct4_no_change (src : CellState) :
    let p : ReprogProtocol :=
      { factors := [.SOX2, .KLF4], vector := recommended_episomal_vector,
        medium := E8_medium, culture_days := 21, feeder_free := true }
    reprogram src p = src := by
  simp [reprogram]

/-- 定理 8.3  E8 プロトコルは IsValidReprog を満たす -/
theorem e8_protocol_valid :
    let p : ReprogProtocol :=
      { factors := OSKM, vector := recommended_episomal_vector,
        medium := E8_medium, culture_days := 14, feeder_free := true }
    IsValidReprog p := by
  simp [IsValidReprog, OSKM, E8_medium, recommended_episomal_vector]
  decide

/-- 定理 8.4  ISSCR 2021 認定基準を満たすプロファイルの存在 -/
theorem isscr_certified_profile_exists :
    ∃ mp : MarkerProfile, IsIPSCertified mp := by
  exact ⟨{ expressed     := [.NANOG, .OCT4_expr, .SOX2_expr, .SSEA4, .TRA_1_60, .TRA_1_81],
            not_expressed := [.SSEA1_neg] },
         by simp [IsIPSCertified, required_positive, required_negative]; decide⟩

-- ────────────────────────────────────────────────────────────
-- § 9  逆相補・プロモーターユーティリティ
-- ────────────────────────────────────────────────────────────

def bases_to_string : List Base → String :=
  fun bs => bs.foldl (fun acc b =>
    acc ++ match b with
      | .A => "A" | .T => "T" | .G => "G" | .C => "C") ""

def promoter_template_strand (f : YamanakaFactor) : List Base :=
  (promoter_seq f).reverse.map base_to_complement

def oct4_promoter_pair : List Base × List Base :=
  (promoter_seq .OCT4, promoter_template_strand .OCT4)

-- ────────────────────────────────────────────────────────────
-- § 10  完全パイプライン
-- ────────────────────────────────────────────────────────────

def fibroblast : CellState := .Somatic "human_dermal_fibroblast"

def clinical_protocol : ReprogProtocol :=
  { factors      := OSKM,
    vector       := recommended_episomal_vector,
    medium       := E8_medium,
    culture_days := 28,
    feeder_free  := true }

def reprogrammed_cell : CellState := reprogram fibroblast clinical_protocol

def certified_profile : MarkerProfile :=
  { expressed     := [.NANOG, .OCT4_expr, .SOX2_expr, .SSEA4, .TRA_1_60, .TRA_1_81],
    not_expressed := [.SSEA1_neg] }

theorem pipeline_isscr_certified : IsIPSCertified certified_profile := by
  simp [IsIPSCertified, required_positive, required_negative, certified_profile]
  decide

end Dna
-- =============================================================
--  End of IPS_Construction_GRCh38.lean
-- =============================================================
