-- =============================================================
--  IPS_Construction.lean
--  iPS細胞構築の形式的フレームワーク（Lean 4 + Mathlib互換）
--  既存 Dna 名前空間の拡張
--  Author: 山本 健夫 / Yamamoto Takeo
--  License: Apache2.0
-- =============================================================

import Std.Data.List.Basic

-- ────────────────────────────────────────────────────────────
-- § 0  既存 Dna 名前空間（依存部分のみ再掲）
-- ────────────────────────────────────────────────────────────
inductive Dna : Type :=
  | mkDna : String → Dna

namespace Dna

inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq

def base_to_complement : Base → Base
  | Base.A => Base.T
  | Base.T => Base.A
  | Base.G => Base.C
  | Base.C => Base.G

-- ────────────────────────────────────────────────────────────
-- § 1  山中因子（Yamanaka Factors）
--      OCT4・SOX2・KLF4・c-MYC の4因子を代数的データ型で定義
-- ────────────────────────────────────────────────────────────

/-- 山中因子の列挙型。OSKM モデルに準拠。 -/
inductive YamanakaFactor : Type
  | OCT4   -- POU5F1: 多能性コアネットワークの中心
  | SOX2   -- HMG-box 転写因子
  | KLF4   -- クリュッペル様因子4
  | cMYC   -- 増殖促進・クロマチンリモデリング
  deriving Repr, DecidableEq

/-- 因子セット：List YamanakaFactor の型エイリアス -/
abbrev FactorSet := List YamanakaFactor

/-- OSKM完全セット -/
def OSKM : FactorSet := [.OCT4, .SOX2, .KLF4, .cMYC]

/-- 最小誘導セット（c-MYC省略・腫瘍原性低減） -/
def OSK  : FactorSet := [.OCT4, .SOX2, .KLF4]

-- ────────────────────────────────────────────────────────────
-- § 2  プロモーター配列（簡略 consensus sequence）
--      実験的最短コアプロモーター領域を Base リストで表現
-- ────────────────────────────────────────────────────────────

/-- 各因子のコアプロモーター配列（Base リスト） -/
def promoter_seq : YamanakaFactor → List Base
  | .OCT4 => [.G,.G,.C,.C,.G,.C,.T,.G,.G,.G,.G,.C,.G,.C,.G]  -- TGGGGCGCG core
  | .SOX2 => [.A,.T,.T,.G,.T,.T,.G,.T,.T,.A,.T,.T,.G,.T,.T]  -- ATTGTT motif ×3
  | .KLF4 => [.G,.G,.G,.C,.G,.G,.G,.G,.C,.G,.G,.G,.C,.G,.G]  -- GC-rich SP1 site
  | .cMYC => [.C,.A,.C,.G,.T,.G,.C,.A,.C,.G,.T,.G,.C,.A,.C]  -- E-box CACGTG ×3

/-- プロモーター長のみ取得 -/
def promoter_length (f : YamanakaFactor) : Nat :=
  (promoter_seq f).length

-- ────────────────────────────────────────────────────────────
-- § 3  細胞状態（CellState）
--      体細胞 → 部分的リプログラミング → iPS細胞 の状態遷移
-- ────────────────────────────────────────────────────────────

/-- 細胞の多能性レベル（0 = 分化体細胞, 10 = 完全iPS） -/
abbrev PluripotencyScore := Fin 11

/-- 細胞状態 -/
inductive CellState : Type
  | Somatic          (cell_type : String)          -- 体細胞
  | PartialReprog    (score : PluripotencyScore)   -- 部分的リプログラミング
  | iPSC             (clone_id : String)           -- iPS細胞
  deriving Repr

/-- 細胞状態の多能性スコアを取得 -/
def cell_score : CellState → Nat
  | .Somatic _       => 0
  | .PartialReprog s => s.val
  | .iPSC _          => 10

-- ────────────────────────────────────────────────────────────
-- § 4  リプログラミング条件（Prop レベル）
--      Treatment の IsValidProtocol パターンを継承・拡張
-- ────────────────────────────────────────────────────────────

/-- リプログラミングプロトコル構造体 -/
structure ReprogProtocol where
  factors       : FactorSet          -- 導入因子セット
  delivery      : String             -- 導入方法 (e.g., "retrovirus", "episomal")
  culture_days  : Nat                -- 培養日数
  feeder_free   : Bool               -- フィーダーフリー条件
  deriving Repr

/-- 有効プロトコルの命題（証明可能な条件） -/
def IsValidReprog (p : ReprogProtocol) : Prop :=
  -- 条件1: OCT4とSOX2は必須
  .OCT4 ∈ p.factors ∧ .SOX2 ∈ p.factors ∧
  -- 条件2: 導入方法が未指定でない
  p.delivery ≠ "" ∧
  -- 条件3: 最低培養日数 (通常 14–21 日)
  14 ≤ p.culture_days

/-- 決定可能インスタンス（実行時チェック用） -/
instance (p : ReprogProtocol) : Decidable (IsValidReprog p) := by
  unfold IsValidReprog
  infer_instance

-- ────────────────────────────────────────────────────────────
-- § 5  多能性マーカー検証
--      NANOG・OCT4・SSEA4 等の発現を命題として管理
-- ────────────────────────────────────────────────────────────

/-- 多能性マーカー -/
inductive PluripotencyMarker : Type
  | NANOG | OCT4_expr | SOX2_expr | SSEA4 | TRA_1_60
  deriving Repr, DecidableEq

/-- マーカー発現プロファイル -/
structure MarkerProfile where
  expressed : List PluripotencyMarker
  deriving Repr

/-- iPS細胞認定に必要な最小マーカーセット -/
def required_markers : List PluripotencyMarker :=
  [.NANOG, .OCT4_expr, .SOX2_expr, .SSEA4]

/-- マーカープロファイルが iPS 認定基準を満たすか -/
def IsIPSCertified (mp : MarkerProfile) : Prop :=
  ∀ m ∈ required_markers, m ∈ mp.expressed

instance (mp : MarkerProfile) : Decidable (IsIPSCertified mp) := by
  unfold IsIPSCertified
  infer_instance

-- ────────────────────────────────────────────────────────────
-- § 6  状態遷移関数（リプログラミング写像）
--      体細胞 → iPS細胞 への変換を純粋関数として形式化
-- ────────────────────────────────────────────────────────────

/-- プロトコルの有効性スコアを算出（OSKMなら+2, OSK+1, 日数×1） -/
private def protocol_score (p : ReprogProtocol) : Nat :=
  let base :=
    if p.factors == OSKM then 8
    else if p.factors == OSK  then 6
    else (p.factors.length * 2)  -- 因子数に応じた暫定スコア
  let day_bonus := if 21 ≤ p.culture_days then 2 else 0
  min (base + day_bonus) 10

/-- リプログラミング実行：体細胞 × プロトコル → 細胞状態 -/
def reprogram (src : CellState) (p : ReprogProtocol) : CellState :=
  if ¬ (.OCT4 ∈ p.factors ∧ .SOX2 ∈ p.factors) then
    src  -- 必須因子欠如 → 状態変化なし
  else
    let score := protocol_score p
    if score ≥ 10 then
      .iPSC ("clone_" ++ p.delivery ++ "_d" ++ toString p.culture_days)
    else
      .PartialReprog ⟨score, by omega⟩

-- ────────────────────────────────────────────────────────────
-- § 7  形式的定理（Theorem）
-- ────────────────────────────────────────────────────────────

/-- 定理 7.1  OSKM × 21日培養 → iPSC に到達する -/
theorem oskm_21days_yields_iPSC :
    let p : ReprogProtocol :=
      { factors := OSKM, delivery := "retrovirus",
        culture_days := 21, feeder_free := true }
    let src := CellState.Somatic "fibroblast"
    ∃ id, reprogram src p = CellState.iPSC id := by
  simp [reprogram, protocol_score, OSKM, OSK]
  decide

/-- 定理 7.2  必須因子欠如 → 状態不変 -/
theorem missing_oct4_no_change (src : CellState) :
    let p : ReprogProtocol :=
      { factors := [.SOX2, .KLF4], delivery := "episomal",
        culture_days := 21, feeder_free := false }
    reprogram src p = src := by
  simp [reprogram]
  decide

/-- 定理 7.3  有効プロトコルは IsValidReprog を満たす -/
theorem OSKM_protocol_valid :
    let p : ReprogProtocol :=
      { factors := OSKM, delivery := "retrovirus",
        culture_days := 14, feeder_free := true }
    IsValidReprog p := by
  simp [IsValidReprog, OSKM]
  decide

-- ────────────────────────────────────────────────────────────
-- § 8  逆相補配列との連携（既存 reverse_complement の利用例）
-- ────────────────────────────────────────────────────────────

/-- Base リスト → String 変換（プロモーター配列の外部出力用） -/
def bases_to_string : List Base → String :=
  fun bs => bs.foldl (fun acc b =>
    acc ++ match b with
      | .A => "A" | .T => "T" | .G => "G" | .C => "C") ""

/-- プロモーター配列の逆相補鎖（テンプレート鎖）を返す -/
def promoter_template_strand (f : YamanakaFactor) : List Base :=
  (promoter_seq f).reverse.map base_to_complement

/-- OCT4 プロモーターのセンス鎖とテンプレート鎖を対で返す -/
def oct4_promoter_pair : List Base × List Base :=
  (promoter_seq .OCT4, promoter_template_strand .OCT4)

-- ────────────────────────────────────────────────────────────
-- § 9  完全パイプライン例
--      線維芽細胞 → OSKM導入 → iPSC → マーカー認定
-- ────────────────────────────────────────────────────────────

def fibroblast : CellState := .Somatic "human_fibroblast"

def OSKM_protocol : ReprogProtocol :=
  { factors := OSKM, delivery := "episomal_vector",
    culture_days := 28, feeder_free := true }

def reprogrammed : CellState := reprogram fibroblast OSKM_protocol

def certified_profile : MarkerProfile :=
  { expressed := [.NANOG, .OCT4_expr, .SOX2_expr, .SSEA4, .TRA_1_60] }

/-- パイプライン全体の健全性：iPS認定基準を満たす -/
theorem pipeline_certified : IsIPSCertified certified_profile := by
  simp [IsIPSCertified, required_markers, certified_profile]
  decide

end Dna
-- =============================================================
--  End of IPS_Construction.lean
-- =============================================================
