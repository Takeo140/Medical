-- =============================================================================
-- Verified DNA Processing & Protocol Architecture
-- License: CC BY 4.0　Apache 2.0 Takeo Yamamoto
-- =============================================================================

import Std.Data.Array.Basic

/-!
# 詳細化のポイント
1. String依存からの脱却: DNA配列を `Array Base` として定義し、不正な文字の混入を型レベルで防ぐ。
2. ゼロオーバーヘッド操作: `List` の再帰的処理を `Array` に置き換え、実行速度とメモリ効率を向上。
3. 依存型（Dependent Types）の導入: `Treatment` 構造体の中に「証明」を埋め込み、無効なプロトコルの生成を物理的に不可能にする。
-/

-- ============================================================
-- 1. Base (塩基) Type & Operations
-- ============================================================

inductive Base : Type
  | A | T | G | C
  deriving Repr, DecidableEq, Inhabited

namespace Base

@[inline]
def complement : Base → Base
  | A => T
  | T => A
  | G => C
  | C => G

@[inline]
def toChar : Base → Char
  | A => 'A'
  | T => 'T'
  | G => 'G'
  | C => 'C'

def fromChar? : Char → Option Base
  | 'A' => some A
  | 'T' => some T
  | 'G' => some G
  | 'C' => some C
  | _   => none

end Base

-- ============================================================
-- 2. Dna (DNA配列) Architecture
-- ============================================================

/-- 
検証済みの塩基配列。
生のStringをラップするのではなく、Array Base を保持することで
「DNA塩基以外が含まれないこと」を構造的に保証します。
-/
structure Dna where
  seq : Array Base
  deriving Repr, Inhabited, BEq

namespace Dna

/-- 文字列からの安全なパース機構（バリデーション境界） -/
def fromString? (s : String) : Option Dna :=
  let chars := s.toList
  let bases := chars.filterMap Base.fromChar?
  -- フィルタリング前後で長さが変わらなければ、全ての文字が有効な塩基
  if bases.length == chars.length then
    some ⟨bases.toArray⟩
  else
    none

/-- 
文字からBaseへの変換・エラーチェックを排除。
すでにDna型である時点で有効性が保証されているため、最速で反転・相補処理を実行できます。
-/
@[inline, export reverse_complement_c]
def reverseComplement (dna : Dna) : Dna :=
  ⟨dna.seq.reverse.map Base.complement⟩

/-- 
Listの drop/take を廃止し、連続メモリ(Array)のスライスによる高速マッチングへ変更。
-/
def findPattern (pattern : Array Base) (dna : Dna) : Array Nat :=
  let pLen := pattern.size
  let dLen := dna.seq.size
  if pLen == 0 || pLen > dLen then
    #[]
  else
    -- C言語の for ループに展開される範囲フィルタリング
    (Array.range (dLen - pLen + 1)).filterMap (fun i =>
      let slice := dna.seq.extract i (i + pLen)
      if slice == pattern then some i else none
    )

end Dna

-- ============================================================
-- 3. Verified Treatment Protocol (依存型パラダイム)
-- ============================================================

/-- 
命題（Prop）をフィールドとして内包する構造体。
この型のインスタンスが存在する時点で、dosage と scheduling が空ではないことが
数学的に証明されている状態になります。
-/
structure Treatment where
  description : String
  dosage      : String
  scheduling  : String
  -- 健全性の証明（コンパイル時に評価され、実行時のオーバーヘッドはゼロ）
  h_dosage    : dosage ≠ ""
  h_scheduling: scheduling ≠ ""

namespace Treatment

/-- 
外部入力（実行時データ）から安全に Treatment を構築するためのスマートコンストラクタ。
-/
def mk? (desc dosage sched : String) : Option Treatment :=
  -- if h : ... の構文で、条件判定と同時にその「証明」を変数に束縛する
  if hd : dosage = "" then none
  else if hs : sched = "" then none
  else some {
    description  := desc
    dosage       := dosage
    scheduling   := sched
    -- 取得した証明を直接代入（これによりコンパイラが納得する）
    h_dosage     := hd
    h_scheduling := hs
  }

end Treatment
