-- CellCulture.lean
-- 同種細胞の培養増殖モデル 形式化
-- F-Theory A1–A4 準拠 / Apache 2.0
-- Takeo Yamamoto

import Std.Data.List.Basic

/- =========================================================
   §1  細胞型・状態の定義 (A4: 階層構造)
   ========================================================= -/

/-- 細胞種別 -/
inductive CellType : Type
  | HEK293       -- ヒト胎児腎細胞（ワクチン製造用）
  | CHO          -- チャイニーズハムスター卵巣細胞
  | Vero         -- アフリカミドリザル腎細胞
  | iPSC         -- 人工多能性幹細胞
  | Custom : String → CellType
  deriving Repr, DecidableEq

/-- 細胞の状態 -/
inductive CellState : Type
  | Viable       -- 生存・増殖可能
  | Quiescent    -- 静止期
  | Senescent    -- 老化
  | Apoptotic    -- アポトーシス中
  deriving Repr, DecidableEq

/-- 継代数（passage number）-/
abbrev Passage := Nat

/- =========================================================
   §2  培養環境パラメータ (A3: 論理整合性)
   ========================================================= -/

/-- 培養条件 -/
structure CultureCondition where
  temp_celsius   : Float   -- 温度 (標準: 37.0)
  co2_percent    : Float   -- CO2濃度 (標準: 5.0)
  humidity       : Float   -- 湿度 (標準: 0.95)
  serum_percent  : Float   -- 血清濃度 % (FBS等)
  deriving Repr

/-- 標準培養条件（哺乳類細胞）-/
def standard_condition : CultureCondition :=
  { temp_celsius  := 37.0
    co2_percent   := 5.0
    humidity      := 0.95
    serum_percent := 10.0 }

/-- 培養条件の妥当性 (Prop) -/
def IsOptimalCondition (c : CultureCondition) : Prop :=
  36.0 ≤ c.temp_celsius ∧ c.temp_celsius ≤ 38.0 ∧
  4.0  ≤ c.co2_percent  ∧ c.co2_percent  ≤ 6.0  ∧
  0.90 ≤ c.humidity                               ∧
  0.0  < c.serum_percent

instance (c : CultureCondition) : Decidable (IsOptimalCondition c) := by
  unfold IsOptimalCondition; infer_instance

/- =========================================================
   §3  細胞集団モデル (A2: 位相空間)
   ========================================================= -/

/-- 細胞集団スナップショット -/
structure CellPopulation where
  cell_type      : CellType
  passage        : Passage
  count          : Nat          -- 細胞数（個）
  viability      : Float        -- 生存率 0.0–1.0
  state          : CellState
  deriving Repr

/-- 生存細胞数 -/
def CellPopulation.viable_count (p : CellPopulation) : Nat :=
  Nat.floor (Float.ofNat p.count * p.viability)

/-- 細胞集団が継代可能か -/
def CellPopulation.can_passage (p : CellPopulation) : Bool :=
  p.viability ≥ 0.85 && p.count ≥ 1_000_000 && p.passage < 30

/-- 継代可能性の Prop -/
def IsPassageable (p : CellPopulation) : Prop :=
  p.viability ≥ 0.85 ∧ p.count ≥ 1_000_000 ∧ p.passage < 30

instance (p : CellPopulation) : Decidable (IsPassageable p) := by
  unfold IsPassageable; infer_instance

/- =========================================================
   §4  増殖モデル: 指数増殖 & ロジスティック (A1: 極値原理)
   ========================================================= -/

/-- 増殖パラメータ -/
structure GrowthParams where
  doubling_time_h : Float     -- 倍加時間（時間）標準HEK293: 24h
  carrying_cap    : Nat       -- 培養容量上限（細胞/cm²換算）
  deriving Repr

/-- 標準 HEK293 増殖パラメータ -/
def hek293_growth : GrowthParams :=
  { doubling_time_h := 24.0
    carrying_cap    := 20_000_000 }

/-- 指数増殖: N(t) = N₀ × 2^(t / td) の整数近似 -/
def exponential_growth (n0 : Nat) (params : GrowthParams) (hours : Nat) : Nat :=
  let doublings : Float := Float.ofNat hours / params.doubling_time_h
  -- 2^doublings の整数近似（Float経由）
  let factor := Float.pow 2.0 doublings
  Nat.max n0 (Nat.floor (Float.ofNat n0 * factor))

/-- ロジスティック増殖: K への収束を考慮 -/
def logistic_growth (n0 : Nat) (params : GrowthParams) (hours : Nat) : Nat :=
  let k := params.carrying_cap
  let n_exp := exponential_growth n0 params hours
  -- min(N_exp, K) で上限規制
  Nat.min n_exp k

/-- 増殖は単調非減少（指数モデル） -/
theorem exponential_nondecreasing
    (n0 : Nat) (params : GrowthParams) (t1 t2 : Nat)
    (h : t1 ≤ t2) :
    exponential_growth n0 params t1 ≤ exponential_growth n0 params t2 := by
  simp only [exponential_growth]
  apply Nat.max_le_max_left
  apply Nat.floor_le_floor
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Float.pow_le_pow_right (by norm_num)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Nat.cast_le.mpr h

/- =========================================================
   §5  継代操作（Passaging）
   ========================================================= -/

/-- 継代操作の結果 -/
inductive PassageResult : Type
  | Success : CellPopulation → PassageResult
  | TooFewCells   : PassageResult
  | TooManyPassages : PassageResult
  | LowViability  : PassageResult
  deriving Repr

/-- 継代実行: split_ratio 分の1に希釈して次世代へ -/
def passage
    (p : CellPopulation)
    (split_ratio : Nat)   -- 例: 4 なら 1:4 分割（新フラスコ1本分）
    (h_ratio : split_ratio > 0) :
    PassageResult :=
  if p.passage ≥ 30 then
    PassageResult.TooManyPassages
  else if p.viability < 0.85 then
    PassageResult.LowViability
  else if p.count < 1_000_000 then
    PassageResult.TooFewCells
  else
    PassageResult.Success
      { cell_type := p.cell_type
        passage   := p.passage + 1
        count     := p.count / split_ratio
        viability := 0.95   -- 継代直後のリセット近似
        state     := CellState.Viable }

/-- 継代成功なら passage 番号が増加する -/
theorem passage_increments
    (p : CellPopulation) (r : Nat) (hr : r > 0)
    (q : CellPopulation)
    (h : passage p r hr = PassageResult.Success q) :
    q.passage = p.passage + 1 := by
  simp only [passage] at h
  split_ifs at h with h1 h2 h3
  all_goals simp_all

/- =========================================================
   §6  培養プロトコル (A4: 手順の階層化)
   ========================================================= -/

/-- 単一培養ステップ -/
structure CultureStep where
  description  : String
  duration_h   : Nat
  action       : String    -- "seed" | "feed" | "passage" | "harvest"
  deriving Repr

/-- 培養プロトコル全体 -/
structure CultureProtocol where
  name         : String
  cell_type    : CellType
  seed_density : Nat        -- 播種密度（cells/cm²）
  steps        : List CultureStep
  condition    : CultureCondition
  deriving Repr

/-- 標準 HEK293 3-day 増殖プロトコル -/
def hek293_protocol : CultureProtocol :=
  { name         := "HEK293 Standard Expansion"
    cell_type    := CellType.HEK293
    seed_density := 30_000
    condition    := standard_condition
    steps        :=
      [ { description := "Flask seeding"
          duration_h  := 2
          action      := "seed" }
      , { description := "Day1 medium exchange"
          duration_h  := 24
          action      := "feed" }
      , { description := "Day2 growth check"
          duration_h  := 24
          action      := "feed" }
      , { description := "Day3 harvest / passage"
          duration_h  := 24
          action      := "passage" } ] }

/-- プロトコル妥当性 -/
def IsValidProtocol (proto : CultureProtocol) : Prop :=
  proto.steps ≠ [] ∧
  proto.seed_density > 0 ∧
  IsOptimalCondition proto.condition

instance (proto : CultureProtocol) : Decidable (IsValidProtocol proto) := by
  unfold IsValidProtocol; infer_instance

/- =========================================================
   §7  バッチシミュレーション
   ========================================================= -/

/-- シミュレーション設定 -/
structure SimConfig where
  initial_pop  : CellPopulation
  growth       : GrowthParams
  total_hours  : Nat
  passage_at_h : List Nat    -- 継代タイミング（時間）
  deriving Repr

/-- 時系列スナップショットの生成 -/
def simulate_timeseries
    (cfg : SimConfig) : List (Nat × Nat) :=
  -- (経過時間h, 細胞数) のリスト (6h間隔)
  (List.range (cfg.total_hours / 6 + 1)).map (fun i =>
    let t := i * 6
    let n := logistic_growth cfg.initial_pop.count cfg.growth t
    (t, n))

/-- 目標細胞数に達するまでの推定時間 -/
def time_to_target
    (n0 : Nat) (target : Nat) (params : GrowthParams) : Option Nat :=
  if target ≤ n0 then some 0
  else
    -- 二分探索的に 1h 刻みで探索（上限 720h = 30日）
    (List.range 720).find? (fun t =>
      logistic_growth n0 params t ≥ target)

/- =========================================================
   §8  品質基準（QC）
   ========================================================= -/

/-- QC チェック項目 -/
structure QCResult where
  viability_pass    : Bool   -- 生存率 ≥ 85%
  mycoplasma_free   : Bool   -- マイコプラズマ陰性
  sterility_pass    : Bool   -- 無菌試験合格
  passage_ok        : Bool   -- 継代数 ≤ 30
  deriving Repr

/-- QC 全合格 -/
def QCResult.all_pass (q : QCResult) : Bool :=
  q.viability_pass && q.mycoplasma_free &&
  q.sterility_pass && q.passage_ok

def IsQCPassed (q : QCResult) : Prop :=
  q.viability_pass = true ∧ q.mycoplasma_free = true ∧
  q.sterility_pass = true ∧ q.passage_ok = true

instance (q : QCResult) : Decidable (IsQCPassed q) := by
  unfold IsQCPassed; infer_instance

/-- 補題: all_pass と IsQCPassed は同値 -/
theorem qc_bool_prop_equiv (q : QCResult) :
    q.all_pass = true ↔ IsQCPassed q := by
  simp [QCResult.all_pass, IsQCPassed, Bool.and_eq_true]

/- =========================================================
   §9  定理まとめ
   ========================================================= -/

/-- ロジスティック増殖は上限を超えない -/
theorem logistic_bounded
    (n0 : Nat) (params : GrowthParams) (t : Nat) :
    logistic_growth n0 params t ≤ params.carrying_cap := by
  simp [logistic_growth, Nat.min_le_right]

/-- 初期細胞数ゼロなら指数増殖も常にゼロ -/
theorem zero_seed_stays_zero
    (params : GrowthParams) (t : Nat) :
    exponential_growth 0 params t = 0 := by
  simp [exponential_growth]

/-- 継代数が上限以上なら必ず TooManyPassages -/
theorem overpassed_fails
    (p : CellPopulation) (r : Nat) (hr : r > 0)
    (h : p.passage ≥ 30) :
    passage p r hr = PassageResult.TooManyPassages := by
  simp [passage, Nat.le_antisymm, h]
  omega

/- =========================================================
   §10  サンプル実行 (#eval)
   ========================================================= -/

def initial_hek293 : CellPopulation :=
  { cell_type  := CellType.HEK293
    passage    := 5
    count      := 2_000_000
    viability  := 0.95
    state      := CellState.Viable }

def sim_cfg : SimConfig :=
  { initial_pop  := initial_hek293
    growth       := hek293_growth
    total_hours  := 96
    passage_at_h := [72] }

-- 96時間シミュレーション結果（6h刻み）
#eval simulate_timeseries sim_cfg

-- 1億細胞に達するまでの推定時間
#eval time_to_target 2_000_000 100_000_000 hek293_growth

-- QCサンプル
def sample_qc : QCResult :=
  { viability_pass  := true
    mycoplasma_free := true
    sterility_pass  := true
    passage_ok      := true }

#eval sample_qc.all_pass          -- true
#eval (IsQCPassed sample_qc)      -- Decidable で検査
#eval (IsValidProtocol hek293_protocol)
#eval (IsPassageable initial_hek293)
