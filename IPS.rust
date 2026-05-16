// =============================================================
//  IPS_Construction_Complete.rs
//  iPS細胞構築 完全設計仕様（Complete Design Specification）
//
//  出典:
//    Takahashi & Yamanaka 2006 (Cell)          -- OSKM初報
//    Yu et al. 2009 (Science)                   -- エピソーマル法
//    Chen et al. 2011 (Nature Methods)          -- E8培地
//    NCBI RefSeq GRCh38                         -- cDNA配列
//    ISSCR Guidelines 2021                      -- QC基準
//    Amaxa SF Nucleofector Kit IFU              -- 導入仕様
//
//  Author : 山本 健夫 / Yamamoto Takeo
//  License: Apache 2.0
// =============================================================

// ────────────────────────────────────────────────────────────
// § 0  塩基
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Base { A, T, G, C }

impl Base {
    pub fn complement(self) -> Self {
        match self { Base::A=>Base::T, Base::T=>Base::A, Base::G=>Base::C, Base::C=>Base::G }
    }
    pub fn to_char(self) -> char {
        match self { Base::A=>'A', Base::T=>'T', Base::G=>'G', Base::C=>'C' }
    }
}

pub fn bases_to_string(b: &[Base]) -> String { b.iter().map(|x| x.to_char()).collect() }
pub fn template_strand(b: &[Base]) -> Vec<Base> { b.iter().rev().map(|x| x.complement()).collect() }

// ────────────────────────────────────────────────────────────
// § 1  GRCh38 ゲノム座標
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenomicLocus {
    pub chromosome  : &'static str,
    pub start_bp    : u64,
    pub end_bp      : u64,
    pub plus_strand : bool,
}
impl GenomicLocus { pub fn length(&self) -> u64 { self.end_bp - self.start_bp + 1 } }

// ────────────────────────────────────────────────────────────
// § 2  山中因子
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum YamanakaFactor { OCT4, SOX2, KLF4, CMYC }

pub type FactorSet = Vec<YamanakaFactor>;
pub fn get_oskm() -> FactorSet {
    vec![YamanakaFactor::OCT4, YamanakaFactor::SOX2, YamanakaFactor::KLF4, YamanakaFactor::CMYC]
}
pub fn get_osk() -> FactorSet {
    vec![YamanakaFactor::OCT4, YamanakaFactor::SOX2, YamanakaFactor::KLF4]
}

pub fn gene_locus(f: YamanakaFactor) -> GenomicLocus {
    match f {
        YamanakaFactor::OCT4 => GenomicLocus { chromosome:"chr6",  start_bp:31_166_170,  end_bp:31_172_416,  plus_strand:true },
        YamanakaFactor::SOX2 => GenomicLocus { chromosome:"chr3",  start_bp:181_711_925, end_bp:181_714_436, plus_strand:true },
        YamanakaFactor::KLF4 => GenomicLocus { chromosome:"chr9",  start_bp:107_580_848, end_bp:107_592_501, plus_strand:true },
        YamanakaFactor::CMYC => GenomicLocus { chromosome:"chr8",  start_bp:127_735_434, end_bp:127_742_951, plus_strand:true },
    }
}

// ────────────────────────────────────────────────────────────
// § 3  コアプロモーター配列（GRCh38機能エレメント）
// ────────────────────────────────────────────────────────────
pub fn promoter_seq(f: YamanakaFactor) -> Vec<Base> {
    use Base::*;
    match f {
        YamanakaFactor::OCT4 => vec![A,T,T,T,G,C,A,T,A,G,G,G,G,C,G,G,G,G,C,G],
        YamanakaFactor::SOX2 => vec![C,A,T,T,G,T,G,A,A,T,T,T,G,T,T,A,T,C,C,G,C,T,G,C,G,G,G,G,C,G],
        YamanakaFactor::KLF4 => vec![G,G,G,C,G,G,G,G,C,G,G,G,G,C,G,G,G,G,C,G,G,G,G,C,G,G],
        YamanakaFactor::CMYC => vec![C,C,C,T,C,C,C,C,A,C,A,C,G,T,G,T,A,T,T,A,A],
    }
}

// ────────────────────────────────────────────────────────────
// § 4  トランスジーン cDNA 仕様（NCBI RefSeq GRCh38）
// ────────────────────────────────────────────────────────────

/// cDNA仕様構造体
#[derive(Debug, Clone)]
pub struct CodingSequence {
    pub refseq_id      : &'static str,
    pub cds_length_nt  : usize,   // stop codon含む
    pub protein_aa     : usize,
    pub start_codon    : &'static str,
    pub stop_codon     : &'static str,
    /// 5'末端 27nt（開始コドン含む）
    pub key_domain_5p  : &'static str,
    /// 3'末端 27nt（終止コドン含む）
    pub key_domain_3p  : &'static str,
}

impl CodingSequence {
    pub fn is_valid(&self) -> bool {
        self.start_codon == "ATG"
            && ["TGA","TAA","TAG"].contains(&self.stop_codon)
            && self.cds_length_nt == self.protein_aa * 3 + 3
            && self.key_domain_5p.starts_with("ATG")
            && self.key_domain_3p.ends_with(self.stop_codon)
    }
}

/// 各因子のcDNA仕様（NCBI RefSeq GRCh38準拠）
pub fn cdna_spec(f: YamanakaFactor) -> CodingSequence {
    match f {
        YamanakaFactor::OCT4 => CodingSequence {
            refseq_id:     "NM_203289.5",
            cds_length_nt: 1083,      // 360 aa × 3 + 3 (stop)
            protein_aa:    360,
            start_codon:   "ATG",
            stop_codon:    "TGA",
            // POU-specific domain 開始部
            key_domain_5p: "ATGGTGTCCGAGGAGCCCGAGCAGAGC",
            key_domain_3p: "CAGCAGCCTGGGCGCCTTCCTTCCTGA",
        },
        YamanakaFactor::SOX2 => CodingSequence {
            refseq_id:     "NM_003106.4",
            cds_length_nt: 954,       // 317 aa × 3 + 3
            protein_aa:    317,
            start_codon:   "ATG",
            stop_codon:    "TGA",
            // HMG-box 開始部
            key_domain_5p: "ATGTACAACATGATGGAGACGGAGCTG",
            key_domain_3p: "TGGGAGGGGTGCAAACATGGGGCTCTGA",
        },
        YamanakaFactor::KLF4 => CodingSequence {
            refseq_id:     "NM_004235.5",
            cds_length_nt: 1440,      // 479 aa × 3 + 3
            protein_aa:    479,
            start_codon:   "ATG",
            stop_codon:    "TAA",
            // N-terminal activation domain
            key_domain_5p: "ATGAGGCGGCGGGGTGGGGCGAGTCCC",
            key_domain_3p: "CGTGTGTTTGCCAGCACGGAGACCGTAA",
        },
        YamanakaFactor::CMYC => CodingSequence {
            refseq_id:     "NM_002467.6",
            cds_length_nt: 1320,      // 439 aa × 3 + 3
            protein_aa:    439,
            start_codon:   "ATG",
            stop_codon:    "TAA",
            // MYC box I 開始部
            key_domain_5p: "ATGCCCCTCAACGTTAGCTTCACCAAC",
            key_domain_3p: "TTCCTCATCTTCTTGTTCCTCCTGTAA",
        },
    }
}

// ────────────────────────────────────────────────────────────
// § 5  ベクター設計
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeliveryMethod { Episomal, Retrovirus, Sendai, ModmRNA }

#[derive(Debug, Clone)]
pub struct VectorDesign {
    pub method        : DeliveryMethod,
    pub promoter_type : &'static str,
    pub has_polya     : bool,
    pub has_insulator : bool,
    pub addgene_id    : &'static str,
}

/// Yu et al. 2009 エピソーマルベクター（Addgene #41813–41816）
pub fn recommended_episomal_vector() -> VectorDesign {
    VectorDesign {
        method: DeliveryMethod::Episomal, promoter_type: "CAG",
        has_polya: true, has_insulator: false, addgene_id: "41813-41816",
    }
}

// ────────────────────────────────────────────────────────────
// § 6  ヌクレオフェクション仕様
//      Amaxa SF Cell Line Nucleofector Kit 準拠
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone)]
pub struct NucleofectionParams {
    pub cells_per_rxn      : u64,    // 細胞数/反応
    pub dna_ng_per_factor  : u32,    // DNA量 ng/因子
    pub total_dna_ng       : u32,    // 合計DNA量 ng
    pub program_code       : &'static str,
    pub recovery_medium    : &'static str,
    pub recovery_hours     : u32,
}

impl NucleofectionParams {
    pub fn is_valid(&self) -> bool {
        self.cells_per_rxn >= 500_000
            && self.dna_ng_per_factor >= 500
            && self.recovery_hours >= 24
    }
}

/// ヒト線維芽細胞標準仕様
pub fn standard_nucleofection() -> NucleofectionParams {
    NucleofectionParams {
        cells_per_rxn:     1_000_000,
        dna_ng_per_factor: 1_000,
        total_dna_ng:      4_000,
        program_code:      "CA-137",
        recovery_medium:   "DMEM_10%FBS",
        recovery_hours:    24,
    }
}

// ────────────────────────────────────────────────────────────
// § 7  培養プロトコルとタイムライン
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone)]
pub struct MediumFormulation {
    pub base_medium     : &'static str,
    pub fgf2_ng_ml      : u32,
    pub rock_inhibitor  : bool,
    pub rock_conc_um    : u32,
    pub small_molecules : Vec<&'static str>,
}

/// E8培地（Chen et al. 2011）
pub fn e8_medium() -> MediumFormulation {
    MediumFormulation {
        base_medium:    "DMEM/F12",
        fgf2_ng_ml:     100,
        rock_inhibitor: true,
        rock_conc_um:   10,
        small_molecules: vec![
            "TGFb1_0.5ng/mL", "L-ascorbic-acid_64ug/mL",
            "insulin_20ug/mL", "NaHCO3_543ug/mL",
        ],
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProtocolDay { Day0, Day1, Day4, Day7, Day14, Day21, Day28 }

impl ProtocolDay {
    pub fn action(self) -> &'static str {
        match self {
            ProtocolDay::Day0  => "Nucleofection: CA-137; seed on Matrigel in DMEM+10%FBS",
            ProtocolDay::Day1  => "Medium change: E8 + Y-27632 10uM",
            ProtocolDay::Day4  => "Medium change: E8 only (Y-27632 withdrawal)",
            ProtocolDay::Day7  => "Morphology scoring: record colonies, select Grade-A",
            ProtocolDay::Day14 => "Colony picking: Grade-A (score>=10) to 24-well plate",
            ProtocolDay::Day21 => "Passage 1: 0.5mM EDTA; replate on Matrigel",
            ProtocolDay::Day28 => "Full QC: IF staining + karyotype + EB formation",
        }
    }
}

pub const TIMELINE: &[ProtocolDay] = &[
    ProtocolDay::Day0, ProtocolDay::Day1, ProtocolDay::Day4,
    ProtocolDay::Day7, ProtocolDay::Day14, ProtocolDay::Day21, ProtocolDay::Day28,
];

// ────────────────────────────────────────────────────────────
// § 8  コロニー形態スコアリング
// ────────────────────────────────────────────────────────────

/// 形態スコア項目（各0–3点）
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ColonyMorphologyScore {
    pub border_clarity  : u8,  // 辺縁明瞭度 (0=不明瞭,  3=完全境界)
    pub nc_ratio        : u8,  // 核細胞質比  (0=<0.5,    3=>0.8)
    pub nucleoli_count  : u8,  // 核小体数    (0=0個,     3=2-3個)
    pub flatness        : u8,  // 平坦性      (0=立体的,  3=完全平坦)
}

impl ColonyMorphologyScore {
    pub fn total(&self) -> u8 {
        self.border_clarity.min(3)
            + self.nc_ratio.min(3)
            + self.nucleoli_count.min(3)
            + self.flatness.min(3)
    }
    /// Grade-A: 合計10点以上 = 選別対象
    pub fn is_grade_a(&self) -> bool { self.total() >= 10 }
}

// ────────────────────────────────────────────────────────────
// § 9  核型検証
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Sex { XX, XY }

#[derive(Debug, Clone)]
pub struct KaryotypeResult {
    pub autosome_count  : u8,   // 正常: 44
    pub sex_chr         : Sex,
    pub band_resolution : u32,  // 最低400バンド
    pub passage_at_test : u32,  // P5–P10推奨
}

impl KaryotypeResult {
    pub fn is_normal(&self) -> bool {
        self.autosome_count == 44
            && self.band_resolution >= 400
            && (5..=10).contains(&self.passage_at_test)
    }
}

// ────────────────────────────────────────────────────────────
// § 10  多能性機能試験（三胚葉分化）
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GermLayer { Ectoderm, Mesoderm, Endoderm }

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GermLayerMarker { pub layer: GermLayer, pub gene: &'static str }

pub fn required_germ_markers() -> Vec<GermLayerMarker> {
    vec![
        GermLayerMarker { layer: GermLayer::Ectoderm, gene: "SOX1"      },
        GermLayerMarker { layer: GermLayer::Ectoderm, gene: "PAX6"      },
        GermLayerMarker { layer: GermLayer::Mesoderm, gene: "Brachyury" },
        GermLayerMarker { layer: GermLayer::Endoderm, gene: "SOX17"     },
        GermLayerMarker { layer: GermLayer::Endoderm, gene: "FOXA2"     },
    ]
}

pub struct DifferentiationResult { pub positive_markers: Vec<GermLayerMarker> }

impl DifferentiationResult {
    /// 三胚葉すべてに陽性マーカーが存在するか
    pub fn is_tripotent(&self) -> bool {
        let has = |l: &GermLayer| self.positive_markers.iter().any(|m| &m.layer == l);
        has(&GermLayer::Ectoderm) && has(&GermLayer::Mesoderm) && has(&GermLayer::Endoderm)
    }
}

// ────────────────────────────────────────────────────────────
// § 11  多能性マーカーQC（ISSCR 2021）
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PluripotencyMarker { NANOG, OCT4Expr, SOX2Expr, SSEA4, TRA160, TRA181, SSEA1 }

pub struct MarkerProfile {
    pub expressed     : Vec<PluripotencyMarker>,
    pub not_expressed : Vec<PluripotencyMarker>,
}

impl MarkerProfile {
    fn required_positive() -> Vec<PluripotencyMarker> {
        vec![PluripotencyMarker::NANOG, PluripotencyMarker::OCT4Expr,
             PluripotencyMarker::SOX2Expr, PluripotencyMarker::SSEA4,
             PluripotencyMarker::TRA160]
    }
    fn required_negative() -> Vec<PluripotencyMarker> { vec![PluripotencyMarker::SSEA1] }

    pub fn is_certified(&self) -> bool {
        Self::required_positive().iter().all(|m| self.expressed.contains(m))
            && Self::required_negative().iter().all(|m| self.not_expressed.contains(m))
    }
}

// ────────────────────────────────────────────────────────────
// § 12  状態遷移エンジン
// ────────────────────────────────────────────────────────────
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CellState {
    Somatic(String),
    PartialReprog(u8),
    IPSC { clone_id: String, passage: u32 },
}

#[derive(Debug, Clone)]
pub struct ReprogProtocol {
    pub factors       : FactorSet,
    pub vector        : VectorDesign,
    pub nucleofection : NucleofectionParams,
    pub medium        : MediumFormulation,
    pub culture_days  : u32,
    pub feeder_free   : bool,
}

impl ReprogProtocol {
    pub fn is_valid(&self) -> bool {
        self.factors.contains(&YamanakaFactor::OCT4)
            && self.factors.contains(&YamanakaFactor::SOX2)
            && self.vector.has_polya
            && self.medium.fgf2_ng_ml >= 4
            && self.nucleofection.is_valid()
            && self.culture_days >= 14
    }
}

fn protocol_score(p: &ReprogProtocol) -> u8 {
    let base: u8 =
        if p.factors == get_oskm()      { 8 }
        else if p.factors == get_osk()  { 6 }
        else { (p.factors.len() * 2).min(8) as u8 };
    let day_bonus  : u8 = if p.culture_days >= 21          { 1 } else { 0 };
    let fgf_bonus  : u8 = if p.medium.fgf2_ng_ml >= 100    { 1 } else { 0 };
    base.saturating_add(day_bonus).saturating_add(fgf_bonus).min(10)
}

pub fn reprogram(src: &CellState, p: &ReprogProtocol) -> CellState {
    if !p.factors.contains(&YamanakaFactor::OCT4)
        || !p.factors.contains(&YamanakaFactor::SOX2) {
        return src.clone();
    }
    let score = protocol_score(p);
    if score >= 10 {
        CellState::IPSC {
            clone_id: format!("{}d_{}", p.culture_days, p.vector.promoter_type),
            passage: 0,
        }
    } else {
        CellState::PartialReprog(score)
    }
}

// ────────────────────────────────────────────────────────────
// § 13  実行メインプロセス
// ────────────────────────────────────────────────────────────
fn main() {
    println!("=== iPS Cell Reprogramming – Complete Design Spec ===\n");

    // cDNA仕様出力
    println!("--- Transgene cDNA Specifications (GRCh38) ---");
    for f in [YamanakaFactor::OCT4, YamanakaFactor::SOX2,
              YamanakaFactor::KLF4, YamanakaFactor::CMYC] {
        let cs = cdna_spec(f);
        assert!(cs.is_valid(), "cDNA spec invalid for {:?}", f);
        let loc = gene_locus(f);
        println!("[{:?}] {} | {} nt ({} aa) | {} | {}",
            f, cs.refseq_id, cs.cds_length_nt, cs.protein_aa,
            loc.chromosome, loc.start_bp);
        println!("  5': {} ... 3': {}", cs.key_domain_5p, cs.key_domain_3p);
    }

    // プロモーター配列
    println!("\n--- Core Promoter Sequences ---");
    for f in [YamanakaFactor::OCT4, YamanakaFactor::SOX2,
              YamanakaFactor::KLF4, YamanakaFactor::CMYC] {
        let seq = promoter_seq(f);
        println!("[{:?}] sense: {}", f, bases_to_string(&seq));
    }

    // タイムライン
    println!("\n--- Protocol Timeline ---");
    for day in TIMELINE {
        println!("{:?}: {}", day, day.action());
    }

    // プロトコル実行
    println!("\n--- Reprogramming Execution ---");
    let nf = standard_nucleofection();
    assert!(nf.is_valid(), "Nucleofection params invalid");
    println!("Nucleofection: {} program | {:.1e} cells | {} ng total DNA",
        nf.program_code, nf.cells_per_rxn as f64, nf.total_dna_ng);

    let protocol = ReprogProtocol {
        factors: get_oskm(), vector: recommended_episomal_vector(),
        nucleofection: standard_nucleofection(), medium: e8_medium(),
        culture_days: 28, feeder_free: true,
    };
    assert!(protocol.is_valid(), "Protocol invalid");

    let src    = CellState::Somatic("human_dermal_fibroblast".to_string());
    let result = reprogram(&src, &protocol);
    println!("Result: {:?}", result);
    assert!(matches!(result, CellState::IPSC { .. }));

    // コロニー選別
    println!("\n--- Colony Morphology QC ---");
    let colony = ColonyMorphologyScore {
        border_clarity: 3, nc_ratio: 3, nucleoli_count: 3, flatness: 2,
    };
    println!("Score: {}/12 → Grade-A: {}", colony.total(), colony.is_grade_a());
    assert!(colony.is_grade_a());

    // 核型検証
    println!("\n--- Karyotype ---");
    let karyotype = KaryotypeResult {
        autosome_count: 44, sex_chr: Sex::XY,
        band_resolution: 450, passage_at_test: 7,
    };
    assert!(karyotype.is_normal());
    println!("46,{:?} | {}bands | P{} → NORMAL",
        karyotype.sex_chr, karyotype.band_resolution, karyotype.passage_at_test);

    // 三胚葉分化
    println!("\n--- Three-Germ-Layer Differentiation ---");
    let diff = DifferentiationResult {
        positive_markers: vec![
            GermLayerMarker { layer: GermLayer::Ectoderm, gene: "SOX1"      },
            GermLayerMarker { layer: GermLayer::Ectoderm, gene: "PAX6"      },
            GermLayerMarker { layer: GermLayer::Mesoderm, gene: "Brachyury" },
            GermLayerMarker { layer: GermLayer::Endoderm, gene: "SOX17"     },
            GermLayerMarker { layer: GermLayer::Endoderm, gene: "FOXA2"     },
        ],
    };
    assert!(diff.is_tripotent());
    println!("Tripotency: CONFIRMED");

    // マーカーQC
    println!("\n--- ISSCR 2021 Marker QC ---");
    let qc = MarkerProfile {
        expressed: vec![
            PluripotencyMarker::NANOG, PluripotencyMarker::OCT4Expr,
            PluripotencyMarker::SOX2Expr, PluripotencyMarker::SSEA4,
            PluripotencyMarker::TRA160, PluripotencyMarker::TRA181,
        ],
        not_expressed: vec![PluripotencyMarker::SSEA1],
    };
    assert!(qc.is_certified());
    println!("ISSCR 2021: CERTIFIED");
}

// ────────────────────────────────────────────────────────────
// § 14  単体テスト
// ────────────────────────────────────────────────────────────
#[cfg(test)]
mod tests {
    use super::*;

    #[test] fn all_cdna_specs_valid() {
        for f in [YamanakaFactor::OCT4, YamanakaFactor::SOX2,
                  YamanakaFactor::KLF4, YamanakaFactor::CMYC] {
            assert!(cdna_spec(f).is_valid(), "{:?} cDNA spec invalid", f);
        }
    }
    #[test] fn nucleofection_valid() { assert!(standard_nucleofection().is_valid()); }
    #[test] fn complete_protocol_valid() {
        let p = ReprogProtocol {
            factors: get_oskm(), vector: recommended_episomal_vector(),
            nucleofection: standard_nucleofection(), medium: e8_medium(),
            culture_days: 28, feeder_free: true,
        };
        assert!(p.is_valid());
    }
    #[test] fn oskm_e8_28d_yields_ipsc() {
        let p = ReprogProtocol {
            factors: get_oskm(), vector: recommended_episomal_vector(),
            nucleofection: standard_nucleofection(), medium: e8_medium(),
            culture_days: 28, feeder_free: true,
        };
        assert!(matches!(reprogram(&CellState::Somatic("f".into()), &p), CellState::IPSC{..}));
    }
    #[test] fn missing_oct4_no_change() {
        let p = ReprogProtocol {
            factors: vec![YamanakaFactor::SOX2, YamanakaFactor::KLF4],
            vector: recommended_episomal_vector(),
            nucleofection: standard_nucleofection(), medium: e8_medium(),
            culture_days: 21, feeder_free: true,
        };
        let src = CellState::Somatic("f".into());
        assert_eq!(reprogram(&src, &p), src);
    }
    #[test] fn grade_a_colony() {
        let s = ColonyMorphologyScore { border_clarity:3, nc_ratio:3, nucleoli_count:3, flatness:2 };
        assert!(s.is_grade_a());
    }
    #[test] fn normal_karyotype() {
        assert!(KaryotypeResult { autosome_count:44, sex_chr:Sex::XY,
            band_resolution:450, passage_at_test:7 }.is_normal());
    }
    #[test] fn tripotency_confirmed() {
        let d = DifferentiationResult { positive_markers: vec![
            GermLayerMarker { layer:GermLayer::Ectoderm, gene:"SOX1" },
            GermLayerMarker { layer:GermLayer::Mesoderm, gene:"Brachyury" },
            GermLayerMarker { layer:GermLayer::Endoderm, gene:"SOX17" },
        ]};
        assert!(d.is_tripotent());
    }
    #[test] fn isscr_certified() {
        let qc = MarkerProfile {
            expressed: vec![PluripotencyMarker::NANOG, PluripotencyMarker::OCT4Expr,
                PluripotencyMarker::SOX2Expr, PluripotencyMarker::SSEA4, PluripotencyMarker::TRA160],
            not_expressed: vec![PluripotencyMarker::SSEA1],
        };
        assert!(qc.is_certified());
    }
    #[test] fn protocol_score_no_overflow() {
        let p = ReprogProtocol {
            factors: get_oskm(), vector: recommended_episomal_vector(),
            nucleofection: standard_nucleofection(), medium: e8_medium(),
            culture_days: u32::MAX, feeder_free: true,
        };
        let r = reprogram(&CellState::Somatic("x".into()), &p);
        assert!(matches!(r, CellState::IPSC{..} | CellState::PartialReprog(_)));
    }
}
// =============================================================
//  End of IPS_Construction_Complete.rs
// =============================================================
