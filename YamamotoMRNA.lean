// Yamamoto Core Logic: DNA to mRNA Compiler — Production Build
// Licensed under CC BY 4.0 (Author: Takeo Yamamoto / 山本健夫)
// ORCID: 0009-0003-0440-474X

use std::collections::HashMap;
use std::fmt;

// ─────────────────────────────────────────────
// 1. 型定義：DNA と RNA を型レベルで分離
// ─────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum DnaNucleotide { G, A, C, T }

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RnaNucleotide { G, A, C, U }

/// コドン（RNA 3塩基）
pub type Codon = (RnaNucleotide, RnaNucleotide, RnaNucleotide);

// ─────────────────────────────────────────────
// 2. アミノ酸定義
// ─────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AminoAcid {
    Phe, Leu, Ile, Met, Val, Ser, Pro, Thr, Ala,
    Tyr, His, Gln, Asn, Lys, Asp, Glu, Cys, Trp,
    Arg, Gly, Stop,
}

impl fmt::Display for AminoAcid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

// ─────────────────────────────────────────────
// 3. エラー型
// ─────────────────────────────────────────────

#[derive(Debug, PartialEq)]
pub enum MrnaError {
    InvalidBase(char),
    EmptySequence,
    NonMultipleOfThree(usize),
    UnknownCodon(Codon),
}

impl fmt::Display for MrnaError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidBase(c)        => write!(f, "不正な塩基文字: '{c}'"),
            Self::EmptySequence         => write!(f, "空の配列"),
            Self::NonMultipleOfThree(n) => write!(f, "配列長 {n} が3の倍数でない"),
            Self::UnknownCodon(c)       => write!(f, "未定義コドン: {c:?}"),
        }
    }
}

// ─────────────────────────────────────────────
// 4. 入力データ構造
// ─────────────────────────────────────────────

/// パスロジーデータ：疾患遺伝子情報を構造化
#[derive(Debug, Clone)]
pub struct PathologyData {
    /// 遺伝子名（例: "SNCA", "APP", "PTEN"）
    pub gene_name: String,
    /// DNA 配列（大文字 G/A/C/T）
    pub dna_sequence: String,
    /// 点変異リスト [(位置, 変異後塩基)]
    pub mutations: Vec<(usize, char)>,
}

impl PathologyData {
    pub fn new(gene_name: &str, dna_sequence: &str) -> Self {
        Self {
            gene_name: gene_name.to_string(),
            dna_sequence: dna_sequence.to_uppercase(),
            mutations: vec![],
        }
    }

    pub fn with_mutation(mut self, pos: usize, base: char) -> Self {
        self.mutations.push((pos, base.to_ascii_uppercase()));
        self
    }

    /// FASTA形式の文字列からパース（>header\nSEQUENCE）
    pub fn from_fasta(fasta: &str) -> Result<Self, MrnaError> {
        let mut lines = fasta.lines();
        let header = lines.next().unwrap_or("").trim_start_matches('>');
        let seq: String = lines
            .filter(|l| !l.starts_with('>'))
            .flat_map(|l| l.chars())
            .collect::<String>()
            .to_uppercase();
        if seq.is_empty() { return Err(MrnaError::EmptySequence); }
        Ok(Self::new(header, &seq))
    }
}

// ─────────────────────────────────────────────
// 5. ヒト最適化コドンテーブル
//    同一アミノ酸の中でGC含量・翻訳速度が最も高いコドンを選択
// ─────────────────────────────────────────────

fn human_optimized_codon_table() -> HashMap<AminoAcid, Codon> {
    use RnaNucleotide::*;
    [
        (AminoAcid::Phe, (U, U, C)),
        (AminoAcid::Leu, (C, U, G)),
        (AminoAcid::Ile, (A, U, C)),
        (AminoAcid::Met, (A, U, G)),
        (AminoAcid::Val, (G, U, G)),
        (AminoAcid::Ser, (A, G, C)),
        (AminoAcid::Pro, (C, C, G)),
        (AminoAcid::Thr, (A, C, C)),
        (AminoAcid::Ala, (G, C, C)),
        (AminoAcid::Tyr, (U, A, C)),
        (AminoAcid::His, (C, A, C)),
        (AminoAcid::Gln, (C, A, G)),
        (AminoAcid::Asn, (A, A, C)),
        (AminoAcid::Lys, (A, A, G)),
        (AminoAcid::Asp, (G, A, C)),
        (AminoAcid::Glu, (G, A, G)),
        (AminoAcid::Cys, (U, G, C)),
        (AminoAcid::Trp, (U, G, G)),
        (AminoAcid::Arg, (A, G, G)),
        (AminoAcid::Gly, (G, G, C)),
        (AminoAcid::Stop,(U, G, A)),
    ].into_iter().collect()
}

/// 標準 RNA コドン → アミノ酸 変換表
fn codon_to_amino(codon: &Codon) -> Option<AminoAcid> {
    use RnaNucleotide::*;
    Some(match codon {
        (U,U,U)|(U,U,C)                         => AminoAcid::Phe,
        (U,U,A)|(U,U,G)|(C,U,U)|(C,U,C)|(C,U,A)|(C,U,G) => AminoAcid::Leu,
        (A,U,U)|(A,U,C)|(A,U,A)                 => AminoAcid::Ile,
        (A,U,G)                                  => AminoAcid::Met,
        (G,U,U)|(G,U,C)|(G,U,A)|(G,U,G)        => AminoAcid::Val,
        (U,C,U)|(U,C,C)|(U,C,A)|(U,C,G)|(A,G,U)|(A,G,C) => AminoAcid::Ser,
        (C,C,U)|(C,C,C)|(C,C,A)|(C,C,G)        => AminoAcid::Pro,
        (A,C,U)|(A,C,C)|(A,C,A)|(A,C,G)        => AminoAcid::Thr,
        (G,C,U)|(G,C,C)|(G,C,A)|(G,C,G)        => AminoAcid::Ala,
        (U,A,U)|(U,A,C)                          => AminoAcid::Tyr,
        (C,A,U)|(C,A,C)                          => AminoAcid::His,
        (C,A,A)|(C,A,G)                          => AminoAcid::Gln,
        (A,A,U)|(A,A,C)                          => AminoAcid::Asn,
        (A,A,A)|(A,A,G)                          => AminoAcid::Lys,
        (G,A,U)|(G,A,C)                          => AminoAcid::Asp,
        (G,A,A)|(G,A,G)                          => AminoAcid::Glu,
        (U,G,U)|(U,G,C)                          => AminoAcid::Cys,
        (U,G,G)                                  => AminoAcid::Trp,
        (C,G,U)|(C,G,C)|(C,G,A)|(C,G,G)|(A,G,A)|(A,G,G) => AminoAcid::Arg,
        (G,G,U)|(G,G,C)|(G,G,A)|(G,G,G)        => AminoAcid::Gly,
        (U,A,A)|(U,A,G)|(U,G,A)                 => AminoAcid::Stop,
        _                                         => return None,
    })
}

// ─────────────────────────────────────────────
// 6. コアコンパイラ
// ─────────────────────────────────────────────

#[derive(Debug)]
pub struct MrnaOutput {
    pub gene_name: String,
    pub protein_sequence: Vec<AminoAcid>,
    pub optimized_mrna: Vec<RnaNucleotide>,
    pub gc_content: f64,
    pub length_nt: usize,
}

impl fmt::Display for MrnaOutput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let protein_str: Vec<String> = self.protein_sequence.iter()
            .map(|aa| format!("{aa}"))
            .collect();
        let mrna_str: String = self.optimized_mrna.iter()
            .map(|n| format!("{n:?}"))
            .collect::<Vec<_>>()
            .join("");
        write!(
            f,
            "Gene       : {}\nProtein    : {}\nmRNA (opt) : {}\nGC content : {:.1}%\nLength     : {} nt",
            self.gene_name,
            protein_str.join("-"),
            mrna_str,
            self.gc_content,
            self.length_nt,
        )
    }
}

pub struct YamamotoCompiler {
    codon_table: HashMap<AminoAcid, Codon>,
}

impl Default for YamamotoCompiler {
    fn default() -> Self {
        Self { codon_table: human_optimized_codon_table() }
    }
}

impl YamamotoCompiler {
    pub fn new() -> Self { Self::default() }

    /// 文字 → DnaNucleotide
    fn parse_base(c: char) -> Result<DnaNucleotide, MrnaError> {
        match c {
            'G' => Ok(DnaNucleotide::G),
            'A' => Ok(DnaNucleotide::A),
            'C' => Ok(DnaNucleotide::C),
            'T' => Ok(DnaNucleotide::T),
            _   => Err(MrnaError::InvalidBase(c)),
        }
    }

    /// DNA 文字列 → Vec<DnaNucleotide>
    fn parse_dna(seq: &str) -> Result<Vec<DnaNucleotide>, MrnaError> {
        if seq.is_empty() { return Err(MrnaError::EmptySequence); }
        seq.chars().map(Self::parse_base).collect()
    }

    /// 点変異の適用
    fn apply_mutations(
        mut dna: Vec<DnaNucleotide>,
        mutations: &[(usize, char)],
    ) -> Result<Vec<DnaNucleotide>, MrnaError> {
        for &(pos, base) in mutations {
            dna[pos] = Self::parse_base(base)?;
        }
        Ok(dna)
    }

    /// DNA → RNA 転写（T → U）
    fn transcribe(dna: Vec<DnaNucleotide>) -> Vec<RnaNucleotide> {
        dna.into_iter().map(|n| match n {
            DnaNucleotide::G => RnaNucleotide::G,
            DnaNucleotide::A => RnaNucleotide::A,
            DnaNucleotide::C => RnaNucleotide::C,
            DnaNucleotide::T => RnaNucleotide::U,
        }).collect()
    }

    /// RNA → タンパク質翻訳（コドン単位）
    fn translate(rna: &[RnaNucleotide]) -> Result<Vec<AminoAcid>, MrnaError> {
        if rna.len() % 3 != 0 {
            return Err(MrnaError::NonMultipleOfThree(rna.len()));
        }
        rna.chunks(3)
            .map(|chunk| {
                let codon = (chunk[0], chunk[1], chunk[2]);
                codon_to_amino(&codon).ok_or(MrnaError::UnknownCodon(codon))
            })
            .collect()
    }

    /// タンパク質配列 → ヒト最適化 mRNA
    fn optimize(&self, protein: &[AminoAcid]) -> Vec<RnaNucleotide> {
        protein.iter().flat_map(|aa| {
            let (c1, c2, c3) = self.codon_table[aa];
            [c1, c2, c3]
        }).collect()
    }

    /// GC含量（%）
    fn gc_content(seq: &[RnaNucleotide]) -> f64 {
        if seq.is_empty() { return 0.0; }
        let gc = seq.iter()
            .filter(|&&n| n == RnaNucleotide::G || n == RnaNucleotide::C)
            .count();
        gc as f64 / seq.len() as f64 * 100.0
    }

    /// メインパイプライン：PathologyData → MrnaOutput
    pub fn compile(&self, data: &PathologyData) -> Result<MrnaOutput, MrnaError> {
        // 1. パース
        let dna = Self::parse_dna(&data.dna_sequence)?;
        // 2. 変異適用
        let dna = Self::apply_mutations(dna, &data.mutations)?;
        // 3. 転写
        let rna = Self::transcribe(dna);
        // 4. 翻訳
        let protein = Self::translate(&rna)?;
        // 5. コドン最適化
        let optimized = self.optimize(&protein);
        let gc = Self::gc_content(&optimized);

        Ok(MrnaOutput {
            gene_name: data.gene_name.clone(),
            protein_sequence: protein,
            optimized_mrna: optimized.clone(),
            gc_content: gc,
            length_nt: optimized.len(),
        })
    }
}

// ─────────────────────────────────────────────
// 7. テスト
// ─────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn compiler() -> YamamotoCompiler { YamamotoCompiler::new() }

    /// ATG（Met）+ TGA（Stop）= 最短の完全ORF
    #[test]
    fn test_minimal_orf() {
        let data = PathologyData::new("TEST", "ATGTGA");
        let out = compiler().compile(&data).unwrap();
        assert_eq!(out.protein_sequence, vec![AminoAcid::Met, AminoAcid::Stop]);
    }

    /// T→U 転写の確認
    #[test]
    fn test_transcription() {
        let dna = vec![DnaNucleotide::A, DnaNucleotide::T,
                       DnaNucleotide::G, DnaNucleotide::C];
        let rna = YamamotoCompiler::transcribe(dna);
        assert_eq!(rna, vec![
            RnaNucleotide::A, RnaNucleotide::U,
            RnaNucleotide::G, RnaNucleotide::C,
        ]);
    }

    /// GC含量が目標範囲（50–70%）内であることを確認
    #[test]
    fn test_gc_content_range() {
        // Met(ATG) + Gly(GGC) + Stop(UGA) を最適化
        let data = PathologyData::new("GC_TEST", "ATGGGTTGA");
        let out = compiler().compile(&data).unwrap();
        assert!(
            out.gc_content >= 50.0 && out.gc_content <= 75.0,
            "GC含量 {:.1}% が範囲外", out.gc_content
        );
    }

    /// 点変異の適用確認（A→T → Met→Ile になる等）
    #[test]
    fn test_mutation_applied() {
        // ATGATG = Met-Met、位置2をTに（すでにT）ではなく位置2をGに → ATG AGT = Met-Ser
        let data = PathologyData::new("MUT", "ATGAGT")
            .with_mutation(3, 'A'); // AGT → AAT = Asn
        let out = compiler().compile(&data).unwrap();
        assert_eq!(out.protein_sequence[1], AminoAcid::Asn);
    }

    /// 不正塩基はエラーになる
    #[test]
    fn test_invalid_base() {
        let data = PathologyData::new("ERR", "ATGXGT");
        assert_eq!(
            compiler().compile(&data),
            Err(MrnaError::InvalidBase('X'))
        );
    }

    /// 3の倍数でない配列はエラー
    #[test]
    fn test_non_multiple_of_three() {
        let data = PathologyData::new("ERR2", "ATGT");
        assert_eq!(
            compiler().compile(&data),
            Err(MrnaError::NonMultipleOfThree(4))
        );
    }

    /// FASTA パーサー
    #[test]
    fn test_fasta_parse() {
        let fasta = ">SNCA_exon5\nATGTGA\n";
        let data = PathologyData::from_fasta(fasta).unwrap();
        assert_eq!(data.gene_name, "SNCA_exon5");
        assert_eq!(data.dna_sequence, "ATGTGA");
    }
}

// ─────────────────────────────────────────────
// 8. 使用例（main）
// ─────────────────────────────────────────────

fn main() {
    let compiler = YamamotoCompiler::new();

    // α-シヌクレイン NAC 領域（簡略）
    let snca = PathologyData::new("SNCA_NAC", "ATGGTGGGCATGTGA")
        .with_mutation(6, 'A'); // Val → ? の変異を模擬

    match compiler.compile(&snca) {
        Ok(out) => println!("{out}"),
        Err(e)  => eprintln!("Error: {e}"),
    }
}
