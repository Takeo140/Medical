inductive Dna : Type := | mkDna : String → Dna

namespace Dna

def reverse_complement (s : String) : String :=
    s.toList.reverse.map (λ c => match c with
        | 'A' => 'T'
        | 'T' => 'A'
        | 'C' => 'G'
        | 'G' => 'C'
        | _ => c).asString

def is_valid_dna (s : String) : Bool :=
    s.toList.all (λ c => c ∈ ['A', 'T', 'C', 'G'])

def find_pattern (pattern : String) (dna : String) : List Nat :=
    let len := pattern.length
    dna.toList.enum.filter (λ ⟨i, _⟩ => dna.drop i |>.take len = pattern).map (λ ⟨i, _⟩ => i)

structure Treatment where
    description : String
    dosage : String
    scheduling : String

def verify_protocol (t : Treatment) : Bool :=
    t.dosage ≠ "" && t.scheduling ≠ ""

-- Example usage
-- let myDna : Dna := mkDna "ATCG"
-- let revComp := reverse_complement myDna
-- let patterns := find_pattern "AT" myDna
-- let treatment := Treatment.mk "Chemotherapy" "1 session/day" "Daily"
-- assert (verify_protocol treatment)

end Dna