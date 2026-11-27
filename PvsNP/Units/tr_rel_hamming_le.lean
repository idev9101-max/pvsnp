import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.m2_zip_bne_polytime
import PvsNP.Units.tf_fun_ones_unary
import PvsNP.Units.m2_tm_pair_fork_polytime
import PvsNP.Units.m2_pair_split_polytime
import PvsNP.Units.m2_const_polytime
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.m2_len_le_polytime
import PvsNP.Units.m2_tm_pair_swap_polytime
import PvsNP.Units.m2_tm_pair_bool_combine

namespace PvsNP.Units.tr_rel_hamming_le

theorem const_pair_string (u : List Bool) :
    PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString (fun _ : List Bool × List Bool => u) := by
  have hfst : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun p : List Bool × List Bool => p.1) := PvsNP.Units.m2_pair_split_polytime.1
  have hconst : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun _ : List Bool => u) := PvsNP.Units.m2_const_polytime u
  exact PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
    (fun p : List Bool × List Bool => p.1) (fun _ : List Bool => u) hfst hconst

theorem count_true_filter_length (l : List Bool) :
    l.count true = (l.filter (fun b => decide (b = true))).length := by
  rw [List.count_eq_length_filter]
  congr 1

end PvsNP.Units.tr_rel_hamming_le

/-- Hamming distance at most one is decidable in polynomial time. -/
theorem PvsNP.Units.tr_rel_hamming_le :
    ∃ f : List Bool × List Bool → Bool, PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeAnswer f ∧
      ∀ p : List Bool × List Bool,
        (p.1.length = p.2.length ∧
          ((List.zipWith (fun a b => a != b) p.1 p.2).filter (fun b => b = true)).length ≤ 1) ↔ f p = true := by
  let z : List Bool × List Bool → List Bool :=
    fun p => List.zipWith (fun a b : Bool => a != b) p.1 p.2
  let ones : List Bool × List Bool → List Bool :=
    fun p => List.replicate ((z p).count true) true
  have hz : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString z :=
    PvsNP.Units.m2_zip_bne_polytime
  have hones0 := PvsNP.Units.tf_fun_ones_unary
  have hones : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString ones :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodeString PvsNP.encodeString
      z (fun x : List Bool => List.replicate (x.count true) true) hz hones0
  have hone : PvsNP.PolyTimeComputable PvsNP.encodePair PvsNP.encodeString
      (fun _ : List Bool × List Bool => [true]) :=
    PvsNP.Units.tr_rel_hamming_le.const_pair_string [true]
  have hfork := PvsNP.Units.m2_tm_pair_fork_polytime ones (fun _ : List Bool × List Bool => [true]) hones hone
  have hcountle := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (ones p, [true]))
    (fun q : List Bool × List Bool => decide (q.1.length ≤ q.2.length)) hfork PvsNP.Units.m2_len_le_polytime
  have hlen21 := PvsNP.Units.m2_polytime_comp PvsNP.encodePair PvsNP.encodePair PvsNP.encodeAnswer
    (fun p : List Bool × List Bool => (p.2, p.1))
    (fun q : List Bool × List Bool => decide (q.1.length ≤ q.2.length))
    PvsNP.Units.m2_tm_pair_swap_polytime PvsNP.Units.m2_len_le_polytime
  have hleneq := PvsNP.Units.m2_tm_pair_bool_combine (fun a b : Bool => a && b)
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length))
    (fun p : List Bool × List Bool => decide (p.2.length ≤ p.1.length))
    PvsNP.Units.m2_len_le_polytime hlen21
  have hfinal := PvsNP.Units.m2_tm_pair_bool_combine (fun a b : Bool => a && b)
    (fun p : List Bool × List Bool => decide (p.1.length ≤ p.2.length) && decide (p.2.length ≤ p.1.length))
    (fun p : List Bool × List Bool => decide ((ones p).length ≤ [true].length))
    hleneq hcountle
  refine ⟨fun p : List Bool × List Bool =>
    (decide (p.1.length ≤ p.2.length) && decide (p.2.length ≤ p.1.length)) &&
      decide ((ones p).length ≤ [true].length), hfinal, ?_⟩
  intro p
  constructor
  · intro h
    have hle12 : p.1.length ≤ p.2.length := Nat.le_of_eq h.1
    have hle21 : p.2.length ≤ p.1.length := Nat.le_of_eq h.1.symm
    have hfilt : ((z p).filter (fun b => decide (b = true))).length ≤ 1 := h.2
    have hcount := PvsNP.Units.tr_rel_hamming_le.count_true_filter_length (z p)
    have hr : (ones p).length = (z p).count true := by simp [ones]
    have hle1 : (ones p).length ≤ [true].length := by
      rw [show [true].length = 1 from rfl]
      omega
    apply (Bool.and_eq_true_iff).2
    constructor
    · apply (Bool.and_eq_true_iff).2
      constructor
      · exact decide_eq_true hle12
      · exact decide_eq_true hle21
    · exact decide_eq_true hle1
  · intro h
    have habc := (Bool.and_eq_true_iff).1 h
    have hab := (Bool.and_eq_true_iff).1 habc.1
    have hle12 : p.1.length ≤ p.2.length := of_decide_eq_true hab.1
    have hle21 : p.2.length ≤ p.1.length := of_decide_eq_true hab.2
    have hle1 : (ones p).length ≤ [true].length := of_decide_eq_true habc.2
    constructor
    · exact Nat.le_antisymm hle12 hle21
    · change ((z p).filter (fun b => decide (b = true))).length ≤ 1
      have hcount := PvsNP.Units.tr_rel_hamming_le.count_true_filter_length (z p)
      have hr : (ones p).length = (z p).count true := by simp [ones]
      rw [show [true].length = 1 from rfl] at hle1
      omega
