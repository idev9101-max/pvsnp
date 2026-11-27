import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_ww_in_p
import PvsNP.Units.m2_exp_down_closed
import PvsNP.Units.m2_exp_inter
import PvsNP.Units.m2_p_subset_exp

set_option autoImplicit false

namespace PvsNP.Units.tc_exp_double

open PvsNP.Units.fr_ladner.PEqualNP.Library
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

def firstHalf (x : List Bool) : List Bool :=
  (unpairB (half x ++ false :: x)).1

theorem firstHalf_eq (x : List Bool) : firstHalf x = x.take (x.length / 2) := by
  rw [firstHalf, half_eq]
  simp [unpairB, un]

theorem cpt_firstHalf :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString firstHalf := by
  have hCut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => half x ++ false :: x) :=
    cpt_app2 cpt_half (cpt_cons1 false cpt_id)
  have hlow : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => (unpairB (half x ++ false :: x)).1) :=
    cpt_comp (ea := fun x : List Bool => x) (eb := fun x : List Bool => x) (ec := fun x : List Bool => x)
      (f := fun x : List Bool => half x ++ false :: x)
      (g := fun s : List Bool => (unpairB s).1) hCut cpt_unpairB1
  exact hlow

theorem firstHalf_of_double (u : List Bool) : firstHalf (u ++ u) = u := by
  rw [firstHalf_eq]
  have hlen : (u ++ u).length / 2 = u.length := by
    rw [List.length_append]
    omega
  rw [hlen, List.take_left]

theorem double_eq_inter (L : Language Bool) :
    ({x : List Bool | ∃ u ∈ L, x = u ++ u} : Language Bool) =
      ({x : List Bool | ∃ u : List Bool, x = u ++ u} : Language Bool) ⊓
        ({x : List Bool | firstHalf x ∈ L} : Language Bool) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨u, hu, rfl⟩
    constructor
    · exact ⟨u, rfl⟩
    · change firstHalf (u ++ u) ∈ L
      rw [firstHalf_of_double]
      exact hu
  · intro hx
    rcases hx with ⟨hs, hl⟩
    rcases hs with ⟨u, hu⟩
    refine ⟨firstHalf x, hl, ?_⟩
    have huu : firstHalf x = u := by
      rw [hu, firstHalf_of_double]
    calc x = u ++ u := hu
    _ = firstHalf x ++ firstHalf x := by rw [← huu]

end PvsNP.Units.tc_exp_double

/-- EXP is closed under doubling: the image of `L` under `u ↦ u ++ u`. -/
theorem PvsNP.Units.tc_exp_double :
    ∀ L : Language Bool,
  (∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ L ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k) →
  ∃ k : ℕ, ∃ (f : List Bool → Bool) (M : Turing.TM2ComputableInTime PvsNP.encodeString PvsNP.encodeAnswer f),
      (∀ x : List Bool, x ∈ ({x : List Bool | ∃ u ∈ L, x = u ++ u} : Language Bool) ↔ f x = true) ∧ ∀ n : ℕ, M.time n ≤ 2 ^ (n ^ k) + k := by
  intro L hL
  let R : Language Bool := {x : List Bool | PvsNP.Units.tc_exp_double.firstHalf x ∈ L}
  have hred : PvsNP.KarpReducible R L :=
    ⟨PvsNP.Units.tc_exp_double.firstHalf,
      PvsNP.Units.tc_exp_double.cpt_firstHalf, fun _ => Iff.rfl⟩
  have hR := PvsNP.Units.m2_exp_down_closed R L hred hL
  have hSP : ({x : List Bool | ∃ u : List Bool, x = u ++ u} : Language Bool) ∈ PvsNP.P :=
    PvsNP.Units.m2_ww_in_p
  have hSexp := PvsNP.Units.m2_p_subset_exp
    ({x : List Bool | ∃ u : List Bool, x = u ++ u} : Language Bool) hSP
  have hI := PvsNP.Units.m2_exp_inter
    ({x : List Bool | ∃ u : List Bool, x = u ++ u} : Language Bool) R hSexp hR
  rw [PvsNP.Units.tc_exp_double.double_eq_inter L]
  exact hI
