import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.m2_dfa_in_p
import PvsNP.Units.m2_polytime_comp
import PvsNP.Units.tf_fun_interleave

set_option autoImplicit false

namespace PvsNP.Units.tl_lang_mid_true_p

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines
open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner

private theorem headD_false_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => x.headD false) := by
  let δ : Option Bool → Bool → Option Bool :=
    fun q b => match q with | none => some b | some c => some c
  obtain ⟨c, hc, hdec⟩ := PvsNP.Units.m2_dfa_in_p (Option Bool) δ none (fun q => q == some true)
  have hfold_some : ∀ (a : Bool) (y : List Bool), y.foldl δ (some a) = some a := by
    intro a y; induction y with | nil => rfl | cons _ _ ih => exact ih
  have heq : c = fun x : List Bool => x.headD false := by
    funext x
    have hx := hdec x
    change ((x.foldl δ none == some true) = true) ↔ c x = true at hx
    cases x with
    | nil =>
      simp only [List.foldl_nil, List.headD_nil] at hx ⊢
      cases hcx : c [] <;> simp_all
    | cons b y =>
      simp only [List.foldl_cons, δ, hfold_some, List.headD_cons] at hx ⊢
      cases b with
      | false => cases hcx : c (false :: y) <;> simp_all
      | true => exact hx.1 (by decide)
  rwa [← heq]

def midBit (x : List Bool) : Bool :=
  ((unpairB (half x ++ false :: x)).2).headD false

theorem midBit_eq (x : List Bool) :
    midBit x = true ↔ x[x.length / 2]? = some true := by
  unfold midBit
  rw [PvsNP.Units.tf_fun_interleave.unpairB_half_cons]
  let n := x.length / 2
  cases h : x.drop n with
  | nil =>
    have hz : (x.drop n)[0]? = x[n + 0]? := List.getElem?_drop
    simp only [h, List.getElem?_nil, Nat.add_zero] at hz
    have hx : x[x.length / 2]? = none := by
      simpa [n] using hz.symm
    simp [hx]
  | cons b ys =>
    have hget : x[n]? = some b := by
      have hz : (x.drop n)[0]? = x[n + 0]? := List.getElem?_drop
      simp only [h, List.getElem?_cons_zero, Nat.add_zero] at hz
      simpa [n] using hz.symm
    simp [h, hget, n]

end PvsNP.Units.tl_lang_mid_true_p

/-- The strings whose middle bit is true are in P (TM2). -/
theorem PvsNP.Units.tl_lang_mid_true_p :
    ({x : List Bool | x[x.length / 2]? = some true} : Language Bool) ∈ PvsNP.P := by
  open PvsNP.Units.fr_ladner.PEqualNP.Library in
  open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal in
  open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines in
  open PvsNP.Units.fr_ladner.PEqualNP.Library.Ladner in
  have hCut : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => half x ++ false :: x) :=
    cpt_app2 cpt_half (cpt_cons1 false cpt_id)
  have hSecond : ComputableInPolyTime (fun x : List Bool => x) (fun x : List Bool => x)
      (fun x : List Bool => (unpairB (half x ++ false :: x)).2) :=
    cpt_comp (ea := fun x : List Bool => x) (eb := fun x : List Bool => x) (ec := fun x : List Bool => x)
      (f := fun x : List Bool => half x ++ false :: x)
      (g := fun s : List Bool => (unpairB s).2) hCut cpt_unpairB2
  have hBit : PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => ((unpairB (half x ++ false :: x)).2).headD false) :=
    PvsNP.Units.m2_polytime_comp PvsNP.encodeString PvsNP.encodeString PvsNP.encodeAnswer
      (fun x : List Bool => (unpairB (half x ++ false :: x)).2)
      (fun s : List Bool => s.headD false)
      hSecond PvsNP.Units.tl_lang_mid_true_p.headD_false_poly
  exact ⟨PvsNP.Units.tl_lang_mid_true_p.midBit, hBit,
    fun x => (PvsNP.Units.tl_lang_mid_true_p.midBit_eq x).symm⟩
