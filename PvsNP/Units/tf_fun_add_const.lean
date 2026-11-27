import Mathlib
import PvsNP.Defs
import CookLevin
import PvsNP.Units.fr_ladner
import PvsNP.Units.tf_fun_pair_add
import PvsNP.Units.m2_polytime_comp

namespace PvsNP.Units.tf_fun_add_const

open PvsNP.Units.fr_ladner.PEqualNP.Library.Universal
open PvsNP.Units.fr_ladner.PEqualNP.Library.Machines

def five : List Bool := [true, false, true]

theorem pair_with_five_poly :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodePair
      (fun x : List Bool => (x, five)) :=
  cpt_pair cpt_id (cpt_const five)

end PvsNP.Units.tf_fun_add_const

/-- Adding the fixed natural number 5 to a binary-encoded natural number is polynomial-time:
pair the input with the constant bit representation of 5 and use binary addition. -/
theorem PvsNP.Units.tf_fun_add_const :
    PvsNP.PolyTimeComputable PvsNP.encodeString PvsNP.encodeString
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 5)) := by
  have hcomp := PvsNP.Units.fr_ladner.PEqualNP.Library.Machines.cpt_comp
    PvsNP.Units.tf_fun_add_const.pair_with_five_poly PvsNP.Units.tf_fun_pair_add
  have heq : (fun a : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ)
        ((a, PvsNP.Units.tf_fun_add_const.five).1.map Bool.toNat) +
        Nat.ofDigits (2 : ℕ) ((a, PvsNP.Units.tf_fun_add_const.five).2.map Bool.toNat))) =
      (fun x : List Bool => Nat.bits (Nat.ofDigits (2 : ℕ) (x.map Bool.toNat) + 5)) := by
    funext x
    simp [PvsNP.Units.tf_fun_add_const.five, Nat.ofDigits, Bool.toNat]
  rw [← heq]
  exact hcomp
