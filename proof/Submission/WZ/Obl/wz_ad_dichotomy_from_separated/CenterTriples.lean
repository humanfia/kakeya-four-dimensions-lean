-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.CenterTriples.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.ModelReduction
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.ModelDensity

namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated

theorem tripleCenter_injective {S T : Finset Plane} :
    Function.Injective (@tripleCenter S T) := by
  intro i j hij
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hij))
    (Prod.ext (Subtype.ext (congrArg (fun p : Triple => p.2.1) hij))
      (Subtype.ext (congrArg (fun p : Triple => p.2.2) hij)))

noncomputable def centerFinset {S T : Finset Plane} (H : Finset (S × T × T)) :
    Finset Triple := H.image tripleCenter

theorem centerFinset_card {S T : Finset Plane} (H : Finset (S × T × T)) :
    (centerFinset H).card = H.card := Finset.card_image_of_injective _ tripleCenter_injective

theorem coe_centerFinset {S T : Finset Plane} (H : Finset (S × T × T)) :
    (↑(centerFinset H) : Set Triple) = CenterSet H := by
  simp only [centerFinset, Finset.coe_image, CenterSet]

theorem centerFinset_subset {S T : Finset Plane} (H : Finset (S × T × T)) :
    centerFinset H ⊆ S ×ˢ (T ×ˢ T) := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  exact Finset.mem_product.mpr ⟨i.1.property,
    Finset.mem_product.mpr ⟨i.2.1.property, i.2.2.property⟩⟩

theorem centerFinset_density {δ η : ℝ} (hδ : 0 < δ) (S T : Finset Plane)
    (H : Finset (S × T × T))
    (hS : (S.card : ℝ) ≤ 75 * δ ^ (-η) / δ)
    (hT : (T.card : ℝ) ≤ 75 * δ ^ (-η) / δ)
    (hH : δ ^ (η - 3) ≤ (H.card : ℝ)) :
    (δ ^ (4 * η) / (75 : ℝ) ^ 3) * (S.card : ℝ) * (T.card : ℝ) ^ 2 ≤
      ((centerFinset H).card : ℝ) := by
  rw [centerFinset_card]
  exact model_relative_density hδ S T H hS hT hH

end WangZahlLot.Obl.wz_ad_dichotomy_from_separated
