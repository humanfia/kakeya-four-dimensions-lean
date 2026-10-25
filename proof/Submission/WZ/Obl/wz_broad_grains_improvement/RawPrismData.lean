-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.RawPrismData.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/- Adapted from this workspace: o196/x0579, commit5ac3173, PrismData.lean (incidence fields only). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.Core
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.Witness
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.NormCovers

namespace WangZahlLot.Obl.wz_broad_grains_improvement

open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (G)

/-- The geometric and incidence information shared by all stages, without the
auxiliary cover witnesses. -/
structure RawPrismData (ω ζ δ h ρ c : ℝ) (n : ℕ)
    (x v : Fin n → V) (Y : Fin n → Set V) where
  a : ℝ
  L : ℕ
  z : Fin L → V
  e : Fin L → V ≃ₗᵢ[ℝ] V
  W : Fin n → Fin L → Set V
  shape : δ ≤ a ∧ a ≤ ρ * c ∧ ρ * c ≤ c ∧ c ≤ 1
  pieces : ∀ i j, M (W i j) ∧ W i j ⊆ Y i ∩ P a (ρ * c) c (z j) (e j) ∧
    ∀ j', j ≠ j' → Disjoint (W i j) (W i j')
  mass : O (δ ^ h) * ∑ i, μ (Y i) ≤ ∑ i, ∑ j, μ (W i j)
  dense : ∀ j, O (δ ^ h) * μ (P a (ρ * c) c (z j) (e j)) ≤ μ (⋃ i, W i j)
  crossing : ∀ i j, (W i j).Nonempty →
    (∀ p ∈ T δ (x i) (v i) ∩ frontier (P a (ρ * c) c (z j) (e j)),
      |ι (e j (p - z j)) 2| = c / 2) ∧
    ∀ t ∈ ({-c / 2, c / 2} : Set ℝ),
      ∃ p ∈ T δ (x i) (v i) ∩ P a (ρ * c) c (z j) (e j),
        ι (e j (p - z j)) 2 = t
  broad : ∀ j (p u : V) (r : ℝ), ‖u‖ = 1 → δ ≤ r → r ≤ ρ →
    q n {i | p ∈ W i j ∧ min ‖v i - u‖ ‖v i + u‖ ≤ r} ≤
      δ ^ (-h) * (r / ρ) ^ (ω * ζ / 100) * q n {i | p ∈ W i j}

/-- Forget the auxiliary coarse cover without changing any prism label or
incidence piece. -/
def raw_prism_of_valid {ω ζ δ h ρ c : ℝ} {n o : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V}
    (D : WangZahlLot.Obl.wz_move_two_capped_prism_overlap.PrismData n)
    (H : D.Valid ω ζ δ h ρ c x v Y o) : RawPrismData ω ζ δ h ρ c n x v Y where
  a := D.a
  L := D.L
  z := D.z
  e := D.e
  W := D.W
  shape := ⟨H.1, H.2.1, H.2.2.1, H.2.2.2.1⟩
  pieces := H.2.2.2.2.1
  mass := H.2.2.2.2.2.1
  dense := H.2.2.2.2.2.2.1
  crossing := fun i j hij => (H.2.2.2.2.2.2.2.1 i j hij).2
  broad := H.2.2.2.2.2.2.2.2.1

/-- Every stage has the same underlying prism and incidence data. -/
theorem raw_prism_data {ω ζ δ h ρ c : ℝ} {n o : ℕ}
    {x v : Fin n → V} {Y : Fin n → Set V} (hG : G ω ζ δ h ρ c n x v Y o) :
    Nonempty (RawPrismData ω ζ δ h ρ c n x v Y) := by
  obtain ⟨a, s, L, N, z, e, W, y, w, γ, hda, hab, hbc, hc,
    hW, hmass, hdense, hcross, hbroad, _⟩ := hG
  exact ⟨⟨a, L, z, e, W, ⟨hda, hab, hbc, hc⟩, hW, hmass, hdense,
    fun i j h => (hcross i j h).2, hbroad⟩⟩

end WangZahlLot.Obl.wz_broad_grains_improvement
