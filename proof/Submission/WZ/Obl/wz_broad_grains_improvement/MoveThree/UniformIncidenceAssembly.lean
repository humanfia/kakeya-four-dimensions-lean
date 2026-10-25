-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.UniformIncidenceAssembly.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/UniformIncidenceAssembly.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from this workspace's o169/x0641, WangZahlLot/Obl/wz_move_three_wide_grains_core/UniformIncidenceAssembly.lean
   (7d05c80, sessions x0450/x0641/x0670). Namespace and grain-witness interface adjusted. -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.OccupiedRows
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.PhysicalBroadnessBudget

set_option autoImplicit false
noncomputable section
namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
open Set MeasureTheory
open WangZahlLot.Obl.wz_measurable_angular_selection (pd)
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis)
open WangZahlLot.Obl.wz_move_two_dense_broad_prisms (Crosses)

/-- The finite-width selection and incidence assembly have one uniform
cutoff. A strict error margin absorbs all fixed mass, density, and angular
constants, while retaining the original long length. -/
theorem uniform_incidence_prisms_of_occupied_rows
    {ω ζ h₀ h' r dens B C₀ K D : ℝ}
    (hβ : 0 ≤ ω * ζ / 100) (hB : 0 ≤ B) (hC₀ : 0 ≤ C₀) (hK : 0 ≤ K)
    (hD : 0 < D) (hr : 0 ≤ r) (hmassgap : h₀ + r < h') (hdengap : dens < h') :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ 1 ∧
    ∀ {κ : Type} [Fintype κ] {δ h ρ ρ₀ a c b g m : ℝ} {n N L : ℕ}
      {x v : Fin n → V} {Y Z : Fin n → Set V} {S : Finset (Fin n)}
      {y w : Fin N → V} {f : Fin n → Fin N}
      {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V}
      {Hs : Fin L → Set V} {γ : Fin L → Fin N}
      (W : κ → Fin L → Set V) (z' : κ → V) (e' : κ → V ≃ₗᵢ[ℝ] V)
      (aRow bRow : κ → ℝ) (ν : κ → Fin L → V) (R : κ → V ≃ₗᵢ[ℝ] V) (θ : κ → ℝ),
    0 < δ → δ ≤ d₀ → 0 ≤ h → h ≤ h₀ → δ ≤ ρ → 0 ≤ m →
    (∀ i, ‖v i‖ = 1) → (∀ i, T δ (x i) (v i) ⊆ I) →
    C δ h n x v Y S Z ρ N y w f True →
    Broad ω ζ δ h ρ n N v S Z f →
    GrainWitnesses δ h n x v S Z ρ N y w f a c b g L z e Hs γ m →
    (∀ k, (⋃ j, W k j).Nonempty → δ ≤ aRow k ∧ aRow k ≤ bRow k ∧ bRow k ≤ c) →
    (∀ k, (⋃ j, W k j).Nonempty → ρ₀ * c ≤ bRow k) →
    (∀ k j, MeasurableSet (W k j)) → (∀ k j, W k j ⊆ Hs j) →
    (∀ j, Pairwise fun k k' => Disjoint (W k j) (W k' j)) →
    (∀ k j, W k j ⊆ P (aRow k) (bRow k) c (z' k) (e' k)) →
    O (δ ^ r / D) * ∑ j, μ (Hs j) ≤ ∑ k, ∑ j, μ (W k j) →
    0 < ∑ k, ∑ j, μ (W k j) →
    (∀ k, (⋃ j, W k j).Nonempty →
      O (δ ^ dens) * μ (P (aRow k) (bRow k) c (z' k) (e' k)) ≤ μ (⋃ j, W k j)) →
    (∀ i ∈ S, ∀ k j, f i = γ j → (Z i ∩ W k j).Nonempty →
      Crosses δ (aRow k) (bRow k) c (x i) (v i) (z' k) (e' k)) →
    (∀ k, (⋃ j, W k j).Nonempty → 0 < θ k) →
    (∀ k j, (W k j).Nonempty → pd (ν k j) (R k (boxAxis (e j) 2)) ≤ C₀ * ρ) →
    (∀ k p u rad, ‖u‖ = 1 → 2 * ρ ≤ rad →
      q L {j | p ∈ W k j ∧ pd (ν k j) u ≤ rad} ≤
        B * (rad / θ k) ^ (ω * ζ / 100) * q L {j | p ∈ W k j}) →
    (∀ k, (⋃ j, W k j).Nonempty → 2 * bRow k ≤ K * c * θ k) →
    ∃ ρ', ρ₀ ≤ ρ' ∧
      WangZahlLot.Obl.wz_move_two_dense_broad_prisms.G ω ζ δ h' ρ' c n x v Y 0 := by
  let s := (h' - h₀ - r) / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hgap : h₀ + r + s < h' := by dsimp [s]; linarith
  obtain ⟨dClass, hdClass, hclass⟩ := prism_width_class_budget hs
  obtain ⟨dMass, hdMass, _, hmass⟩ :=
    const_absorption (C := 2 * D) (by positivity) hgap
  obtain ⟨dDen, hdDen, _, hdensity⟩ :=
    const_absorption (C := 4) (by norm_num) hdengap
  obtain ⟨dBroad, hdBroad, hdBroad1, hbroad⟩ :=
    physical_packet_broadness_budget hβ hB hC₀ hK (by linarith : h₀ < h')
  refine ⟨min dClass (min dMass (min dDen dBroad)),
    lt_min hdClass (lt_min hdMass (lt_min hdDen hdBroad)),
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans hdBroad1)), ?_⟩
  intro κ _ δ h ρ ρ₀ a c b g m n N L x v Y Z S y w f z e Hs γ
    W z' e' aRow bRow ν R θ hδ hδ0 hh hh₀ hδρ hm hv hTI hC hbr hHB
    hdim hgrow hWm hWH hWdisj hWU hretain hpos hdense hcross hθ hclose haxis hratio
  have hδClass := hδ0.trans (min_le_left _ _)
  have hδMass := (hδ0.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδDen := ((hδ0.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδBroad := ((hδ0.trans (min_le_right _ _)).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hδ1 : δ ≤ 1 := hδBroad.trans hdBroad1
  have hc : 0 < c := hδ.trans_le ((hHB.1.trans hHB.2.1).trans hHB.2.2.1)
  have hmassBudget : δ ^ h' ≤ (δ ^ r / D * δ ^ s / 2) * δ ^ h := by
    have H := (hmass δ hδ hδMass).trans
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith : h + r + s ≤ h₀ + r + s))
    have he : (δ ^ r / D * δ ^ s / 2) * δ ^ h = δ ^ (h + r + s) / (2 * D) := by
      rw [Real.rpow_add hδ, Real.rpow_add hδ]
      ring
    rw [he, le_div_iff₀ (by positivity)]
    nlinarith [H]
  apply variable_incidence_prisms_of_occupied_rows W z' e' aRow bRow ν R θ
    hδ hδ1 hh hδρ hβ hB hm hC₀ (by positivity : 0 ≤ δ ^ r / D) hv hTI hC hbr hHB
    hdim hgrow hWm hWH hWdisj hWU hretain hpos (hclass δ hδ hδ1 hδClass)
    hmassBudget hdense (hdensity δ hδ hδDen) hcross hθ hclose haxis
  intro k hk
  have hbk : 0 ≤ bRow k := (hδ.le.trans (hdim k hk).1).trans (hdim k hk).2.1
  have hrange : 2 * bRow k / c ≤ K * θ k := by
    rw [div_le_iff₀ hc]
    nlinarith only [hratio k hk]
  simpa only [div_div] using hbroad δ h (θ k) (2 * bRow k / c)
    hδ hδBroad hh₀ (hθ k hk) (by positivity) hrange

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
