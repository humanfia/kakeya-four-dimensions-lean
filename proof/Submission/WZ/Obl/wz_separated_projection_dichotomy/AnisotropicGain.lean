-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_separated_projection_dichotomy.AnisotropicGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_separated_projection_dichotomy.AnisotropicStrips
import Submission.WZ.Obl.wz_separated_projection_dichotomy.RadialGain

namespace WangZahlLot.Obl.wz_separated_projection_dichotomy

open Set Metric
open scoped BigOperators

/-- The quantitative projection estimate in the second alignment step.
No coarsening is needed: indexed directions retain all original weights. -/
theorem anisotropic_radial_gain {δ w t h C d γ c : ℝ} {e b : Plane}
    (F G : Finset Plane) (T : G → Finset Plane)
    (hδ : 0 < δ) (hδw : δ ≤ w) (hh : 0 < h) (hh1 : h ≤ 1)
    (ht : 0 < t) (hth : t ≤ h) (hwt : w ≤ t / 2) (hwh : 2 * w / h ≤ 1)
    (hC : 1 ≤ C) (hd : 0 < d) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (he : ‖e‖ = 1)
    (hF : ClosedFiniteFrostman δ C F) (hG : ClosedFiniteFrostman δ C G)
    (hstrip : ∀ x ∈ G, |inner ℝ x (perp e) - c| ≤ w)
    (hpin : |inner ℝ b (perp e) - c| = t)
    (hsep : ∀ x ∈ G, 1 / 2 ≤ ‖b - x‖) (hfar : ∀ x ∈ G, ‖b - x‖ ≤ 8)
    (hT : ∀ x, T x ⊆ F) (hne : ∃ x, (T x).Nonempty)
    (hdensity : d * (G.card : ℝ) * (F.card : ℝ) ≤ ∑ x, ((T x).card : ℝ)) :
    ∃ x : G, ∀ (m : ℕ) (cc : Fin m → ℝ),
      Covers w ((fun a => inner ℝ a (b - x)) '' (↑(T x) : Set Plane)) cc →
        d ^ 2 ≤ (8 * (8192 * C * h / t) ^ 2 * energyConstant γ * (2 * w / h) ^ γ) * (m : ℝ) := by
  classical
  let φ := anisotropicMap e 1 h⁻¹
  let ψ := anisotropicMap e h⁻¹ 1
  let K := 8192 * C * h / t
  let ρ := 2 * w / h
  have hhinv : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr hh1
  have hφ : ∀ x y, dist x y ≤ dist (φ x) (φ y) := anisotropicMap_dist_lower he le_rfl hhinv
  have hψ : ∀ x y, dist x y ≤ dist (ψ x) (ψ y) := anisotropicMap_dist_lower he hhinv le_rfl
  have hψinj : Function.Injective ψ := anisotropicMap_injective he hhinv le_rfl
  have hw : 0 < w := hδ.trans_le hδw
  have hδρ : δ ≤ ρ := by
    dsimp [ρ]
    apply (le_div_iff₀ hh).mpr
    nlinarith [mul_le_mul_of_nonneg_left hh1 hδ.le]
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := hwh
  have h2CK : 2 * C ≤ K := by
    dsimp [K]
    apply (le_div_iff₀ ht).mpr
    have hCh := mul_le_mul_of_nonneg_left hth (zero_le_one.trans hC)
    nlinarith [mul_nonneg (zero_le_one.trans hC) ht.le]
  have hK : 1 ≤ K := (by linarith : 1 ≤ 2 * C).trans h2CK
  have hF' : ClosedFiniteFrostman ρ K (F.image ψ) :=
    ((hF.map_expanding hδ.le (zero_le_one.trans hC) ψ hψ).mono_scale hδρ).mono_constant hρ.le h2CK
  have hG' : IndexedFrostman δ (2 * C) (fun x : G => φ x) :=
    hG.indexed.map_expanding hδ.le (zero_le_one.trans hC) φ hφ
  have hnorm : ∀ x : G, 1 / 2 ≤ ‖φ b - φ x‖ ∧ ‖φ b - φ x‖ ≤ 16 := by
    intro x
    constructor
    · have h := hφ b x
      rw [dist_eq_norm, dist_eq_norm] at h
      exact (hsep x x.property).trans h
    · exact (anisotropic_difference_norm he hh hth
        ((hstrip x x.property).trans (by linarith)) hpin.le (hfar x x.property)).trans (by norm_num)
  have hneφ : ∀ x : G, φ b ≠ φ x := by
    intro x heq
    have hl := (hnorm x).1
    rw [heq, sub_self, norm_zero] at hl
    norm_num at hl
  have hdir0 := hG'.radial_of_strip hρ.le hδρ (by positivity : 0 ≤ 2 * C)
    ((perp_norm e).trans he) (by positivity : 0 < t / (2 * h))
    (show t / (2 * h) ≤ 16 by apply (div_le_iff₀ (by positivity)).mpr; linarith)
    (show w / h ≤ ρ by dsimp [ρ]; apply div_le_div_of_nonneg_right _ hh.le; linarith)
    hneφ (fun x => anisotropic_strip_bound he hh (hstrip x x.property))
    (fun x => anisotropic_strip_gap he hh hwt (hstrip x x.property) hpin.ge)
    (fun x => (hnorm x).2)
  have hdir : IndexedFrostman ρ K (fun x : G => radialDirection (φ b) (φ x)) := by
    convert hdir0 using 1 <;> dsimp [K] <;> field_simp <;> ring
  let T' (x : G) := (T x).image ψ
  have hT' : ∀ x, T' x ⊆ F.image ψ := fun x => Finset.image_subset_image (hT x)
  have hne' : ∃ x, (T' x).Nonempty := by
    obtain ⟨x, a, ha⟩ := hne
    exact ⟨x, ψ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  have hdensity' : d * (Fintype.card G : ℝ) * ((F.image ψ).card : ℝ) ≤
      ∑ x, ((T' x).card : ℝ) := by
    simpa only [T', Fintype.card_coe, Finset.card_image_of_injective _ hψinj] using hdensity
  obtain ⟨x, hx⟩ := indexed_kaufman_energy_gain T' hF' hdir hρ hρ1 hK hd
    (fun x => radialDirection_norm (hneφ x)) hγ hγ1 hT' hne' hdensity'
  refine ⟨x, ?_⟩
  intro m cc hcov
  have hscaled : Covers (w / h)
      ((fun a => inner ℝ a (φ b - φ x)) '' (↑(T' x) : Set Plane)) (fun i => cc i / h) := by
    rintro z ⟨a, ha, rfl⟩
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ⟨a₀, ha₀, rfl⟩)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    have hid : inner ℝ (ψ a₀) (φ b - φ x) = inner ℝ a₀ (b - x) / h := by
      apply (eq_div_iff hh.ne').mpr
      have hh' := anisotropicMap_dual_dot he hh a₀ b x
      dsimp [ψ, φ]
      nlinarith [hh']
    change dist (inner ℝ (ψ a₀) (φ b - φ x)) (cc i / h) ≤ w / h
    rw [hid, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hh]
    exact div_le_div_of_nonneg_right hi hh.le
  have hnormalized := hscaled.normalized_radial_dot (by positivity : 0 ≤ w / h) (hnorm x).1
  have hfinal := hx m _ (by simpa only [ρ, show 2 * (w / h) = 2 * w / h by ring] using hnormalized)
  exact hfinal

end WangZahlLot.Obl.wz_separated_projection_dichotomy
