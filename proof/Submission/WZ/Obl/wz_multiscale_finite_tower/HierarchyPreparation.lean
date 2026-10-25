-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.HierarchyPreparation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.PreparedHierarchy
import Submission.WZ.Obl.wz_multiscale_finite_tower.DyadicMeshes

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya

lemma AlignedFamily.polynomial_card_bound {d θ L h : ℝ} {u : Space} {n : ℕ}
    {x v : Fin n → Space} {Y : Fin n → Set Space}
    (F : AlignedFamily d (d ^ θ) (d ^ (-θ)) L u h n x v Y)
    (hd : 0 < d) (hd1 : d ≤ 1) (hθ : θ ≤ 1) (hsmall : 56 * d ≤ 1) :
    (n : ℝ) ≤ d ^ (-4 : ℝ) := by
  have hs : 56 * d ^ (2 - θ) ≤ 1 := power_coefficient_bound hd hd1
    (by norm_num) le_rfl (by linarith : (1 : ℝ) ≤ 2 - θ) (by simpa using hsmall)
  have hh := (F.card_bound (Real.rpow_nonneg hd.le _)).trans (inverse_power_error_bound hd hs)
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hd)).mp
  convert hh using 1
  rw [← Real.rpow_two, ← Real.rpow_add hd]
  norm_num

/-- Uniform preparation of a hierarchy for the product argument. Constants depend
only on the number of levels and the requested error exponent. -/
theorem prepare_hierarchy_analysis (B : ℕ) {ε D : ℝ} (hε : 0 < ε) (hD : 0 < D) :
    ∃ η d₀ : ℝ, 0 < η ∧ 0 < d₀ ∧ d₀ ≤ D ∧ d₀ ≤ 1 / 100000 ∧
      ∀ d θ g gap : ℝ, ∀ J : ℕ, 0 < d → d ≤ d₀ → θ ≤ η → J ≤ B → d ^ gap ≤ 1 / 64 →
      ∀ C : HierarchyCertificate d θ g gap J,
      ∃ C' : HierarchyCertificate d ε g gap J,
        (∀ j, (C'.tree.layer j).radius = (C.tree.layer j).radius) ∧
        (C'.tree.layer J).card ≤ (C.tree.layer J).card ∧
        (⋃ i, C'.shading i) ⊆ (⋃ i, C.shading i) ∧
        ENNReal.ofReal (d ^ (ε / 4)) * (∑ i, volume (C.shading i)) ≤ ∑ i, volume (C'.shading i) ∧
        Nonempty (HierarchyAnalysis C'.tree (⋃ i, C.shading i) d ε (d ^ (ε / 8))) := by
  let τ := ε / 8
  have hτ : 0 < τ := by dsimp [τ]; positivity
  obtain ⟨q, hq'⟩ := exists_nat_gt (5 / τ)
  have hq : 0 < q := by
    have hp : (0 : ℝ) < q := (by positivity : (0 : ℝ) < 5 / τ).trans hq'
    exact_mod_cast hp
  have hqτ : 5 < τ * q := by
    have hh := (div_lt_iff₀ hτ).mp hq'
    nlinarith
  let C₀ : ℝ := max 8388608 (2 * (q : ℝ) ^ (B + 1))
  have hC₀ : 0 < C₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨d₁, hd₁, hd₁D, hcut⟩ := exists_scale_cutoff (1 / C₀) τ (min D (1 / 100000))
    (by positivity) hτ (lt_min hD (by norm_num))
  obtain ⟨d₀, hd₀, hd₀d₁, Hgrid⟩ := regularize_multiple_grids (B + 1) hτ hd₁
  refine ⟨min τ (1 / 2), d₀, lt_min hτ (by norm_num), hd₀,
    hd₀d₁.trans (hd₁D.trans (min_le_left _ _)),
    hd₀d₁.trans (hd₁D.trans (min_le_right _ _)), ?_⟩
  intro d θ g gap J hd hdd hθη hJB hgap C
  have hθτ : θ ≤ τ := hθη.trans (min_le_left _ _)
  have hθhalf : θ ≤ 1 / 2 := hθη.trans (min_le_right _ _)
  have hdsmall : d ≤ 1 / 100000 := hdd.trans (hd₀d₁.trans (hd₁D.trans (min_le_right _ _)))
  have hd1 : d < 1 := by linarith
  have hc : C₀ * d ^ τ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hcut d hd (hdd.trans hd₀d₁)) hC₀.le
    simpa only [one_div, mul_inv_cancel₀ hC₀.ne'] using hh
  have hsmallG : 8388608 * d ^ τ ≤ 1 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd.le _)).trans hc
  have hsmallq : 2 * (q : ℝ) ^ (J + 1) * d ^ τ ≤ 1 := by
    have hp : (q : ℝ) ^ (J + 1) ≤ q ^ (B + 1) :=
      pow_le_pow_right₀ (by exact_mod_cast hq) (by omega)
    have hqC : 2 * (q : ℝ) ^ (J + 1) ≤ C₀ :=
      (mul_le_mul_of_nonneg_left hp (by norm_num)).trans (le_max_right _ _)
    exact (mul_le_mul_of_nonneg_right hqC (Real.rpow_nonneg hd.le _)).trans hc
  have hcard : ((C.tree.layer J).card : ℝ) < (d ^ (-τ)) ^ q := by
    apply (C.family.polynomial_card_bound hd hd1.le (by linarith) (by linarith)).trans_lt
    rw [← Real.rpow_mul_natCast hd.le]
    exact Real.rpow_lt_rpow_of_exponent_gt hd hd1 (by nlinarith)
  obtain ⟨a, ha, hnest⟩ := dyadic_meshes (d := d / 64) (by positivity)
    (fun j : ℕ => (C.tree.layer (min j J)).radius / 64)
    (fun j => div_le_div_of_nonneg_right (C.control.radius_bounds (Nat.min_le_right j J)).1 (by norm_num))
  have haall (j : ℕ) : 0 < a j ∧ a j ≤ 1 := by
    have hh := ha j
    have hr := (C.control.radius_bounds (Nat.min_le_right j J)).2
    exact ⟨hh.1, by linarith [hh.2.2]⟩
  have haj (j : ℕ) (hj : j < J) : 0 < a j ∧ (C.tree.layer j).radius / 512 ≤ a j ∧
      a j ≤ (C.tree.layer j).radius / 256 := by
    have hh := ha j
    rw [Nat.min_eq_left hj.le] at hh
    exact ⟨hh.1, by linarith [hh.2.1], by linarith [hh.2.2]⟩
  have hanest (j : ℕ) (hj : j + 1 < J) : ∃ k : ℕ, 0 < k ∧ a j = (k : ℝ) * a (j + 1) := by
    apply hnest j (j + 1)
    rw [Nat.min_eq_left (by omega : j + 1 ≤ J), Nat.min_eq_left (by omega : j ≤ J)]
    exact div_le_div_of_nonneg_right (C.control.decreasing j (by omega)).le (by norm_num)
  obtain ⟨Z, G, t, hZ, hret, hclass⟩ := Hgrid d θ hd hdd hθhalf a (fun j _ => haall j)
    (C.tree.layer J).card C.shading C.family.measurable
    (fun i => (C.family.shading i).trans (C.family.ball i)) C.family.mass_lower
  have hh := prepare_hierarchy_from_classes C hd hd1 hτ hθτ hgap q hq hcard hsmallq hsmallG
    Z hZ hret a t G haj hanest (fun j hj => (hclass j (by omega)).2.1)
    (fun j hj => (hclass j (by omega)).1) (fun j hj => (hclass j (by omega)).2.2)
  have he8 : 8 * τ = ε := by dsimp [τ]; ring
  have he2 : 2 * τ = ε / 4 := by dsimp [τ]; ring
  rw [he8, he2] at hh
  exact hh

end WangZahlLot.Obl.wz_multiscale_finite_tower
