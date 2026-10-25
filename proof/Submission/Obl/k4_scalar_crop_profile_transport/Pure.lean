import Submission.Obl.k4_scalar_crop_profile_transport.Affine
import Submission.Obl.k4_scalar_crop_profile_transport.Geometry
import Submission.Obl.k4_crop_base_finite_tail.FiniteTail
import Submission.Obl.k4_crop_angular_finite_tail.Transfer
import Submission.Obl.k4_dyadic_crop_typicality.Assembly

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set Filter
open scoped ENNReal

local instance : SigmaFinite BaseRef := by unfold BaseRef; infer_instance
local instance : SigmaFinite JointRef := by unfold JointRef; infer_instance

lemma exists_crop_density (a p : ℝ) (ha : 0 < a) (hp : 0 < p) (z : Fin 2 → ℤ)
    (N r : ℝ) (μ₀ μ : Measure Inc) [IsFiniteMeasure μ₀]
    (hlift : ∀ Z, MeasurableSet Z → ENNReal.ofReal p * μ Z =
      μ₀ {b | b.1 ∈ Cell a z ∧ CropInc a z b ∈ Z})
    (H : Base → ENNReal) (hHlaw : μ₀.map (Obs N r) = BaseRef.withDensity H) :
    ∃ g : Base → ENNReal, Measurable g ∧ μ.map (Obs N r) = BaseRef.withDensity g := by
  obtain ⟨D, hD, hDlaw⟩ := k4_crop_angular_finite_tail.exists_density_of_le
    BaseRef (μ := μ₀) (μ' := μ₀.restrict (Cell a z ×ˢ univ))
    Measure.restrict_le_self (measurable_Obs N r) hHlaw
  let g : Base → ENNReal := fun b =>
    (ENNReal.ofReal a / ENNReal.ofReal p) * D ((obsEquiv a ha.ne' z).symm b)
  refine ⟨g, measurable_const.mul (hD.comp (obsEquiv a ha.ne' z).symm.measurable), ?_⟩
  rw [map_obs_lift a p ha.ne' hp z N r μ₀ μ hlift, hDlaw]
  rw [← Measure.map_smul _ (obsEquiv a ha.ne' z).measurable.aemeasurable]
  exact k4_dyadic_crop_affine_laws.Framework.normalized_density_transport
    (obsEquiv a ha.ne' z) BaseRef BaseRef (ENNReal.ofReal a) (ENNReal.ofReal p)
    (map_obs_reference a ha z) D hD

lemma raw_window_iff {a p : ℝ} (ha : 0 < a) (hp : 0 < p)
    (v : ENNReal) (lo upper δ : ℝ) :
    ((ENNReal.ofReal p / ENNReal.ofReal a) * v < ENNReal.ofReal (δ * lo) ∨
      ENNReal.ofReal upper < (ENNReal.ofReal p / ENNReal.ofReal a) * v) ↔
    (v < ENNReal.ofReal ((a / p) * δ * lo) ∨
      ENNReal.ofReal ((a / p) * upper) < v) := by
  have hc : 0 < a / p := div_pos ha hp
  have hraw : (ENNReal.ofReal (a / p))⁻¹ = ENNReal.ofReal p / ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_div_of_pos ha, ← ENNReal.ofReal_inv_of_pos hc]
    congr 1
    field_simp
  have hlo : ENNReal.ofReal (a / p) * ENNReal.ofReal (δ * lo) =
      ENNReal.ofReal ((a / p) * δ * lo) := by
    rw [← ENNReal.ofReal_mul hc.le, mul_assoc]
  have hhi : ENNReal.ofReal (a / p) * ENNReal.ofReal upper =
      ENNReal.ofReal ((a / p) * upper) := (ENNReal.ofReal_mul hc.le).symm
  simpa only [hraw, hlo, hhi] using k4_crop_base_finite_tail.BaseTransport.density_scale_window_iff
    (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top v
    (ENNReal.ofReal (δ * lo)) (ENNReal.ofReal upper)

/-- Scalar finite crop estimate before weighting by the retained mass. -/
theorem base_tail (N r u : ℝ) (hN : 0 < N)
    (ν₀ : Measure Line) (hprob : IsProbabilityMeasure ν₀) (E₀ : Set Inc)
    (hE₀ : MeasurableSet E₀) (htime : E₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (w : ℕ) (p : Fin w → ℝ) (z : Fin w → Fin 2 → ℤ)
    (μ : Fin w → Measure Inc) (g : Fin w → Base → ENNReal) (H : Joint → ENNReal)
    (hz : Function.Injective z) (hp : ∀ γ, 0 < p γ)
    (hlift : ∀ γ Z, MeasurableSet Z → ENNReal.ofReal (p γ) * μ γ Z =
      Selected ν₀ E₀ {b | b.1 ∈ Cell (N ^ (-u)) (z γ) ∧ CropInc (N ^ (-u)) (z γ) b ∈ Z})
    (hH : Measurable H) (hHlaw : (Selected ν₀ E₀).map (Aug N r u) = JointRef.withDensity H)
    (hg : ∀ γ, Measurable (g γ) ∧ (μ γ).map (Obs N r) = BaseRef.withDensity (g γ))
    (lo hi δ upper : ℝ) (hδ : 0 < δ) (hupper : hi ≤ upper) :
    (∑ γ, ENNReal.ofReal (p γ) * μ γ
      {b | g γ (Obs N r b) < ENNReal.ofReal ((N ^ (-u) / p γ) * δ * lo) ∨
        ENNReal.ofReal ((N ^ (-u) / p γ) * upper) < g γ (Obs N r b)}) ≤
      Selected ν₀ E₀ {b | H (Aug N r u b) < ENNReal.ofReal lo ∨
        ENNReal.ofReal hi < H (Aug N r u b)} + ENNReal.ofReal (2 * δ) := by
  classical
  let : IsProbabilityMeasure ν₀ := hprob
  let a := N ^ (-u)
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  let μ₀ := Selected ν₀ E₀
  let S : Fin w → Set Inc := fun γ => Cell a (z γ) ×ˢ univ
  let Q := Aug N r u
  let raw : Fin w → Base → ENNReal := fun γ b =>
    (ENNReal.ofReal (p γ) / ENNReal.ofReal a) * g γ (obsEquiv a ha.ne' (z γ) b)
  let D : Fin w → Joint → ENNReal := fun γ =>
    {b | b.2 = z γ 1}.indicator (fun b => raw γ b.1)
  let C : Fin w → Set Joint := fun γ => compatibleCrop a (z γ)
  have hS (γ : Fin w) : MeasurableSet (S γ) := (measurableSet_Cell _ _).prod MeasurableSet.univ
  have hQ : Measurable Q := measurable_Aug N r u
  have hraw (γ : Fin w) : Measurable (raw γ) :=
    measurable_const.mul ((hg γ).1.comp (obsEquiv a ha.ne' (z γ)).measurable)
  have hD (γ : Fin w) : Measurable (D γ) :=
    ((hraw γ).comp measurable_fst).indicator
      (measurableSet_eq_fun measurable_snd measurable_const)
  have hconst (γ : Fin w) : ∀ᵐ b ∂μ₀.restrict (S γ), (Q b).2 = z γ 1 := by
    filter_upwards [ae_restrict_mem (hS γ)] with b hb
    exact hb.1.2
  have hrawlaw (γ : Fin w) :
      (μ₀.restrict (S γ)).map (Obs N r) = BaseRef.withDensity (raw γ) :=
    raw_density_law a (p γ) ha (hp γ) (z γ) N r μ₀ (μ γ) (g γ) (hg γ).1 (hlift γ) (hg γ).2
  have hDlaw (γ : Fin w) : (μ₀.restrict (S γ)).map Q = JointRef.withDensity (D γ) :=
    k4_crop_base_finite_tail.map_pair_const_label BaseRef (measurable_Obs N r) (z γ 1)
      (hconst γ) (hraw γ) (hrawlaw γ)
  have hDeval (γ : Fin w) :
      ∀ᵐ b ∂μ₀.restrict (S γ), D γ (Q b) = raw γ (Obs N r b) := by
    filter_upwards [hconst γ] with b hb
    change ({b : Joint | b.2 = z γ 1}.indicator (fun b => raw γ b.1)) (Q b) = _
    exact Set.indicator_of_mem (s := {b : Joint | b.2 = z γ 1}) hb (fun b => raw γ b.1)
  have hsupp (γ : Fin w) : ∀ᵐ b ∂μ₀.restrict (S γ), Q b ∈ C γ := by
    have he : ∀ᵐ b ∂μ₀, b ∈ E₀ := ae_restrict_mem hE₀
    filter_upwards [ae_restrict_mem (hS γ), ae_restrict_of_ae he] with b hb hbe
    exact cell_Aug_compatible hN r hb.1 (htime hbe).2
  have hdisj : Pairwise fun γ γ' => Disjoint (S γ) (S γ') := by
    intro γ γ' hne
    rw [Set.disjoint_left]
    intro b hb hb'
    apply hz.ne hne
    ext j
    fin_cases j
    · exact hb.1.1.symm.trans hb'.1.1
    · exact hb.1.2.symm.trans hb'.1.2
  have hleft (γ : Fin w) :
      ENNReal.ofReal (p γ) * μ γ
        {b | g γ (Obs N r b) < ENNReal.ofReal ((a / p γ) * δ * lo) ∨
          ENNReal.ofReal ((a / p γ) * upper) < g γ (Obs N r b)} =
      μ₀ (S γ ∩ {b | D γ (Q b) < ENNReal.ofReal δ * ENNReal.ofReal lo ∨
        ENNReal.ofReal upper < D γ (Q b)}) := by
    have hbad : MeasurableSet {b | g γ (Obs N r b) < ENNReal.ofReal ((a / p γ) * δ * lo) ∨
        ENNReal.ofReal ((a / p γ) * upper) < g γ (Obs N r b)} :=
      (measurableSet_lt ((hg γ).1.comp (measurable_Obs N r)) measurable_const).union
        (measurableSet_lt measurable_const ((hg γ).1.comp (measurable_Obs N r)))
    rw [hlift γ _ hbad]
    have hset : MeasurableSet {b | D γ (Q b) < ENNReal.ofReal δ * ENNReal.ofReal lo ∨
        ENNReal.ofReal upper < D γ (Q b)} :=
      (measurableSet_lt ((hD γ).comp hQ) measurable_const).union
        (measurableSet_lt measurable_const ((hD γ).comp hQ))
    rw [inter_comm (S γ), ← Measure.restrict_apply hset]
    have hrset : MeasurableSet {b | g γ (Obs N r (CropInc a (z γ) b)) <
        ENNReal.ofReal ((a / p γ) * δ * lo) ∨ ENNReal.ofReal ((a / p γ) * upper) <
          g γ (Obs N r (CropInc a (z γ) b))} := hbad.preimage (measurable_CropInc a (z γ))
    have heq : {b | b.1 ∈ Cell a (z γ) ∧
        (g γ (Obs N r (CropInc a (z γ) b)) < ENNReal.ofReal ((a / p γ) * δ * lo) ∨
          ENNReal.ofReal ((a / p γ) * upper) < g γ (Obs N r (CropInc a (z γ) b)))} =
        {b | g γ (Obs N r (CropInc a (z γ) b)) < ENNReal.ofReal ((a / p γ) * δ * lo) ∨
          ENNReal.ofReal ((a / p γ) * upper) < g γ (Obs N r (CropInc a (z γ) b))} ∩ S γ := by
      ext b
      simp [S, and_comm]
    change μ₀ {b | b.1 ∈ Cell a (z γ) ∧
      (g γ (Obs N r (CropInc a (z γ) b)) < ENNReal.ofReal ((a / p γ) * δ * lo) ∨
        ENNReal.ofReal ((a / p γ) * upper) < g γ (Obs N r (CropInc a (z γ) b)))} = _
    rw [heq, ← Measure.restrict_apply hrset]
    apply measure_congr
    filter_upwards [hDeval γ] with b hb
    simp only [hb, raw, obs_crop a ha.ne', ← ENNReal.ofReal_mul hδ.le]
    exact propext (raw_window_iff ha (hp γ) _ lo upper δ).symm
  have htail := k4_crop_base_finite_tail.finite_density_tail JointRef μ₀ Q hQ H hH hHlaw
    S hS hdisj D hD hDlaw C (fun γ => measurableSet_compatibleCrop a (z γ)) hsupp
    2 (compatibleCrop_overlap z hz a) (ENNReal.ofReal lo) (ENNReal.ofReal hi)
    (ENNReal.ofReal upper) (ENNReal.ofReal δ) (ENNReal.ofReal_le_ofReal hupper)
  calc
    _ = ∑ γ, μ₀ (S γ ∩ {b | D γ (Q b) < ENNReal.ofReal δ * ENNReal.ofReal lo ∨
      ENNReal.ofReal upper < D γ (Q b)}) := Finset.sum_congr rfl fun γ _ => hleft γ
    _ ≤ μ₀ {b | H (Q b) < ENNReal.ofReal lo ∨ ENNReal.ofReal hi < H (Q b)} +
        2 * ENNReal.ofReal δ * μ₀ univ := htail
    _ ≤ μ₀ {b | H (Q b) < ENNReal.ofReal lo ∨ ENNReal.ofReal hi < H (Q b)} +
        ENNReal.ofReal (2 * δ) := by
      gcongr
      calc
        2 * ENNReal.ofReal δ * μ₀ univ ≤ 2 * ENNReal.ofReal δ * 1 :=
          mul_le_mul' le_rfl (selected_mass_le_one ν₀ E₀ htime)
        _ = ENNReal.ofReal (2 * δ) := by rw [mul_one, ENNReal.ofReal_mul (by norm_num)]; norm_num

/-- The existing weighted-tail theorem may use a dyadic proxy for the scalar Jacobian. -/
lemma scalar_scale_comparison (N : ℕ → ℝ) (k : ℕ) (hN : 0 < N k) (u : ℝ) :
    N k ^ (-u) ≤ k4_dyadic_crop_affine_laws.Scale N k (u / 2) ^ 2 ∧
      k4_dyadic_crop_affine_laws.Scale N k (u / 2) ^ 2 ≤ 4 * N k ^ (-u) := by
  have he : (N k ^ (-(u / 2))) ^ 2 = N k ^ (-u) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    congr 1
    ring
  constructor
  · rw [← he]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hN.le _)
      (k4_dyadic_crop_affine_laws.rpow_le_scale N k (u / 2) hN) 2
  · convert k4_dyadic_crop_affine_laws.scale_sq_le_four_rpow N k (u / 2) hN using 1
    congr 2
    ring

/-- Finite tails with a comparable Jacobian give the scalar normalization exponent. -/
theorem scalar_finite_tail (N : ℕ → ℝ) (k : ℕ) (r u : ℝ) (hN : 0 < N k)
    (ν₀ : Measure Line) (hprob : IsProbabilityMeasure ν₀) (E₀ : Set Inc)
    (hE₀ : MeasurableSet E₀) (htime : E₀ ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (w : ℕ) (p : Fin w → ℝ) (z : Fin w → Fin 2 → ℤ)
    (μ : Fin w → Measure Inc) (g : Fin w → Base → ENNReal) (H : Joint → ENNReal)
    (hz : Function.Injective z) (hp : ∀ γ, 0 < p γ)
    (hlift : ∀ γ Z, MeasurableSet Z → ENNReal.ofReal (p γ) * μ γ Z =
      Selected ν₀ E₀ {b | b.1 ∈ Cell (N k ^ (-u)) (z γ) ∧
        CropInc (N k ^ (-u)) (z γ) b ∈ Z})
    (hH : Measurable H)
    (hHlaw : (Selected ν₀ E₀).map (Aug (N k) r u) = JointRef.withDensity H)
    (hg : ∀ γ, Measurable (g γ) ∧ (μ γ).map (Obs (N k) r) = BaseRef.withDensity (g γ))
    (lo hi δ : ℝ) (hlo : 0 < lo) (hhi : 0 < hi) (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :
    (∑ γ, ENNReal.ofReal (p γ) * μ γ
      {b | g γ (Obs (N k) r b) < ENNReal.ofReal
          ((k4_dyadic_crop_affine_laws.Scale N k (u / 2) ^ 2 / p γ) * δ * lo) ∨
        ENNReal.ofReal ((k4_dyadic_crop_affine_laws.Scale N k (u / 2) ^ 2 / p γ) * hi / δ) <
          g γ (Obs (N k) r b)}) ≤
      Selected ν₀ E₀ {b | H (Aug (N k) r u b) < ENNReal.ofReal lo ∨
        ENNReal.ofReal hi < H (Aug (N k) r u b)} + ENNReal.ofReal (32 * δ) := by
  let a := N k ^ (-u)
  let b := k4_dyadic_crop_affine_laws.Scale N k (u / 2) ^ 2
  have ha : 0 < a := Real.rpow_pos_of_pos hN _
  obtain ⟨hab, hba⟩ := scalar_scale_comparison N k hN u
  have hratio₁ : 1 ≤ b / a := (le_div_iff₀ ha).mpr (by simpa [a, b] using hab)
  have hratio₄ : b / a ≤ 4 := (div_le_iff₀ ha).mpr (by simpa [a, b] using hba)
  have hratio : 0 < b / a := lt_of_lt_of_le zero_lt_one hratio₁
  have hu : hi ≤ (b / a) * hi / δ := by
    apply (le_div_iff₀ hδ).mpr
    calc
      hi * δ ≤ hi * 1 := mul_le_mul_of_nonneg_left hδ₁ hhi.le
      _ ≤ (b / a) * hi := by nlinarith
  have htail := base_tail (N k) r u hN ν₀ hprob E₀ hE₀ htime w p z μ g H hz hp
    hlift hH hHlaw hg lo hi ((b / a) * δ) ((b / a) * hi / δ) (mul_pos hratio hδ) hu
  have hl (γ : Fin w) : (a / p γ) * ((b / a) * δ) * lo = (b / p γ) * δ * lo := by
    field_simp
  have hh (γ : Fin w) : (a / p γ) * ((b / a) * hi / δ) = (b / p γ) * hi / δ := by
    field_simp
  change (∑ γ, ENNReal.ofReal (p γ) * μ γ
      {q | g γ (Obs (N k) r q) < ENNReal.ofReal ((b / p γ) * δ * lo) ∨
        ENNReal.ofReal ((b / p γ) * hi / δ) < g γ (Obs (N k) r q)}) ≤ _
  have heq : (∑ γ, ENNReal.ofReal (p γ) * μ γ
      {q | g γ (Obs (N k) r q) < ENNReal.ofReal ((b / p γ) * δ * lo) ∨
        ENNReal.ofReal ((b / p γ) * hi / δ) < g γ (Obs (N k) r q)}) =
      ∑ γ, ENNReal.ofReal (p γ) * μ γ
      {q | g γ (Obs (N k) r q) < ENNReal.ofReal ((a / p γ) * ((b / a) * δ) * lo) ∨
        ENNReal.ofReal ((a / p γ) * ((b / a) * hi / δ)) < g γ (Obs (N k) r q)} := by
    simp only [hl, hh]
  rw [heq]
  have herr : ENNReal.ofReal (2 * ((b / a) * δ)) ≤ ENNReal.ofReal (32 * δ) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  exact htail.trans (add_le_add le_rfl herr)

open k4_native_grid_profile_extension.Profiles in
/-- Weighted pure windows survive scalar conditional normalization. -/
theorem pure_typical (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hlim : Tendsto N atTop atTop)
    (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set Inc)
    (hsource : ∀ k, IsProbabilityMeasure (ν₀ k) ∧ MeasurableSet (E₀ k) ∧
      E₀ k ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (W : ℕ → ℕ) (ω p : (k : ℕ) → Fin (W k) → ℝ)
    (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ)
    (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc) (ρ : ℕ → ℝ) (u α r e : ℝ)
    (hz : ∀ k, Function.Injective (z k)) (hp : ∀ k γ, 0 < p k γ)
    (hlift : LiftFacts N u W ν₀ E₀ ν E p z)
    (hρ : ∀ k, 0 < ρ k) (hω : ∀ k γ, ω k γ = p k γ / ρ k)
    (hpclass : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ γ,
      N k ^ (-α - ε) ≤ p k γ ∧ p k γ ≤ N k ^ (-α + ε))
    (hρsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (ρ k)⁻¹ ≤ N k ^ ε)
    (H : ℕ → Joint → ENNReal)
    (hH : ∀ k, Measurable (H k) ∧ (Selected (ν₀ k) (E₀ k)).map (Aug (N k) r u) =
      JointRef.withDensity (H k))
    (htyp : HasTypicalDensity N (fun k => Selected (ν₀ k) (E₀ k))
      (fun k q => H k (Aug (N k) r u q)) e)
    (g : (k : ℕ) → Fin (W k) → Base → ENNReal)
    (hg : ∀ k γ, Measurable (g k γ) ∧
      (Selected (ν k γ) (E k γ)).map (Obs (N k) r) = BaseRef.withDensity (g k γ)) :
    ∀ τ : ℝ, 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
      (∑ γ, ENNReal.ofReal (ω k γ) * Selected (ν k γ) (E k γ)
        {q | g k γ (Obs (N k) r q) < ENNReal.ofReal (N k ^ (-(e + u - α) - τ)) ∨
          ENNReal.ofReal (N k ^ (-(e + u - α) + τ)) < g k γ (Obs (N k) r q)}) ≤
        ENNReal.ofReal (N k ^ (-c)) := by
  have hfinite (k : ℕ) (lo hi δ : ℝ) (hlo : 0 < lo) (hhi : 0 < hi)
      (hδ : 0 < δ) (hδ₁ : δ ≤ 1) :=
    scalar_finite_tail N k r u (by linarith [hN k]) (ν₀ k) (hsource k).1 (E₀ k)
      (hsource k).2.1 (hsource k).2.2 (W k) (p k) (z k)
      (fun γ => Selected (ν k γ) (E k γ)) (g k) (H k) (hz k) (hp k)
      (hlift.2.2.2.1 k) (hH k).1 (hH k).2 (hg k) lo hi δ hlo hhi hδ hδ₁
  simpa only [show 2 * (u / 2) = u by ring] using
    k4_dyadic_crop_typicality.typical_of_finite_tails N hN hlim W p ω ρ
      (fun k => Selected (ν₀ k) (E₀ k)) (fun k γ => Selected (ν k γ) (E k γ))
      (fun k q => H k (Aug (N k) r u q)) (fun k γ q => g k γ (Obs (N k) r q))
      (u / 2) α e hρ hω hpclass hρsub htyp hfinite

end Submission.Obl.k4_scalar_crop_profile_transport
