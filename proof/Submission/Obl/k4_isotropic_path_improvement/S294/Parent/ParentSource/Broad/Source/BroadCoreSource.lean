-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.BroadCoreSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/BroadCoreSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/BroadCoreSource.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ValueCoreRetention
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.CoreRetentionNumerics
import Submission.Obl.k4_scalar_grid_cartesian_field.HeavyCells

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open scoped ENNReal BigOperators

noncomputable section

/-- The actual value and coherent core cuts retain fixed original mass. -/
theorem ValueBranchData.core_retained_mass
    {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Event} {mid : ℕ} {K : ℝ} {e R : ℕ}
    (V : ValueBranchData d k p H mid K 40 e R) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hK : 2304 ≤ K) (hκK : 3 * p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ (3 * R + 58))⁻¹)))
    (hmass : ENNReal.ofReal (p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w)) :
    ENNReal.ofReal (p.κ⁻¹ / 64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (V.coreRetained cores w) := by
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hlocal (w : Fin (d.W k)) :
      ((d.ν k w).prod volume) (H w) ≤
        ((d.ν k w).prod volume) (V.coreRetained cores w) +
          ((d.ν k w).prod volume) (H w \ V.residual w) +
          ((d.ν k w).prod volume) (V.residual w \ V.coreRetained cores w) := by
    have hcover : H w ⊆ (V.coreRetained cores w ∪ (H w \ V.residual w)) ∪
        (V.residual w \ V.coreRetained cores w) := by
      intro z hz
      by_cases hres : z ∈ V.residual w
      · by_cases hcore : z ∈ V.coreRetained cores w
        · exact Or.inl (Or.inl hcore)
        · exact Or.inr ⟨hres, hcore⟩
      · exact Or.inl (Or.inr ⟨hz, hres⟩)
    exact (measure_mono hcover).trans ((measure_union_le _ _).trans
      (add_le_add (measure_union_le _ _) le_rfl))
  have hbudget : (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w)) ≤
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (V.coreRetained cores w)) +
        ENNReal.ofReal ((K ^ 20)⁻¹) := by
    calc
      _ ≤ ∑ w, ENNReal.ofReal (d.ω k w) *
          (((d.ν k w).prod volume) (V.coreRetained cores w) +
            ((d.ν k w).prod volume) (H w \ V.residual w) +
            ((d.ν k w).prod volume) (V.residual w \ V.coreRetained cores w)) :=
        Finset.sum_le_sum (fun w _ => mul_le_mul' le_rfl (hlocal w))
      _ = (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (V.coreRetained cores w)) +
          (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w \ V.residual w)) +
          (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume)
            (V.residual w \ V.coreRetained cores w)) := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ ≤ (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (V.coreRetained cores w)) +
          ENNReal.ofReal (K ^ 10) * ENNReal.ofReal ((K ^ 40)⁻¹) +
          ENNReal.ofReal (K ^ 10) * ENNReal.ofReal (2 * K ^ (3 * R + 18)) *
            ENNReal.ofReal ((K ^ (3 * R + 58))⁻¹) :=
        add_le_add (add_le_add le_rfl V.loss) (V.core_retention_budget hd hp cores).2
      _ ≤ _ := by
        rw [add_assoc]
        exact add_le_add le_rfl (original_value_core_loss_bound (by linarith : 2 ≤ K) R)
  have hdouble : ENNReal.ofReal (p.κ⁻¹ / 64) + ENNReal.ofReal (p.κ⁻¹ / 64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (H w) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    convert hmass using 1
    congr 1
    ring
  have hcost : ENNReal.ofReal ((K ^ 20)⁻¹) ≤ ENNReal.ofReal (p.κ⁻¹ / 64) :=
    ENNReal.ofReal_le_ofReal ((original_core_loss_small hp.1 hK hκK).trans
      (by nlinarith [inv_nonneg.mpr hκ.le]))
  exact Submission.Obl.k4_scalar_grid_cartesian_field.pruning_mass_floor
    ENNReal.ofReal_ne_top hdouble hbudget hcost

/-- A broad source after actual original value and core/sign preparation.
Every raw core keeps its original full-reference floor and fixed branch. -/
structure BroadCoreSource (d : ProblemData) (k : ℕ) (p : PathData (d.W k))
    (original : Fin (d.W k) → Set Event) (mid : ℕ) (K : ℝ) (e R : ℕ) where
  source : Fin (d.W k) → Set Event
  measurable : ∀ w, MeasurableSet (source w)
  subset : ∀ w, source w ⊆ original w
  original_law : ∀ w, (((d.ν k w).prod volume).restrict (source w)) =
    (((d.ν k w).prod volume).restrict (original w))
  values : ValueBranchData d k p source mid K 40 e R
  cores : values.CoreFamilies (ENNReal.ofReal ((K ^ (3 * R + 58))⁻¹))
  retained_measurable : ∀ w, MeasurableSet (values.coreRetained cores w)
  retained_subset : ∀ w, values.coreRetained cores w ⊆ original w
  original_mass : ENNReal.ofReal (p.κ⁻¹ / 64) ≤
    ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (values.coreRetained cores w)

/-- The branch exponents are fixed before all original problem and source
data. Actual pure bands and the broad residual construct the entire core
source; no value bins, branches, entry floors, or retained mass are inputs. -/
theorem exists_broad_core_source :
    ∃ e rad : ℕ, 4 ≤ e ∧ 1 ≤ rad ∧
    ∀ {T : Type*} {d : ProblemData}, d.Valid →
    ∀ {k : ℕ} {p : PathData (d.W k)}
      {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ},
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ →
    ∀ {H : Fin (d.W k) → Set Event} {u : T → ℝ} {τ ε : ℝ},
    ∀ Q : PreparedAngularPath d k p m H u τ, Q.uniformPureBounds ε → 0 ≤ τ + ε →
      (∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b}) →
    ∀ {i stop : ℕ} {mesh envelope r fraction : ℝ} {θ : ENNReal}
      {F : PaletteFamily Q i stop mesh envelope θ},
      ∀ broad : BroadResidual F r fraction,
    ∀ mid : ℕ, mid < m → 0 ≤ p.r mid → p.r mid ≤ d.L →
      Nonempty (BroadCoreSource d k p broad.residual mid
        (nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + ε)) e rad) := by
  obtain ⟨e, rad, he, hrad, hfactory⟩ := exists_broad_value_branch_data 40 (by norm_num)
  refine ⟨e, rad, he, hrad, ?_⟩
  intro T d hd k p κ₁ m s δ₀ Mp Dp σ hp H u τ ε Q hpure htol hH
    i stop mesh envelope r fraction θ F broad mid hmid hr hrL
  obtain ⟨J, hJ, hsub, heq, ⟨V⟩⟩ := hfactory hd hp Q hpure htol hH broad mid hmid hr hrL
  let K := nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ + ε)
  have hN : 1 ≤ d.N k := (by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k)
  obtain ⟨hK, hκK, _, _⟩ := native_pre_geometry_envelope_bounds hp.1 hN htol
  obtain ⟨cores⟩ := V.exists_core_families hd hp (show 2 ≤ K by dsimp [K]; linarith) hκK
    (ENNReal.ofReal ((K ^ (3 * rad + 58))⁻¹))
  have hJmass : ENNReal.ofReal (p.κ⁻¹ / 32) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (J w) := by
    have hmassEq (w : Fin (d.W k)) := congrArg (fun μ : Measure Event => μ univ) (heq w)
    simp only [Measure.restrict_apply_univ] at hmassEq
    simpa only [hmassEq, show p.κ⁻¹ / 8 * ((1 : ℝ) / 2 / 2) = p.κ⁻¹ / 32 by ring] using broad.mass
  refine ⟨⟨J, hJ, hsub, heq, V, cores,
    fun w => ((V.core_retention_budget hd hp cores).1 w).1,
    fun w => ?_, V.core_retained_mass hd hp hK hκK cores hJmass⟩⟩
  exact (((V.core_retention_budget hd hp cores).1 w).2.trans (V.residual_subset w)).trans (hsub w)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
