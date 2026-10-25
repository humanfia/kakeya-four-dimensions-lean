import Submission.Obl.k4_affine_skew_row_fit.Monotonicity
import Submission.Obl.k4_affine_skew_row_fit.EdgeRecovery
import Submission.Obl.k4_affine_skew_row_fit.Numerics

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Submission.Obl.k4_affine_skew_row_fit

/-- Apply the measure recovery to a retained subgraph of one represented direction. -/
theorem row_fit_from_witness {α : Type} [MeasurableSpace α]
    {ν : Measure α} [IsProbabilityMeasure ν] {μ : Measure (α × ℝ)}
    {z T : α × ℝ → Fin 2 → ℝ} {h E K S : ℝ}
    (w : RowGraphWitness ν μ z T h E K S)
    (hK : 1 ≤ K) (hh : 0 < h) (hE : 0 < E) (hEone : E ≤ 1)
    (hztime : ∀ p, z p 0 = p.2)
    {i : Fin w.planar.size} (G : Finset Edge) (hG : G ⊆ w.planar.graph i)
    (hcard : 1 / (K * h ^ 2) ≤ (G.card : ℝ))
    {ℓ₀ c₁ c₂ : ℝ} (hℓ : |ℓ₀| ≤ K)
    (hstrips : ∀ e ∈ G,
      |e.1.2 - ℓ₀ * e.1.1 - c₁| + |e.2.2 - ℓ₀ * e.2.1 - c₂| ≤ K * h) :
    ∃ B : Fin 2 → ℝ, ∃ ℓ : ℝ,
      |B 0| + |B 1| + |ℓ| ≤ 23328 * K ^ 12 ∧
      ENNReal.ofReal (1 / (3 * K ^ 2)) ≤ μ {p |
        |T p 0 - B 0 + ℓ * z p 1| ≤ 81 * K ^ 6 * E ∧
        |T p 1 - B 1 - ℓ * z p 0| ≤ 81 * K ^ 6 * E} := by
  exact row_from_retained_edges ν μ hK hh hE hEone w.domination z T hztime G w.witness
    (fun e _ => w.measurable_witness e)
    (fun e _ f _ hef => w.disjoint_witness hef)
    hcard (fun e he => w.witness_mass i e (hG he))
    (fun e he => w.witness_bounds i e (hG he))
    w.velocity_bound₁ w.velocity_bound₂ w.velocity_separation hℓ
    (fun e he => w.witness_projections i e (hG he)) hstrips

/-- The analytic inputs imply the complete fixed-tolerance row-fit assertion. -/
theorem uniform_row_fit_of_graphs (hgraph : GraphReduction) (hrigid : PlanarRigidity) :
    UniformRowFit := by
  intro S a ε hS ha hε
  obtain ⟨δ, hδ, hδε, Nrec, hNrec, hrec⟩ := exists_recovery_budget hε
  let t : ℝ := δ / (4 * a)
  have ht : 0 < t := by dsimp [t]; positivity
  have hS' : 0 < S / 4 := by positivity
  obtain ⟨ηcore, hηcore, h₀, hh₀, hcore⟩ := hrigid (S / 4) hS' t ht
  let θ : ℝ := min ηcore t
  have hθ : 0 < θ := lt_min hηcore ht
  obtain ⟨η, hη, Ng, hNg, hg⟩ := hgraph S a θ hS ha hθ
  have hmesh : ∀ᶠ N : ℝ in atTop, N ^ (-a) < h₀ :=
    (tendsto_rpow_neg_atTop ha).eventually (eventually_lt_nhds hh₀)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hmesh
  refine ⟨η, hη, max Ng (max Nrec M), hNg.trans (le_max_left _ _), ?_⟩
  intro N hN α inst d
  have : IsProbabilityMeasure d.prior := d.prior_probability
  have hNg' : Ng ≤ N := (le_max_left _ _).trans hN
  have hNrec' : Nrec ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hMN : M ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNtwo : 2 ≤ N := hNrec.trans hNrec'
  have hNpos : 0 < N := by linarith
  have hNone : 1 ≤ N := by linarith
  let h : ℝ := N ^ (-a)
  have hh : 0 < h := Real.rpow_pos_of_pos hNpos _
  have hhsmall : h < h₀ := hM N hMN
  let K₀ : ℝ := h ^ (-θ)
  let K : ℝ := N ^ δ
  have hK₀ : 0 < K₀ := Real.rpow_pos_of_pos hh _
  have hat : a * t ≤ δ := by
    have : a * t = δ / 4 := by dsimp [t]; field_simp
    linarith
  have hK₀K : K₀ ≤ K := mesh_loss_le hNone
    ((mul_le_mul_of_nonneg_left (min_le_right ηcore t) ha.le).trans hat)
  have hKoutK : h ^ (-t) ≤ K := mesh_loss_le hNone hat
  have hK₀core : K₀ ≤ h ^ (-ηcore) := by
    change (N ^ (-a)) ^ (-θ) ≤ (N ^ (-a)) ^ (-ηcore)
    rw [mesh_negative_rpow hNpos, mesh_negative_rpow hNpos]
    exact Real.rpow_le_rpow_of_exponent_le hNone
      (mul_le_mul_of_nonneg_left (min_le_left ηcore t) ha.le)
  obtain ⟨w₀⟩ := hg N hNg' α d
  let w := w₀.enlarge hh hK₀ hK₀K
  let pc := w₀.planar.enlarge hh hK₀ hK₀core
  obtain ⟨i, G, hG, hGcard, ℓ₀, c₁, c₂, hcoeff, hstrips⟩ := hcore h hh hhsmall pc
  have hGK : G ⊆ w.planar.graph i := hG
  have hrecip : 1 / K ≤ h ^ t := by
    have := one_div_le_one_div_of_le (Real.rpow_pos_of_pos hh (-t)) hKoutK
    simpa only [one_div, Real.rpow_neg hh.le, inv_inv] using this
  have hcard : 1 / (K * h ^ 2) ≤ (G.card : ℝ) := by
    have := div_le_div_of_nonneg_right hrecip (sq_nonneg h)
    exact (show 1 / (K * h ^ 2) ≤ h ^ t / h ^ 2 from by
      simpa only [div_div] using this).trans hGcard
  have hℓ : |ℓ₀| ≤ K := by
    have hc₁ := abs_nonneg c₁
    have hc₂ := abs_nonneg c₂
    linarith
  have hstripsK : ∀ e ∈ G,
      |e.1.2 - ℓ₀ * e.1.1 - c₁| + |e.2.2 - ℓ₀ * e.2.1 - c₂| ≤ K * h := by
    intro e he
    apply (hstrips e he).trans
    rw [show (1 : ℝ) - t = 1 + (-t) by ring, Real.rpow_add hh, Real.rpow_one]
    exact (mul_le_mul_of_nonneg_left hKoutK hh.le).trans_eq (mul_comm _ _)
  obtain ⟨hK, hcoef, herr, hmass⟩ := hrec N hNrec'
  have hE : 0 < d.error := hh.trans_le d.error_lower
  obtain ⟨B, ℓ, hB, hfit⟩ := row_fit_from_witness w hK hh hE d.error_upper
    (fun _ => rfl) G hGK hcard hℓ hstripsK
  refine ⟨B, ℓ, hB.trans hcoef, ?_⟩
  apply (ENNReal.ofReal_le_ofReal hmass).trans
  apply hfit.trans
  apply measure_mono
  intro p hp
  have he := mul_le_mul_of_nonneg_right herr hE.le
  exact ⟨hp.1.trans he, hp.2.trans he⟩

end Submission.Obl.k4_affine_skew_row_fit
