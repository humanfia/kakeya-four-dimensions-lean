import Submission.Obl.k4_clean_cover_graph_atlas.SampleInput
import Submission.Obl.k4_clean_cover_graph_atlas.CleanCaps
import Submission.Obl.k4_clean_cover_graph_atlas.GroupBaseCap

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory MvPolynomial Set

section Sample
variable {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ}
  {Mpr Dpr : ℕ} {d₁ ρ gain δ₀ τ ε : ℝ} {m : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
  {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ}
  {A : Fin C → Set (ℕ × (Fin 6 → ℝ))} {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
  {Mg Dg : ℕ} {i : ℕ} {h : ℝ} {n : ℕ} {old : Fin n → Fin C}
  {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
  {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ}

/-- The original continuous observation ceiling, directly from the cleaned sample input.
The fixed menu depth may lie below the true candidate depth. -/
theorem sampleInput_candidate_base_cap (hNk : 1 ≤ Nk)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q) (a : Fin n) :
    let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
    (((ν (γ (old a))).prod volume).restrict (V a)).map obsBase ≤
      ENNReal.ofReal (Nk ^ (-f q + τ) * (16 * (1 + U ^ 2))) • volume := by
  obtain ⟨hscalar, _, _, _, _, _, _, hentry, _, _, _, _, _, _, _, hqhi⟩ := hsi
  obtain ⟨_, _, hdeg, _, _, _, _, htests, _, hVsub, _, hcap, _⟩ := hentry a
  let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
  have hNkpos : 0 < Nk := lt_of_lt_of_le zero_lt_one hNk
  have hU : 0 < U := Real.rpow_pos_of_pos hNkpos _
  have hB : 0 < B (γ (old a)) := (hscalar.2.2.2 (γ (old a))).2.1
  have hdelta := delta_antitone hNk hqhi
  change _ ≤ ENNReal.ofReal (Nk ^ (-f q + τ) * (16 * (1 + U ^ 2))) • volume
  rw [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hNkpos _).le]
  apply candidate_base_map_cap _ (R' a) hdeg (Submission.Lib.K4XInterface.gδ_pos Nk q) hB hU
    (V a) (ENNReal.ofReal (Nk ^ (-f q + τ))) hcap
  intro p hp
  obtain ⟨_, hpA, hpt, hder⟩ := hVsub hp
  have ht := htests p.1 hpA p.2 hpt
  exact ⟨ht.1.trans (mul_le_mul_of_nonneg_left hdelta hU.le), hder⟩

/-- Any subsequently retained subset inherits terminal absolute continuity of the
original witness. This is the only observation-law input of `group_step_of_ac`. -/
theorem sampleInput_cov_observation_ac
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q) (a : Fin n)
    {cov : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hcov : cov ⊆ V a) :
    (((ν (γ (old a))).prod volume).restrict cov).map (obs (B (γ (old a))) (δ Nk L)) ≪
      (volume.prod Measure.count) := by
  obtain ⟨_, _, _, _, _, _, _, hentry, _⟩ := hsi
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hAC⟩ := hentry a
  exact (Measure.map_mono (Measure.restrict_mono_set _ hcov)
    (measurable_obs _ _)).absolutelyContinuous.trans hAC

/-- The original candidate law in a group's comparison coordinates, retaining the
exact radius, determinant and original time normalization. -/
theorem sampleInput_candidate_group_cap (hNk : 1 ≤ Nk)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q) (a : Fin n)
    (c u : Fin C → EuclideanSpace ℝ (Fin 2)) (Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ)
    (hQ : (Q (old a)).det ≠ 0) (v0 : EuclideanSpace ℝ (Fin 3)) {radius : ℝ} (hradius : 0 < radius)
    {cov : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hcov : cov ⊆ V a) :
    let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
    let H := Nk ^ (-f q + τ) * (16 * (1 + U ^ 2))
    (((ν (γ (old a))).prod volume).restrict cov).map
      ((groupBase (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) v0 radius) ∘
        obs (B (γ (old a))) (δ Nk L)) ≤
      ENNReal.ofReal (H * radius ^ 3 * |(Q (old a)).det| / 2 ^ T i) • volume := by
  let U := Nk ^ (4 * ρ * gain * L + 4 * ε)
  let H := Nk ^ (-f q + τ) * (16 * (1 + U ^ 2))
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hbase : (((ν (γ (old a))).prod volume).restrict cov).map
      (fun p => (obs (B (γ (old a))) (δ Nk L) p).1) ≤ ENNReal.ofReal H • volume := by
    exact (Measure.map_mono (Measure.restrict_mono_set _ hcov) measurable_obsBase).trans
      (sampleInput_candidate_base_cap hNk hsi a)
  exact original_group_base_law_le _ _ (measurable_obs _ _) hH hbase
    (T i) (j (old a)) (c (old a)) (u (old a)) (Q (old a)) hQ v0 hradius

/-- Covered witness mass is bounded by the full original assignment times its old
block length, without conditioning the assignment. -/
theorem sampleInput_cov_cylinder_bound
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q) (a : Fin n)
    {cov : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hcov : cov ⊆ V a) :
    ((ν (γ (old a))).prod volume) cov ≤
      ν (γ (old a)) (A (old a)) * ENNReal.ofReal ((2 : ℝ) ^ T i)⁻¹ := by
  obtain ⟨hscalar, _, _, _, _, _, _, hentry, _⟩ := hsi
  obtain ⟨_, _, _, _, _, hA'A, _, _, _, hVsub, _⟩ := hentry a
  letI := (hscalar.2.2.2 (γ (old a))).1
  have hsub : cov ⊆ A (old a) ×ˢ
      Icc ((j (old a) : ℝ) / 2 ^ T i) (((j (old a) : ℝ) + 1) / 2 ^ T i) := by
    intro p hp
    have h := hVsub (hcov hp)
    exact ⟨hA'A h.2.1, h.2.2.1⟩
  calc
    _ ≤ ((ν (γ (old a))).prod volume)
        (A (old a) ×ˢ Icc ((j (old a) : ℝ) / 2 ^ T i) (((j (old a) : ℝ) + 1) / 2 ^ T i)) :=
      measure_mono hsub
    _ = _ := by
      rw [Measure.prod_prod, Real.volume_Icc]
      congr 2
      ring

/-- Finite original component mass follows from the prior probability and the old
time block. No boundedness assumption on the whole world incidence set is needed. -/
theorem sampleInput_cov_finite
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q) (a : Fin n)
    {cov : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} (hcov : cov ⊆ V a) :
    ((ν (γ (old a))).prod volume) cov ≠ ⊤ := by
  letI := (hsi.1.2.2.2 (γ (old a))).1
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (measure_ne_top _ _)
    ENNReal.ofReal_ne_top) (sampleInput_cov_cylinder_bound hsi a hcov)

end Sample
end Submission.Obl.k4_clean_cover_graph_atlas
