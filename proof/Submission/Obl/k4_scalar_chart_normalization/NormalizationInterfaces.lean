import Submission.Obl.k4_scalar_chart_normalization.Defs

namespace Submission.Obl.k4_scalar_chart_normalization

open MeasureTheory Filter
open scoped ENNReal Topology

/-- Tempered geometry and the original weighted product laws, without a profile. -/
noncomputable def RawScalar : Problem → Prop :=
  (fun edc => ((∀ k,2 ≤ edc.N k) ∧
    Filter.Tendsto edc.N Filter.atTop Filter.atTop ∧
    ((∀ k,1 ≤ edc.K k) ∧
    ∀ ε:ℝ,0 < ε → ∀ᶠ k in Filter.atTop,edc.K k ≤ edc.N k ^ ε) ∧
    1 ≤ edc.M ∧
    1 ≤ edc.D ∧
    0 < edc.L ∧
    0 ≤ edc.d ∧
    edc.d < 1 ∧
    0 < edc.S ∧
    0 < edc.U) ∧ ((∀ k,(((edc).1) k:ℝ) ≤ edc.N k ^ (edc.M:ℝ) ∧
    (∀ γ,0 ≤ edc.w k γ) ∧
    (∑ γ,edc.w k γ) = 1 ∧
    (∀ γ,MeasureTheory.IsProbabilityMeasure (edc.nu k γ) ∧
    (∃ n:ℕ,(n:ℝ) ≤ edc.N k ^ (edc.M:ℝ) ∧
    ∃ (h:Fin n → ℝ) (i:Fin n → ℕ) (B:Fin n → Set (Fin 5 → ℝ)),(∀ j,0 ≤ h j ∧
    h j ≤ edc.N k ^ (edc.M:ℝ) ∧
    (i j:ℝ) ≤ edc.N k ^ (edc.M:ℝ) ∧
    Format 5 (edc.N k ^ (edc.M:ℝ)) edc.D (B j) ∧
    (∀ b ∈ B j,∀ e,|b e| ≤ edc.N k ^ (edc.M:ℝ))) ∧
    edc.nu k γ = ∑ j,ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j,b)) (MeasureTheory.volume.restrict (B j))) ∧
    (∀ᵐ l ∂edc.nu k γ,∀ e,|l.2 e| ≤ edc.K k) ∧
    MeasurableSet (edc.E k γ) ∧
    edc.E k γ ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1 ∧
    (∀ p ∈ edc.E k γ,(p.1.1:ℝ) ≤ edc.N k ^ (edc.M:ℝ)) ∧
    (∀ i:ℕ,Format 6 (edc.N k ^ (edc.M:ℝ)) edc.D {b:Fin 6 → ℝ | ((i,fun e:Fin 5 => b e.castSucc),b 5) ∈ edc.E k γ})) ∧
    ENNReal.ofReal ((edc.K k)⁻¹) ≤ ∑ γ,ENNReal.ofReal (edc.w k γ) * (mu edc) k γ Set.univ)))

/-- Pure observation laws, profile shape and power-small typicality. -/
noncomputable def PureProfile : Problem → Prop :=
  (fun edc => ((∀ k γ r,0 ≤ r → r ≤ edc.L → Measurable (edc.rho k γ r) ∧
    MeasureTheory.Measure.map (fun p => ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-r))⌋:ℤ))) ((mu edc) k γ) = (MeasureTheory.volume.prod MeasureTheory.Measure.count).withDensity (edc.rho k γ r))) ∧ ((∀ r s:ℝ,0 ≤ r → r ≤ s → s ≤ edc.L → 0 ≤ edc.f s - edc.f r ∧
    edc.f s - edc.f r ≤ s - r)) ∧ ((∀ r τ:ℝ,0 ≤ r → r ≤ edc.L → 0 < τ → ∃ c:ℝ,0 < c ∧
    ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal (edc.w k γ) * (mu edc) k γ {p | edc.rho k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-r))⌋:ℤ)) < ENNReal.ofReal (edc.N k ^ (-edc.f r - τ))∨ENNReal.ofReal (edc.N k ^ (-edc.f r + τ)) < edc.rho k γ r ((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-r))⌋:ℤ))}) ≤ ENNReal.ofReal (edc.N k ^ (-c)))))

/-- The Exact clauses grouped for sharing the raw and pure-profile interfaces. -/
noncomputable def ProfiledExact : Problem → Prop :=
  (fun edc => RawScalar edc ∧ PureProfile edc ∧ ((∀ k γ u,0 < u → u ≤ edc.U → Measurable (edc.rhoA k γ u) ∧
    MeasureTheory.Measure.map (fun p => (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-edc.L))⌋:ℤ)),(⌊p.1.2 1 / (edc.N k ^ (-u))⌋:ℤ))) ((mu edc) k γ) = ((MeasureTheory.volume.prod MeasureTheory.Measure.count).prod MeasureTheory.Measure.count).withDensity (edc.rhoA k γ u))) ∧ ((∀ r:ℝ,0 ≤ r → r ≤ edc.L → edc.f edc.L - edc.f r ≤ edc.d * (edc.L - r))) ∧ ((∀ u τ:ℝ,0 < u → u ≤ edc.U → 0 < τ → ∃ c:ℝ,0 < c ∧
    ∀ᶠ k in Filter.atTop,(∑ γ,ENNReal.ofReal (edc.w k γ) * (mu edc) k γ {p | ENNReal.ofReal (edc.N k ^ (-edc.f edc.L - edc.S * u + τ)) < edc.rhoA k γ u (((![p.2,y p.1 p.2]:Fin 2 → ℝ),(⌊x p.1 p.2 / (edc.N k ^ (-edc.L))⌋:ℤ)),(⌊p.1.2 1 / (edc.N k ^ (-u))⌋:ℤ))}) ≤ ENNReal.ofReal (edc.N k ^ (-c)))))

/-- Regrouping the Exact clauses adds no hypothesis. -/
theorem profiledExact_iff (p : Problem) : ProfiledExact p ↔ Exact p := by
  constructor
  · rintro ⟨⟨hbase, hworld⟩, ⟨hlaw, hshape, htypical⟩, hjoint, hcap, hangular⟩
    exact ⟨hbase, hworld, hlaw, hjoint, hshape, htypical, hcap, hangular⟩
  · rintro ⟨hbase, hworld, hlaw, hjoint, hshape, htypical, hcap, hangular⟩
    exact ⟨⟨hbase, hworld⟩, ⟨hlaw, hshape, htypical⟩, hjoint, hcap, hangular⟩

/-- Homogenization selects incidences and a subsequence; priors and weights stay fixed. -/
noncomputable def PureHomogenization : Prop :=
  (∀ p : Problem, RawScalar p →
  ∃ (φ : ℕ → ℕ) (K' : ℕ → ℝ) (M' D' : ℕ)
    (E' : (k : ℕ) → Fin (p.1 (φ k)) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ))
    (ρ' : (k : ℕ) → Fin (p.1 (φ k)) → ℝ → ((Fin 2 → ℝ) × ℤ) → ENNReal)
    (F : ℝ → ℝ),
    (fun q : Problem => StrictMono φ ∧
      (∀ k γ, E' k γ ⊆ p.E (φ k) γ) ∧ RawScalar q ∧ PureProfile q)
    ⟨(fun k => p.1 (φ k)), (fun k => p.N (φ k)), K', M', D', p.L, p.d,
      p.S, p.U, (fun k => p.w (φ k)), (fun k => p.nu (φ k)), E', ρ',
      (fun _ _ _ _ => 0), F⟩)

end Submission.Obl.k4_scalar_chart_normalization
