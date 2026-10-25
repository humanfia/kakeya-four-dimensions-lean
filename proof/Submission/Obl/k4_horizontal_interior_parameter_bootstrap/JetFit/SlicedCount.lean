import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit.SlicedGeom

/-!
Moved from o217 (branch x0763, same author, session x0763 = x0931), namespace changed.
# The sliced fit: many occupied cells

`many_occupied_cells` chains the starting time, the heavy first starting bin, the light time
bins, the quadrant and the cell bound: at least `p^{-3}/(179712 K^16)` cells of side `p` carry
pruned collisions (paper: "The represented triples then have `p`-covering number at least
`p^{-3}/K`").
-/

open MeasureTheory Set Metric

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The real arithmetic of the cell count. -/
theorem occ_arith {K p q O C₁ c₀ M : ℝ} (hK : 1 ≤ K) (_hp : 0 < p) (hq : 0 < q)
    (hC₁ : C₁ ≤ 24 * K ^ 3 / q) (hC₁0 : 0 ≤ C₁) (hc₀ : c₀ ≤ 4 * K ^ 2 * q) (hc₀0 : 0 ≤ c₀)
    (hM : M ≤ 39 * K ^ 4 * p ^ 3 * q ^ 2) (hM0 : 0 ≤ M) (hO : 0 ≤ O)
    (h : (1 / K ^ 3) ^ 2 ≤ C₁ * (C₁ * (4 * (O * M) + c₀ * c₀ * (2 / (36864 * K ^ 16))))) :
    1 ≤ 179712 * K ^ 16 * p ^ 3 * O := by
  have hK0 : 0 < K := by linarith
  set X := 4 * (O * M) + c₀ * c₀ * (2 / (36864 * K ^ 16)) with hX
  have hX0 : 0 ≤ X := by positivity
  have hXle : X ≤ 4 * (O * (39 * K ^ 4 * p ^ 3 * q ^ 2)) +
      (4 * K ^ 2 * q) * (4 * K ^ 2 * q) * (2 / (36864 * K ^ 16)) := by
    have a1 : O * M ≤ O * (39 * K ^ 4 * p ^ 3 * q ^ 2) := mul_le_mul_of_nonneg_left hM hO
    have a2 : c₀ * c₀ ≤ (4 * K ^ 2 * q) * (4 * K ^ 2 * q) := mul_le_mul hc₀ hc₀ hc₀0 (by positivity)
    have a3 : c₀ * c₀ * (2 / (36864 * K ^ 16)) ≤
        (4 * K ^ 2 * q) * (4 * K ^ 2 * q) * (2 / (36864 * K ^ 16)) :=
      mul_le_mul_of_nonneg_right a2 (by positivity)
    linarith
  have hCC : C₁ * (C₁ * X) ≤ (24 * K ^ 3 / q) * ((24 * K ^ 3 / q) * X) := by
    have b1 : C₁ * X ≤ (24 * K ^ 3 / q) * X := mul_le_mul_of_nonneg_right hC₁ hX0
    calc C₁ * (C₁ * X) ≤ C₁ * ((24 * K ^ 3 / q) * X) := mul_le_mul_of_nonneg_left b1 hC₁0
      _ ≤ (24 * K ^ 3 / q) * ((24 * K ^ 3 / q) * X) :=
          mul_le_mul_of_nonneg_right hC₁ (by positivity)
  have hfin : (24 * K ^ 3 / q) * ((24 * K ^ 3 / q) * (4 * (O * (39 * K ^ 4 * p ^ 3 * q ^ 2)) +
      (4 * K ^ 2 * q) * (4 * K ^ 2 * q) * (2 / (36864 * K ^ 16)))) =
      89856 * K ^ 10 * p ^ 3 * O + 1 / (2 * K ^ 6) := by
    field_simp; ring
  have hmain : (1 / K ^ 3) ^ 2 ≤ 89856 * K ^ 10 * p ^ 3 * O + 1 / (2 * K ^ 6) := by
    calc (1 / K ^ 3) ^ 2 ≤ C₁ * (C₁ * X) := h
      _ ≤ (24 * K ^ 3 / q) * ((24 * K ^ 3 / q) * X) := hCC
      _ ≤ (24 * K ^ 3 / q) * ((24 * K ^ 3 / q) * (4 * (O * (39 * K ^ 4 * p ^ 3 * q ^ 2)) +
          (4 * K ^ 2 * q) * (4 * K ^ 2 * q) * (2 / (36864 * K ^ 16)))) := by gcongr
      _ = _ := hfin
  have hK6 : 0 < K ^ 6 := by positivity
  have e1 : (1 / K ^ 3) ^ 2 = 1 / K ^ 6 := by rw [div_pow]; ring
  rw [e1] at hmain
  have h2 : 1 / (2 * K ^ 6) ≤ 89856 * K ^ 10 * p ^ 3 * O := by
    have : 1 / K ^ 6 = 2 * (1 / (2 * K ^ 6)) := by field_simp
    linarith
  rw [div_le_iff₀ (by positivity)] at h2
  have : 89856 * K ^ 10 * p ^ 3 * O * (2 * K ^ 6) = 179712 * K ^ 16 * p ^ 3 * O := by ring
  linarith

/-- The pruned collision set: heavy first starting bin, good time bins, one quadrant. -/
def Sstar (D : SlicedData Ω) (p u₀ K₁ s₁ s₂ : ℝ) (β₀ : ℤ) : Set ((Ω × Ω) × ℝ) :=
  Scol D p u₀ β₀ ∩ {x | ⌊x.2 / p⌋ ∈ goodIdx D p K₁} ∩ quadSet D u₀ s₁ s₂

/-- **Many occupied cells**: after the three pigeonholes at least `p^{-3}/(179712 K^16)` cells
carry pruned collisions. -/
theorem many_occupied_cells {D : SlicedData Ω} {p K d : ℝ} (H : SlicedHyp D p K d)
    (hp : 0 < p) (hp1 : p ≤ 1) (hK : 1 ≤ K) (hd : 0 ≤ d) (hd1 : d ≤ 1) {u₀ : ℝ}
    (hu₀ : u₀ ∈ Icc (0:ℝ) 1)
    (hmass : ENNReal.ofReal (1 / K ^ 3) ≤ (D.ν.prod volume) (Elab D u₀)) :
    ∃ (β₀ : ℤ) (s₁ s₂ : ℝ), (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
      ∃ Occ : Finset (ℤ × ℤ × ℤ), 1 ≤ 179712 * K ^ 16 * p ^ 3 * Occ.card ∧
        ∀ c ∈ Occ, (Sstar D p u₀ (36864 * K ^ 16) s₁ s₂ β₀ ∩ cellSet D p c.1 c.2.1 c.2.2).Nonempty := by
  have hK0 : 0 < K := by linarith
  set K₁ : ℝ := 36864 * K ^ 16 with hK₁
  have hK₁0 : 0 < K₁ := by positivity
  set Γ : Measure ((Ω × Ω) × ℝ) := (D.ν.prod D.ν).prod (volume : Measure ℝ) with hΓ
  obtain ⟨β₀, hβ⟩ := exists_heavy_start_bin H hp hp1 hK u₀
  set Sg := Scol D p u₀ β₀ ∩ {x | ⌊x.2 / p⌋ ∈ goodIdx D p K₁} with hSg
  have hbad := badBins_mass_le H hp hp1 hK hK₁0 u₀ β₀
  have hsplit : Γ (Scol D p u₀ β₀) ≤ Γ Sg + Γ (Scol D p u₀ β₀ ∩ {x | ⌊x.2 / p⌋ ∉ goodIdx D p K₁}) := by
    refine (measure_mono ?_).trans (measure_union_le _ _)
    intro x hx
    by_cases hg : ⌊x.2 / p⌋ ∈ goodIdx D p K₁
    · exact Or.inl ⟨hx, hg⟩
    · exact Or.inr ⟨hx, hg⟩
  obtain ⟨s₁, s₂, hs₁, hs₂, hquad⟩ := exists_heavy_quad (D := D) Γ u₀ Sg
  obtain ⟨Occ, hOcc, hne⟩ := exists_occupied_cells H hp hK hu₀ β₀ (Sg ∩ quadSet D u₀ s₁ s₂)
    (fun x hx => hx.1.1)
  refine ⟨β₀, s₁, s₂, hs₁, hs₂, Occ, ?_, fun c hc => hne c hc⟩
  -- real quantities
  set q : ℝ := p ^ d with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos hp d
  set C₁ : ℝ := 3 * (K * (8 * K ^ 2 / p) ^ d) with hC₁
  set c₀ : ℝ := (2 * K / p + 2) * (K * p ^ (1 + d)) with hc₀
  set a₁ : ℝ := K * p ^ (1 + d) with ha₁
  set a₂ : ℝ := (36 * K ^ 2 + 3) * (K * p ^ (1 + d)) with ha₂
  set M : ℝ := p * (a₁ * a₂) with hM
  set O : ℝ := (Occ.card : ℝ) with hO
  have hp1d : p ^ (1 + d) = p * q := by rw [Real.rpow_add hp, Real.rpow_one]
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hc₀0 : 0 ≤ c₀ := by positivity
  have ha₁0 : 0 ≤ a₁ := by positivity
  have ha₂0 : 0 ≤ a₂ := by positivity
  have hM0 : 0 ≤ M := by positivity
  -- the ENNReal chain
  have hchain : ENNReal.ofReal ((1 / K ^ 3) ^ 2) ≤
      ENNReal.ofReal (C₁ * (C₁ * (4 * (O * M) + c₀ * c₀ * (2 / K₁)))) := by
    rw [ENNReal.ofReal_pow (by positivity)]
    calc ENNReal.ofReal (1 / K ^ 3) ^ 2 ≤ ((D.ν.prod volume) (Elab D u₀)) ^ 2 := by gcongr
      _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal C₁ * Γ (Scol D p u₀ β₀)) := hβ
      _ ≤ ENNReal.ofReal C₁ * (ENNReal.ofReal C₁ *
            (4 * (Occ.card * (ENNReal.ofReal p * (ENNReal.ofReal a₁ * ENNReal.ofReal a₂))) +
              ENNReal.ofReal c₀ * ENNReal.ofReal c₀ * ENNReal.ofReal (2 / K₁))) := by
          gcongr
          calc Γ (Scol D p u₀ β₀) ≤ Γ Sg + Γ (Scol D p u₀ β₀ ∩ {x | ⌊x.2 / p⌋ ∉ goodIdx D p K₁}) :=
                hsplit
            _ ≤ 4 * Γ (Sg ∩ quadSet D u₀ s₁ s₂) + ENNReal.ofReal c₀ * ENNReal.ofReal c₀ *
                  ENNReal.ofReal (2 / K₁) := add_le_add hquad hbad
            _ ≤ _ := by gcongr
      _ = ENNReal.ofReal (C₁ * (C₁ * (4 * (O * M) + c₀ * c₀ * (2 / K₁)))) := by
          rw [← ENNReal.ofReal_mul ha₁0, ← ENNReal.ofReal_mul hp.le, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hc₀0,
            ← ENNReal.ofReal_mul (by positivity)]
          rw [show (4 : ENNReal) = ENNReal.ofReal 4 by simp, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hC₁0,
            ← ENNReal.ofReal_mul hC₁0]
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hchain
  apply occ_arith hK hp hq0 _ hC₁0 _ hc₀0 _ hM0 (by positivity) hreal
  · -- `C₁ ≤ 24 K³ / q`
    have h8 : (8 * K ^ 2 / p) ^ d = (8 * K ^ 2) ^ d / q := Real.div_rpow (by positivity) hp.le d
    have h8' : (8 * K ^ 2) ^ d ≤ 8 * K ^ 2 := by
      calc (8 * K ^ 2) ^ d ≤ (8 * K ^ 2) ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by nlinarith) hd1
        _ = 8 * K ^ 2 := Real.rpow_one _
    rw [hC₁, h8]
    calc 3 * (K * ((8 * K ^ 2) ^ d / q)) ≤ 3 * (K * ((8 * K ^ 2) / q)) := by gcongr
      _ = 24 * K ^ 3 / q := by ring
  · -- `c₀ ≤ 4 K² q`
    rw [hc₀, ha₁, hp1d]
    have : (2 * K / p + 2) * (K * (p * q)) = 2 * K ^ 2 * q + 2 * K * p * q := by field_simp
    rw [this]
    have : K * p ≤ K ^ 2 := by nlinarith
    nlinarith
  · -- `M ≤ 39 K⁴ p³ q²`
    rw [hM, ha₁, ha₂, hp1d]
    have : p * (K * (p * q) * ((36 * K ^ 2 + 3) * (K * (p * q)))) =
        (36 * K ^ 2 + 3) * K ^ 2 * p ^ 3 * q ^ 2 := by ring
    rw [this]
    have : (36 * K ^ 2 + 3) * K ^ 2 ≤ 39 * K ^ 4 := by
      have h1 : 1 ≤ K ^ 2 := by nlinarith
      have h2 : K ^ 2 ≤ K ^ 2 * K ^ 2 := by nlinarith
      nlinarith
    have hpq : 0 ≤ p ^ 3 * q ^ 2 := by positivity
    nlinarith

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.JetFit

end
