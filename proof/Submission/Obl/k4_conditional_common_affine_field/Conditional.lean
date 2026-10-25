import Submission.Obl.k4_conditional_common_affine_field.ReturnNumerics
import Submission.Obl.k4_conditional_common_affine_field.OriginalPalette
import Submission.Obl.k4_conditional_common_affine_field.InputBounds

namespace Submission.Obl.k4_conditional_common_affine_field

open Set MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem common_affine_field_of_grid (hgrid : UniformGridField) : ∀ S : ℝ, 0 < S → ∃ C₀ : ℝ, 100 < C₀ ∧ ∀ A θ : ℝ, 0 < A → 0 < θ → ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ η ≤ ε ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (π : MeasureTheory.Measure ℝ) (b v : α → ℝ) (v₀ χb χv : ℝ) (f : α × ℝ → Fin 2 → ℝ) (L : (ℤ × ℤ) → Finset (Fin 3 → ℝ)), (fun (δ e : ℝ) => (fun (z : α × ℝ → Fin 2 → ℝ) => (fun (state : α × ℝ → Fin 4 → ℤ) => Measurable b → Measurable v → Measurable f → MeasureTheory.IsProbabilityMeasure ν → MeasureTheory.IsProbabilityMeasure π → N ^ (-A) ≤ χb → χb ≤ 1 → N ^ (-A) ≤ χv → χv ≤ 1 → (∀ l, |b l| + |v l| + |v₀| ≤ N ^ η) → μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod MeasureTheory.volume) → μ (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 → ENNReal.ofReal (N ^ (-η)) ≤ μ Set.univ → (∀ᵐ p ∂μ, ∀ i, |f p i| ≤ N ^ η) → (∀ q : Fin 2 → ℤ, μ {p | (fun i => ⌊z p i / δ⌋) = q} ≤ ENNReal.ofReal (N ^ η * δ ^ 2)) → (∀ x r : ℝ, δ ≤ r → r ≤ 1 → π (Set.Icc (x - r) (x + r)) ≤ ENNReal.ofReal (N ^ η * r ^ S)) → (∀ (q : Fin 4 → ℤ) (j : ℤ), μ {p | state p = q ∧ ⌊v p.1 / δ⌋ = j} ≤ ENNReal.ofReal (N ^ η) * μ {p | state p = q} * π (Set.Ico ((j : ℝ) * δ) (((j : ℝ) + 1) * δ))) → (∀ q, ((L q).card : ℝ) ≤ N ^ η) → (∀ q, ∀ a ∈ L q, ∀ i, |a i| ≤ N ^ η) → (∀ᵐ p ∂μ, ∃ a ∈ L (⌊b p.1 / χb⌋, ⌊v p.1 / χv⌋), |f p 0 - a 0 - a 1 * p.2| ≤ N ^ η * e ∧ |f p 1 - a 2| ≤ N ^ η * e) → ∃ C : Fin 4 → ℝ, (∀ i, |C i| ≤ N ^ ε) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | |f p 0 - C 0 - C 1 * z p 0 - C 2 * z p 1| ≤ N ^ ε * e ∧ |f p 1 - C 3| ≤ N ^ ε * e}) (fun p => ![⌊z p 0 / δ⌋, ⌊z p 1 / δ⌋, ⌊f p 0 / e⌋, ⌊f p 1 / e⌋])) (fun p => ![p.2, b p.1 + p.2 * (v p.1 - v₀)])) (N ^ (-(C₀ * (A + θ)))) (N ^ (-θ)) := by
  classical
  obtain ⟨P,hP,hgrid⟩ := hgrid
  intro S hS
  refine ⟨101,by norm_num,?_⟩
  intro A θ hA hθ ε hε
  obtain ⟨h,η,hh,hη,hηε,N₀,hN₀,hnum⟩ := exists_return_parameters S A θ ε P hS hA hθ hε
  refine ⟨η,hη,hηε,N₀,hN₀,?_⟩
  intro N hN α _ ν μ π b v v₀ χb χv f L
  dsimp only
  intro hb hv hf hν hπ hχb hχb1 hχv hχv1 hcoeff hdom htime hmass hfbound
    hbase hpalette hcond hcard hlist hfit
  letI : IsProbabilityMeasure ν := hν
  letI : IsProbabilityMeasure π := hπ
  have num := hnum N hN
  have hNpos : 0 < N := by linarith [num.N_two]
  let K := N^η
  let H := N^(2*h)
  let B := N^(20*h)
  let δ := N^(-(101*(A+θ)))
  let e := N^(-θ)
  let ω := N^(-2*(A+θ))
  let r := N^(-h)
  let ρ := N^(-avoidExponent S h P)
  let D := K^3*(4*ρ)^S
  have hKpos : 0 < K := Real.rpow_pos_of_pos hNpos _
  have hHpos : 0 < H := Real.rpow_pos_of_pos hNpos _
  have hBpos : 0 < B := Real.rpow_pos_of_pos hNpos _
  have hδpos : 0 < δ := Real.rpow_pos_of_pos hNpos _
  have hepos : 0 < e := Real.rpow_pos_of_pos hNpos _
  have hωpos : 0 < ω := Real.rpow_pos_of_pos hNpos _
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hNpos _
  have hχbpos : 0 < χb := (Real.rpow_pos_of_pos hNpos (-A)).trans_le hχb
  have hχvpos : 0 < χv := (Real.rpow_pos_of_pos hNpos (-A)).trans_le hχv
  have hK1 : 1 ≤ K := num.K_one
  have hKH : K ≤ H := by have h := num.H_large; change K+1 ≤ H at h; linarith
  have hH1 : 1 ≤ H := hK1.trans hKH
  have h2HB : 2*H ≤ B := num.axes_to_budget
  have hHB : H ≤ B := by linarith
  have hKB : K ≤ B := hKH.trans hHB
  have hBlarge : 1000 ≤ B := num.budget_large
  have hB2 : 2 ≤ B := by linarith
  have hμupper : μ univ ≤ ENNReal.ofReal K := original_mass_upper ν μ K hdom htime
  letI : IsFiniteMeasure μ := original_measure_finite ν μ K hdom htime
  have hμlower : ENNReal.ofReal K⁻¹ ≤ μ univ := by
    simpa only [K,Real.rpow_neg hNpos.le] using hmass
  have hμ : μ univ ≠ 0 := ((ENNReal.ofReal_pos.mpr (inv_pos.mpr hKpos)).trans_le hμlower).ne'
  have hgood : ∀ᵐ p ∂μ, p ∈ goodSet b v χb χv K e f L :=
    ae_goodSet μ b v χb χv K e f L htime hfbound hfit
  obtain ⟨prep⟩ := prepare_axes μ hμ π b v v₀ χb χv δ e ω K H r S f L hb hv hf
    hδpos hepos hχbpos hχvpos hK1 num.H_large num.fine_le_one num.fine_le_grid
    num.fine_le_error num.fine_le_radius num.radius_small num.inverse_H
    (num.grid_le_chart.trans hχb) (num.fine_le_chart.trans hχv) num.palette_small
    hcoeff hgood hbase hpalette hcond hcard hlist
  have hprepMass : ENNReal.ofReal B⁻¹ ≤ μ prep.region := by
    have hden : 0 < 2*K^3 := by positivity
    have hBmass : B⁻¹ ≤ 1/(2*K^3) := by
      have h := one_div_le_one_div_of_le hden num.mass_to_budget
      simpa only [one_div] using h
    calc
      _ ≤ ENNReal.ofReal (1/(2*K^3)) := ENNReal.ofReal_le_ofReal hBmass
      _ = ENNReal.ofReal (1/(2*K^2))*ENNReal.ofReal K⁻¹ := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(2*K^2))]
        congr 1
        field_simp
      _ ≤ ENNReal.ofReal (1/(2*K^2))*μ univ := mul_le_mul' le_rfl hμlower
      _ ≤ μ prep.region := prep.mass
  have hpencil : ∀ w : ℝ, μ {p | |v p.1-w| < ρ} ≤ ENNReal.ofReal D := by
    intro w
    have h := original_velocity_pencil_cap μ (fineState b v v₀ δ e f)
      (measurable_fineState hb hv v₀ δ e hf) (fun p => v p.1) (hv.comp measurable_fst) π
      δ ρ K S hδpos num.fine_le_avoid num.avoid_small hKpos.le hpalette hcond w
    calc
      _ ≤ ENNReal.ofReal (K^2*(4*ρ)^S)*μ univ := h
      _ ≤ ENNReal.ofReal (K^2*(4*ρ)^S)*ENNReal.ofReal K := mul_le_mul' le_rfl hμupper
      _ = ENNReal.ofReal D := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ K^2*(4*ρ)^S)]
        congr 1
        dsimp only [D]
        ring
  obtain ⟨C,hC,hCMass⟩ := common_field_from_axes P hgrid ν μ b v v₀ χb χv δ e ω K H r B ρ D f L
    hb hv hf prep hK1 hH1 hB2 hepos hωpos hKH hHB h2HB num.menus_to_budget
    num.cap_to_budget num.inverse_H num.grid_small hprepMass hdom hcard hρpos
    (by dsimp only [D]; positivity) num.pencil_small hpencil
  have hρ1 : ρ ≤ 1 := by have h := num.avoid_small; change 4*ρ ≤ 1 at h; linarith
  have herror : returnError P B K H e ω ρ ≤ N^ε*e := by
    calc
      _ ≤ B^(returnDegree P)*e/ρ^2 := returnError_bound P hBlarge hKpos.le hHpos.le
        hKB hHB hepos.le hωpos.le num.grid_le_error hρpos hρ1
      _ = (B^(returnDegree P)/ρ^2)*e := by ring
      _ ≤ N^ε*e := mul_le_mul_of_nonneg_right num.final_loss hepos.le
  refine ⟨C,?_,?_⟩
  · intro i
    exact (hC i).trans ((coefficient_budget_bound P hBlarge hHpos.le hHB).trans num.final_coefficient)
  · calc
      ENNReal.ofReal (N^(-ε)) ≤ ENNReal.ofReal (B^P)⁻¹ :=
        ENNReal.ofReal_le_ofReal num.final_mass
      _ ≤ μ {p | |f p 0-C 0-C 1*base b v v₀ p 0-C 2*base b v v₀ p 1| ≤ returnError P B K H e ω ρ ∧
          |f p 1-C 3| ≤ returnError P B K H e ω ρ} := hCMass
      _ ≤ _ := by
        apply measure_mono
        intro p hp
        exact ⟨hp.1.trans herror,hp.2.trans herror⟩

end Submission.Obl.k4_conditional_common_affine_field
