import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Contract
import Submission.Obl.k4_scalar_capped_heavy_potential.CompactCaps
import Submission.Obl.k4_scalar_capped_heavy_potential.Losses

namespace Submission.Obl.k4_scalar_capped_heavy_potential

open Set MeasureTheory MvPolynomial

noncomputable section

/-- The output of the finite heavy selection, before enlarging all
constants to one common subpower envelope. -/
def SelectedAt (N K C η d Z B R cstar : ℝ) (Dp Tk : ℕ) (jj : Fin (2 ^ Tk))
    (ν : Measure (ℕ × (Fin 5 → ℝ))) (π : Measure ℝ) (A : Set (ℕ × (Fin 5 → ℝ)))
    (μ σ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (z : Fin 2 → ℝ)
    (P : MvPolynomial (Fin 2) ℝ) : Prop :=
  let h := ((2 : ℝ) ^ Tk)⁻¹
  let a := N ^ (-1 : ℝ)
  let w := N ^ (-1 - cstar)
  let ξ := N ^ (-Z)
  let b := N ^ (-B)
  let I := Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk) ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk)
  σ ≤ μ ∧
    ENNReal.ofReal (h * (ν A).toReal * (η / (K + 1) ^ 2) /
      (13478400 * C * K ^ 6 * (a / w) ^ d)) ≤ σ univ ∧
    P.totalDegree ≤ Dp ∧ (∀ m, |P.coeff m| ≤ 2 * K + w) ∧
    (∀ᵐ p ∂σ, ∀ t ∈ I, |Cons.xL p.1 t - eval (Cons.ubase z h p.1 t) P| ≤ 2 * w) ∧
    (∀ q : Fin 2 → ℤ,
      σ {p | (fun i => (⌊Cons.ubase z h p.1 p.2 i / ξ⌋ : ℤ)) = q} ≤
        ENNReal.ofReal (735 * K ^ 2 * h * ξ ^ 2 * (w / a) ^ d) * ν A) ∧
    ∀ r, R⁻¹ ≤ r → r ≤ R → ∀ (q : Fin 3 → ℤ) (j : ℤ),
      σ {p | Cons.physState b p = q ∧ (⌊p.1.2 1 / (N ^ (-r))⌋ : ℤ) = j} ≤
        ENNReal.ofReal (1000 * K) * σ {p | Cons.physState b p = q} *
          π {v | (⌊v / (N ^ (-r))⌋ : ℤ) = j}

/-- The per-sample heavy potential certificate, definitionally the
frozen output body when `cstar = κ * (1-d) / 1000`. -/
def HeavyAt (N H d κ S Z B R cstar : ℝ) (D Tk : ℕ) (jj : Fin (2 ^ Tk))
    (ν : Measure (ℕ × (Fin 5 → ℝ))) (π : Measure ℝ)
    (ρ μ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (A : Set (ℕ × (Fin 5 → ℝ)))
    (z : Fin 2 → ℝ) (P : MvPolynomial (Fin 2) ℝ) : Prop :=
  let h := ((2 : ℝ) ^ Tk)⁻¹
  let I := Icc (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk) ((((jj : ℕ) : ℝ) + 1) / (2 : ℝ) ^ Tk)
  MeasurableSet A ∧ IsProbabilityMeasure ν ∧ IsProbabilityMeasure π ∧
    (∀ᵐ l ∂ν, ∀ e, |l.2 e| ≤ H) ∧
    N ^ (-κ) / H ≤ h ∧ h ≤ H * N ^ (-κ) ∧ 0 < h ∧ h ≤ 1 ∧
    ENNReal.ofReal (N ^ (-d) * h / H) ≤ ν A ∧ ν A ≤ ENNReal.ofReal (H * N ^ (-d) * h) ∧
    μ ≤ ρ ∧ μ ≤ ENNReal.ofReal H • ν.prod volume ∧
    μ {p | p.1 ∈ A ∧ p.2 ∈ I}ᶜ = 0 ∧
    ENNReal.ofReal (h * N ^ (-d * cstar) / H) * ν A ≤ μ univ ∧
    z 0 = (((jj : ℕ) : ℝ) / (2 : ℝ) ^ Tk) ∧ (∀ e, |z e| ≤ H) ∧
    (∀ᵐ p ∂μ, ∀ t ∈ I, ∀ e, |Cons.ubase z h p.1 t e| ≤ H) ∧
    (∀ q : Fin 2 → ℤ,
      μ {p | (fun e => (⌊Cons.ubase z h p.1 p.2 e / (N ^ (-Z))⌋ : ℤ)) = q} ≤
        ENNReal.ofReal ((H * h * N ^ (-d * cstar)) * N ^ (-2 * Z)) * ν A) ∧
    (∀ r, R⁻¹ ≤ r → r ≤ R →
      (∀ j : ℤ, π {v | (⌊v / (N ^ (-r))⌋ : ℤ) = j} ≤ ENNReal.ofReal (H * N ^ (-S * r))) ∧
      ∀ (q : Fin 3 → ℤ) (j : ℤ),
        μ {p | Cons.physState (N ^ (-B)) p = q ∧ (⌊p.1.2 1 / (N ^ (-r))⌋ : ℤ) = j} ≤
          ENNReal.ofReal H * μ {p | Cons.physState (N ^ (-B)) p = q} *
            π {v | (⌊v / (N ^ (-r))⌋ : ℤ) = j}) ∧
    P.totalDegree ≤ D ∧ (∀ m, |P.coeff m| ≤ H) ∧
    ∀ᵐ p ∂μ, ∀ t ∈ I,
      |Cons.xL p.1 t - eval (Cons.ubase z h p.1 t) P| ≤ H * N ^ (-1 - cstar)

/-- Enlarge the finite heavy output to the one common loss appearing
in the frozen certificate. Original packet and prior facts are inherited
from the same field witness. -/
theorem heavy_certificate_of_selected_packet
    {N Hf K L C η d κ S Z B Rf R cstar : ℝ}
    (hN : 1 < N) (hHf : 1 ≤ Hf) (hK : 1 ≤ K) (hFH : Hf ≤ K)
    (hC : 0 < C) (hη : 0 < η) (hcstar : 0 ≤ cstar) (hR : 0 < R) (hRR : R ≤ Rf)
    (hLpalette : 1000 * K ≤ L) (hLbase : 735 * K ^ 2 ≤ L) (hLcoeff : 3 * K ≤ L)
    (hLmass : 13478400 * C * K ^ 6 * (K + 1) ^ 2 * η⁻¹ ≤ L)
    (D Dp Tk : ℕ) (jj : Fin (2 ^ Tk))
    (ν : Measure (ℕ × (Fin 5 → ℝ))) (π : Measure ℝ)
    (ρ μ σ : Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) (A : Set (ℕ × (Fin 5 → ℝ)))
    (z : Fin 2 → ℝ) (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (hField : Cons.FieldAt N Hf d κ S Z B Rf D ν π ρ A Tk jj μ z 𝒯)
    (hSelected : SelectedAt N K C η d Z B Rf cstar Dp Tk jj ν π A μ σ z P) :
    HeavyAt N L d κ S Z B R cstar Dp Tk jj ν π ρ σ A z P := by
  let h := ((2 : ℝ) ^ Tk)⁻¹
  let a := N ^ (-1 : ℝ)
  let w := N ^ (-1 - cstar)
  let ξ := N ^ (-Z)
  rcases hField with ⟨hA, hνprob, hπprob, hcoeff, hlo, hup, hh, hh₁, hpriorlo, hpriorhi,
    hμρ, hdom, hsupport, hmass, hz₀, hz, hbox, hbase, hpalette, h𝒯coeff, h𝒯fit, hjoint⟩
  rcases hSelected with ⟨hσμ, hheavy, hDout, hcout, hfitout, hbaseout, hpalout⟩
  letI := hνprob
  have hN₀ : 0 < N := by linarith
  have hHf₀ : 0 < Hf := by linarith
  have hK₀ : 0 < K := by linarith
  have hLf : Hf ≤ L := by linarith
  have hL₀ : 0 < L := by linarith
  have hw : 0 < w := Real.rpow_pos_of_pos hN₀ _
  have ha : 0 < a := Real.rpow_pos_of_pos hN₀ _
  have hw₁ : w ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN.le (by linarith)
  have hratio : 0 < (a / w) ^ d := Real.rpow_pos_of_pos (div_pos ha hw) _
  have hpow : N ^ (-d * cstar) = (N ^ (d * cstar))⁻¹ := by
    convert Real.rpow_neg hN₀.le (d * cstar) using 1 <;> congr 1 <;> ring
  have hmassCompare : (h * N ^ (-d * cstar) / L) * (ν A).toReal ≤
      h * (ν A).toReal * (η / (K + 1) ^ 2) /
        (13478400 * C * K ^ 6 * (a / w) ^ d) := by
    calc
      _ = h * (ν A).toReal / (L * (a / w) ^ d) := by
        change _ = h * (ν A).toReal / (L * (N ^ (-1 : ℝ) / N ^ (-1 - cstar)) ^ d)
        rw [target_intercept_width_gain hN₀ cstar d, hpow]
        field_simp [hL₀.ne', (Real.rpow_pos_of_pos hN₀ (d * cstar)).ne'] <;> ring
      _ ≤ _ := heavy_mass_envelope hC hK hη hh.le ENNReal.toReal_nonneg hratio hLmass
  have hmassFinal : ENNReal.ofReal (h * N ^ (-d * cstar) / L) * ν A ≤ σ univ := by
    calc
      _ = ENNReal.ofReal ((h * N ^ (-d * cstar) / L) * (ν A).toReal) := by
        rw [ENNReal.ofReal_mul (by positivity : 0 ≤ h * N ^ (-d * cstar) / L),
          ENNReal.ofReal_toReal (measure_ne_top ν A)]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hmassCompare
      _ ≤ _ := hheavy
  have hbaseFinal (q : Fin 2 → ℤ) :
      σ {p | (fun e => (⌊Cons.ubase z h p.1 p.2 e / (N ^ (-Z))⌋ : ℤ)) = q} ≤
        ENNReal.ofReal ((L * h * N ^ (-d * cstar)) * N ^ (-2 * Z)) * ν A := by
    apply (hbaseout q).trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    change 735 * K ^ 2 * h * (N ^ (-Z)) ^ 2 *
      (N ^ (-1 - cstar) / N ^ (-1 : ℝ)) ^ d ≤ _
    rw [normalized_mesh_square hN₀ Z, target_intercept_base_gain hN₀ cstar d]
    convert mul_le_mul_of_nonneg_right hLbase
      (by positivity : 0 ≤ h * N ^ (-d * cstar) * N ^ (-2 * Z)) using 1 <;> ring
  have hpaletteFinal : ∀ r, R⁻¹ ≤ r → r ≤ R →
      (∀ j : ℤ, π {v | (⌊v / (N ^ (-r))⌋ : ℤ) = j} ≤ ENNReal.ofReal (L * N ^ (-S * r))) ∧
      ∀ (q : Fin 3 → ℤ) (j : ℤ),
        σ {p | Cons.physState (N ^ (-B)) p = q ∧ (⌊p.1.2 1 / (N ^ (-r))⌋ : ℤ) = j} ≤
          ENNReal.ofReal L * σ {p | Cons.physState (N ^ (-B)) p = q} *
            π {v | (⌊v / (N ^ (-r))⌋ : ℤ) = j} := by
    intro r hr₀ hr₁
    have hr := compact_exponent_range_mono hR hRR hr₀ hr₁
    refine ⟨?_, ?_⟩
    · intro j
      exact ((hpalette r hr.1 hr.2).1 j).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hLf (Real.rpow_nonneg hN₀.le _)))
    · intro q j
      exact (hpalout r hr.1 hr.2 q j).trans (mul_le_mul'
        (mul_le_mul' (ENNReal.ofReal_le_ofReal hLpalette) le_rfl) le_rfl)
  refine ⟨hA, hνprob, hπprob, ?_, ?_, ?_, hh, hh₁, ?_, ?_, hσμ.trans hμρ,
    ?_, ?_, hmassFinal, hz₀, ?_, ?_, hbaseFinal, hpaletteFinal, hDout, ?_, ?_⟩
  · exact hcoeff.mono (fun l hl e => (hl e).trans hLf)
  · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg hN₀.le _) hHf₀ hLf).trans hlo
  · exact hup.trans (mul_le_mul_of_nonneg_right hLf (Real.rpow_nonneg hN₀.le _))
  · exact (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_left (by positivity) hHf₀ hLf)).trans hpriorlo
  · exact hpriorhi.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hLf (Real.rpow_nonneg hN₀.le _)) hh.le))
  · exact hσμ.trans (hdom.trans (by intro E; exact mul_le_mul' (ENNReal.ofReal_le_ofReal hLf) le_rfl))
  · exact le_antisymm ((hσμ _).trans_eq hsupport) zero_le
  · intro e
    exact (hz e).trans hLf
  · filter_upwards [ae_mono hσμ hbox] with p hp
    intro t ht e
    exact (hp t ht e).trans hLf
  · intro m
    exact (hcout m).trans (by linarith)
  · filter_upwards [hfitout] with p hp
    intro t ht
    exact (hp t ht).trans (mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ L) hw.le)

end
end Submission.Obl.k4_scalar_capped_heavy_potential
