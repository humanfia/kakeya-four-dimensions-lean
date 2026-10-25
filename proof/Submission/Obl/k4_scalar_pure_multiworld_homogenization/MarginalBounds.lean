import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Observation
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Straddling

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction Submission.Lib.K4MarginalAveraging

abbrev box (n : ℕ) (R : ℝ) : Set (Fin n → ℝ) :=
  Icc (fun _ => -R) (fun _ => R)

theorem volume_box (n : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume (box n R) = ENNReal.ofReal ((2 * R) ^ n) := by
  simp only [box, Real.volume_Icc_pi, sub_neg_eq_add, ← two_mul,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact (ENNReal.ofReal_pow (by positivity) n).symm

@[simp] theorem join_base (b : Fin 2 → ℝ) (v : Fin 4 → ℝ) (i : Fin 2) :
    join (b, v) (Fin.castAdd 4 i) = b i := by fin_cases i <;> rfl

@[simp] theorem join_fibre (b : Fin 2 → ℝ) (v : Fin 4 → ℝ) (i : Fin 4) :
    join (b, v) (Fin.natAdd 2 i) = v i := by fin_cases i <;> rfl

theorem nonzero_mem_box {f : (Fin 6 → ℝ) → ℝ} {R : ℝ}
    (hs : supportedInCube f R) {z : Fin 6 → ℝ} (hz : f z ≠ 0) : z ∈ box 6 R := by
  constructor <;> intro i
  · have hi : |z i| ≤ R := le_of_not_gt (fun hi => hz (hs z i hi))
    exact (abs_le.mp hi).1
  · have hi : |z i| ≤ R := le_of_not_gt (fun hi => hz (hs z i hi))
    exact (abs_le.mp hi).2

theorem joined_fibre_zero {f : (Fin 6 → ℝ) → ℝ} {R : ℝ}
    (hs : supportedInCube f R) {v : Fin 4 → ℝ} (hv : v ∉ box 4 R) (b : Fin 2 → ℝ) :
    f (join (b, v)) = 0 := by
  by_contra hz
  have hbox := nonzero_mem_box hs hz
  apply hv
  constructor <;> intro i
  · simpa only [join_fibre] using hbox.1 (Fin.natAdd 2 i)
  · simpa only [join_fibre] using hbox.2 (Fin.natAdd 2 i)

theorem marginal_bound (a : ℝ) {f : (Fin 6 → ℝ) → ℝ} {R M : ℝ}
    (hR : 0 ≤ R) (hM : 0 ≤ M) (hs : supportedInCube f R) (hb : ∀ z, f z ≤ M)
    (z : Observation) : marginal a f z ≤ ENNReal.ofReal (M * (2 * R) ^ 4) := by
  have h := countedMarginal_le_of_support (volume : Measure (Fin 4 → ℝ))
    (fun v b => ENNReal.ofReal (f (join (b, v)))) (fibreLabel a) (box 4 R)
    measurableSet_Icc (ENNReal.ofReal M)
    (fun v _ b => ENNReal.ofReal_le_ofReal (hb _))
    (fun v hv b => by rw [joined_fibre_zero hs hv b, ENNReal.ofReal_zero]) z
  calc
    marginal a f z ≤ ENNReal.ofReal M * volume (box 4 R) := h
    _ = _ := by rw [volume_box 4 hR, ENNReal.ofReal_mul hM]

theorem marginal_support {a R : ℝ} (ha : 0 < a)
    {f : (Fin 6 → ℝ) → ℝ} (hs : supportedInCube f R) :
    {z | marginal a f z ≠ 0} ⊆ box 2 R ×ˢ
      (Submission.Obl.k4_native_base_flattening.cubeBins R a : Set ℤ) := by
  classical
  intro z hz
  constructor
  · by_contra hb
    have hzero (v : Fin 4 → ℝ) : f (join (z.1, v)) = 0 := by
      by_contra hn
      have hm := nonzero_mem_box hs hn
      apply hb
      constructor <;> intro i
      · simpa only [join_base] using hm.1 (Fin.castAdd 4 i)
      · simpa only [join_base] using hm.2 (Fin.castAdd 4 i)
    apply hz
    simp [marginal, countedMarginal, hzero]
  · by_contra hbin
    apply hz
    unfold marginal countedMarginal
    calc
      _ = ∫⁻ _v : Fin 4 → ℝ, (0 : ENNReal) := by
        apply lintegral_congr
        intro v
        dsimp
        split_ifs with hlabel
        · have hv : R < |v 1| := by
            apply lt_of_not_ge
            intro hv
            apply hbin
            have hh := Submission.Obl.k4_native_base_flattening.mem_cubeBins ha hv
            exact hlabel ▸ hh
          have hzero : f (join (z.1, v)) = 0 := hs _ 3 hv
          simp only [hzero, ENNReal.ofReal_zero]
        · rfl
      _ = 0 := by simp

theorem reference_marginal_support_bound {a R : ℝ} (ha : 0 < a) (hR : 0 ≤ R)
    {f : (Fin 6 → ℝ) → ℝ} (hs : supportedInCube f R) :
    reference {z | marginal a f z ≠ 0} ≤
      ENNReal.ofReal ((2 * R) ^ 2 * (2 * R / a + 5)) := by
  calc
    _ ≤ reference (box 2 R ×ˢ
        (Submission.Obl.k4_native_base_flattening.cubeBins R a : Set ℤ)) :=
      measure_mono (marginal_support ha hs)
    _ = volume (box 2 R) *
        (Submission.Obl.k4_native_base_flattening.cubeBins R a).card := by
      rw [Measure.prod_prod, Measure.count_apply_finset]
    _ ≤ ENNReal.ofReal ((2 * R) ^ 2) * ENNReal.ofReal (2 * R / a + 5) := by
      rw [volume_box 2 hR]
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal
        (Submission.Obl.k4_native_base_flattening.card_cubeBins_le hR ha)
    _ = _ := (ENNReal.ofReal_mul (by positivity)).symm

theorem withDensity_le_cube {f : (Fin 6 → ℝ) → ℝ} {R M : ℝ}
    (hs : supportedInCube f R) (hb : ∀ z, f z ≤ M) :
    volume.withDensity (fun z => ENNReal.ofReal (f z)) ≤
      ENNReal.ofReal M • (volume : Measure (Fin 6 → ℝ)).restrict (box 6 R) := by
  calc
    _ ≤ volume.withDensity ((box 6 R).indicator (fun _ => ENNReal.ofReal M)) := by
      apply withDensity_mono
      apply Filter.Eventually.of_forall
      intro z
      by_cases hz : z ∈ box 6 R
      · rw [indicator_of_mem hz]
        exact ENNReal.ofReal_le_ofReal (hb z)
      · rw [indicator_of_notMem hz]
        have hfz : f z = 0 := by
          by_contra hn
          exact hz (nonzero_mem_box hs hn)
        simp only [hfz, ENNReal.ofReal_zero, le_refl]
    _ = _ := by rw [withDensity_indicator measurableSet_Icc, withDensity_const]

theorem source_straddling_bound {μ : Measure Incidence} {f : (Fin 6 → ℝ) → ℝ}
    (hsource : μ.map chartPoint = volume.withDensity (fun z => ENNReal.ofReal (f z)))
    {R M σ a : ℝ} (hR : 0 ≤ R) (hσ : 0 < σ) (ha : 0 < a)
    (hs : supportedInCube f R) (hb : ∀ z, f z ≤ M) :
    μ {z | x z.1 z.2 ∈ straddles σ a} ≤
      ENNReal.ofReal M * ENNReal.ofReal ((2 * R / a + 5) * (2 * σ * (2 * R) ^ 5)) := by
  have hm : MeasurableSet {z : Fin 6 → ℝ | z 3 ∈ straddles σ a} := by
    unfold straddles meshLeft
    exact (measurableSet_eq_fun (by fun_prop) (by fun_prop)).compl
  have heq : {z : Incidence | x z.1 z.2 ∈ straddles σ a} =
      chartPoint ⁻¹' {z : Fin 6 → ℝ | z 3 ∈ straddles σ a} := rfl
  rw [heq, ← Measure.map_apply measurable_chartPoint hm, hsource]
  calc
    _ ≤ (ENNReal.ofReal M • (volume : Measure (Fin 6 → ℝ)).restrict (box 6 R))
        {z | z 3 ∈ straddles σ a} := withDensity_le_cube hs hb _
    _ = ENNReal.ofReal M * volume
        {z : Fin 6 → ℝ | (∀ i, |z i| ≤ R) ∧ z 3 ∈ straddles σ a} := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hm]
      congr 1
      apply congrArg (fun S : Set (Fin 6 → ℝ) => volume S)
      ext z
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Icc, Pi.le_def, ← forall_and, ← abs_le]
      tauto
    _ ≤ _ := mul_le_mul' le_rfl (volume_straddling_cube hR hσ ha)

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
