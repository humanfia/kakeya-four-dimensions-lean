-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 334b24fb.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/UniformRawHiddenCaps.lean.
-- Only the namespace and own-module import prefix are changed here.
import Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.PolynomialDensityImage
import Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.CalibratedRawBinCaps
import Submission.Obl.k4_two_velocity_row_list_completion.MeasureTable

/-! Uniform raw-hidden caps from native signal caps. Calibration is applied
to a supposedly excessive raw cell itself, so its original palette factor
cancels in the density-to-mass ratio. The chosen meshes precede the law,
polynomial, hidden endpoint, and all original coefficient-size bounds. -/

namespace Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade

noncomputable section

open MeasureTheory Set MvPolynomial
open scoped ENNReal
open RawBinTranslation
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

/-- Two fixed native cap meshes suffice for one raw cap. Their exponents
are chosen uniformly on the requested range, independently of all original
polynomial coefficients and hidden coordinates. -/
theorem uniform_raw_hidden_cell_cap_from_signal (R : ℝ) (hR : 1 ≤ R) :
    ∃ c A N₀ : ℝ, 0 < c ∧ 1 ≤ A ∧ 2 ≤ N₀ ∧
      ∀ N K r s d : ℝ, N₀ ≤ N → 1 ≤ K → K ≤ N →
        0 ≤ r → r ≤ R → 0 ≤ s → s ≤ R → 0 ≤ d → d ≤ 1 →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
          (x : Ω → Fin 4 → ℝ), Measurable x →
          ∀ P : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 →
          (∀ᵐ p ∂μ, (∀ i : Fin 3, |x p i.castSucc| ≤ K) ∧
            |eval (x p) P| ≤ K ∧ |eval (x p) (pderiv (3 : Fin 4) P)| ≤ K ∧
            |eval (x p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K) →
          ∀ β : ENNReal, β ≠ ⊤ →
          (∀ (q : Fin 3 → ℤ) (j : ℤ),
            μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-c))
                (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊eval (x p) P⌋ = j} ≤
              ENNReal.ofReal (K * (N ^ (-c)) ^ (3 : ℕ)) * β) →
          (∀ (q : Fin 3 → ℤ) (j : ℤ),
            μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh
                (N ^ (-(r + s + 10 * (A + 6) + 10)))
                (fun i : Fin 3 => x p i.castSucc) = q ∧
              ⌊eval (x p) P / N ^ (-s)⌋ = j} ≤
              ENNReal.ofReal (K * N ^ (-3 * (r + s + 10 * (A + 6) + 10) - d * s)) * β) →
          ∀ (q : Fin 3 → ℤ) (j : ℤ),
            μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
                (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊x p 3 / N ^ (-s)⌋ = j} ≤
              ENNReal.ofReal (400 * K ^ 2 * N ^ (-3 * r - d * s)) * β := by
  obtain ⟨c, M, N₀, hc, hM, hN₀, hcal⟩ :=
    polynomial_density_original_grid_calibration (4 * R) (by linarith)
  refine ⟨c, M+3, N₀, hc, by linarith, hN₀, ?_⟩
  intro N K r s d hN hK hKN hr hrR hs hsR hd hd1 Ω _ μ _ x hx P hP hgood β hβ hunit hfine q j
  have hN2 : 2 ≤ N := hN₀.trans hN
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hKpos : 0 < K := by linarith
  have hK0 : 0 ≤ K := hKpos.le
  let Z : Ω → Fin 3 → ℝ := fun p i => x p i.castSucc
  have hZ : Measurable Z := by dsimp [Z]; fun_prop
  by_cases hβ0 : β = 0
  · let record : Ω → (Fin 3 → ℤ) × ℤ := fun p =>
      (Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-c)) (Z p), ⌊eval (x p) P⌋)
    have hzero (p : Ω) : μ {p' | record p' = record p} = 0 := by
      apply le_antisymm ?_ bot_le
      change μ {p' | record p' = record p} ≤ (0 : ENNReal)
      simpa only [record, Prod.mk.injEq, hβ0, mul_zero, Z] using
        hunit (record p).1 (record p).2
    have hpos := Submission.Obl.k4_two_velocity_row_list_completion.ae_record_mass_ne_zero μ record
    have hfalse : ∀ᵐ p ∂μ, False := hpos.mono (fun p hp => hp (hzero p))
    have hμ0 : μ univ = 0 := by simpa using ae_iff.mp hfalse
    have hraw0 := (measure_mono (subset_univ
      {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r)) (Z p) = q ∧
        ⌊x p 3 / N ^ (-s)⌋ = j})).trans_eq hμ0
    simpa only [hβ0, mul_zero] using hraw0
  have hφ : 0 < β.toReal := ENNReal.toReal_pos hβ0 hβ
  have ha : 0 < N ^ (-s) := by positivity
  have ha1 : N ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  let E : Set Ω := {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r)) (Z p) = q ∧
    ⌊x p 3 / N ^ (-s)⌋ = j}
  have hE : MeasurableSet E := by
    have hb : Measurable (fun p => Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r)) (Z p)) :=
      (Submission.Lib.K4AffineMeshCaps.measurable_baseMesh _).comp hZ
    have hh : Measurable (fun p => ⌊x p 3 / N ^ (-s)⌋ : Ω → ℤ) := by fun_prop
    exact (measurableSet_eq_fun hb measurable_const).inter (measurableSet_eq_fun hh measurable_const)
  by_contra hbad
  have hbad' : ENNReal.ofReal (400 * K ^ 2 * N ^ (-3 * r - d * s)) * β < μ E :=
    lt_of_not_ge hbad
  let μE := μ.restrict E
  let m : ℝ := 400 * K ^ 2 * N ^ (-3 * r - d * s) * β.toReal
  let b : ℝ := (4 * K + 2) * K * β.toReal
  have hm : 0 < m := by dsimp [m]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hmENN : ENNReal.ofReal m =
      ENNReal.ofReal (400 * K ^ 2 * N ^ (-3 * r - d * s)) * β := by
    dsimp [m]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hβ]
  have hmass : ENNReal.ofReal m ≤ μE univ := by
    rw [hmENN]
    simpa only [μE, Measure.restrict_apply_univ] using hbad'.le
  have hmass0 : μE univ ≠ 0 := ne_of_gt ((ENNReal.ofReal_pos.mpr hm).trans_le hmass)
  have hratio : b / m ≤ N ^ (4 * R) := by
    have hnum : (4 * K + 2) * K ≤ 400 * K ^ 2 := by nlinarith
    have heq : N ^ (3 * r + d * s) * m = 400 * K ^ 2 * β.toReal := by
      dsimp [m]
      calc
        _ = (400 * K ^ 2 * β.toReal) * (N ^ (3 * r + d * s) * N ^ (-3 * r - d * s)) := by ring
        _ = _ := by rw [← Real.rpow_add hNpos]; norm_num
    have hratio0 : b / m ≤ N ^ (3 * r + d * s) := by
      apply (div_le_iff₀ hm).mpr
      rw [heq]
      exact mul_le_mul_of_nonneg_right hnum hφ.le
    exact hratio0.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by
      have hds : d * s ≤ s := by nlinarith
      linarith))
  have hAE : ∀ᵐ p ∂μE, (∀ i : Fin 3, |x p i.castSucc| ≤ K) ∧
      |eval (x p) P| ≤ K ∧ |eval (x p) (pderiv (3 : Fin 4) P)| ≤ K ∧
      |eval (x p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K := ae_restrict_of_ae hgood
  have hmem : ∀ᵐ p ∂μE, p ∈ E := ae_restrict_mem hE
  have hunitE (q' : Fin 3 → ℤ) (j' : ℤ) :
      μE {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-c)) (Z p) = q' ∧
        ⌊eval (x p) P / 1⌋ = j' ∧ True} ≤
        ENNReal.ofReal ((K * β.toReal) * (N ^ (-c)) ^ (3 : ℕ)) := by
    calc
      _ ≤ μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-c)) (Z p) = q' ∧
          ⌊eval (x p) P⌋ = j'} := by
        simpa only [div_one, and_true] using (Measure.restrict_le_self : μE ≤ μ) _
      _ ≤ ENNReal.ofReal (K * (N ^ (-c)) ^ (3 : ℕ)) * β := hunit q' j'
      _ = _ := by
        conv_lhs => rw [← ENNReal.ofReal_toReal hβ]
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
  have hbasecap (q' : Fin 3 → ℤ) :
      μE {p | (fun i => ⌊Z p i / N ^ (-c)⌋) = q'} ≤
        ENNReal.ofReal (b * (N ^ (-c)) ^ (3 : ℕ)) := by
    have h := Submission.Lib.K4AffineMeshCaps.base_cell_cap_of_bounded_signal μE Z
      (fun p => eval (x p) P) (fun _ => True) (by positivity) (by norm_num : (0 : ℝ) < 1)
      hK0 (by positivity : 0 ≤ K * β.toReal)
      (hAE.mono (fun _ hp _ => hp.2.1)) hunitE q'
    have hcode (p : Ω) : Submission.Lib.K4MovingMeshBoxes.baseMesh (N ^ (-c)) (Z p) =
        (fun i => ⌊Z p i / N ^ (-c)⌋) := rfl
    simpa only [div_one, and_true, b, mul_assoc, Submission.Lib.K4AffineMeshCaps.baseMesh,
      hcode] using h
  let Q := shiftedTest ((j : ℝ) * N ^ (-s)) P
  have hQ : Q.totalDegree ≤ 2 := (shiftedTest_degree _ P).trans hP
  have hdeg0 : (restrictBase Q).totalDegree ≤ 2 := (totalDegree_restrictBase _).trans hQ
  have hdeg1 : (restrictBase (pderiv (3 : Fin 4) Q)).totalDegree ≤ 2 :=
    (totalDegree_restrictBase _).trans
      ((Submission.Lib.K4HiddenQuadratic.totalDegree_pderiv_le_pred Q 3).trans (by omega))
  have hslice : ∀ᵐ p ∂μE,
      |eval (Z p) (restrictBase Q)| ≤ 3 * K ∧
      |eval (Z p) (restrictBase (pderiv (3 : Fin 4) Q))| ≤ 2 * K ∧
      |curvature Q (3 : Fin 4)| ≤ K := by
    filter_upwards [hAE, hmem] with p hp hpm
    exact raw_bin_base_slice_bounds P hP ha ha1 hK0 j (x p) hpm.2
      hp.2.1 hp.2.2.1 hp.2.2.2
  have hG0 : ∀ᵐ p ∂μE, (∀ i, |Z p i| ≤ K) ∧ |eval (Z p) (restrictBase Q)| ≤ 3 * K := by
    filter_upwards [hAE, hslice] with p hp hsp
    exact ⟨hp.1, hsp.1⟩
  have hG1 : ∀ᵐ p ∂μE, (∀ i, |Z p i| ≤ K) ∧
      |eval (Z p) (restrictBase (pderiv (3 : Fin 4) Q))| ≤ 3 * K := by
    filter_upwards [hAE, hslice] with p hp hsp
    exact ⟨hp.1, hsp.2.1.trans (by linarith)⟩
  have hcal0 := hcal N K b m (3*K) hN hK hKN hb hm hratio (by positivity)
    Ω μE Z hZ hmass hbasecap (restrictBase Q) hdeg0 hG0
  have hcal1 := hcal N K b m (3*K) hN hK hKN hb hm hratio (by positivity)
    Ω μE Z hZ hmass hbasecap (restrictBase (pderiv (3 : Fin 4) Q)) hdeg1 hG1
  have h3K : 3 * K ≤ N ^ (3 : ℝ) := by
    have hsq : (3 : ℝ) ≤ N ^ (2 : ℕ) := by nlinarith [sq_nonneg (N-2)]
    calc
      _ ≤ 3 * N := mul_le_mul_of_nonneg_left hKN (by norm_num)
      _ ≤ N ^ (2 : ℕ) * N := mul_le_mul_of_nonneg_right hsq hNpos.le
      _ = _ := by norm_num; ring
  have hscale : N ^ M * (3*K) ≤ N ^ (M+3) := by
    calc
      _ ≤ N ^ M * N ^ (3 : ℝ) := mul_le_mul_of_nonneg_left h3K (by positivity)
      _ = _ := (Real.rpow_add hNpos M 3).symm
  have hcurv : |curvature Q (3 : Fin 4)| ≤ K := by
    by_contra hn
    have hfalse : ∀ᵐ p ∂μE, False := hslice.mono (fun _ hp => hn hp.2.2)
    exact hmass0 (by simpa using ae_iff.mp hfalse)
  have hKN' : K ≤ N ^ (M+3) := hKN.trans (by
    have h := Real.rpow_le_rpow_of_exponent_le hN1 (show (1 : ℝ) ≤ M+3 by linarith)
    simpa only [Real.rpow_one] using h)
  have hgood' : ∀ᵐ p ∂μE,
      (∀ i : Fin 3, |x p i.castSucc| ≤ K) ∧
      Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r)) (Z p) = q ∧
      ⌊x p 3 / N ^ (-s)⌋ = j ∧ |eval (x p) (pderiv (3 : Fin 4) P)| ≤ K ∧
      |eval (x p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K := by
    filter_upwards [hAE, hmem] with p hp hpm
    exact ⟨hp.1, hpm.1, hpm.2, hp.2.2.1, hp.2.2.2⟩
  have hfineE (q' : Fin 3 → ℤ) (j' : ℤ) :
      μE {p | Submission.Lib.K4AffineMeshCaps.baseMesh
          (N ^ (-(r+s+10*((M+3)+6)+10))) (Z p) = q' ∧
        ⌊eval (x p) P / N ^ (-s)⌋ = j'} ≤
        ENNReal.ofReal (K * N ^ (-3*(r+s+10*((M+3)+6)+10)-d*s)) * β :=
    ((Measure.restrict_le_self : μE ≤ μ) _).trans (hfine q' j')
  have hfinal := calibrated_raw_bin_mass_cap μE x P hP hN2 (by linarith : 0 ≤ M+3)
    hr hs hK hKN' q j (fun e => (hcal0 e).trans hscale) (fun e => (hcal1 e).trans hscale)
    (hcurv.trans hKN') hgood' β hβ hfineE
  have hfinal' : μ E ≤ ENNReal.ofReal (400*K^2*N^(-3*r-d*s))*β := by
    simpa only [μE, Measure.restrict_apply_univ] using hfinal
  exact not_lt_of_ge hfinal' hbad'

/-- The two native meshes can be supplied by one larger fixed exponent
window. This is the uniform cap upgrade needed by prepared-model stages. -/
theorem uniform_raw_hidden_caps_from_signal (R : ℝ) (hR : 1 ≤ R) :
    ∃ T N₀ : ℝ, R < T ∧ 1 < T ∧ 2 ≤ N₀ ∧
      ∀ N K d : ℝ, N₀ ≤ N → 1 ≤ K → K ≤ N → 0 ≤ d → d ≤ 1 →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
          (x : Ω → Fin 4 → ℝ), Measurable x →
          ∀ P : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 →
          (∀ᵐ p ∂μ, (∀ i : Fin 3, |x p i.castSucc| ≤ K) ∧
            |eval (x p) P| ≤ K ∧ |eval (x p) (pderiv (3 : Fin 4) P)| ≤ K ∧
            |eval (x p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K) →
          ∀ β : ENNReal, β ≠ ⊤ →
          (∀ u t : ℝ, T⁻¹ ≤ u → u ≤ T → 0 ≤ t → t ≤ T →
            ∀ (q : Fin 3 → ℤ) (j : ℤ),
              μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-u))
                  (fun i : Fin 3 => x p i.castSucc) = q ∧
                ⌊eval (x p) P / N ^ (-t)⌋ = j} ≤
                ENNReal.ofReal (K * N ^ (-3 * u - d * t)) * β) →
          ∀ r s : ℝ, 0 ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
            ∀ (q : Fin 3 → ℤ) (j : ℤ),
              μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
                  (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊x p 3 / N ^ (-s)⌋ = j} ≤
                ENNReal.ofReal (400 * K ^ 2 * N ^ (-3 * r - d * s)) * β := by
  obtain ⟨c, A, N₀, hc, hA, hN₀, hraw⟩ := uniform_raw_hidden_cell_cap_from_signal R hR
  let T := 2*R + c + c⁻¹ + 10*A + 100
  have hcInv : 0 < c⁻¹ := inv_pos.mpr hc
  have hRT : R < T := by dsimp [T]; linarith
  have hT : 1 < T := by linarith
  have hcT : c ≤ T := by dsimp [T]; linarith
  have hcInvT : c⁻¹ ≤ T := by dsimp [T]; linarith
  have hTc : T⁻¹ ≤ c := by
    simpa only [inv_inv] using inv_anti₀ hcInv hcInvT
  refine ⟨T, N₀, hRT, hT, hN₀, ?_⟩
  intro N K d hN hK hKN hd hd1 Ω _ μ _ x hx P hP hgood β hβ hcap r s hr hrR hs hsR q j
  have hNpos : 0 < N := by linarith [hN₀.trans hN]
  have hunit (q' : Fin 3 → ℤ) (j' : ℤ) :
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-c))
          (fun i : Fin 3 => x p i.castSucc) = q' ∧ ⌊eval (x p) P⌋ = j'} ≤
        ENNReal.ofReal (K * (N ^ (-c)) ^ (3 : ℕ)) * β := by
    have h := hcap c 0 hTc hcT le_rfl (by linarith) q' j'
    have hmesh : (N ^ (-c)) ^ (3 : ℕ) = N ^ (-3*c) := by
      rw [← Real.rpow_mul_natCast hNpos.le]
      congr 1
      ring
    simpa only [neg_zero, Real.rpow_zero, div_one, mul_zero, sub_zero, hmesh] using h
  have hfineLo : T⁻¹ ≤ r+s+10*(A+6)+10 := by
    have hInv : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT.le
    linarith
  have hfineHi : r+s+10*(A+6)+10 ≤ T := by dsimp [T]; linarith
  apply hraw N K r s d hN hK hKN hr hrR hs hsR hd hd1 Ω μ x hx P hP hgood β hβ hunit ?_ q j
  exact hcap (r+s+10*(A+6)+10) s hfineLo hfineHi hs (hsR.trans hRT.le)

end

end Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade
