-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 334b24fb.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/RawHiddenSignalCaps.lean.
-- Only the namespace and own-module import prefix are changed here.
import Submission.Lib.K4AffineMeshCaps.Transport
import Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.QuadraticSignalOscillation

/-! Native signal caps transfer to raw hidden cells after resolving the
signal on a sufficiently fine base grid. The original palette factor is
retained; no number of occupied raw hidden cells enters the estimate. -/

namespace Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade

noncomputable section

open MeasureTheory Set
open scoped ENNReal

/-- A raw hidden cell has a bounded list of signal bins over each fine base
cell when the signal oscillates by at most `D*a` there. Summation over fine
base cells then costs only a fixed enlargement of the coarse base cell. -/
theorem raw_hidden_cell_cap_of_signal_oscillation
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (hidden signal : Ω → ℝ)
    (condition : Ω → Prop) {fine coarse a C D : ℝ}
    (hfine : 0 < fine) (hcoarse : 0 < coarse) (ha : 0 < a)
    (hfc : fine ≤ coarse) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (β : ENNReal) (hβ : β ≠ ⊤)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh fine (Z p) = q ∧
        ⌊signal p / a⌋ = j ∧ condition p} ≤ ENNReal.ofReal (C * fine ^ 3) * β)
    (hosc : ∀ p p', condition p → condition p' →
      (∀ i, |Z p i - Z p' i| ≤ fine) → |hidden p - hidden p'| ≤ a →
      |signal p - signal p'| ≤ D * a)
    (q : Fin 3 → ℤ) (j : ℤ) :
    μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh coarse (Z p) = q ∧
      ⌊hidden p / a⌋ = j ∧ condition p} ≤
      ENNReal.ofReal (27 * (4 * D + 2) * C * coarse ^ 3) * β := by
  classical
  have hratio : 0 ≤ 4 * D + 2 := by positivity
  have hlocal (q' : Fin 3 → ℤ) :
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh fine (Z p) = q' ∧
        ⌊hidden p / a⌋ = j ∧ condition p} ≤
      ENNReal.ofReal (((4 * D + 2) * C * β.toReal) * fine ^ 3) := by
    by_cases hex : ∃ p, Submission.Lib.K4AffineMeshCaps.baseMesh fine (Z p) = q' ∧
        ⌊hidden p / a⌋ = j ∧ condition p
    · obtain ⟨p₀, hp₀⟩ := hex
      obtain ⟨J, hJ, hcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover
        ha (mul_nonneg hD ha.le) (signal p₀)
      have hJ' : (J.card : ℝ) ≤ 4 * D + 2 := by
        convert hJ using 1 <;> field_simp
      have hsub : {p | Submission.Lib.K4AffineMeshCaps.baseMesh fine (Z p) = q' ∧
          ⌊hidden p / a⌋ = j ∧ condition p} ⊆
          ⋃ z ∈ J, {p | Submission.Lib.K4AffineMeshCaps.baseMesh fine (Z p) = q' ∧
            ⌊signal p / a⌋ = z ∧ condition p} := by
        intro p hp
        have hdist (i : Fin 3) : |Z p i - Z p₀ i| ≤ fine :=
          Submission.Lib.K4AffineMeshCaps.meshBox_coordinate_distance hfine hp.1 hp₀.1 i
        have hh : |hidden p - hidden p₀| ≤ a := by
          have hpj := Int.floor_eq_iff.mp hp.2.1
          have hqj := Int.floor_eq_iff.mp hp₀.2.1
          rw [le_div_iff₀ ha, div_lt_iff₀ ha] at hpj hqj
          rw [abs_le]
          constructor <;> linarith
        exact mem_iUnion.mpr ⟨⌊signal p / a⌋, mem_iUnion.mpr
          ⟨hcover _ (hosc p p₀ hp.2.2 hp₀.2.2 hdist hh), hp.1, rfl, hp.2.2⟩⟩
      calc
        _ ≤ μ (⋃ z ∈ J, {p | Submission.Lib.K4AffineMeshCaps.baseMesh fine (Z p) = q' ∧
            ⌊signal p / a⌋ = z ∧ condition p}) := measure_mono hsub
        _ ≤ ∑ z ∈ J, μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh fine (Z p) = q' ∧
            ⌊signal p / a⌋ = z ∧ condition p} := measure_biUnion_finset_le J _
        _ ≤ ∑ _z ∈ J, ENNReal.ofReal (C * fine ^ 3) * β :=
          Finset.sum_le_sum (fun z _ => hcap q' z)
        _ = ENNReal.ofReal ((J.card : ℝ) * C * fine ^ 3 * β.toReal) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast]
          calc
            _ = ENNReal.ofReal (J.card : ℝ) *
                (ENNReal.ofReal (C * fine ^ 3) * ENNReal.ofReal β.toReal) := by
              rw [ENNReal.ofReal_toReal hβ]
            _ = _ := by
              rw [← ENNReal.ofReal_mul (by positivity),
                ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
              congr 1
              ring
        _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          calc
            _ ≤ (4 * D + 2) * C * fine ^ 3 * β.toReal := by gcongr
            _ = _ := by ring
    · have hz : {p | Submission.Lib.K4AffineMeshCaps.baseMesh fine (Z p) = q' ∧
          ⌊hidden p / a⌋ = j ∧ condition p} = ∅ := by
        ext p
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun hp => hex ⟨p, hp⟩
      rw [hz, measure_empty]
      exact bot_le
  have hresolve (i : Fin 3) :
      (∑ z : Fin 3, |(1 : Matrix (Fin 3) (Fin 3) ℝ) i z| * fine) ≤ coarse := by
    have hterm (z : Fin 3) : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i z| * fine =
        if z = i then fine else 0 := by
      by_cases hz : z = i
      · subst z
        simp
      · simp [hz, Ne.symm hz]
    simp_rw [hterm]
    simpa using hfc
  have h := Submission.Lib.K4AffineMeshCaps.affine_mesh_cell_cap μ Z
    (fun p => ⌊hidden p / a⌋ = j ∧ condition p)
    (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 (by simp) hfine hcoarse
    (by positivity : 0 ≤ (4 * D + 2) * C * β.toReal) hresolve hlocal q
  have heq : Submission.Lib.K4AffineMeshCaps.affineBase
      (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 = id := by
    funext z
    simp [Submission.Lib.K4AffineMeshCaps.affineBase]
  have hnum : ENNReal.ofReal (27 * ((4 * D + 2) * C * β.toReal) * coarse ^ 3) =
      ENNReal.ofReal (27 * (4 * D + 2) * C * coarse ^ 3) * β := by
    rw [show 27 * ((4 * D + 2) * C * β.toReal) * coarse ^ 3 =
      (27 * (4 * D + 2) * C * coarse ^ 3) * β.toReal by ring,
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hβ]
  simpa only [heq, id_eq, Matrix.det_one, abs_one, inv_one, mul_one, hnum] using h

/-- Actual quadratic native signals satisfy the oscillation condition at
any base mesh resolving their coefficient and coordinate bounds. The
original extra condition can be a velocity bin, whose palette factor is
preserved exactly. -/
theorem raw_hidden_cell_cap_of_quadratic_signal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Ω → Fin 4 → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (condition : Ω → Prop)
    {fine coarse a C A R K : ℝ}
    (hfine : 0 < fine) (hcoarse : 0 < coarse) (ha : 0 < a) (ha1 : a ≤ 1)
    (hfc : fine ≤ coarse) (hC : 0 ≤ C) (hA : 0 ≤ A) (hR : 1 ≤ R) (hK : 0 ≤ K)
    (hcoeff : ∀ e, |P.coeff e| ≤ A)
    (hresolve : 648 * A * R ^ 9 * fine ≤ a)
    (hgood : ∀ᵐ p ∂μ, (∀ i, |x p i| ≤ R) ∧
      |MvPolynomial.eval (x p) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K ∧
      |MvPolynomial.eval (x p) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K)
    (β : ENNReal) (hβ : β ≠ ⊤)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh fine
          (fun i : Fin 3 => x p i.castSucc) = q ∧
        ⌊MvPolynomial.eval (x p) P / a⌋ = j ∧ condition p} ≤
        ENNReal.ofReal (C * fine ^ 3) * β)
    (q : Fin 3 → ℤ) (j : ℤ) :
    μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh coarse
        (fun i : Fin 3 => x p i.castSucc) = q ∧
      ⌊x p 3 / a⌋ = j ∧ condition p} ≤
      ENNReal.ofReal (27 * (8 * K + 6) * C * coarse ^ 3) * β := by
  let good : Ω → Prop := fun p => (∀ i, |x p i| ≤ R) ∧
    |MvPolynomial.eval (x p) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K ∧
    |MvPolynomial.eval (x p) (MvPolynomial.pderiv (3 : Fin 4)
      (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K
  have heq : μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh coarse
        (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊x p 3 / a⌋ = j ∧ condition p} =
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh coarse
        (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊x p 3 / a⌋ = j ∧
        (condition p ∧ good p)} := by
    apply measure_congr
    filter_upwards [hgood] with p hp
    simp only [show good p from hp, and_true]
  rw [heq]
  have hcap' (q' : Fin 3 → ℤ) (j' : ℤ) :
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh fine
          (fun i : Fin 3 => x p i.castSucc) = q' ∧
        ⌊MvPolynomial.eval (x p) P / a⌋ = j' ∧ (condition p ∧ good p)} ≤
        ENNReal.ofReal (C * fine ^ 3) * β := by
    apply (measure_mono ?_).trans (hcap q' j')
    intro p hp
    exact ⟨hp.1, hp.2.1, hp.2.2.1⟩
  have hosc (p p' : Ω) (hp : condition p ∧ good p) (hp' : condition p' ∧ good p')
      (hb : ∀ i : Fin 3, |x p i.castSucc - x p' i.castSucc| ≤ fine)
      (hh : |x p 3 - x p' 3| ≤ a) :
      |MvPolynomial.eval (x p) P - MvPolynomial.eval (x p') P| ≤ (2 * K + 1) * a :=
    quadratic_signal_oscillation P hP hA hR hK hfine.le ha.le ha1 hcoeff hresolve
      (x p) (x p') hp.2.1 hp'.2.1 hb hh hp.2.2.1 hp.2.2.2
  have h := raw_hidden_cell_cap_of_signal_oscillation μ
    (fun p => fun i : Fin 3 => x p i.castSucc) (fun p => x p 3)
    (fun p => MvPolynomial.eval (x p) P) (fun p => condition p ∧ good p)
    hfine hcoarse ha hfc hC (by positivity : 0 ≤ 2 * K + 1) β hβ hcap' hosc q j
  convert h using 1
  congr 3
  ring

/-- In power meshes, polynomial growth shifts the base exponent by the
fixed amount `s+10*M+10`. The cap loss is only `400*K^2`; its original
palette factor is unchanged. -/
theorem raw_hidden_power_cell_cap_of_native_signal
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x : Ω → Fin 4 → ℝ) (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (condition : Ω → Prop)
    {N M r s d K : ℝ} (hN : 2 ≤ N) (hM : 0 ≤ M)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hcoeff : ∀ e, |P.coeff e| ≤ N ^ M)
    (hgood : ∀ᵐ p ∂μ, (∀ i, |x p i| ≤ N ^ M) ∧
      |MvPolynomial.eval (x p) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K ∧
      |MvPolynomial.eval (x p) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K)
    (β : ENNReal) (hβ : β ≠ ⊤)
    (hcap : ∀ (q : Fin 3 → ℤ) (j : ℤ),
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh
          (N ^ (-(r + s + 10 * M + 10))) (fun i : Fin 3 => x p i.castSucc) = q ∧
        ⌊MvPolynomial.eval (x p) P / N ^ (-s)⌋ = j ∧ condition p} ≤
        ENNReal.ofReal (K * N ^ (-3 * (r + s + 10 * M + 10) - d * s)) * β)
    (q : Fin 3 → ℤ) (j : ℤ) :
    μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
        (fun i : Fin 3 => x p i.castSucc) = q ∧
      ⌊x p 3 / N ^ (-s)⌋ = j ∧ condition p} ≤
      ENNReal.ofReal (400 * K ^ 2 * N ^ (-3 * r - d * s)) * β := by
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hK0 : 0 ≤ K := by linarith
  obtain ⟨hfine, hfc, hresolve⟩ := quadratic_signal_mesh_resolution hN hM hr hs
  have hmesh (u : ℝ) : N ^ (-d * s) * (N ^ (-u)) ^ (3 : ℕ) =
      N ^ (-3 * u - d * s) := by
    rw [← Real.rpow_mul_natCast hNpos.le, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hcap' (q' : Fin 3 → ℤ) (j' : ℤ) :
      μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh
          (N ^ (-(r + s + 10 * M + 10))) (fun i : Fin 3 => x p i.castSucc) = q' ∧
        ⌊MvPolynomial.eval (x p) P / N ^ (-s)⌋ = j' ∧ condition p} ≤
        ENNReal.ofReal ((K * N ^ (-d * s)) *
          (N ^ (-(r + s + 10 * M + 10))) ^ (3 : ℕ)) * β := by
    simpa only [mul_assoc, hmesh] using hcap q' j'
  have h := raw_hidden_cell_cap_of_quadratic_signal μ x P hP condition hfine
    (by positivity) (by positivity)
    (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)) hfc
    (by positivity) (by positivity) (Real.one_le_rpow hN1 hM) hK0
    hcoeff hresolve hgood β hβ hcap' q j
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  have hcost : 27 * (8 * K + 6) * K ≤ 400 * K ^ 2 := by nlinarith
  calc
    _ = (27 * (8 * K + 6) * K) * N ^ (-3 * r - d * s) := by
      rw [← hmesh r]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hcost (by positivity)

/-- The fixed exponent shift is harmless in an eventual cap interface:
request the native cap on one larger bounded exponent interval. -/
theorem eventually_raw_hidden_caps_of_native_signal
    {Ω : Type*} [MeasurableSpace Ω]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hK : ∀ k, 1 ≤ K k)
    (μ : ℕ → Measure Ω) (x : ℕ → Ω → Fin 4 → ℝ)
    (P : ℕ → MvPolynomial (Fin 4) ℝ) (hP : ∀ k, (P k).totalDegree ≤ 2)
    (M d : ℝ) (hM : 0 ≤ M)
    (hcoeff : ∀ᶠ k in Filter.atTop, ∀ e, |(P k).coeff e| ≤ N k ^ M)
    (hgood : ∀ᶠ k in Filter.atTop, ∀ᵐ p ∂μ k,
      (∀ i, |x k p i| ≤ N k ^ M) ∧
      |MvPolynomial.eval (x k p) (MvPolynomial.pderiv (3 : Fin 4) (P k))| ≤ K k ∧
      |MvPolynomial.eval (x k p) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) (P k)))| ≤ K k)
    (condition : ℕ → ℝ → ℤ → Ω → Prop) (β : ℕ → ℝ → ℤ → ENNReal)
    (hβ : ∀ k v z, β k v z ≠ ⊤)
    (hcap : ∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop,
      ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
      ∀ (q : Fin 3 → ℤ) (j z : ℤ),
        μ k {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N k ^ (-r))
            (fun i : Fin 3 => x k p i.castSucc) = q ∧
          ⌊MvPolynomial.eval (x k p) (P k) / N k ^ (-s)⌋ = j ∧ condition k v z p} ≤
          ENNReal.ofReal (K k * N k ^ (-3 * r - d * s)) * β k v z) :
    ∀ R : ℝ, 1 < R → ∀ᶠ k in Filter.atTop,
      ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
      ∀ (q : Fin 3 → ℤ) (j z : ℤ),
        μ k {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N k ^ (-r))
            (fun i : Fin 3 => x k p i.castSucc) = q ∧
          ⌊x k p 3 / N k ^ (-s)⌋ = j ∧ condition k v z p} ≤
          ENNReal.ofReal (400 * K k ^ 2 * N k ^ (-3 * r - d * s)) * β k v z := by
  intro R hR
  let R' := 2 * R + 10 * M + 11
  have hR' : 1 < R' := by dsimp [R']; linarith
  have hRR' : R ≤ R' := by dsimp [R']; linarith
  have hR0 : 0 < R := by linarith
  have hInv : R'⁻¹ ≤ R⁻¹ := inv_anti₀ hR0 hRR'
  filter_upwards [hcap R' hR', hcoeff, hgood] with k hk hck hgk
  intro r s v hrl hrh hs0 hsh hvl hvh q j z
  have hr0 : 0 ≤ r := (inv_pos.mpr hR0).le.trans hrl
  have hr'lo : R'⁻¹ ≤ r + s + 10 * M + 10 := by
    have hi : R'⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hR'.le
    linarith
  have hr'hi : r + s + 10 * M + 10 ≤ R' := by dsimp [R']; linarith
  apply raw_hidden_power_cell_cap_of_native_signal (μ k) (x k) (P k) (hP k)
    (condition k v z) (hN k) hM hr0 hs0 (hK k) hck hgk (β k v z) (hβ k v z) ?_ q j
  intro q' j'
  exact hk (r+s+10*M+10) s v hr'lo hr'hi hs0 (hsh.trans hRR')
    (hInv.trans hvl) (hvh.trans hRR') q' j' z

end

end Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade
