-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
-- Adapted from this LOT tree, o107, session x0735, commit 334b24fb.
-- Source: Submission/Obl/k4_finite_narrowness_path_improvement/ConditionalRawHiddenCaps.lean.
-- Only the namespace and own-module import prefix are changed here.
import Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade.UniformRawHiddenCaps

/-! Extra original events, including velocity bins, survive the uniform
signal-to-raw cap upgrade with their original palette factor unchanged. -/

namespace Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade

noncomputable section

open MeasureTheory Set MvPolynomial Filter
open scoped ENNReal

/-- Apply the raw-cap upgrade to an unnormalized original event. The
exponent window is chosen before the event and its palette mass. -/
theorem uniform_conditional_raw_hidden_caps_from_signal (R : ℝ) (hR : 1 ≤ R) :
    ∃ T N₀ : ℝ, R < T ∧ 1 < T ∧ 2 ≤ N₀ ∧
      ∀ N K d : ℝ, N₀ ≤ N → 1 ≤ K → K ≤ N → 0 ≤ d → d ≤ 1 →
        ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
          (x : Ω → Fin 4 → ℝ), Measurable x →
          ∀ P : MvPolynomial (Fin 4) ℝ, P.totalDegree ≤ 2 →
          (∀ᵐ p ∂μ, (∀ i : Fin 3, |x p i.castSucc| ≤ K) ∧
            |eval (x p) P| ≤ K ∧ |eval (x p) (pderiv (3 : Fin 4) P)| ≤ K ∧
            |eval (x p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K) →
          ∀ (C : Set Ω) (β : ENNReal), β ≠ ⊤ →
          (∀ u t : ℝ, T⁻¹ ≤ u → u ≤ T → 0 ≤ t → t ≤ T →
            ∀ (q : Fin 3 → ℤ) (j : ℤ),
              μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-u))
                  (fun i : Fin 3 => x p i.castSucc) = q ∧
                ⌊eval (x p) P / N ^ (-t)⌋ = j ∧ p ∈ C} ≤
                ENNReal.ofReal (K * N ^ (-3*u-d*t)) * β) →
          ∀ r s : ℝ, 0 ≤ r → r ≤ R → 0 ≤ s → s ≤ R →
            ∀ (q : Fin 3 → ℤ) (j : ℤ),
              μ {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
                  (fun i : Fin 3 => x p i.castSucc) = q ∧
                ⌊x p 3 / N ^ (-s)⌋ = j ∧ p ∈ C} ≤
                ENNReal.ofReal (400*K^2*N^(-3*r-d*s)) * β := by
  obtain ⟨T,N₀,hRT,hT,hN₀,hraw⟩ := uniform_raw_hidden_caps_from_signal R hR
  refine ⟨T,N₀,hRT,hT,hN₀,?_⟩
  intro N K d hN hK hKN hd hd1 Ω _ μ _ x hx P hP hgood C β hβ hcap r s hr hrR hs hsR q j
  have hmBase (u : ℝ) : Measurable (fun p =>
      Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-u)) (fun i : Fin 3 => x p i.castSucc)) := by
    apply (Submission.Lib.K4AffineMeshCaps.measurable_baseMesh _).comp
    fun_prop
  have hEval : Measurable (fun p => eval (x p) P) := P.continuous_eval.measurable.comp hx
  have hmSignal (t : ℝ) : Measurable (fun p => ⌊eval (x p) P / N ^ (-t)⌋ : Ω → ℤ) := by
    fun_prop
  have hnative (u t : ℝ) (hu₀ : T⁻¹ ≤ u) (hu₁ : u ≤ T) (ht₀ : 0 ≤ t) (ht₁ : t ≤ T)
      (q' : Fin 3 → ℤ) (j' : ℤ) :
      μ.restrict C {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-u))
          (fun i : Fin 3 => x p i.castSucc) = q' ∧ ⌊eval (x p) P / N ^ (-t)⌋ = j'} ≤
        ENNReal.ofReal (K * N ^ (-3*u-d*t)) * β := by
    have he : MeasurableSet {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-u))
        (fun i : Fin 3 => x p i.castSucc) = q' ∧ ⌊eval (x p) P / N ^ (-t)⌋ = j'} :=
      (measurableSet_eq_fun (hmBase u) measurable_const).inter
        (measurableSet_eq_fun (hmSignal t) measurable_const)
    rw [Measure.restrict_apply he]
    have hset : {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-u))
          (fun i : Fin 3 => x p i.castSucc) = q' ∧ ⌊eval (x p) P / N ^ (-t)⌋ = j'} ∩ C =
        {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-u))
          (fun i : Fin 3 => x p i.castSucc) = q' ∧ ⌊eval (x p) P / N ^ (-t)⌋ = j' ∧ p ∈ C} := by
      ext p
      simp only [mem_inter_iff, mem_ofPred_eq, and_assoc]
    rw [hset]
    exact hcap u t hu₀ hu₁ ht₀ ht₁ q' j'
  have h := hraw N K d hN hK hKN hd hd1 Ω (μ.restrict C) x hx P hP
    (ae_restrict_of_ae hgood) β hβ hnative r s hr hrR hs hsR q j
  have he : MeasurableSet {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
      (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊x p 3 / N ^ (-s)⌋ = j} := by
    apply (measurableSet_eq_fun (hmBase r) measurable_const).inter
    apply measurableSet_eq_fun _ measurable_const
    fun_prop
  rw [Measure.restrict_apply he] at h
  have hset : {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
        (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊x p 3 / N ^ (-s)⌋ = j} ∩ C =
      {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N ^ (-r))
        (fun i : Fin 3 => x p i.castSucc) = q ∧ ⌊x p 3 / N ^ (-s)⌋ = j ∧ p ∈ C} := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, and_assoc]
  rwa [hset] at h

/-- One larger native exponent window gives all eventual raw caps, even
when the original auxiliary event and palette bin vary with the index. -/
theorem eventually_conditional_raw_hidden_caps_from_signal
    {Ω : Type*} [MeasurableSpace Ω]
    (N K : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hK : ∀ k, 1 ≤ K k)
    (hNlim : Tendsto N atTop atTop) (hKN : ∀ᶠ k in atTop, K k ≤ N k)
    (μ : ℕ → Measure Ω) [∀ k, IsFiniteMeasure (μ k)]
    (x : ℕ → Ω → Fin 4 → ℝ) (hx : ∀ k, Measurable (x k))
    (P : ℕ → MvPolynomial (Fin 4) ℝ) (hP : ∀ k, (P k).totalDegree ≤ 2)
    (d : ℝ) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hgood : ∀ k, ∀ᵐ p ∂μ k, (∀ i : Fin 3, |x k p i.castSucc| ≤ K k) ∧
      |eval (x k p) (P k)| ≤ K k ∧ |eval (x k p) (pderiv (3 : Fin 4) (P k))| ≤ K k ∧
      |eval (x k p) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (P k)))| ≤ K k)
    (C : ℕ → ℝ → ℤ → Set Ω) (β : ℕ → ℝ → ℤ → ENNReal)
    (hβ : ∀ k v z, β k v z ≠ ⊤)
    (hcap : ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop,
      ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
      ∀ (q : Fin 3 → ℤ) (j z : ℤ),
        μ k {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N k ^ (-r))
            (fun i : Fin 3 => x k p i.castSucc) = q ∧
          ⌊eval (x k p) (P k) / N k ^ (-s)⌋ = j ∧ p ∈ C k v z} ≤
          ENNReal.ofReal (K k * N k ^ (-3*r-d*s)) * β k v z) :
    ∀ R : ℝ, 1 < R → ∀ᶠ k in atTop,
      ∀ r s v : ℝ, R⁻¹ ≤ r → r ≤ R → 0 ≤ s → s ≤ R → R⁻¹ ≤ v → v ≤ R →
      ∀ (q : Fin 3 → ℤ) (j z : ℤ),
        μ k {p | Submission.Lib.K4AffineMeshCaps.baseMesh (N k ^ (-r))
            (fun i : Fin 3 => x k p i.castSucc) = q ∧
          ⌊x k p 3 / N k ^ (-s)⌋ = j ∧ p ∈ C k v z} ≤
          ENNReal.ofReal (400*(K k)^2*N k^(-3*r-d*s)) * β k v z := by
  intro R hR
  obtain ⟨T,N₀,hRT,hT,hN₀,hraw⟩ := uniform_conditional_raw_hidden_caps_from_signal R hR.le
  have hRpos : 0 < R := by linarith
  have hInv : T⁻¹ ≤ R⁻¹ := inv_anti₀ hRpos hRT.le
  filter_upwards [hcap T hT, hNlim.eventually_ge_atTop N₀, hKN] with k hk hNk hKNk
  intro r s v hrl hrh hs0 hsh hvl hvh q j z
  apply hraw (N k) (K k) d hNk (hK k) hKNk hd hd1 Ω (μ k) (x k) (hx k)
    (P k) (hP k) (hgood k) (C k v z) (β k v z) (hβ k v z) ?_ r s
    ((inv_pos.mpr hRpos).le.trans hrl) hrh hs0 hsh q j
  intro u t hu₀ hu₁ ht₀ ht₁ q' j'
  exact hk u t v hu₀ hu₁ ht₀ ht₁ (hInv.trans hvl) (hvh.trans hRT.le) q' j' z

end

end Submission.Obl.k4_finite_affine_parent_sources.SignalUpgrade
