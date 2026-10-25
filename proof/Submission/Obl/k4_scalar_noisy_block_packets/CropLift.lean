import Submission.Obl.k4_scalar_noisy_block_packets.DirectAngular
import Submission.Obl.k4_scalar_noisy_block_packets.CommonBlock
import Submission.Obl.k4_scalar_noisy_block_packets.PolynomialFormat
import Submission.Obl.k4_eligibility_sign_description.Families

namespace Submission.Obl.k4_scalar_noisy_block_packets

open MeasureTheory Set Filter MvPolynomial
open scoped ENNReal

noncomputable def liftPredictor (β u v : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  aeval ![X 0, C β⁻¹ * (X 1 - C u - X 0 * C v)] P

lemma liftPredictor_degree (β u v : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    (liftPredictor β u v P).totalDegree ≤ P.totalDegree := by
  apply k4_eligibility_sign_description.degree_aeval_le
  intro i
  fin_cases i
  · simp
  · apply (k4_eligibility_sign_description.degree_C_mul_le _ _).trans
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact linear_test_degree 1 u
    · simpa only [totalDegree_C, totalDegree_X, add_zero] using
        (totalDegree_mul (X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ) (C v))

lemma liftPredictor_eval (β u v t z : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    eval ![t, z] (liftPredictor β u v P) = eval ![t, (z - u - t * v) / β] P := by
  rw [liftPredictor, k4_eligibility_sign_description.eval_aeval_real]
  apply congrArg (fun q : Fin 2 → ℝ => eval q P)
  funext i
  fin_cases i <;> simp [div_eq_mul_inv, mul_comm]

lemma liftPredictor_adapted {β : ℝ} (hβ : β ≠ 0) (u v t w : ℝ)
    (P : MvPolynomial (Fin 2) ℝ) :
    eval ![t, u + t * v + β * w] (liftPredictor β u v P) = eval ![t, w] P := by
  rw [liftPredictor_eval]
  have hr : (u + t * v + β * w - u - t * v) / β = w := by
    field_simp [hβ]
    ring
  rw [hr]

/-- A finite exact packet system with its original world weights. -/
def MultiExactOutput (N L fL h ε : ℝ) (W : ℕ) (ω : Fin W → ℝ)
    (μ : Fin W → Measure Inc) : Prop :=
  ∃ (T n : ℕ) (γ : Fin n → Fin W) (j : Fin n → Fin (2 ^ T))
      (A : Fin n → Set Line) (P : Fin n → MvPolynomial (Fin 2) ℝ),
    (2 : ℝ) ^ T ≤ N ^ h ∧ (∀ i, MeasurableSet (A i)) ∧
    (∀ i i', i ≠ i' → γ i = γ i' → j i = j i' → Disjoint (A i) (A i')) ∧
    (∀ i, (P i).totalDegree ≤ 2 ∧
      (∀ t ∈ blockInterval T (j i), ∀ w ∈ Icc (-1 : ℝ) 1,
        |eval ![t, w] (P i)| ≤ N ^ ε) ∧
      (∀ l ∈ A i, ∀ t ∈ blockInterval T (j i),
        |x l t - eval ![t, y l t] (P i)| ≤ N ^ ε * N ^ (-L)) ∧
      ENNReal.ofReal (N ^ (-fL) / (N ^ ε * (2 : ℝ) ^ T)) ≤
        μ (γ i) (A i ×ˢ blockInterval T (j i))) ∧
    ENNReal.ofReal (N ^ (-ε)) ≤ ∑ g, ENNReal.ofReal (ω g) *
      μ g {p | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ blockInterval T (j i)}

/-- The data needed to return a finite packet system from conditional crop worlds to
its original incidence law. No normalized conditional bound is used in this transfer. -/
structure CropLiftData (W : ℕ) (β : ℝ) (μ : Measure Inc) (μc : Fin W → Measure Inc) where
  crop : Fin W → Set Line
  phi : Fin W → Line → Line
  prior : Fin W → ℝ
  u : Fin W → ℝ
  v : Fin W → ℝ
  measurable_crop : ∀ g, MeasurableSet (crop g)
  measurable_phi : ∀ g, Measurable (phi g)
  disjoint_crop : Pairwise (fun g g' => Disjoint (crop g) (crop g'))
  law : ∀ g Z, MeasurableSet Z → ENNReal.ofReal (prior g) * μc g Z =
    μ {p | p.1 ∈ crop g ∧ (phi g p.1, p.2) ∈ Z}
  x_eq : ∀ g l, l ∈ crop g → ∀ t, x (phi g l) t = x l t
  y_eq : ∀ g l, l ∈ crop g → ∀ t,
    y (phi g l) t = (y l t - u g - t * v g) / β
  y_bound : ∀ g l, l ∈ crop g → ∀ t ∈ Icc (0 : ℝ) 1, |y (phi g l) t| ≤ 2

/-- Pull conditional-world packets back to disjoint original trajectory assignments. -/
theorem noisyOutput_of_crop_exact
    (N d s m c ε L fL h δ β total : ℝ) (angular : Bool) (W : ℕ)
    (ω : Fin W → ℝ) (μ : Measure Inc) (μc : Fin W → Measure Inc)
    (D : CropLiftData W β μ μc)
    (hN : 1 ≤ N) (hβ : 0 < β) (hδ : δ ≤ ε) (hone : 2 ≤ N ^ ε)
    (hq : N ^ (-ε) ≤ (N ^ h)⁻¹)
    (hβlo : N ^ (-m) / N ^ ε ≤ β) (hβhi : β ≤ N ^ ε)
    (hang : angular = true → N ^ (-ε) ≤ β)
    (hcenters : ∀ g, |D.u g| + |D.v g| ≤ N ^ ε)
    (hprior : ∀ g, 0 ≤ D.prior g)
    (hweights : ∀ g, ENNReal.ofReal (D.prior g) =
      ENNReal.ofReal total * ENNReal.ofReal (ω g))
    (hfloor : ∀ g, c * (N ^ (-s)) ^ d * β / N ^ ε ≤ D.prior g * N ^ (-fL) / N ^ δ)
    (hmass : N ^ (-ε) * N ^ h ≤ total * N ^ (-δ))
    (herror : N ^ δ * N ^ (-L) ≤ N ^ ε * N ^ (-s))
    (hout : MultiExactOutput N L fL h δ W ω μc) :
    NoisyOutput N d s m c ε angular μ := by
  classical
  rcases hout with ⟨T, n, γ, j, A, P, hb, hA, hdis, hfit, hdense⟩
  let A' : Fin n → Set Line := fun i => D.crop (γ i) ∩ D.phi (γ i) ⁻¹' A i
  let P' : Fin n → MvPolynomial (Fin 2) ℝ :=
    fun i => liftPredictor β (D.u (γ i)) (D.v (γ i)) (P i)
  have hNpos : 0 < N := by linarith
  have hpow : N ^ δ ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN hδ
  have hAi (i : Fin n) : MeasurableSet (A' i) :=
    (D.measurable_crop (γ i)).inter ((D.measurable_phi (γ i)) (hA i))
  have htime (i : Fin n) (t : ℝ) (ht : t ∈ blockInterval T (j i)) :
      t ∈ Icc (0 : ℝ) 1 :=
    ⟨(blockLeft_nonneg T (j i)).trans ht.1, ht.2.trans (blockRight_le_one T (j i))⟩
  have hlaw (i : Fin n) :
      ENNReal.ofReal (D.prior (γ i)) * μc (γ i) (A i ×ˢ blockInterval T (j i)) =
        μ (A' i ×ˢ blockInterval T (j i)) := by
    rw [D.law (γ i) (A i ×ˢ blockInterval T (j i))
      ((hA i).prod (show MeasurableSet (blockInterval T (j i)) from measurableSet_Icc))]
    congr 1
    ext p
    simp only [A', mem_ofPred_eq, mem_prod, mem_inter_iff, mem_preimage, and_assoc]
  apply noisyOutput_of_blocks N d s m c ε β angular μ T n j A'
    (fun i => D.u (γ i)) (fun i => D.v (γ i)) P'
  · exact hq.trans (inv_anti₀ (by positivity) hb)
  · exact hβlo
  · exact hβhi
  · exact hang
  · exact hAi
  · intro i i' hne hji
    by_cases hγ : γ i = γ i'
    · exact Disjoint.mono inter_subset_right inter_subset_right
        (Set.disjoint_left.2 (fun l hi hi' =>
          Set.disjoint_left.1 (hdis i i' hne hγ hji) hi (hγ ▸ hi')))
    · exact (D.disjoint_crop hγ).mono inter_subset_left inter_subset_left
  · intro i
    rcases hfit i with ⟨hdeg, hnorm, happrox, _⟩
    refine ⟨hcenters _, (liftPredictor_degree _ _ _ _).trans hdeg, ?_, ?_⟩
    · intro t ht w hw
      simpa only [P', liftPredictor_adapted hβ.ne'] using (hnorm t ht w hw).trans hpow
    · intro l hl t ht
      have hy := D.y_eq (γ i) l hl.1 t
      have hyb := D.y_bound (γ i) l hl.1 t (htime i t ht)
      have hyabs : |y l t - D.u (γ i) - t * D.v (γ i)| ≤ 2 * β := by
        rw [hy, abs_div, abs_of_pos hβ] at hyb
        exact (div_le_iff₀ hβ).1 hyb
      refine ⟨hyabs.trans (by nlinarith), ?_⟩
      have herr := (happrox (D.phi (γ i) l) hl.2 t ht).trans herror
      simpa only [P', liftPredictor_eval, D.x_eq _ _ hl.1, hy] using herr
  · intro i
    rw [← hlaw i]
    have hnum := mul_le_mul_of_nonneg_right (hfloor (γ i))
      (le_of_lt (show 0 < ((2 : ℝ) ^ T)⁻¹ by positivity))
    have hnum' : blockLength T * c * (N ^ (-s)) ^ d * β / N ^ ε ≤
        D.prior (γ i) * (N ^ (-fL) / (N ^ δ * (2 : ℝ) ^ T)) := by
      convert hnum using 1 <;> (try unfold blockLength) <;> ring
    apply (ENNReal.ofReal_le_ofReal hnum').trans
    rw [ENNReal.ofReal_mul (hprior _)]
    exact mul_le_mul_of_nonneg_left (hfit i).2.2.2 (by positivity)
  · let Z : Fin W → Set Inc := fun g =>
      {p | ∃ i, γ i = g ∧ p.1 ∈ A i ∧ p.2 ∈ blockInterval T (j i)}
    let S : Fin W → Set Inc := fun g =>
      {p | p.1 ∈ D.crop g ∧ (D.phi g p.1, p.2) ∈ Z g}
    have hZ (g : Fin W) : MeasurableSet (Z g) := by
      simp only [Z, ofPred_exists, ofPred_and]
      apply MeasurableSet.iUnion
      intro i
      exact (MeasurableSet.const _).inter ((hA i).prod measurableSet_Icc)
    have hS (g : Fin W) : MeasurableSet (S g) :=
      ((D.measurable_crop g).preimage measurable_fst).inter
        (((D.measurable_phi g).comp measurable_fst |>.prodMk measurable_snd) (hZ g))
    have hSd : Pairwise (fun g g' => Disjoint (S g) (S g')) := by
      intro g g' hne
      exact Set.disjoint_left.2 fun p hp hp' =>
        Set.disjoint_left.1 (D.disjoint_crop hne) hp.1 hp'.1
    have hU : (⋃ g, S g) =
        {p | ∃ i, p.1 ∈ A' i ∧ p.2 ∈ blockInterval T (j i)} := by
      ext p
      simp only [mem_iUnion, S, Z, A', mem_ofPred_eq, mem_inter_iff, mem_preimage]
      constructor
      · rintro ⟨g, hcrop, i, hgi, hAi, ht⟩
        subst g
        exact ⟨i, ⟨hcrop, hAi⟩, ht⟩
      · rintro ⟨i, ⟨hcrop, hAi⟩, ht⟩
        exact ⟨γ i, hcrop, i, rfl, hAi, ht⟩
    have htotal : ENNReal.ofReal total * (∑ g, ENNReal.ofReal (ω g) * μc g (Z g)) =
        μ {p | ∃ i, p.1 ∈ A' i ∧ p.2 ∈ blockInterval T (j i)} := by
      calc
        _ = ∑ g, ENNReal.ofReal (D.prior g) * μc g (Z g) := by
          simp only [Finset.mul_sum, ← mul_assoc, ← hweights]
        _ = ∑ g, μ (S g) := Finset.sum_congr rfl fun g _ => D.law g _ (hZ g)
        _ = μ (⋃ g, S g) := by rw [measure_iUnion hSd hS]; simp [tsum_fintype]
        _ = _ := by rw [hU]
    apply (ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))).2
    apply le_trans _ ((mul_le_mul_of_nonneg_left hdense (by positivity)).trans_eq htotal)
    have he : ENNReal.ofReal ((2 : ℝ) ^ T) = (2 : ENNReal) ^ T := by
      rw [ENNReal.ofReal_pow (by norm_num)]
      norm_num
    have hnum := (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hNpos.le (-ε))).trans hmass
    simpa only [ENNReal.ofReal_mul (Real.rpow_nonneg hNpos.le (-ε)), he,
      ENNReal.ofReal_mul' (Real.rpow_nonneg hNpos.le (-δ)), Nat.cast_pow,
      Nat.cast_ofNat] using ENNReal.ofReal_le_ofReal hnum

end Submission.Obl.k4_scalar_noisy_block_packets
