import Submission.Obl.k4_scalar_guarded_tangent_preparation.ReferenceLaws
import Submission.Obl.k4_scalar_guarded_tangent_preparation.WeightedSigned
import Submission.Obl.k4_scalar_guarded_tangent_preparation.ScalarGrid
import Submission.Obl.k4_scalar_guarded_tangent_preparation.RectangularReadout
import Submission.Obl.k4_scalar_guarded_tangent_preparation.MeshRounding
import Submission.Obl.k4_scalar_guarded_tangent_preparation.DefaultPalette

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Filter Set
open scoped ENNReal Topology

noncomputable section

/-- Finite original reference laws give half-mass restrictions and
all-real rectangular caps with one fixed predeletion palette per world. -/
theorem prepare_reference_caps
    (N B : ℕ → ℝ) (d S : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (σ : (k : ℕ) → Fin (W k) → Measure Incidence)
    (href : ReferenceLaws N B d S W ω σ) :
    ∃ (K : ℕ → ℝ) (ρ : (k : ℕ) → Fin (W k) → Measure Incidence)
      (π : (k : ℕ) → Fin (W k) → Measure ℝ),
      (∀ k g, ρ k g ≤ σ k g) ∧
      (∀ k, ENNReal.ofReal (1 / 2 : ℝ) *
        (∑ g, ENNReal.ofReal (ω k g) * σ k g univ) ≤
          ∑ g, ENNReal.ofReal (ω k g) * ρ k g univ) ∧
      RectangularCaps N K d S W ρ π := by
  classical
  rcases href with ⟨hN, hNt, hB, hBsub, hd, hd1, hS, hS1, hworld,
    m, n, X, Y, Z, qY, cY, α, π₀, hm, hmt, hα, hαt, hcode, hangular, hbudget⟩
  have hN0 (k) : 0 < N k := by linarith [hN k]
  have hN1 (k) : 1 ≤ N k := by linarith [hN k]
  have hB0 (k) : 0 ≤ B k := by linarith [hB k]
  have hm0 (k) : 0 < (m k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hm k))
  letI (k : ℕ) (g : Fin (W k)) : IsFiniteMeasure (σ k g) :=
    ⟨lt_of_le_of_lt ((hworld k).2.2 g) (by simp)⟩
  choose ρ hρ hmass hlikelihood using fun k => exists_weighted_signed_original_truncation
    (σ k) (ω k) (hworld k).1 (n k) (X k) (fun g => (hcode k g).1)
    (Y k) (Z k) (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (hα k).2) (hbudget k)
  let δ := fun k => N k ^ (-(m k : ℝ))
  let π := fun k (g : Fin (W k)) => if σ k g univ = 0 then unitPalette
    else fixedVelocityPalette (σ k g) (X k g) (Z k g) (δ k)
  let K := fun k => 108 * B k * N k ^ (α k + 3 / (m k : ℝ))
  have hδ (k) : 0 < δ k := Real.rpow_pos_of_pos (hN0 k) _
  have hpower (k) : 1 ≤ N k ^ (α k + 3 / (m k : ℝ)) :=
    Real.one_le_rpow (hN1 k) (add_nonneg (hα k).1.le (by positivity))
  have hK6 (k) : 6 * B k ≤ K k := by
    have h := mul_le_mul_of_nonneg_left (hpower k)
      (show 0 ≤ (108 : ℝ) * B k from mul_nonneg (by norm_num) (hB0 k))
    dsimp only [K]
    nlinarith [hB k]
  have hK1 (k) : 1 ≤ K k := by linarith [hK6 k, hB k]
  have hKexpanded (k) : K k = 108 * (N k ^ α k) * B k * N k ^ (3 / (m k : ℝ)) := by
    dsimp only [K]
    rw [Real.rpow_add (hN0 k)]
    ring
  have hvelcode (k) (g : Fin (W k)) :
      ∀ᵐ z ∂σ k g, Z k g (X k g z) = (⌊z.1.2 1 / δ k⌋ : ℤ) := by
    exact ((hcode k g).2.2.2.1).mono (fun _ hz => hz.1)
  have hπprob (k) (g : Fin (W k)) : IsProbabilityMeasure (π k g) := by
    dsimp only [π]
    split_ifs with hz
    · exact unitPalette_probability
    · exact fixedVelocityPalette_probability (σ k g) hz (X k g) (hcode k g).1 (Z k g) (hδ k)
  refine ⟨K, ρ, π, hρ, hmass, hK1,
    rectangular_slack_subpower hN1 hNt hB0 hBsub hαt hmt, hπprob, ?_⟩
  intro R hR
  filter_upwards [hmt.eventually (eventually_ge_atTop (R + 1)), hangular R hR]
    with k hmk hang
  intro g r s b hrl hru hsl hsu hbl hbu
  have hr0 : 0 ≤ r := (inv_pos.mpr (show 0 < R by linarith)).le.trans hrl
  have hs0 : 0 ≤ s := (inv_pos.mpr (show 0 < R by linarith)).le.trans hsl
  have hb0 : 0 ≤ b := (inv_pos.mpr (show 0 < R by linarith)).le.trans hbl
  have hwidth : 2 * δ k ≤ N k ^ (-b) := fine_velocity_width (hN k) (by linarith)
  by_cases hz : σ k g univ = 0
  · have hσzero : σ k g = 0 := Measure.measure_univ_eq_zero.mp hz
    have hρzero : ρ k g = 0 := le_antisymm ((hρ k g).trans_eq hσzero) bot_le
    refine ⟨?_, ?_, ?_⟩
    · intro e
      dsimp only [π]
      rw [ite_eq_left hz]
      exact (unitPalette_rpow_cap (hN1 k) hS1 hb0 e).trans
        (ENNReal.ofReal_le_ofReal (by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right (hK1 k)
            (Real.rpow_nonneg (hN0 k).le (-S * b))))
    · intro q c
      simp [hρzero]
    · intro q c e
      simp [hρzero]
  · have hπfixed : π k g = fixedVelocityPalette (σ k g) (X k g) (Z k g) (δ k) := by
      dsimp only [π]
      rw [ite_eq_right hz]
    have hV : Measurable (fun z : Incidence => z.1.2 1) :=
      (measurable_pi_apply 1).comp (measurable_snd.comp measurable_fst)
    have hmap := cond_map_of_original_marginal (σ k g) hz (fun z : Incidence => z.1.2 1)
      hV (π₀ k g) (hcode k g).2.2.1
    have hold : ∀ e : ℤ,
        ProbabilityTheory.cond (σ k g) univ {z | (⌊z.1.2 1 / (N k ^ (-b))⌋ : ℤ) = e} ≤
          ENNReal.ofReal (B k * N k ^ (-S * b)) := by
      intro e
      have hmeas : MeasurableSet {v : ℝ | (⌊v / (N k ^ (-b))⌋ : ℤ) = e} :=
        (measurable_id.div_const _).floor (measurableSet_singleton e)
      have h := hang g b hbl hbu e
      simp only [velocityBin] at h
      rw [← hmap, Measure.map_apply hV hmeas] at h
      exact h
    refine ⟨?_, ?_⟩
    · intro e
      rw [hπfixed]
      have h := fixedVelocityPalette_cap (σ k g) hz (X k g) (hcode k g).1 (Z k g)
        (fun z => z.1.2 1) (hδ k) hwidth (hvelcode k g)
        (ENNReal.ofReal (B k * N k ^ (-S * b))) hold e
      apply h.trans
      rw [show (6 : ℝ≥0∞) = ENNReal.ofReal (6 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_right (hK6 k) (Real.rpow_nonneg (hN0 k).le (-S * b))]
    · obtain ⟨jr, hjr, hjr'⟩ := exists_grid_depth_below (hm k) hr0 (by linarith)
      obtain ⟨js, hjs, hjs'⟩ := exists_grid_depth_below (hm k) hs0 (by linarith)
      let r₀ := (jr : ℝ) / (m k : ℝ)
      let s₀ := (js : ℝ) / (m k : ℝ)
      have hA : N k ^ (-r) ≤ N k ^ (-r₀) :=
        Real.rpow_le_rpow_of_exponent_le (hN1 k) (by dsimp only [r₀]; linarith)
      have hB' : N k ^ (-s) ≤ N k ^ (-s₀) :=
        Real.rpow_le_rpow_of_exponent_le (hN1 k) (by dsimp only [s₀]; linarith)
      have hround : N k ^ (-2 * r₀ - d * s₀) ≤
          N k ^ (3 / (m k : ℝ)) * N k ^ (-2 * r - d * s) := by
        simpa only [div_eq_mul_inv, one_mul] using rounded_rectangle_rpow (hN1 k) hd hd1.le
          (show 0 ≤ 1 / (m k : ℝ) by positivity)
          (show r - r₀ ≤ 1 / (m k : ℝ) by dsimp only [r₀]; linarith)
          (show s - s₀ ≤ 1 / (m k : ℝ) by dsimp only [s₀]; linarith)
      have h108R : 0 ≤ 108 * (N k ^ α k) :=
        mul_nonneg (by norm_num) (Real.rpow_nonneg (hN0 k).le _)
      have h108RB : 0 ≤ 108 * (N k ^ α k) * B k := mul_nonneg h108R (hB0 k)
      have hnum : 108 * (N k ^ α k) * B k * N k ^ (-2 * r₀ - d * s₀) ≤
          K k * N k ^ (-2 * r - d * s) := by
        calc
          _ ≤ (108 * (N k ^ α k) * B k) *
              (N k ^ (3 / (m k : ℝ)) * N k ^ (-2 * r - d * s)) :=
            mul_le_mul_of_nonneg_left hround h108RB
          _ = _ := by rw [hKexpanded]; ring
      have hcoeff : 27 * (4 * (ENNReal.ofReal (N k ^ α k) *
          ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀)))) ≤
          ENNReal.ofReal (K k * N k ^ (-2 * r - d * s)) := by
        calc
          _ = ENNReal.ofReal (108 * (N k ^ α k) * B k * N k ^ (-2 * r₀ - d * s₀)) := by
            rw [ENNReal.ofReal_mul h108RB,
              ENNReal.ofReal_mul h108R,
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108), ENNReal.ofReal_mul (hB0 k)]
            norm_num <;> ring
          _ ≤ _ := ENNReal.ofReal_le_ofReal hnum
      have hgrid : ∀ q c, σ k g {z | baseBin (N k) r₀ z = q ∧ hiddenBin (N k) s₀ z = c} ≤
          ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀)) :=
        scalar_grid_pure_cap (σ k g) (hN0 k) (B k) d r₀ s₀ (hB0 k) ((hcode k g).2.2.2.2 js)
      have hqr : ∀ᵐ z ∂σ k g, baseBin (N k) r₀ z = qY k g jr (Y k g (X k g z)) :=
        ((hcode k g).2.2.2.1).mono (fun _ hz => (hz.2 jr).1)
      have hcs : ∀ᵐ z ∂σ k g, hiddenBin (N k) s₀ z = cY k g js (Y k g (X k g z)) :=
        ((hcode k g).2.2.2.1).mono (fun _ hz => (hz.2 js).2)
      constructor
      · intro q c
        have h := rectangular_cap_from_coarse (ρ k g)
          (fun z : Incidence => ![z.2, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y z.1 z.2])
          (fun z => Submission.Obl.k4_scalar_linear_critical_extremizers.Split.x z.1 z.2) univ
          (Real.rpow_pos_of_pos (hN0 k) (-r)) (Real.rpow_pos_of_pos (hN0 k) (-s)) hA hB'
          (ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀)))
          (fun q c => by simpa only [univ_inter, funext_iff, baseBin, hiddenBin] using
            (hρ k g _).trans (hgrid q c)) q c
        have hRof : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (N k ^ α k) :=
          ENNReal.one_le_ofReal.mpr (by linarith [(hα k).2])
        have hinc : ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀)) ≤
            4 * (ENNReal.ofReal (N k ^ α k) * ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀))) := by
          calc
            _ = 1 * (1 * ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀))) := by ring
            _ ≤ _ := mul_le_mul (by norm_num) (mul_le_mul hRof le_rfl bot_le bot_le) bot_le bot_le
        have hread : ρ k g {z | baseBin (N k) r z = q ∧ hiddenBin (N k) s z = c} ≤
            27 * ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀)) := by
          simpa only [univ_inter, funext_iff, baseBin, hiddenBin] using h
        exact hread.trans ((mul_le_mul le_rfl hinc bot_le bot_le).trans hcoeff)
      · intro q c e
        have hgridJ : ∀ q c, ρ k g
            ({z | (⌊z.1.2 1 / (N k ^ (-b))⌋ : ℤ) = e} ∩
              {z | baseBin (N k) r₀ z = q ∧ hiddenBin (N k) s₀ z = c}) ≤
            (4 * (ENNReal.ofReal (N k ^ α k) * ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀)))) *
              π k g {v | velocityBin (N k) b v = e} := by
          intro q c
          have h := scalar_grid_joint_cap (σ k g) (ρ k g) hz (hρ k g) (X k g) (hcode k g).1
            (Y k g) (Z k g) (hN0 k) (hδ k) hwidth (Real.rpow_nonneg (hN0 k).le _)
            (hvelcode k g) (hlikelihood k g (ρ k g) le_rfl) (B k) d r₀ s₀ (hB0 k)
            ((hcode k g).2.2.2.2 js) (qY k g jr) (cY k g js) hqr hcs q c e
          rw [hπfixed]
          have hset : ({z | (⌊z.1.2 1 / (N k ^ (-b))⌋ : ℤ) = e} ∩
              {z | baseBin (N k) r₀ z = q ∧ hiddenBin (N k) s₀ z = c}) =
              {z | baseBin (N k) r₀ z = q ∧ hiddenBin (N k) s₀ z = c ∧
                (⌊z.1.2 1 / (N k ^ (-b))⌋ : ℤ) = e} := by
            ext z
            simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_comm, and_left_comm, and_assoc]
          rw [hset]
          simpa only [velocityBin] using h
        have h := rectangular_cap_from_coarse (ρ k g)
          (fun z : Incidence => ![z.2, Submission.Obl.k4_scalar_linear_critical_extremizers.Split.y z.1 z.2])
          (fun z => Submission.Obl.k4_scalar_linear_critical_extremizers.Split.x z.1 z.2)
          {z | (⌊z.1.2 1 / (N k ^ (-b))⌋ : ℤ) = e}
          (Real.rpow_pos_of_pos (hN0 k) (-r)) (Real.rpow_pos_of_pos (hN0 k) (-s)) hA hB'
          ((4 * (ENNReal.ofReal (N k ^ α k) * ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀)))) *
            π k g {v | velocityBin (N k) b v = e}) hgridJ q c
        have hbound := h.trans (by
          calc
            _ = (27 * (4 * (ENNReal.ofReal (N k ^ α k) * ENNReal.ofReal (B k * N k ^ (-2 * r₀ - d * s₀))))) *
                π k g {v | velocityBin (N k) b v = e} := by ring
            _ ≤ _ := mul_le_mul hcoeff le_rfl bot_le bot_le)
        convert hbound using 1
        congr 1
        ext z
        simp only [funext_iff, baseBin, hiddenBin, velocityBin, Set.mem_inter_iff, Set.mem_ofPred_eq,
          and_comm, and_left_comm, and_assoc]

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
