import Submission.Obl.k4_critical_switching_state_preparation.AsymptoticUpper

namespace Submission.Obl.k4_critical_switching_state_preparation

open Set MeasureTheory Filter Inherited

noncomputable section

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

/-- The same original-source count works for every finer positive mesh,
chosen after the asymptotic exponent and sample. -/
theorem Valid.eventually_source_pair_upper_mesh (h : cfg.Valid) {s v ζ : ℝ}
    (hs : 0 < s) (hv : 0 < v) (hvs : v ≤ s) (hsU : s + v ≤ cfg.U)
    (hζ : 0 < ζ) (hζs : ζ ≤ s) (hgap : 0 < cfg.κ * s - v - ζ) :
    ∀ᶠ k in atTop, ∀ (ω : ℝ), 0 < ω → ω ≤ cfg.N k ^ (-10 * s) →
      ∀ (ip : Fin (cfg.n k s)) (L : Fin 4 → ℝ) (source : Set (α × ℝ)),
      L 0 = 0 → (∀ e : Fin 3, |L e.succ| ≤ cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) →
      source ⊆ cfg.primitiveEvent k s ip L (cfg.N k ^ ζ * cfg.N k ^ (-s)) →
      (∀ p ∈ source, ∀ e : Fin 6, |cfg.b k p.1 e| ≤ 2 * cfg.K k) →
      (∀ p ∈ source, ∃ i : Fin (cfg.n k (s + v)),
        p.1 ∈ cfg.B k (s + v) i ∧ p.2 ∈ I (cfg.T k (s + v)) (cfg.j k (s + v) i) ∧
        cfg.A k (s + v) i ⊆ cfg.A k s ip ∧
        I (cfg.T k (s + v)) (cfg.j k (s + v) i) ⊆ I (cfg.T k s) (cfg.j k s ip)) →
      ∃ F : Finset (ℤ × (Fin 3 → ℤ)),
        (∀ u, u ∈ F ↔ ∃ p ∈ source,
          cfg.sourcePair k s ip L (cfg.N k ^ (-s - v)) (ω) p = u) ∧
        (F.card : ℝ) * (ω) ^ 3 ≤
          1073741824 * cfg.K k ^ 20 * cfg.N k ^ (cfg.d * v) := by
  classical
  filter_upwards [h.eventually_pair_parameters hs hv hvs hsU hζ hζs hgap]
    with k hk ω hω hωle ip L source hL₀ hL hsource hcoeff hcover
  obtain ⟨parent, child, hsmall, hmesh₀, hδbase₀⟩ := hk
  have hδbase := hωle.trans hδbase₀
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK := h.subpower.1 k
  have hH := cfg.timeLength_pos k s
  have hmesh : 3 * cfg.sourcePredictorSlope k s
      (cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) * ω ≤
      (4 * cfg.K k ^ 4) * cfg.N k ^ (-(s + v)) := by
    apply le_trans _ hmesh₀
    apply mul_le_mul_of_nonneg_left hωle
    dsimp [sourcePredictorSlope]
    positivity
  have hδ : 0 < ω := hω
  have hd : (cfg.N k ^ (-s) / cfg.N k ^ (-(s + v))) ^ cfg.d = cfg.N k ^ (cfg.d * v) := by
    have hr : cfg.N k ^ (-s) / cfg.N k ^ (-(s + v)) = cfg.N k ^ v := by
      rw [← Real.rpow_sub hN]
      congr 1
      ring
    rw [hr, ← Real.rpow_mul hN.le]
    congr 1
    ring
  by_cases hnonempty : source.Nonempty
  · obtain ⟨p₀, hp₀⟩ := hnonempty
    obtain ⟨i₀, hi₀, hit₀, hA₀, hI₀⟩ := hcover p₀ hp₀
    have hT := time_depth_le_of_block_subset _ _ hI₀
    have hHorder : cfg.timeLength k (s + v) ≤ cfg.timeLength k s := by
      unfold timeLength
      exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) hT)
    have hrel : cfg.timeLength k (s + v) / cfg.timeLength k s ≤ 1 :=
      (div_le_one (cfg.timeLength_pos k s)).mpr hHorder
    have hδrel : ω ≤
        (cfg.timeLength k (s + v) / cfg.timeLength k s) ^ 2 := by
      apply hδbase.trans
      apply pow_le_pow_left₀ (cfg.timeLength_pos k (s + v)).le _ 2
      exact (le_div_iff₀ (cfg.timeLength_pos k s)).mpr
        ((mul_le_mul_of_nonneg_left (cfg.timeLength_le_one k s)
          (cfg.timeLength_pos k (s + v)).le).trans_eq (mul_one _))
    have hM : 1 ≤ cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s := by
      have h₁ : 1 ≤ cfg.N k ^ ζ := Real.one_le_rpow (by linarith [h.scale k]) hζ.le
      have h₂ : 1 ≤ (2 : ℝ) ^ cfg.T k s := one_le_pow₀ (by norm_num)
      nlinarith
    obtain ⟨F, hF, hcard⟩ := parent.exists_source_pair_table h child ip (by linarith : 0 ≤ s + v)
      L (cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s) (cfg.N k ^ ζ * cfg.N k ^ (-s))
      (4 * cfg.K k ^ 4) (ω)
      (16 * cfg.K k * (cfg.N k ^ ζ * (2 : ℝ) ^ cfg.T k s))
      (by positivity) hL le_rfl hδ hrel hδrel hsmall hmesh source
      (fun p hp => hsource hp) hcover
      (fun p hp => midpointValue_bound k s ip L (cfg.K k) _ hK hM hL₀ hL p (hcoeff p hp))
    rw [hd] at hcard
    refine ⟨F, ?_, ?_⟩
    · simpa only [show -(s + v) = -s - v by ring] using hF
    · convert hcard using 1 <;> ring
  · refine ⟨∅, ?_, ?_⟩
    · have hsource_empty := Set.not_nonempty_iff_eq_empty.mp hnonempty
      simp [hsource_empty]
    · simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
      positivity


end Data

end

end Submission.Obl.k4_critical_switching_state_preparation
