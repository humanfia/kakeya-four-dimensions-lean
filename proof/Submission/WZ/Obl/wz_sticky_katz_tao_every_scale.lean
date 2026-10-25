-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_sticky_katz_tao_every_scale.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_nsp_random_rigid_copies
import Submission.WZ.Obl.wz_nsp_frostman_rigid_copies
import Submission.WZ.Obl.wz_frostman_rigid_copies_volume
import Submission.WZ.Obl.wz_essentially_distinct_tube_count
import Submission.WZ.Obl.wz_direction_density_transfer
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_sticky_katz_tao_every_scale`

Wang–Zahl Theorem 10.2 from Theorem 6.2 (the hypothesis, o015's statement), split along WZ §10:
* `wz_nsp_random_rigid_copies` — Lemma 10.6 (random rigid copies at one scale);
* `wz_nsp_frostman_rigid_copies` — Proposition 10.3 (given Lemma 10.6): rigid copies of a dense
  sub-family forming a family with the Frostman convex Wolff axioms at every scale;
* `wz_frostman_rigid_copies_volume` — Theorem 6.2 applied to the copies with transported shadings;
* `wz_essentially_distinct_tube_count` — `n δ⁶ ≤ C`, used for `δ` bounded below.

The glue below chooses the parameters, selects the tubes with large shading, and treats small and
large `δ` separately (see `PROOF.md`, §3).
-/

namespace WangZahlLot.Obl.wz_sticky_katz_tao_every_scale

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- The Katz–Tao convex Wolff axioms at every scale with error `K` (the hypothesis of the
conclusion of o018, with the error as a parameter). -/
def KTEvery (T : ℝ → Space → Space → Set Space) (δ K : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ < K * ρ₀ ∧ ∃ (N : ℕ) (y w : Fin N → Space)
    (f : Fin n → Fin N), (∀ k : Fin N, ‖w k‖ = 1) ∧
    (∀ i : Fin n, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧
    (∀ k k' : Fin N, ((Set.ncard {i : Fin n | f i = k} : ℕ) : ℝ) ≤
      K * ((Set.ncard {i : Fin n | f i = k'} : ℕ) : ℝ)) ∧
    (∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (((Set.ncard {k : Fin N | T ρ (y k) (w k) ⊆ W} : ℕ) : ℝ) * ρ ^ 2) ≤
        ENNReal.ofReal K * volume W)

/-- The Frostman convex Wolff axioms at every scale with error `K`, as in o015. -/
def FEvery (T : ℝ → Space → Space → Set Space) (d K : ℝ) (n : ℕ) (x v : Fin n → Space) : Prop :=
  ∀ ρ₀ : ℝ, d ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ K * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧
    ∃ (z w : Fin k → Space), (∀ j : Fin k, ‖w j‖ = 1) ∧
    (∀ j j' : Fin k, j ≠ j' → volume (T ρ (z j) (w j) ∩ T ρ (z j') (w j')) ≤
      (1 / 2 : ENNReal) * volume (T ρ (z j) (w j))) ∧
    (∀ i : Fin n, ∃! j : Fin k, T d (x i) (v i) ⊆ T ρ (z j) (w j)) ∧
    (∀ j : Fin k, ∃ i : Fin n, T d (x i) (v i) ⊆ T ρ (z j) (w j)) ∧
    (∀ j j' : Fin k, (((Set.ncard {i : Fin n | T d (x i) (v i) ⊆ T ρ (z j) (w j)} : ℕ) : ℝ)) ≤
      K * (((Set.ncard {i : Fin n | T d (x i) (v i) ⊆ T ρ (z j') (w j')} : ℕ) : ℝ))) ∧
    (∀ j : Fin k, ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal ((((Set.ncard {i : Fin n | T d (x i) (v i) ⊆ T ρ (z j) (w j) ∧
          T d (x i) (v i) ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤
        ENNReal.ofReal (K * (((Set.ncard {i : Fin n | T d (x i) (v i) ⊆ T ρ (z j) (w j)} :
          ℕ) : ℝ))) * volume W)

/-- `KTEvery` is monotone in the error. -/
theorem KTEvery.mono {T : ℝ → Space → Space → Set Space} {δ K K' : ℝ} {n : ℕ}
    {x v : Fin n → Space} (hδ : 0 ≤ δ) (hK : K ≤ K') (h : KTEvery T δ K n x v) :
    KTEvery T δ K' n x v := by
  intro ρ₀ h₁ h₂
  obtain ⟨ρ, hρ₁, hρ₂, N, y, w, f, hw, hcov, hbal, hkt⟩ := h ρ₀ h₁ h₂
  refine ⟨ρ, hρ₁, hρ₂.trans_le (mul_le_mul_of_nonneg_right hK (hδ.trans h₁)), N, y, w, f, hw,
    hcov, fun k k' => (hbal k k').trans (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _)),
    fun W hW => (hkt W hW).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hK) _)⟩

/-- `FEvery` is monotone in the error. -/
theorem FEvery.mono {T : ℝ → Space → Space → Set Space} {d K K' : ℝ} {n : ℕ}
    {x v : Fin n → Space} (hd : 0 ≤ d) (hK : K ≤ K') (h : FEvery T d K n x v) :
    FEvery T d K' n x v := by
  intro ρ₀ h₁ h₂
  obtain ⟨ρ, hρ₁, hρ₂, hρ₃, k, hk, z, w, hw, hdist, huniq, hne, hbal, hfr⟩ := h ρ₀ h₁ h₂
  refine ⟨ρ, hρ₁, hρ₂, hρ₃.trans (mul_le_mul_of_nonneg_right hK (hd.trans h₁)), k, hk, z, w, hw,
    hdist, huniq, hne, fun j j' => (hbal j j').trans (mul_le_mul_of_nonneg_right hK
      (Nat.cast_nonneg _)), fun j W hW => (hfr j W hW).trans (mul_le_mul_left
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg _))) _)⟩

/-- A unit tube of radius `δ ≤ 1/100` has volume at most `300 δ²`. -/
theorem tube_volume_le {δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1 / 100) (x v : Space) (hv : ‖v‖ = 1) :
    volume (Metric.thickening δ (segment ℝ x (x + v))) ≤ ENNReal.ofReal (300 * δ ^ 2) := by
  have h := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper x v hv
    (T := Set.Icc 0 1) subset_rfl (r := δ) (A := 1) hδ zero_le_one
    (fun s hs t ht => Real.dist_le_of_mem_Icc_01 hs ht)
  have hseg : (fun t : ℝ => x + t • v) '' Set.Icc 0 1 = segment ℝ x (x + v) := by
    rw [segment_eq_image']
    simp
  rw [hseg] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  nlinarith [sq_nonneg δ]

/-- Linear bookkeeping for the size of the selected sub-family. -/
theorem count_aux {X Y Z : ℝ} (h₁ : X ≤ 300 * Y + Z) (h₂ : Z ≤ X / 600) (hY : 0 ≤ Y) :
    X ≤ 600 * Y := by
  linarith

end WangZahlLot.Obl.wz_sticky_katz_tao_every_scale

theorem WangZahlLot.wz_sticky_katz_tao_every_scale : ∀ T, T = (fun (d : ℝ) (p q : LeanEval.Analysis.WangZahlKakeya.Space) => Metric.thickening d (segment ℝ p (p + q))) → (∀ ε : ℝ, 0 < ε → ∃ a : ℝ, 0 < a ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, T δ (x i) (v i) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ T δ (x i) (v i)) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ ≤ 1 ∧ ρ ≤ (δ ^ (-η)) * ρ₀ ∧ ∃ k : ℕ, 0 < k ∧ ∃ (z w : Fin k → LeanEval.Analysis.WangZahlKakeya.Space), (∀ j : Fin k, ‖w j‖ = 1) ∧ (∀ j j' : Fin k, j ≠ j' → MeasureTheory.volume (T ρ (z j) (w j) ∩ T ρ (z j') (w j')) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T ρ (z j) (w j))) ∧ (∀ i : Fin n, ∃! j : Fin k, T δ (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j : Fin k, ∃ i : Fin n, T δ (x i) (v i) ⊆ T ρ (z j) (w j)) ∧ (∀ j j' : Fin k, (((Set.ncard {i : Fin n | T δ (x i) (v i) ⊆ T ρ (z j) (w j)} : ℕ) : ℝ)) ≤ (δ ^ (-η)) * (((Set.ncard {i : Fin n | T δ (x i) (v i) ⊆ T ρ (z j') (w j')} : ℕ) : ℝ))) ∧ (∀ j : Fin k, ∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal ((((Set.ncard {i : Fin n | T δ (x i) (v i) ⊆ T ρ (z j) (w j) ∧ T δ (x i) (v i) ⊆ W} : ℕ) : ℝ)) * ρ ^ 2) ≤ ENNReal.ofReal ((δ ^ (-η)) * (((Set.ncard {i : Fin n | T δ (x i) (v i) ⊆ T ρ (z j) (w j)} : ℕ) : ℝ))) * MeasureTheory.volume W)) → ENNReal.ofReal (a * δ ^ ε) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i)) → ∀ ε : ℝ, 0 < ε → ∃ κ : ℝ, 0 < κ ∧ ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space) (Y : Fin n → Set LeanEval.Analysis.WangZahlKakeya.Space), 0 < n → (∀ i : Fin n, ‖v i‖ = 1) → (∀ i : Fin n, T δ (x i) (v i) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ i j : Fin n, i ≠ j → MeasureTheory.volume (T δ (x i) (v i) ∩ T δ (x j) (v j)) ≤ (1 / 2 : ENNReal) * MeasureTheory.volume (T δ (x i) (v i))) → (∀ i : Fin n, MeasurableSet (Y i)) → (∀ i : Fin n, Y i ⊆ T δ (x i) (v i)) → ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤ Finset.sum Finset.univ (fun i : Fin n => MeasureTheory.volume (Y i)) → (∀ ρ₀ : ℝ, δ ≤ ρ₀ → ρ₀ ≤ 1 → ∃ ρ : ℝ, ρ₀ ≤ ρ ∧ ρ < δ ^ (-η) * ρ₀ ∧ ∃ (N : ℕ) (y w : Fin N → LeanEval.Analysis.WangZahlKakeya.Space) (f : Fin n → Fin N), (∀ k : Fin N, ‖w k‖ = 1) ∧ (∀ i : Fin n, T δ (x i) (v i) ⊆ T ρ (y (f i)) (w (f i))) ∧ (∀ k k' : Fin N, ((Set.ncard {i : Fin n | f i = k} : ℕ) : ℝ) ≤ δ ^ (-η) * ((Set.ncard {i : Fin n | f i = k'} : ℕ) : ℝ)) ∧ (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {k : Fin N | T ρ (y k) (w k) ⊆ W} : ℕ) : ℝ) * ρ ^ 2) ≤ ENNReal.ofReal (δ ^ (-η)) * MeasureTheory.volume W)) → ENNReal.ofReal (κ * δ ^ ε * ((n : ℝ) * δ ^ 2)) ≤ MeasureTheory.volume (⋃ i : Fin n, Y i) := by
  classical
  intro T hT h015 ε hε
  open WangZahlLot.Obl.wz_sticky_katz_tao_every_scale in
  -- the children
  obtain ⟨a, ha, ηc, hηc, hC⟩ :=
    WangZahlLot.wz_frostman_rigid_copies_volume T hT _ rfl h015 (ε / 3) (by positivity)
  obtain ⟨ηb, hηb, δ₀, hδ₀, C, hC0, hB⟩ :=
    WangZahlLot.wz_nsp_frostman_rigid_copies T hT (WangZahlLot.wz_nsp_random_rigid_copies T hT)
      (min (ε / 3) ηc) (lt_min (by positivity) hηc)
  obtain ⟨Cd, hCd, hD⟩ := WangZahlLot.wz_essentially_distinct_tube_count
  -- the parameters
  set εb := min (ε / 3) ηc with hεb_def
  have hεb_le : εb ≤ ε / 3 := min_le_left _ _
  have hεb_ηc : εb ≤ ηc := min_le_right _ _
  set η := min (min ηb ηc) (min (ε / 3) 1) / 2 with hη_def
  have hη2 : 2 * η = min (min ηb ηc) (min (ε / 3) 1) := by rw [hη_def]; ring
  have hη : 0 < η := by
    have : 0 < min (min ηb ηc) (min (ε / 3) 1) :=
      lt_min (lt_min hηb hηc) (lt_min (by positivity) one_pos)
    linarith
  have hηb' : 2 * η ≤ ηb := hη2 ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hηc' : 2 * η ≤ ηc := hη2 ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hηε : 2 * η ≤ ε / 3 := hη2 ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hη1 : 2 * η ≤ 1 := hη2 ▸ (min_le_right _ _).trans (min_le_right _ _)
  set δs := min δ₀ ((1 / 600 : ℝ) ^ (1 / η)) with hδs_def
  have hδs : 0 < δs := lt_min hδ₀ (by positivity)
  set κ := min (a / (600 * C)) (δs ^ 7 / Cd) with hκ_def
  have hκ : 0 < κ := lt_min (by positivity) (by positivity)
  refine ⟨κ, hκ, η, hη, ?_⟩
  intro δ hδ hδ1 n x v Y hn hv hball hdist hmeas hsub hdense hKT
  have hδle1 : δ ≤ 1 := by linarith
  have hTi : ∀ i : Fin n, T δ (x i) (v i) = Metric.thickening δ (segment ℝ (x i) (x i + v i)) := by
    intro i; rw [hT]
  by_cases hsmall : δ ≤ δs
  · -- small `δ`: the Nikishin–Stein–Pisier copies and Theorem 6.2
    have hδδ₀ : δ ≤ δ₀ := hsmall.trans (min_le_left _ _)
    have hδη : δ ^ η ≤ 1 / 600 := by
      have h1 : δ ≤ (1 / 600 : ℝ) ^ (1 / η) := hsmall.trans (min_le_right _ _)
      calc δ ^ η ≤ ((1 / 600 : ℝ) ^ (1 / η)) ^ η := Real.rpow_le_rpow hδ.le h1 hη.le
        _ = 1 / 600 := by
          rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hη.ne', Real.rpow_one]
    have hδη_pos : 0 < δ ^ η := Real.rpow_pos_of_pos hδ η
    have h2η : δ ^ (2 * η) = δ ^ η * δ ^ η := by rw [two_mul, Real.rpow_add hδ]
    have hsq : δ ^ η * δ ^ η ≤ δ ^ η / 600 := by
      calc δ ^ η * δ ^ η ≤ δ ^ η * (1 / 600) := mul_le_mul_of_nonneg_left hδη hδη_pos.le
        _ = δ ^ η / 600 := by ring
    have hηc_le : δ ^ ηc ≤ δ ^ η / 600 :=
      ((Real.rpow_le_rpow_of_exponent_ge hδ hδle1 hηc').trans_eq h2η).trans hsq
    have hηb_le : δ ^ ηb ≤ δ ^ η / 600 :=
      ((Real.rpow_le_rpow_of_exponent_ge hδ hδle1 hηb').trans_eq h2η).trans hsq
    -- the tubes with large shading
    set G : Finset (Fin n) :=
      Finset.univ.filter (fun i => ENNReal.ofReal (δ ^ ηc * δ ^ 2) ≤ MeasureTheory.volume (Y i))
      with hG_def
    have hcount : (n : ℝ) * δ ^ η ≤ 600 * (G.card : ℝ) := by
      have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => ENNReal.ofReal (δ ^ ηc * δ ^ 2) ≤ MeasureTheory.volume (Y i))
        (fun i => MeasureTheory.volume (Y i))
      have hin : ∑ i ∈ G, MeasureTheory.volume (Y i) ≤
          ENNReal.ofReal ((G.card : ℝ) * (300 * δ ^ 2)) := by
        calc ∑ i ∈ G, MeasureTheory.volume (Y i) ≤ ∑ i ∈ G, ENNReal.ofReal (300 * δ ^ 2) := by
              apply Finset.sum_le_sum
              intro i _
              calc MeasureTheory.volume (Y i) ≤ MeasureTheory.volume (T δ (x i) (v i)) :=
                    MeasureTheory.measure_mono (hsub i)
                _ = MeasureTheory.volume (Metric.thickening δ (segment ℝ (x i) (x i + v i))) := by
                    rw [hTi i]
                _ ≤ ENNReal.ofReal (300 * δ ^ 2) := tube_volume_le hδ hδ1 (x i) (v i) (hv i)
          _ = ENNReal.ofReal ((G.card : ℝ) * (300 * δ ^ 2)) := by
              rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
                ENNReal.ofReal_natCast]
      have hout : ∑ i ∈ Finset.univ.filter
            (fun i => ¬ ENNReal.ofReal (δ ^ ηc * δ ^ 2) ≤ MeasureTheory.volume (Y i)),
            MeasureTheory.volume (Y i) ≤ ENNReal.ofReal ((n : ℝ) * (δ ^ ηc * δ ^ 2)) := by
        calc _ ≤ ∑ i ∈ Finset.univ.filter
              (fun i => ¬ ENNReal.ofReal (δ ^ ηc * δ ^ 2) ≤ MeasureTheory.volume (Y i)),
              ENNReal.ofReal (δ ^ ηc * δ ^ 2) := by
              apply Finset.sum_le_sum
              intro i hi
              exact (not_le.mp (Finset.mem_filter.mp hi).2).le
          _ ≤ ∑ i : Fin n, ENNReal.ofReal (δ ^ ηc * δ ^ 2) :=
              Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
          _ = ENNReal.ofReal ((n : ℝ) * (δ ^ ηc * δ ^ 2)) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
                ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      have htot : ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) ≤
          ENNReal.ofReal ((G.card : ℝ) * (300 * δ ^ 2) + (n : ℝ) * (δ ^ ηc * δ ^ 2)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
        calc ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2)
            ≤ ∑ i, MeasureTheory.volume (Y i) := hdense
          _ = _ := hsplit.symm
          _ ≤ _ := add_le_add hin hout
      have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htot
      have hδ2 : 0 < δ ^ 2 := by positivity
      have h2 : (n : ℝ) * (δ ^ ηc * δ ^ 2) ≤ (n : ℝ) * (δ ^ η / 600 * δ ^ 2) := by
        gcongr
      have hGnn : 0 ≤ (G.card : ℝ) * δ ^ 2 := by positivity
      have h1' : (n : ℝ) * δ ^ η * δ ^ 2 ≤
          300 * ((G.card : ℝ) * δ ^ 2) + (n : ℝ) * (δ ^ ηc * δ ^ 2) := by
        calc (n : ℝ) * δ ^ η * δ ^ 2 = δ ^ η * (n : ℝ) * δ ^ 2 := by ring
          _ ≤ _ := hreal
          _ = _ := by ring
      have h2' : (n : ℝ) * (δ ^ ηc * δ ^ 2) ≤ (n : ℝ) * δ ^ η * δ ^ 2 / 600 := by
        calc _ ≤ (n : ℝ) * (δ ^ η / 600 * δ ^ 2) := h2
          _ = _ := by ring
      have h3 : (n : ℝ) * δ ^ η * δ ^ 2 ≤ 600 * (G.card : ℝ) * δ ^ 2 := by
        calc (n : ℝ) * δ ^ η * δ ^ 2 ≤ 600 * ((G.card : ℝ) * δ ^ 2) := count_aux h1' h2' hGnn
          _ = _ := by ring
      exact le_of_mul_le_mul_right h3 hδ2
    have hGb : δ ^ ηb * (n : ℝ) ≤ (G.card : ℝ) := by
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      calc δ ^ ηb * (n : ℝ) ≤ δ ^ η / 600 * (n : ℝ) := mul_le_mul_of_nonneg_right hηb_le hn0
        _ = ((n : ℝ) * δ ^ η) / 600 := by ring
        _ ≤ (600 * (G.card : ℝ)) / 600 := by gcongr
        _ = (G.card : ℝ) := by ring
    -- Proposition 10.3
    have hKT' : KTEvery T δ (δ ^ (-ηb)) n x v :=
      KTEvery.mono (K := δ ^ (-η)) hδ.le
        (Real.rpow_le_rpow_of_exponent_ge hδ hδle1 (by linarith)) hKT
    obtain ⟨N, m, A, c, g, x', v', hm, hNG, hcopy, hdist', hF⟩ :=
      hB δ hδ hδδ₀ n x v hn (fun i => ⟨hv i, hball i⟩) hdist hKT' G hGb
    -- Theorem 6.2 on the copies
    have hF' : FEvery T δ (δ ^ (-ηc)) m x' v' :=
      FEvery.mono (K := δ ^ (-εb)) hδ.le
        (Real.rpow_le_rpow_of_exponent_ge hδ hδle1 (by linarith)) hF
    have hvol := hC δ hδ hδ1 n N m x v Y A c g x' v' hm (fun i => ⟨hv i, hmeas i, hsub i⟩)
      (fun s => ⟨(Finset.mem_filter.mp (hcopy s).1).2, (hcopy s).2.1, (hcopy s).2.2.1,
        (hcopy s).2.2.2⟩) hdist' hF'
    -- the arithmetic
    have hNpos : 0 < N := Fin.pos (g ⟨0, hm⟩)
    have hA : (N : ℝ) * (n : ℝ) * δ ^ 2 * δ ^ η ≤ 600 * C * δ ^ (-εb) := by
      have h1 := mul_le_mul_of_nonneg_left hcount (by positivity : (0 : ℝ) ≤ (N : ℝ) * δ ^ 2)
      calc (N : ℝ) * (n : ℝ) * δ ^ 2 * δ ^ η = ((N : ℝ) * δ ^ 2) * ((n : ℝ) * δ ^ η) := by ring
        _ ≤ ((N : ℝ) * δ ^ 2) * (600 * (G.card : ℝ)) := h1
        _ = 600 * ((N : ℝ) * (G.card : ℝ) * δ ^ 2) := by ring
        _ ≤ 600 * (C * δ ^ (-εb)) := by gcongr
        _ = 600 * C * δ ^ (-εb) := by ring
    have hinv : δ ^ η * δ ^ (-η) = 1 := by
      rw [← Real.rpow_add hδ]; simp
    have hB' : (N : ℝ) * (n : ℝ) * δ ^ 2 ≤ 600 * C * δ ^ (-εb) * δ ^ (-η) := by
      have h1 := mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg hδ.le (-η))
      calc (N : ℝ) * (n : ℝ) * δ ^ 2 = (N : ℝ) * (n : ℝ) * δ ^ 2 * (δ ^ η * δ ^ (-η)) := by
            rw [hinv, mul_one]
        _ = (N : ℝ) * (n : ℝ) * δ ^ 2 * δ ^ η * δ ^ (-η) := by ring
        _ ≤ _ := h1
    have hexp : δ ^ ε * δ ^ (-εb) * δ ^ (-η) ≤ δ ^ (ε / 3) := by
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
      apply Real.rpow_le_rpow_of_exponent_ge hδ hδle1
      linarith
    have hκa : κ ≤ a / (600 * C) := min_le_left _ _
    have hreal : (N : ℝ) * (κ * δ ^ ε * ((n : ℝ) * δ ^ 2)) ≤ a * δ ^ (ε / 3) := by
      calc (N : ℝ) * (κ * δ ^ ε * ((n : ℝ) * δ ^ 2))
          = κ * δ ^ ε * ((N : ℝ) * (n : ℝ) * δ ^ 2) := by ring
        _ ≤ a / (600 * C) * δ ^ ε * (600 * C * δ ^ (-εb) * δ ^ (-η)) := by
            gcongr
        _ = a * (δ ^ ε * δ ^ (-εb) * δ ^ (-η)) := by
            field_simp
        _ ≤ a * δ ^ (ε / 3) := by gcongr
    have hmul : (N : ENNReal) * ENNReal.ofReal (κ * δ ^ ε * ((n : ℝ) * δ ^ 2)) ≤
        (N : ENNReal) * MeasureTheory.volume (⋃ i : Fin n, Y i) := by
      calc (N : ENNReal) * ENNReal.ofReal (κ * δ ^ ε * ((n : ℝ) * δ ^ 2))
          = ENNReal.ofReal ((N : ℝ) * (κ * δ ^ ε * ((n : ℝ) * δ ^ 2))) := by
            rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        _ ≤ ENNReal.ofReal (a * δ ^ (ε / 3)) := ENNReal.ofReal_le_ofReal hreal
        _ ≤ _ := hvol
    exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hNpos.ne')
      (ENNReal.natCast_ne_top N)).mp hmul
  · -- large `δ`: count the tubes
    have hlarge : δs < δ := lt_of_not_ge hsmall
    have hn6 : (n : ℝ) * δ ^ 6 ≤ Cd :=
      hD δ hδ hδ1 n x v hv (fun i => by rw [← hTi i]; exact hball i)
        (fun i j hij => by rw [← hTi i, ← hTi j]; exact hdist i j hij)
    obtain ⟨i₀, hi₀⟩ : ∃ i, ENNReal.ofReal (δ ^ η * δ ^ 2) ≤ MeasureTheory.volume (Y i) := by
      by_contra hcon
      simp only [not_exists, not_le] at hcon
      have hlt := ENNReal.sum_lt_sum_of_nonempty (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun i _ => hcon i)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
      have heq : (n : ENNReal) * ENNReal.ofReal (δ ^ η * δ ^ 2) =
          ENNReal.ofReal (δ ^ η * (n : ℝ) * δ ^ 2) := by
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        ring_nf
      rw [heq] at hlt
      exact absurd hdense (not_le.mpr hlt)
    have hκ2 : κ ≤ δs ^ 7 / Cd := min_le_right _ _
    have hδε : δ ^ ε ≤ 1 := Real.rpow_le_one hδ.le hδle1 hε.le
    have hδη1 : δ ≤ δ ^ η := by
      calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
        _ ≤ δ ^ η := Real.rpow_le_rpow_of_exponent_ge hδ hδle1 (by linarith)
    have hδs7 : δs ^ 7 ≤ δ ^ 7 := pow_le_pow_left₀ hδs.le hlarge.le 7
    have key : δs ^ 7 / Cd * ((n : ℝ) * δ ^ 2) ≤ δ ^ 3 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hCd]
      have h1 : δs ^ 7 * ((n : ℝ) * δ ^ 2) * δ ^ 4 ≤ δ ^ 3 * Cd * δ ^ 4 := by
        calc δs ^ 7 * ((n : ℝ) * δ ^ 2) * δ ^ 4 = δs ^ 7 * ((n : ℝ) * δ ^ 6) := by ring
          _ ≤ δ ^ 7 * Cd := mul_le_mul hδs7 hn6 (by positivity) (by positivity)
          _ = δ ^ 3 * Cd * δ ^ 4 := by ring
      exact le_of_mul_le_mul_right h1 (by positivity)
    have hreal : κ * δ ^ ε * ((n : ℝ) * δ ^ 2) ≤ δ ^ η * δ ^ 2 := by
      calc κ * δ ^ ε * ((n : ℝ) * δ ^ 2) ≤ (δs ^ 7 / Cd) * 1 * ((n : ℝ) * δ ^ 2) := by
            gcongr
        _ = δs ^ 7 / Cd * ((n : ℝ) * δ ^ 2) := by ring
        _ ≤ δ ^ 3 := key
        _ = δ * δ ^ 2 := by ring
        _ ≤ δ ^ η * δ ^ 2 := by gcongr
    calc ENNReal.ofReal (κ * δ ^ ε * ((n : ℝ) * δ ^ 2)) ≤ ENNReal.ofReal (δ ^ η * δ ^ 2) :=
          ENNReal.ofReal_le_ofReal hreal
      _ ≤ MeasureTheory.volume (Y i₀) := hi₀
      _ ≤ MeasureTheory.volume (⋃ i : Fin n, Y i) :=
          MeasureTheory.measure_mono (Set.subset_iUnion Y i₀)
